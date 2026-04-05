#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path

import copy_verified_targets as copy_targets
import generate_recreations as generate


REPO_ROOT = Path(__file__).resolve().parents[1]
LEAN_WORKSPACE_ROOT = REPO_ROOT / "LeanWorkspace"
RECREATIONS_ROOT = generate.RECREATIONS_ROOT
VERIFIED_TARGETS_ROOT = copy_targets.VERIFIED_TARGETS_ROOT
APPENDED_ROOT = REPO_ROOT / "LeanWorkspace" / "LeanWorkspace" / "Appended"

# Source basenames in this list are skipped entirely.
PARAM_SKIP = {
    "AffineEquiv.lean",
}

# Theorem files whose proof bodies are shorter than this are ignored.
PARAM_MIN_PROOF_LENGTH = copy_targets.PARAM_MIN_PROOF_LENGTH

# Example usage:
# python3 PythonWorkspace/verify_targets_fast.py --source Mathlib/LinearAlgebra/AffineSpace
# python3 PythonWorkspace/verify_targets_fast.py --source Mathlib/LinearAlgebra/AffineSpace/Ceva.lean

# Ran until FAILED Algebra/Homology/Embedding/ExtendHomology.lean/extendHomologyIso_hom_homologyι.lean

THEOREM_NAME_RE = re.compile(r"^\s*(?:protected\s+)?theorem\s+([^\s(:{]+)", re.MULTILINE)
LEAN_ERROR_RE = re.compile(
    r"^(?P<path>.+\.lean):(?P<line>\d+):(?P<col>\d+):\s*error(?:\([^)]+\))?:",
    re.MULTILINE,
)


@dataclass(frozen=True)
class BatchChunk:
    theorem_file: Path
    start_line: int
    end_line: int


@dataclass(frozen=True)
class SourceBatchResult:
    source_file: Path
    verified: list[Path]
    failed: list[Path]
    skipped: list[Path]
    appended_file: Path | None


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate recreations, verify them in fast appended batches, and copy verified targets."
    )
    parser.add_argument("--source", type=Path, default=generate.DEFAULT_SOURCE)
    parser.add_argument("--verified-root", type=Path, default=VERIFIED_TARGETS_ROOT)
    parser.add_argument("--appended-root", type=Path, default=APPENDED_ROOT)
    return parser.parse_args()


def strip_import_mathlib(content: str) -> str:
    kept_lines = [line for line in content.splitlines() if line.strip() != "import Mathlib"]
    return "\n".join(kept_lines).strip()


def theorem_name_for(theorem_file: Path) -> str | None:
    text = theorem_file.read_text(encoding="utf-8")
    match = THEOREM_NAME_RE.search(text)
    if match is None:
        return None
    return match.group(1)


def appended_filename_for_source(source_file: Path) -> str:
    relative = source_file.resolve().relative_to(generate.find_mathlib_root(source_file))
    parts = list(relative.parts)
    parts[-1] = source_file.stem
    if len(parts) > 1:
        parts = parts[1:]
    return ".".join(parts) + ".lean"


def expected_theorem_files_for_source(source_file: Path) -> list[Path]:
    decls = generate.parse_source_file(source_file)
    target_theorems = generate.iter_target_theorems(decls)
    name_counts: dict[str, int] = {}
    for decl in target_theorems:
        name_counts[decl.name] = name_counts.get(decl.name, 0) + 1

    recreation_dir = generate.output_dir_for_source(source_file, RECREATIONS_ROOT)
    theorem_files: list[Path] = []
    for theorem in target_theorems:
        theorem_path = recreation_dir / generate.theorem_filename(theorem, name_counts)
        if theorem_path.is_file():
            theorem_files.append(theorem_path)
    return theorem_files


def filter_by_proof_length(theorem_files: list[Path]) -> tuple[list[Path], list[Path]]:
    kept: list[Path] = []
    skipped: list[Path] = []
    for theorem_file in theorem_files:
        proof_length = copy_targets.proof_length_for(theorem_file)
        if proof_length is None or proof_length < PARAM_MIN_PROOF_LENGTH:
            skipped.append(theorem_file)
            continue
        kept.append(theorem_file)
    return kept, skipped


def remove_duplicate_theorem_names(theorem_files: list[Path]) -> tuple[list[Path], list[Path]]:
    names_to_files: dict[str, list[Path]] = {}
    skipped: list[Path] = []
    for theorem_file in theorem_files:
        name = theorem_name_for(theorem_file)
        if name is None:
            skipped.append(theorem_file)
            continue
        names_to_files.setdefault(name, []).append(theorem_file)

    kept: list[Path] = []
    for name, files in names_to_files.items():
        if len(files) == 1:
            kept.extend(files)
            continue
        print(f"DUPLICATE_THEOREM_NAME {name}")
        for theorem_file in files:
            print(f"FAILED {theorem_file.resolve().relative_to(RECREATIONS_ROOT)}")
        skipped.extend(files)
    return sorted(kept), sorted(skipped)


def build_appended_batch(theorem_files: list[Path], destination: Path) -> list[BatchChunk]:
    destination.parent.mkdir(parents=True, exist_ok=True)
    lines = ["import Mathlib", ""]
    chunks: list[BatchChunk] = []

    for theorem_file in theorem_files:
        body = strip_import_mathlib(theorem_file.read_text(encoding="utf-8"))
        if not body:
            continue
        chunk_lines = ["section", ""] + body.splitlines() + ["", "end", ""]
        start_line = len(lines) + 1
        end_line = len(lines) + len(chunk_lines)
        lines.extend(chunk_lines)
        chunks.append(BatchChunk(theorem_file=theorem_file, start_line=start_line, end_line=end_line))

    destination.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")
    return chunks


def theorem_for_error_line(chunks: list[BatchChunk], line_number: int) -> Path | None:
    for chunk in chunks:
        if chunk.start_line <= line_number <= chunk.end_line:
            return chunk.theorem_file
    return None


def lean_error_theorems(output: str, appended_file: Path, chunks: list[BatchChunk]) -> list[Path]:
    failing: set[Path] = set()
    appended_resolved = appended_file.resolve()
    appended_str = str(appended_resolved)
    for match in LEAN_ERROR_RE.finditer(output):
        path = Path(match.group("path")).resolve()
        if path != appended_resolved and match.group("path") != appended_str:
            continue
        theorem_file = theorem_for_error_line(chunks, int(match.group("line")))
        if theorem_file is not None:
            failing.add(theorem_file)
    return sorted(failing)


def run_appended_check(appended_file: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["lake", "env", "lean", str(appended_file)],
        cwd=LEAN_WORKSPACE_ROOT,
        capture_output=True,
        text=True,
    )


def copy_verified_files(theorem_files: list[Path], verified_root: Path) -> None:
    verified_root.mkdir(parents=True, exist_ok=True)
    for theorem_file in theorem_files:
        target_name = copy_targets.verified_name_for(theorem_file)
        target_path = verified_root / target_name
        if target_path.exists():
            print(f"ALREADY_IN_VERIFIED {target_path.name}")
            continue
        shutil.copy2(theorem_file, target_path)
        print(f"VERIFIED {target_path.name}")


def verify_source_file(
    source_file: Path,
    *,
    verified_root: Path,
    appended_root: Path,
) -> SourceBatchResult:
    if source_file.name in PARAM_SKIP:
        print(f"SKIP_SOURCE {source_file.name}")
        return SourceBatchResult(source_file, [], [], [], None)

    generate.generate_for_source_file(source_file, RECREATIONS_ROOT)
    theorem_files = expected_theorem_files_for_source(source_file)
    theorem_files, skipped_for_length = filter_by_proof_length(theorem_files)
    theorem_files, skipped_for_duplicates = remove_duplicate_theorem_names(theorem_files)
    skipped = sorted(skipped_for_length + skipped_for_duplicates)

    if not theorem_files:
        return SourceBatchResult(source_file, [], [], skipped, None)

    appended_file = appended_root / appended_filename_for_source(source_file)
    active = theorem_files[:]
    failed: list[Path] = []

    while active:
        chunks = build_appended_batch(active, appended_file)
        result = run_appended_check(appended_file)
        if result.returncode == 0:
            copy_verified_files(active, verified_root)
            return SourceBatchResult(source_file, active, failed, skipped, appended_file)

        combined_output = (result.stdout or "") + (result.stderr or "")
        currently_failing = lean_error_theorems(combined_output, appended_file, chunks)
        if not currently_failing:
            currently_failing = active[:]
            print(f"UNMAPPED_FAILURES {source_file}")

        for theorem_file in currently_failing:
            relative = theorem_file.resolve().relative_to(RECREATIONS_ROOT)
            print(f"FAILED {relative}")

        failed.extend(currently_failing)
        failed_set = set(failed)
        active = [theorem_file for theorem_file in active if theorem_file not in failed_set]

    return SourceBatchResult(source_file, [], sorted(set(failed)), skipped, appended_file)


def main() -> int:
    args = parse_args()
    verified_root = args.verified_root.resolve()
    appended_root = args.appended_root.resolve()
    source_files = generate.source_files_from_input(args.source)

    processed = 0
    total_verified = 0
    total_failed = 0
    total_skipped = 0

    for source_file in source_files:
        result = verify_source_file(
            source_file,
            verified_root=verified_root,
            appended_root=appended_root,
        )
        processed += 1
        total_verified += len(result.verified)
        total_failed += len(result.failed)
        total_skipped += len(result.skipped)

    print(
        f"Processed {processed} source file(s); "
        f"verified {total_verified} theorem file(s); "
        f"failed {total_failed}; skipped {total_skipped}."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
