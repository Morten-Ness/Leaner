#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import shutil
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
RECREATIONS_ROOT = REPO_ROOT / "LeanWorkspace" / "LeanWorkspace" / "Recreations"
VERIFIED_TARGETS_ROOT = REPO_ROOT / "LeanWorkspace" / "LeanWorkspace" / "VerifiedTargets"

# Minimum trimmed proof-body length required for a theorem file to be copied.
# The proof body is measured from the first ":=" after the first theorem declaration
# up to EOF, ignoring trailing `end ...` namespace lines.
PARAM_MIN_PROOF_LENGTH = 35

# Example usage:
# python3 PythonWorkspace/copy_verified_targets.py --source LeanWorkspace/LeanWorkspace/Recreations/LinearAlgebra/AffineSpace/AffineEquiv.lean

THEOREM_RE = re.compile(r"^\s*(?:protected\s+)?theorem\b", re.MULTILINE)
END_NAMESPACE_RE = re.compile(r"^\s*end(?:\s+\S.*)?\s*$")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Flatten recreation theorem files into VerifiedTargets using the "
            "<source-file>.<theorem-file>.lean naming convention."
        )
    )
    parser.add_argument(
        "--source",
        required=True,
        help=(
            "Path inside Recreations to a theorem file, a source-file directory "
            "(for example AffineEquiv.lean), or any folder containing them."
        ),
    )
    parser.add_argument(
        "--output-root",
        default=str(VERIFIED_TARGETS_ROOT),
        help="Destination directory for flattened verified targets.",
    )
    return parser.parse_args()


def resolve_source(source_arg: str) -> Path:
    raw = Path(source_arg)
    source = raw if raw.is_absolute() else (REPO_ROOT / raw)
    source = source.resolve()
    try:
        source.relative_to(RECREATIONS_ROOT)
    except ValueError as exc:
        raise SystemExit(
            f"Source must be inside {RECREATIONS_ROOT}, got: {source}"
        ) from exc
    if not source.exists():
        raise SystemExit(f"Source path does not exist: {source}")
    return source


def theorem_files_under(source: Path) -> list[Path]:
    if source.is_file():
        if source.suffix != ".lean":
            raise SystemExit(f"Expected a .lean file, got: {source}")
        return [source]
    return sorted(p for p in source.rglob("*.lean") if p.is_file())


def source_file_dir_for(theorem_file: Path) -> Path | None:
    for parent in theorem_file.parents:
        if parent == RECREATIONS_ROOT.parent:
            break
        if parent.name.endswith(".lean"):
            return parent
    return None


def verified_name_for(theorem_file: Path) -> str:
    source_dir = source_file_dir_for(theorem_file)
    if source_dir is None:
        raise ValueError(
            f"Could not find a source .lean directory above theorem file: {theorem_file}"
        )
    source_stem = source_dir.name.removesuffix(".lean")
    return f"{source_stem}.{theorem_file.name}"


def trim_trailing_namespace_endings(text: str) -> str:
    lines = text.splitlines()
    while lines and not lines[-1].strip():
        lines.pop()
    while lines and END_NAMESPACE_RE.match(lines[-1]):
        lines.pop()
        while lines and not lines[-1].strip():
            lines.pop()
    return "\n".join(lines).strip()


def theorem_proof_text(content: str) -> str | None:
    theorem_match = THEOREM_RE.search(content)
    if theorem_match is None:
        return None
    assign_index = content.find(":=", theorem_match.end())
    if assign_index == -1:
        return None
    proof_text = content[assign_index + 2 :]
    return trim_trailing_namespace_endings(proof_text)


def proof_length_for(theorem_file: Path) -> int | None:
    proof_text = theorem_proof_text(theorem_file.read_text(encoding="utf-8"))
    if proof_text is None:
        return None
    return len(proof_text)


def main() -> None:
    args = parse_args()
    source = resolve_source(args.source)
    output_root = Path(args.output_root).resolve()
    output_root.mkdir(parents=True, exist_ok=True)

    copied = 0
    skipped = 0

    for theorem_file in theorem_files_under(source):
        proof_length = proof_length_for(theorem_file)
        if proof_length is None:
            print(f"SKIPPED {theorem_file}: could not locate theorem proof body")
            skipped += 1
            continue
        if proof_length < PARAM_MIN_PROOF_LENGTH:
            print(
                f"SKIPPED {theorem_file}: proof length {proof_length} is below "
                f"PARAM_MIN_PROOF_LENGTH={PARAM_MIN_PROOF_LENGTH}"
            )
            skipped += 1
            continue

        try:
            target_name = verified_name_for(theorem_file)
        except ValueError as err:
            print(f"SKIPPED {theorem_file}: {err}")
            skipped += 1
            continue

        target_path = output_root / target_name
        if target_path.exists():
            print(
                f"COLLISION {theorem_file}: target already exists at {target_path}"
            )
            skipped += 1
            continue

        shutil.copy2(theorem_file, target_path)
        copied += 1

    print(f"Copied {copied} file(s) to {output_root}")
    if skipped:
        print(f"Skipped {skipped} file(s)")


if __name__ == "__main__":
    main()
