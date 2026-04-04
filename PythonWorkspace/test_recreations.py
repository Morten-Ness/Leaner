#!/usr/bin/env python3
from __future__ import annotations

"""
Compile recreation theorem files and report which ones fail.

Usage model:
- point `--source` at a single `.lean` file, or
- point `--source` at any directory under `Mathlib/`

The script uses the same source-to-recreation routing as `generate_recreations.py`.
For each source `.lean` file, it looks for theorem files inside the mirrored
`Recreations/<relative-source-path>.lean/` directory and runs `lake env lean`
on each one, sequentially.

Modes:
- default: test the recreation files exactly as written
- `--fast`: replace `import Mathlib` with the source file's own imports plus an
  import of the source module itself

Example usage:
python3 PythonWorkspace/test_recreations.py --source Mathlib/LinearAlgebra/AffineSpace/Ceva.lean --fast
"""

import argparse
import re
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path

import generate_recreations as generate


REPO_ROOT = Path(__file__).resolve().parents[1]
LEAN_WORKSPACE_ROOT = REPO_ROOT / "LeanWorkspace"

# If false, compile recreation files exactly as written.
# If true, replace `import Mathlib` with the source file imports and the source module import.
PARAM_FAST = False


IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+([A-Za-z0-9_.']+)\s*$")


@dataclass(frozen=True)
class RecreationTarget:
    source_file: Path
    recreation_file: Path


def source_module_name(source_file: Path) -> str:
    mathlib_root = generate.find_mathlib_root(source_file)
    relative = source_file.resolve().relative_to(mathlib_root)
    parts = list(relative.parts)
    parts[-1] = source_file.stem
    return ".".join([mathlib_root.name, *parts])


def source_imports_for_fast_mode(source_file: Path) -> list[str]:
    imports: list[str] = []
    seen: set[str] = set()
    for line in source_file.read_text(encoding="utf-8").splitlines():
        match = IMPORT_RE.match(line.strip())
        if match is None:
            continue
        normalized = f"import {match.group(1)}"
        if normalized in seen:
            continue
        seen.add(normalized)
        imports.append(normalized)
    source_module_import = f"import {source_module_name(source_file)}"
    if source_module_import not in seen:
        imports.append(source_module_import)
    return imports


def rewrite_imports_for_fast_mode(content: str, source_file: Path) -> str:
    import_block = "\n".join(source_imports_for_fast_mode(source_file)) + "\n\n"
    lines = content.splitlines(keepends=True)
    index = 0
    while index < len(lines) and not lines[index].strip():
        index += 1
    if index < len(lines) and lines[index].strip() == "import Mathlib":
        index += 1
        while index < len(lines) and not lines[index].strip():
            index += 1
        return import_block + "".join(lines[index:])
    return import_block + content


def gather_targets(source: Path, output_root: Path) -> tuple[list[RecreationTarget], list[Path]]:
    targets: list[RecreationTarget] = []
    missing_recreation_dirs: list[Path] = []
    for source_file in generate.source_files_from_input(source):
        recreation_dir = generate.output_dir_for_source(source_file, output_root)
        if not recreation_dir.is_dir():
            missing_recreation_dirs.append(recreation_dir)
            continue
        for recreation_file in sorted(recreation_dir.glob("*.lean")):
            targets.append(
                RecreationTarget(
                    source_file=source_file,
                    recreation_file=recreation_file,
                )
            )
    return targets, missing_recreation_dirs


def temp_test_path(temp_root: Path, recreation_file: Path, output_root: Path) -> Path:
    relative = recreation_file.resolve().relative_to(output_root.resolve())
    destination = temp_root / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    return destination


def run_recreation_check(
    target: RecreationTarget,
    *,
    fast: bool,
    output_root: Path,
    temp_root: Path | None,
) -> bool:
    test_path = target.recreation_file
    if fast:
        assert temp_root is not None
        test_path = temp_test_path(temp_root, target.recreation_file, output_root)
        rewritten = rewrite_imports_for_fast_mode(
            target.recreation_file.read_text(encoding="utf-8"),
            target.source_file,
        )
        test_path.write_text(rewritten, encoding="utf-8")
    result = subprocess.run(
        ["lake", "env", "lean", str(test_path)],
        cwd=LEAN_WORKSPACE_ROOT,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    return result.returncode == 0


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compile recreation theorem files for a mathlib file or directory."
    )
    parser.add_argument("--source", type=Path, default=generate.DEFAULT_SOURCE)
    parser.add_argument("--output-root", type=Path, default=generate.RECREATIONS_ROOT)
    parser.add_argument("--fast", action="store_true", default=PARAM_FAST)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    output_root = args.output_root.resolve()
    targets, missing_recreation_dirs = gather_targets(args.source, output_root)

    for missing_dir in missing_recreation_dirs:
        print(f"MISSING_RECREATION_DIR {missing_dir}", flush=True)

    if not targets:
        print("No recreation files found to test.", flush=True)
        return 1 if missing_recreation_dirs else 0

    print(
        f"Testing {len(targets)} recreation file(s)"
        f"{' in fast mode' if args.fast else ''}..."
        ,
        flush=True,
    )

    failures: list[Path] = []
    temp_dir_cm = tempfile.TemporaryDirectory(prefix="recreation_fast_test_") if args.fast else None
    try:
        temp_root = Path(temp_dir_cm.name) if temp_dir_cm is not None else None
        for target in targets:
            ok = run_recreation_check(
                target,
                fast=args.fast,
                output_root=output_root,
                temp_root=temp_root,
            )
            if ok:
                continue
            failures.append(target.recreation_file)
            relative = target.recreation_file.resolve().relative_to(output_root)
            print(f"FAILED {relative}", flush=True)
    finally:
        if temp_dir_cm is not None:
            temp_dir_cm.cleanup()

    if not failures and not missing_recreation_dirs:
        print("All recreation files compiled successfully.", flush=True)
        return 0

    print(
        f"Finished with {len(failures)} failing file(s)"
        f" and {len(missing_recreation_dirs)} missing recreation directories.",
        flush=True,
    )
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
