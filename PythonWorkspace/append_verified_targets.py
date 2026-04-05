#!/usr/bin/env python3

from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
VERIFIED_TARGETS_ROOT = REPO_ROOT / "LeanWorkspace" / "LeanWorkspace" / "VerifiedTargets"
APPENDED_ROOT = REPO_ROOT / "LeanWorkspace" / "LeanWorkspace" / "Appended"
APPENDED_FILE = APPENDED_ROOT / "Full.lean"

# Example usage:
# python3 PythonWorkspace/append_verified_targets.py


def verified_target_files() -> list[Path]:
    return sorted(
        path for path in VERIFIED_TARGETS_ROOT.glob("*.lean")
        if path.is_file()
    )


def strip_import_mathlib(content: str) -> str:
    kept_lines = [line for line in content.splitlines() if line.strip() != "import Mathlib"]
    return "\n".join(kept_lines).strip()


def appended_content() -> str:
    pieces: list[str] = ["import Mathlib"]
    for lean_file in verified_target_files():
        body = strip_import_mathlib(lean_file.read_text(encoding="utf-8"))
        if not body:
            continue
        pieces.append(f"section\n\n{body}\n\nend")
    return "\n\n".join(pieces) + "\n"


def main() -> None:
    APPENDED_ROOT.mkdir(parents=True, exist_ok=True)
    APPENDED_FILE.write_text(appended_content(), encoding="utf-8")
    print(f"Wrote {APPENDED_FILE}")


if __name__ == "__main__":
    main()
