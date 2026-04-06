#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
LEAN_WORKSPACE_ROOT = REPO_ROOT / "LeanWorkspace" / "LeanWorkspace"
VERIFIED_TARGETS_ROOT = LEAN_WORKSPACE_ROOT / "VerifiedTargets"
LLM_RESPONSES_ROOT = LEAN_WORKSPACE_ROOT / "LLMresponses"
LLM_RESPONSES_LEAN_ROOT = LLM_RESPONSES_ROOT / "Lean"
LLM_HINTS_ROOT = LLM_RESPONSES_ROOT / "Hints"
DEFAULT_OUTPUT_PATH = LLM_RESPONSES_ROOT / "finetune_hints.jsonl"

FIXED_USER_PREFIX = "Help me improve this Lean proof"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate chat-format JSONL finetuning data from LLMresponses/Hints, "
            "LLMresponses/Lean, and VerifiedTargets."
        )
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT_PATH,
        help=f"Destination JSONL path. Defaults to {DEFAULT_OUTPUT_PATH}",
    )
    return parser.parse_args()


def resolve_output(path: Path) -> Path:
    resolved = path if path.is_absolute() else (REPO_ROOT / path)
    return resolved.resolve()


def read_text_or_skip(path: Path) -> str | None:
    if not path.is_file():
        print(f"MISSING {path}", file=sys.stderr)
        return None
    return path.read_text(encoding="utf-8").rstrip() + "\n"


def hint_files() -> list[Path]:
    return sorted(p for p in LLM_HINTS_ROOT.glob("*.txt") if p.is_file())


def associated_lean_name(hint_file: Path) -> str:
    return f"{hint_file.stem}.lean"


def build_user_content(llm_response: str) -> str:
    return f"{FIXED_USER_PREFIX}\n\n{llm_response.rstrip()}\n"


def build_assistant_content(hints: str, verified_target: str) -> str:
    return f"{hints.rstrip()}\n\n{verified_target.rstrip()}\n"


def main() -> int:
    args = parse_args()
    output_path = resolve_output(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)

    written = 0
    skipped = 0

    with output_path.open("w", encoding="utf-8") as handle:
        for hint_file in hint_files():
            lean_name = associated_lean_name(hint_file)
            verified_path = VERIFIED_TARGETS_ROOT / lean_name
            llm_response_path = LLM_RESPONSES_LEAN_ROOT / lean_name

            hints = read_text_or_skip(hint_file)
            verified_target = read_text_or_skip(verified_path)
            llm_response = read_text_or_skip(llm_response_path)
            if hints is None or verified_target is None or llm_response is None:
                skipped += 1
                continue

            example = {
                "messages": [
                    {
                        "role": "user",
                        "content": build_user_content(llm_response),
                    },
                    {
                        "role": "assistant",
                        "content": build_assistant_content(hints, verified_target),
                    },
                ]
            }
            handle.write(json.dumps(example, ensure_ascii=False) + "\n")
            written += 1

    print(f"Wrote {written} JSONL example(s) to {output_path}")
    if skipped:
        print(f"Skipped {skipped} example(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
