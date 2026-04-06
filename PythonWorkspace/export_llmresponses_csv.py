#!/usr/bin/env python3

from __future__ import annotations

import argparse
import csv
import json
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
LEAN_WORKSPACE_ROOT = REPO_ROOT / "LeanWorkspace" / "LeanWorkspace"
VERIFIED_TARGETS_ROOT = LEAN_WORKSPACE_ROOT / "VerifiedTargets"
LLM_RESPONSES_ROOT = LEAN_WORKSPACE_ROOT / "LLMresponses"
LLM_RESPONSES_LEAN_ROOT = LLM_RESPONSES_ROOT / "Lean"
RESULTS_JSON_PATH = LLM_RESPONSES_ROOT / "results.json"
DEFAULT_OUTPUT_PATH = LLM_RESPONSES_ROOT / "proofs.csv"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Export results.json together with the matching VerifiedTargets and "
            "LLMresponses/Lean file contents to a CSV file."
        )
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT_PATH,
        help=f"Destination CSV path. Defaults to {DEFAULT_OUTPUT_PATH}",
    )
    return parser.parse_args()


def load_results() -> dict[str, dict[str, object]]:
    if not RESULTS_JSON_PATH.is_file():
        raise SystemExit(f"Missing results file: {RESULTS_JSON_PATH}")
    raw = json.loads(RESULTS_JSON_PATH.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise SystemExit(f"Expected a JSON object in {RESULTS_JSON_PATH}")
    return raw


def read_text_or_empty(path: Path) -> str:
    if not path.is_file():
        print(f"MISSING {path}", file=sys.stderr)
        return ""
    return path.read_text(encoding="utf-8")


def strip_lean_comment_lines(text: str) -> str:
    kept_lines = [line for line in text.splitlines() if not line.startswith("-- ")]
    if not kept_lines:
        return ""
    return "\n".join(kept_lines).rstrip() + "\n"


def main() -> int:
    args = parse_args()
    output_path = args.output if args.output.is_absolute() else (REPO_ROOT / args.output)
    output_path = output_path.resolve()
    output_path.parent.mkdir(parents=True, exist_ok=True)

    results = load_results()

    with output_path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "filename",
                "VerifiedTarget",
                "LLMresponse",
                "status",
                "attempts",
                "CharDiff",
            ],
            quoting=csv.QUOTE_ALL,
        )
        writer.writeheader()

        for key in sorted(results):
            entry = results[key]
            filename = str(entry.get("filename", key))
            status = str(entry.get("status", ""))
            attempts = entry.get("attempts", "")

            verified_path = VERIFIED_TARGETS_ROOT / filename
            llm_path = LLM_RESPONSES_LEAN_ROOT / filename
            verified_text = strip_lean_comment_lines(read_text_or_empty(verified_path))
            llm_text = strip_lean_comment_lines(read_text_or_empty(llm_path))

            writer.writerow(
                {
                    "filename": filename,
                    "VerifiedTarget": verified_text,
                    "LLMresponse": llm_text,
                    "CharDiff": len(llm_text) - len(verified_text),
                    "status": status,
                    "attempts": attempts,
                }
            )

    print(f"Wrote CSV for {len(results)} result entries to {output_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
