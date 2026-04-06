#!/usr/bin/env python3

from __future__ import annotations

import argparse
import csv
import json
import os
import sys
import urllib.error
import urllib.request
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
LEAN_WORKSPACE_ROOT = REPO_ROOT / "LeanWorkspace" / "LeanWorkspace"
VERIFIED_TARGETS_ROOT = LEAN_WORKSPACE_ROOT / "VerifiedTargets"
LLM_RESPONSES_ROOT = LEAN_WORKSPACE_ROOT / "LLMresponses"
LLM_RESPONSES_LEAN_ROOT = LLM_RESPONSES_ROOT / "Lean"
LLM_HINTS_ROOT = LLM_RESPONSES_ROOT / "Hints"
PROOFS_CSV_PATH = LLM_RESPONSES_ROOT / "proofs.csv"

PARAM_MODEL = "gpt-5.4"
PARAM_API_KEY_ENV = "OPENAI_API_KEY"
PARAM_OVERWRITE = False


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate short first-person hint files from filtered proof pairs in "
            "LLMresponses/proofs.csv."
        )
    )
    parser.add_argument(
        "--csv",
        type=Path,
        default=PROOFS_CSV_PATH,
        help=f"CSV file to read. Defaults to {PROOFS_CSV_PATH}",
    )
    parser.add_argument(
        "--max-files",
        type=int,
        default=None,
        help="Optional cap on the number of hint files to generate in this run.",
    )
    return parser.parse_args()


def resolve_path(path: Path) -> Path:
    resolved = path if path.is_absolute() else (REPO_ROOT / path)
    return resolved.resolve()


def csv_rows(csv_path: Path) -> list[dict[str, str]]:
    with csv_path.open("r", encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle))


def is_false_string(value: str | None) -> bool:
    return (value or "").strip().lower() == "false"


def parse_int(value: str | None) -> int | None:
    try:
        return int((value or "").strip())
    except ValueError:
        return None


def filtered_rows(rows: list[dict[str, str]]) -> list[dict[str, str]]:
    kept: list[dict[str, str]] = []
    for row in rows:
        if (row.get("status") or "").strip() != "PASS":
            continue
        if not is_false_string(row.get("SelfRef")):
            continue
        char_diff = parse_int(row.get("CharDiff"))
        if char_diff is None or char_diff < 20:
            continue
        filename = (row.get("filename") or "").strip()
        if not filename:
            continue
        kept.append(row)
    return kept


def read_text_or_die(path: Path) -> str:
    if not path.is_file():
        raise SystemExit(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def hint_filename_for(filename: str) -> str:
    return str(Path(filename).with_suffix(".txt").name)


def build_prompt(verified_target: str, llm_response: str) -> str:
    return (
        'I will show you two Lean math proofs. The first is the target "Optimal" proof. '
        "The 2nd is a suboptimal proof. You will help someone try to improve the 2nd proof.\n\n"
        "Now, assume one has access to the 2nd proof. You are now going to guide them to improve "
        "the proof, however, you cannot give them the ideal proof directly. You are only allowed "
        "to supply a maximum of 2 quick suggestions for patterns to think about. 1 short sentence "
        'for each. What would you suggest to help guide? If the 2 proofs are already very similar, '
        'just respond "No meaningful room for improvement here". \n\n'
        "In your answer, provide only the tips. No extra commentary. Also, give the tips in first "
        'person, as if you are reasoning yourself. Example "I\'ll make things easier with...", '
        '"This proof is simpler when..."\n\n'
        "Ideal proof:\n\n"
        f"{verified_target.rstrip()}\n\n"
        "Other proof:\n\n"
        f"{llm_response.rstrip()}\n"
    )


def call_openai(prompt: str, *, api_key: str) -> str:
    payload = {
        "model": PARAM_MODEL,
        "instructions": (
            "Return only the requested hint text. Do not use markdown fences. "
            "Do not include any commentary before or after the hints."
        ),
        "input": prompt,
    }
    request = urllib.request.Request(
        "https://api.openai.com/v1/responses",
        data=json.dumps(payload).encode("utf-8"),
        headers={
            "Content-Type": "application/json",
            "Authorization": f"Bearer {api_key}",
        },
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=300) as response:
            raw = json.loads(response.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"OpenAI API request failed: {exc.code} {detail}") from exc
    except urllib.error.URLError as exc:
        raise RuntimeError(f"OpenAI API connection failed: {exc}") from exc

    output_text = raw.get("output_text")
    if isinstance(output_text, str) and output_text.strip():
        return output_text.rstrip() + "\n"

    pieces: list[str] = []
    for item in raw.get("output", []):
        if item.get("type") != "message":
            continue
        for content in item.get("content", []):
            if content.get("type") == "output_text" and isinstance(content.get("text"), str):
                pieces.append(content["text"])

    if not pieces:
        raise RuntimeError(f"OpenAI API returned no text output: {raw}")
    return "\n".join(pieces).rstrip() + "\n"


def main() -> int:
    args = parse_args()
    api_key = os.environ.get(PARAM_API_KEY_ENV)
    if not api_key:
        raise SystemExit(
            f"Missing {PARAM_API_KEY_ENV} in the environment. Set it before running this script."
        )

    csv_path = resolve_path(args.csv)
    if not csv_path.is_file():
        raise SystemExit(f"Missing CSV file: {csv_path}")

    LLM_HINTS_ROOT.mkdir(parents=True, exist_ok=True)

    rows = filtered_rows(csv_rows(csv_path))
    generated = 0
    skipped = 0

    for row in rows:
        if args.max_files is not None and generated >= args.max_files:
            break

        filename = row["filename"].strip()
        verified_path = VERIFIED_TARGETS_ROOT / filename
        llm_path = LLM_RESPONSES_LEAN_ROOT / filename
        output_path = LLM_HINTS_ROOT / hint_filename_for(filename)

        if output_path.exists() and not PARAM_OVERWRITE:
            skipped += 1
            print(f"SKIPPED {output_path.name}")
            continue

        verified_text = read_text_or_die(verified_path)
        llm_text = read_text_or_die(llm_path)
        prompt = build_prompt(verified_text, llm_text)
        hint_text = call_openai(prompt, api_key=api_key)
        output_path.write_text(hint_text, encoding="utf-8")
        generated += 1
        print(f"WROTE {output_path.name}")

    print(f"Filtered {len(rows)} row(s); generated {generated}; skipped {skipped}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
