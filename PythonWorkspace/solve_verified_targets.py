#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
import urllib.error
import urllib.request
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
LEAN_WORKSPACE_ROOT = REPO_ROOT / "LeanWorkspace"
VERIFIED_TARGETS_ROOT = LEAN_WORKSPACE_ROOT / "LeanWorkspace" / "VerifiedTargets"
LLM_SOLUTIONS_ROOT = LEAN_WORKSPACE_ROOT / "LeanWorkspace" / "LLMsolutions"
LLM_RESPONSES_TXT_ROOT = LEAN_WORKSPACE_ROOT / "LeanWorkspace" / "LLMresponsesTxt"
ATTEMPT_LOG_PATH = LLM_SOLUTIONS_ROOT / "results.json"

PARAM_MODEL = "gpt-5.4"
PARAM_MAX_ATTEMPTS = 3
PARAM_API_KEY_ENV = "OPENAI_API_KEY"
# Set to an integer like 5 to stop after that many completed files this run.
# Leave as None for no limit.
PARAM_MAX_SOLUTIONS: int | None = None

THEOREM_RE = re.compile(r"^\s*(?:protected\s+)?theorem\b", re.MULTILINE)
END_NAMESPACE_RE = re.compile(r"^\s*end(?:\s+\S.*)?\s*$")
CODE_BLOCK_RE = re.compile(r"```(?:lean)?\s*(.*?)```", re.DOTALL | re.IGNORECASE)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Iterate over VerifiedTargets, ask the OpenAI API to replace `sorry` "
            "with a Lean proof, and save successful or final failed attempts to "
            "LLMsolutions."
        )
    )
    parser.add_argument(
        "--source",
        type=Path,
        default=VERIFIED_TARGETS_ROOT,
        help=(
            "Optional file or directory inside VerifiedTargets. Defaults to the "
            "entire VerifiedTargets directory."
        ),
    )
    return parser.parse_args()


def resolve_source(source_arg: Path) -> Path:
    source = source_arg if source_arg.is_absolute() else (REPO_ROOT / source_arg)
    source = source.resolve()
    try:
        source.relative_to(VERIFIED_TARGETS_ROOT)
    except ValueError as exc:
        raise SystemExit(
            f"Source must be inside {VERIFIED_TARGETS_ROOT}, got: {source}"
        ) from exc
    if not source.exists():
        raise SystemExit(f"Source path does not exist: {source}")
    return source


def verified_target_files(source: Path) -> list[Path]:
    if source.is_file():
        if source.suffix != ".lean":
            raise SystemExit(f"Expected a .lean file, got: {source}")
        return [source]
    return sorted(p for p in source.rglob("*.lean") if p.is_file())


def split_trailing_namespace_endings(text: str) -> tuple[str, str]:
    lines = text.splitlines()
    tail: list[str] = []

    while lines and not lines[-1].strip():
        tail.append(lines.pop())

    while lines and END_NAMESPACE_RE.match(lines[-1]):
        tail.append(lines.pop())
        while lines and not lines[-1].strip():
            tail.append(lines.pop())

    tail.reverse()
    prefix = "\n".join(lines)
    suffix = "\n".join(tail)
    return prefix, suffix


def theorem_with_sorry(content: str) -> str:
    theorem_match = THEOREM_RE.search(content)
    if theorem_match is None:
        raise ValueError("Could not locate theorem declaration.")

    assign_index = content.find(":=", theorem_match.end())
    if assign_index == -1:
        raise ValueError("Could not locate theorem proof assignment ':='.")

    prefix = content[: assign_index + 2]
    _, suffix = split_trailing_namespace_endings(content[assign_index + 2 :])
    body = f"{prefix} sorry"
    if suffix.strip():
        return body + "\n\n" + suffix.strip() + "\n"
    return body + "\n"


def extract_lean_file_text(response_text: str) -> str:
    text = response_text.strip()
    code_match = CODE_BLOCK_RE.search(text)
    if code_match is not None:
        text = code_match.group(1).strip()
    return text.rstrip() + "\n"


def build_initial_prompt(filename: str, theorem_text: str) -> str:
    return "\n".join(
        [
            f"Filename: {filename}",
            "",
            "Fill in the Lean proof for this file.",
            "Return the complete .lean file content only.",
            "Do not use markdown fences.",
            "Preserve the theorem statement and surrounding context exactly if possible.",
            "Replace `sorry` with a valid Lean proof that compiles with Mathlib.",
            "",
            theorem_text.rstrip(),
        ]
    )


def build_retry_prompt(
    filename: str,
    theorem_text: str,
    previous_solution: str,
    lean_error: str,
    attempt_number: int,
) -> str:
    return "\n".join(
        [
            f"Filename: {filename}",
            f"Retry attempt: {attempt_number}",
            "",
            "The previous Lean solution did not compile.",
            "Return the complete corrected .lean file content only.",
            "Do not use markdown fences.",
            "Keep the theorem statement and surrounding context unchanged if possible.",
            "",
            "Original target file with `sorry`:",
            theorem_text.rstrip(),
            "",
            "Previous attempted solution:",
            previous_solution.rstrip(),
            "",
            "Lean compiler output:",
            lean_error.rstrip(),
        ]
    )


def call_openai(prompt: str, *, api_key: str) -> str:
    payload = {
        "model": PARAM_MODEL,
        "instructions": (
            "You are a precise Lean 4 and mathlib theorem prover. "
            "Return only the full .lean file content, with no markdown fences "
            "and no explanation."
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
        return output_text

    pieces: list[str] = []
    for item in raw.get("output", []):
        if item.get("type") != "message":
            continue
        for content in item.get("content", []):
            if content.get("type") == "output_text" and isinstance(content.get("text"), str):
                pieces.append(content["text"])

    if not pieces:
        raise RuntimeError(f"OpenAI API returned no text output: {raw}")
    return "\n".join(pieces)


def parse_lean_json_messages(raw_output: str) -> list[dict[str, object]]:
    messages: list[dict[str, object]] = []
    for line in raw_output.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        try:
            payload = json.loads(stripped)
        except json.JSONDecodeError:
            continue
        if isinstance(payload, dict) and "severity" in payload and "fileName" in payload:
            messages.append(payload)
    return messages


def source_span_excerpt(content: str, message: dict[str, object]) -> str:
    pos = message.get("pos")
    end_pos = message.get("endPos")
    if not isinstance(pos, dict):
        return ""

    line_no = pos.get("line")
    start_col = pos.get("column")
    if not isinstance(line_no, int) or not isinstance(start_col, int):
        return ""

    lines = content.splitlines()
    if line_no < 1 or line_no > len(lines):
        return ""

    line = lines[line_no - 1]
    start_idx = max(start_col - 1, 0)

    end_col: int | None = None
    if isinstance(end_pos, dict) and isinstance(end_pos.get("column"), int):
        end_col = end_pos["column"]

    if end_col is not None and end_col >= start_col:
        end_idx = max(end_col - 1, start_idx + 1)
    else:
        end_idx = start_idx + 1

    excerpt = line[start_idx:end_idx] or line[start_idx : start_idx + 1]
    underline = " " * start_idx + "^" * max(len(excerpt), 1)
    return "\n".join(
        [
            f"Source line {line_no}:",
            line,
            underline,
            f"Highlighted span: {excerpt}",
        ]
    )


def format_lean_output(raw_output: str, source_path: Path) -> str:
    messages = parse_lean_json_messages(raw_output)
    if not messages:
        return raw_output

    source_content = source_path.read_text(encoding="utf-8")
    formatted: list[str] = []
    for message in messages:
        severity = str(message.get("severity", "unknown")).upper()
        pos = message.get("pos")
        end_pos = message.get("endPos")

        line_no = "?"
        col_no = "?"
        end_line = "?"
        end_col = "?"
        if isinstance(pos, dict):
            line_no = str(pos.get("line", "?"))
            col_no = str(pos.get("column", "?"))
        if isinstance(end_pos, dict):
            end_line = str(end_pos.get("line", line_no))
            end_col = str(end_pos.get("column", col_no))
        else:
            end_line = line_no
            end_col = col_no

        data = str(message.get("data", "")).rstrip()
        formatted.extend(
            [
                f"{severity} {source_path.name}:{line_no}:{col_no}-{end_line}:{end_col}",
                data,
            ]
        )
        excerpt = source_span_excerpt(source_content, message)
        if excerpt:
            formatted.append(excerpt)
        formatted.append("")

    return "\n".join(formatted).rstrip()


def compile_candidate(content: str, filename: str) -> tuple[bool, str]:
    LLM_SOLUTIONS_ROOT.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        "w",
        encoding="utf-8",
        suffix=f".{filename}",
        prefix=".tmp_",
        dir=LLM_SOLUTIONS_ROOT,
        delete=False,
    ) as handle:
        handle.write(content)
        temp_path = Path(handle.name)

    try:
        relative_path = temp_path.relative_to(LEAN_WORKSPACE_ROOT)
        result = subprocess.run(
            ["lake", "env", "lean", "--json", str(relative_path)],
            cwd=LEAN_WORKSPACE_ROOT,
            capture_output=True,
            text=True,
        )
        raw_output = ((result.stdout or "") + (result.stderr or "")).strip()
        output = format_lean_output(raw_output, temp_path)
        return result.returncode == 0, output
    finally:
        temp_path.unlink(missing_ok=True)


def final_output_for_failure(content: str) -> str:
    return "FAIL\n" + content


def transcript_path_for(target_file: Path) -> Path:
    return LLM_RESPONSES_TXT_ROOT / f"{target_file.stem}.txt"


def load_results_log() -> dict[str, dict[str, object]]:
    if not ATTEMPT_LOG_PATH.exists():
        return {}
    try:
        raw = json.loads(ATTEMPT_LOG_PATH.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {}
    return raw if isinstance(raw, dict) else {}


def save_results_log(results: dict[str, dict[str, object]]) -> None:
    ATTEMPT_LOG_PATH.write_text(
        json.dumps(results, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def solve_file(target_file: Path, *, api_key: str) -> tuple[str, str, int, str]:
    theorem_text = theorem_with_sorry(target_file.read_text(encoding="utf-8"))
    prompt = build_initial_prompt(target_file.name, theorem_text)
    last_candidate = ""
    last_error = ""
    transcript_parts = [f"FILE: {target_file.name}", ""]

    for attempt in range(1, PARAM_MAX_ATTEMPTS + 1):
        transcript_parts.extend(
            [
                f"===== ATTEMPT {attempt} PROMPT =====",
                prompt.rstrip(),
                "",
            ]
        )
        raw_response = call_openai(prompt, api_key=api_key)
        candidate = extract_lean_file_text(raw_response)
        transcript_parts.extend(
            [
                f"===== ATTEMPT {attempt} RESPONSE =====",
                candidate.rstrip(),
                "",
            ]
        )
        ok, lean_output = compile_candidate(candidate, target_file.name)
        if ok:
            print(f"{attempt}. ATTEMPT PASS")
            transcript_parts.extend(
                [
                    f"===== ATTEMPT {attempt} LEAN OUTPUT =====",
                    "PASS",
                    "",
                ]
            )
            return candidate, "PASS", attempt, "\n".join(transcript_parts).rstrip() + "\n"

        last_candidate = candidate
        last_error = lean_output or "Lean failed without emitting compiler output."
        print(f"{attempt}. ATTEMPT FAIL")
        transcript_parts.extend(
            [
                f"===== ATTEMPT {attempt} LEAN OUTPUT =====",
                last_error.rstrip(),
                "",
            ]
        )
        prompt = build_retry_prompt(
            target_file.name,
            theorem_text,
            last_candidate,
            last_error,
            attempt + 1,
        )

    return (
        final_output_for_failure(last_candidate or theorem_text),
        "FAIL",
        PARAM_MAX_ATTEMPTS,
        "\n".join(transcript_parts).rstrip() + "\n",
    )


def main() -> int:
    args = parse_args()
    source = resolve_source(args.source)
    api_key = os.environ.get(PARAM_API_KEY_ENV)
    if not api_key:
        raise SystemExit(
            f"Missing {PARAM_API_KEY_ENV} in the environment. "
            "Set it before running this script."
        )

    LLM_SOLUTIONS_ROOT.mkdir(parents=True, exist_ok=True)
    LLM_RESPONSES_TXT_ROOT.mkdir(parents=True, exist_ok=True)
    results_log = load_results_log()
    targets = verified_target_files(source)

    completed = 0
    skipped = 0

    for target_file in targets:
        if PARAM_MAX_SOLUTIONS is not None and completed >= PARAM_MAX_SOLUTIONS:
            print(f"STOPPED reached PARAM_MAX_SOLUTIONS={PARAM_MAX_SOLUTIONS}")
            break

        destination = LLM_SOLUTIONS_ROOT / target_file.name
        if destination.exists():
            skipped += 1
            print(f"SKIPPED {target_file.name}")
            continue

        print(f"SOLVING {target_file.name}")
        try:
            final_content, status, attempts, transcript = solve_file(
                target_file, api_key=api_key
            )
        except Exception as exc:
            print(f"ERROR {target_file.name}: {exc}", file=sys.stderr)
            raise

        destination.write_text(final_content, encoding="utf-8")
        transcript_path_for(target_file).write_text(transcript, encoding="utf-8")
        results_log[target_file.name] = {
            "filename": target_file.name,
            "status": status,
            "attempts": attempts,
        }
        save_results_log(results_log)
        completed += 1

    print(
        f"Processed {len(targets)} file(s); completed {completed}; skipped {skipped}."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
