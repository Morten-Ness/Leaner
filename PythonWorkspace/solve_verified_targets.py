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
from urllib.parse import unquote, urlparse


REPO_ROOT = Path(__file__).resolve().parents[1]
LEAN_WORKSPACE_ROOT = REPO_ROOT / "LeanWorkspace"
VERIFIED_TARGETS_ROOT = LEAN_WORKSPACE_ROOT / "LeanWorkspace" / "VerifiedTargets"
LLM_RESPONSES_ROOT = LEAN_WORKSPACE_ROOT / "LeanWorkspace" / "LLMresponses"
LLM_SOLUTIONS_ROOT = LLM_RESPONSES_ROOT / "Lean"
LLM_RESPONSES_TXT_ROOT = LLM_RESPONSES_ROOT / "Txt"
ATTEMPT_LOG_PATH = LLM_RESPONSES_ROOT / "results.json"

PARAM_MODEL = "gpt-5.4"
PARAM_MAX_ATTEMPTS = 3
PARAM_API_KEY_ENV = "OPENAI_API_KEY"
# Set to an integer like 5 to stop after that many completed files this run.
# Leave as None for no limit.
PARAM_MAX_SOLUTIONS: int | None = None
SYSTEM_PROMPT = (
    "You are a precise Lean 4 and mathlib theorem prover. "
    "Return only the full .lean file content, with no markdown fences "
    "and no explanation."
)

THEOREM_RE = re.compile(r"^\s*(?:protected\s+)?theorem\b", re.MULTILINE)
END_NAMESPACE_RE = re.compile(r"^\s*end(?:\s+\S.*)?\s*$")
CODE_BLOCK_RE = re.compile(r"```(?:lean)?\s*(.*?)```", re.DOTALL | re.IGNORECASE)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Iterate over VerifiedTargets, ask the OpenAI API to replace `sorry` "
            "with a Lean proof, and save successful or final failed attempts to "
            "LLMresponses."
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
    lean_error: str,
    attempt_number: int,
) -> str:
    return "\n".join(
        [
            f"Retry attempt: {attempt_number}",
            "",
            "The previous Lean solution did not compile.",
            "Return a corrected complete .lean file content only.",
            "Do not use markdown fences.",
            "",
            "Lean compiler output for your previous answer:",
            lean_error.rstrip(),
        ]
    )


def make_message(role: str, text: str) -> dict[str, object]:
    return {
        "role": role,
        "content": text,
    }


def format_message_for_transcript(role: str, text: str) -> str:
    return "\n".join(
        [
            f"===== {role.upper()} =====",
            text.rstrip(),
            "",
        ]
    )


def call_openai(messages: list[dict[str, object]], *, api_key: str) -> str:
    payload = {
        "model": PARAM_MODEL,
        "input": messages,
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


def path_to_file_uri(path: Path) -> str:
    return path.resolve().as_uri()


def file_uri_to_path(uri: str) -> Path:
    parsed = urlparse(uri)
    if parsed.scheme != "file":
        raise ValueError(f"Expected file URI, got: {uri}")
    return Path(unquote(parsed.path))


class LeanServerClient:
    def __init__(self, workspace_root: Path, check_file: Path):
        self.workspace_root = workspace_root.resolve()
        self.check_file = check_file.resolve()
        self.uri = path_to_file_uri(self.check_file)
        self.version = 0
        self.next_id = 1
        self.is_open = False

        self.check_file.parent.mkdir(parents=True, exist_ok=True)
        self.check_file.write_text("", encoding="utf-8")

        self.proc = subprocess.Popen(
            ["lake", "env", "lean", "--server"],
            cwd=self.workspace_root,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
        )
        if self.proc.stdin is None or self.proc.stdout is None:
            raise RuntimeError("Failed to start Lean server with stdio pipes.")

        self._initialize()

    def close(self) -> None:
        if self.proc.poll() is None:
            try:
                if self.is_open:
                    self._send_notification(
                        "textDocument/didClose",
                        {"textDocument": {"uri": self.uri}},
                    )
                shutdown_id = self._next_id()
                self._send_request(shutdown_id, "shutdown", None)
                self._read_until_response(shutdown_id)
                self._send_notification("exit", None)
            except Exception:
                pass
            try:
                self.proc.kill()
            except Exception:
                pass
        self.check_file.unlink(missing_ok=True)

    def check_content(self, content: str) -> tuple[bool, str]:
        self.version += 1
        self.check_file.write_text(content, encoding="utf-8")

        if not self.is_open:
            self._send_notification(
                "textDocument/didOpen",
                {
                    "textDocument": {
                        "uri": self.uri,
                        "languageId": "lean",
                        "version": self.version,
                        "text": content,
                    }
                },
            )
            self.is_open = True
        else:
            self._send_notification(
                "textDocument/didChange",
                {
                    "textDocument": {
                        "uri": self.uri,
                        "version": self.version,
                    },
                    "contentChanges": [{"text": content}],
                },
            )

        wait_id = self._next_id()
        self._send_request(
            wait_id,
            "textDocument/waitForDiagnostics",
            {"uri": self.uri, "version": self.version},
        )
        last_diagnostics = self._read_until_response(wait_id)
        diagnostics = []
        if isinstance(last_diagnostics, dict):
            diagnostics = list(last_diagnostics.get("diagnostics", []))

        output = self._format_diagnostics(diagnostics, content, self.check_file.name)
        has_error = any(self._is_error_diagnostic(diagnostic) for diagnostic in diagnostics)
        return not has_error, output

    def _initialize(self) -> None:
        init_id = self._next_id()
        self._send_request(
            init_id,
            "initialize",
            {
                "processId": None,
                "rootUri": path_to_file_uri(self.workspace_root),
                "capabilities": {
                    "textDocument": {},
                    "workspace": {},
                    "lean": {"silentDiagnosticSupport": True},
                },
                "initializationOptions": {
                    "hasWidgets": False,
                },
            },
        )
        self._read_until_response(init_id)
        self._send_notification("initialized", {})

    def _next_id(self) -> int:
        current = self.next_id
        self.next_id += 1
        return current

    def _send_request(self, request_id: int, method: str, params: object) -> None:
        payload = {"jsonrpc": "2.0", "id": request_id, "method": method}
        if params is not None:
            payload["params"] = params
        self._send_message(payload)

    def _send_notification(self, method: str, params: object) -> None:
        payload = {"jsonrpc": "2.0", "method": method}
        if params is not None:
            payload["params"] = params
        self._send_message(payload)

    def _send_response(self, request_id: object, result: object) -> None:
        self._send_message({"jsonrpc": "2.0", "id": request_id, "result": result})

    def _send_message(self, payload: dict[str, object]) -> None:
        raw = json.dumps(payload).encode("utf-8")
        header = f"Content-Length: {len(raw)}\r\n\r\n".encode("ascii")
        assert self.proc.stdin is not None
        self.proc.stdin.write(header)
        self.proc.stdin.write(raw)
        self.proc.stdin.flush()

    def _read_message(self) -> dict[str, object]:
        assert self.proc.stdout is not None
        headers: dict[str, str] = {}
        while True:
            line = self.proc.stdout.readline()
            if not line:
                raise RuntimeError("Lean server closed its stdout unexpectedly.")
            if line in (b"\r\n", b"\n"):
                break
            header_line = line.decode("utf-8").strip()
            if ":" in header_line:
                key, value = header_line.split(":", 1)
                headers[key.strip().lower()] = value.strip()

        content_length = int(headers.get("content-length", "0"))
        body = self.proc.stdout.read(content_length)
        if len(body) != content_length:
            raise RuntimeError("Lean server returned a truncated message body.")
        payload = json.loads(body.decode("utf-8"))
        if not isinstance(payload, dict):
            raise RuntimeError(f"Unexpected Lean server payload: {payload}")
        return payload

    def _read_until_response(self, request_id: int) -> dict[str, object] | None:
        diagnostics_by_key: dict[str, object] = {}
        last_publish_meta: dict[str, object] | None = None
        while True:
            message = self._read_message()
            if "method" in message:
                method = message["method"]
                if message.get("id") is not None:
                    self._send_response(message["id"], None)
                    continue
                if method == "textDocument/publishDiagnostics":
                    params = message.get("params")
                    if isinstance(params, dict) and params.get("uri") == self.uri:
                        last_publish_meta = params
                        for diagnostic in params.get("diagnostics", []):
                            diagnostics_by_key[json.dumps(diagnostic, sort_keys=True)] = diagnostic
                    continue
                continue

            if message.get("id") == request_id:
                if "error" in message:
                    raise RuntimeError(f"Lean server request failed: {message['error']}")
                if last_publish_meta is None:
                    return None
                merged = dict(last_publish_meta)
                merged["diagnostics"] = list(diagnostics_by_key.values())
                return merged

    @staticmethod
    def _is_error_diagnostic(diagnostic: object) -> bool:
        if not isinstance(diagnostic, dict):
            return False
        severity = diagnostic.get("severity")
        return severity == 1 or severity == "error"

    @staticmethod
    def _severity_name(severity: object) -> str:
        if severity == 1:
            return "ERROR"
        if severity == 2:
            return "WARNING"
        if severity == 3:
            return "INFORMATION"
        if severity == 4:
            return "HINT"
        return str(severity).upper() if severity is not None else "UNKNOWN"

    def _format_diagnostics(
        self, diagnostics: list[object], content: str, display_name: str
    ) -> str:
        if not diagnostics:
            return ""

        lines = content.splitlines()
        formatted: list[str] = []
        for diagnostic in diagnostics:
            if not isinstance(diagnostic, dict):
                continue
            range_info = diagnostic.get("range")
            if not isinstance(range_info, dict):
                continue
            start = range_info.get("start")
            end = range_info.get("end")
            if not isinstance(start, dict) or not isinstance(end, dict):
                continue

            line_no = int(start.get("line", 0)) + 1
            col_no = int(start.get("character", 0)) + 1
            end_line = int(end.get("line", start.get("line", 0))) + 1
            end_col = int(end.get("character", start.get("character", 0))) + 1
            severity = self._severity_name(diagnostic.get("severity"))
            message = str(diagnostic.get("message", "")).rstrip()
            formatted.extend(
                [
                    f"{severity} {display_name}:{line_no}:{col_no}-{end_line}:{end_col}",
                    message,
                ]
            )

            if 1 <= line_no <= len(lines):
                line = lines[line_no - 1]
                start_idx = max(col_no - 1, 0)
                end_idx = max(end_col - 1, start_idx + 1)
                excerpt = line[start_idx:end_idx] or line[start_idx : start_idx + 1]
                underline = " " * start_idx + "^" * max(len(excerpt), 1)
                formatted.extend(
                    [
                        f"Source line {line_no}:",
                        line,
                        underline,
                        f"Highlighted span: {excerpt}",
                    ]
                )
            formatted.append("")

        return "\n".join(formatted).rstrip()


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


def solve_file(
    target_file: Path, *, api_key: str, lean_client: LeanServerClient
) -> tuple[str, str, int, str]:
    theorem_text = theorem_with_sorry(target_file.read_text(encoding="utf-8"))
    last_candidate = ""
    last_error = ""
    transcript_parts = [f"FILE: {target_file.name}", ""]
    conversation: list[dict[str, object]] = [
        make_message("system", SYSTEM_PROMPT),
        make_message("user", build_initial_prompt(target_file.name, theorem_text)),
    ]
    transcript_parts.append(format_message_for_transcript("system", SYSTEM_PROMPT))
    transcript_parts.append(
        format_message_for_transcript(
            "user", build_initial_prompt(target_file.name, theorem_text)
        )
    )

    for attempt in range(1, PARAM_MAX_ATTEMPTS + 1):
        raw_response = call_openai(conversation, api_key=api_key)
        candidate = extract_lean_file_text(raw_response)
        conversation.append(make_message("assistant", candidate))
        transcript_parts.append(format_message_for_transcript("assistant", candidate))
        ok, lean_output = lean_client.check_content(candidate)
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
        retry_message = build_retry_prompt(last_error, attempt + 1)
        conversation.append(make_message("user", retry_message))
        transcript_parts.append(format_message_for_transcript("user", retry_message))

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
    lean_client = LeanServerClient(
        LEAN_WORKSPACE_ROOT,
        LLM_SOLUTIONS_ROOT / ".LspCheck.lean",
    )

    completed = 0
    skipped = 0

    try:
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
                    target_file,
                    api_key=api_key,
                    lean_client=lean_client,
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
    finally:
        lean_client.close()

    print(
        f"Processed {len(targets)} file(s); completed {completed}; skipped {skipped}."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
