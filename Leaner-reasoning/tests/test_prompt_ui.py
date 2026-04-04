import os
import io
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")


def test_prompt_padding_lines_parses_and_clamps():
    from nano_claude import _prompt_padding_lines

    assert _prompt_padding_lines({"prompt_padding_lines": 2}) == 2
    assert _prompt_padding_lines({"prompt_padding_lines": "3"}) == 3
    assert _prompt_padding_lines({"prompt_padding_lines": -5}) == 0
    assert _prompt_padding_lines({"prompt_padding_lines": "oops"}) == 0


def test_build_prompt_ui_without_padding_keeps_old_style():
    from nano_claude import build_prompt_ui

    prelude, prompt = build_prompt_ui(
        "nano-claude-code",
        {"prompt_padding_lines": 0},
        interactive=True,
        term_columns=60,
    )

    assert prelude == ""
    assert "[nano-claude-code]" in prompt
    assert "\n[" in prompt


def test_build_prompt_ui_with_padding_adds_divider_and_cursor_reserve():
    from nano_claude import build_prompt_ui

    prelude, prompt = build_prompt_ui(
        "nano-claude-code",
        {"prompt_padding_lines": 2},
        interactive=True,
        term_columns=40,
    )

    assert "─" * 38 in prelude
    assert "\033[2A" in prelude
    assert "[nano-claude-code]" in prompt
    assert "\n[" not in prompt


def test_build_prompt_ui_disables_padding_for_non_interactive_streams():
    from nano_claude import build_prompt_ui

    prelude, prompt = build_prompt_ui(
        "nano-claude-code",
        {"prompt_padding_lines": 2},
        interactive=False,
        term_columns=40,
    )

    assert prelude == ""
    assert "\n[" in prompt


def test_stream_text_prints_plain_multiline_output(capsys):
    from nano_claude import _reset_response_render_state, flush_response, stream_text

    _reset_response_render_state()
    stream_text("first line\nsecond line\n\nfourth line")
    flush_response()

    out = capsys.readouterr().out
    assert out == "first line\nsecond line\n\nfourth line\n"


def test_stream_text_handles_split_chunks_without_extra_frame(capsys):
    from nano_claude import _reset_response_render_state, flush_response, stream_text

    _reset_response_render_state()
    stream_text("first")
    stream_text(" line\nsecond")
    stream_text(" line")
    flush_response()

    out = capsys.readouterr().out
    assert out == "first line\nsecond line\n"


def test_build_assistant_header_keeps_claude_green_dot():
    from nano_claude import build_assistant_header

    header = ANSI_RE.sub("", build_assistant_header())
    assert header == "\nClaude ●"


def test_looks_like_markdown_detects_bold_and_lists():
    from nano_claude import _looks_like_markdown

    assert _looks_like_markdown("Here are **five** facts")
    assert _looks_like_markdown("1. first\n2. second")
    assert not _looks_like_markdown("plain sentence without markdown")


def test_markdown_rendering_buffers_stream_until_flush(monkeypatch, capsys):
    from rich.console import Console
    import nano_claude

    buf = io.StringIO()
    monkeypatch.setattr(
        nano_claude,
        "console",
        Console(file=buf, force_terminal=False, color_system=None, width=80),
    )
    monkeypatch.setattr(nano_claude, "_supports_markdown_rendering", lambda: True)

    nano_claude._reset_response_render_state()
    nano_claude.stream_text("Here are **five** facts")
    assert capsys.readouterr().out == ""

    nano_claude.flush_response()
    rendered = buf.getvalue()
    assert "Here are five facts" in rendered
    assert "**" not in rendered
