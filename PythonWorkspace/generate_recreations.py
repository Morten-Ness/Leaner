#!/usr/bin/env python3
from __future__ import annotations

"""
Generate standalone theorem recreation files from mathlib files.

Usage model:
- point `--source` at a single `.lean` file, or
- point `--source` at any directory under `Mathlib/`

The script mirrors the source tree under `Recreations/`, and for each source
`.lean` file it creates a directory named `<File>.lean/` containing one file
per theorem.

This generator stays in mathlib world:
- every output file starts with `import Mathlib`
- it copies the active `variable` blocks for the target theorem
- it copies the theorem text
- it adds namespace prefixes where needed so the theorem works without any
  `open`
- it never overwrites existing files
"""

import argparse
import re
from dataclasses import dataclass
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
MATHLIB_ROOT = REPO_ROOT / "Mathlib"
RECREATIONS_ROOT = REPO_ROOT / "LeanWorkspace/LeanWorkspace/Recreations"
DEFAULT_SOURCE = MATHLIB_ROOT / "LinearAlgebra/AffineSpace"

DECL_START_RE = re.compile(
    r"^(?P<kind>noncomputable def|protected theorem|theorem|lemma|def|instance)\s+"
    r"(?P<name>[^\s(:{]+)"
)

THEOREM_KINDS = {"theorem", "lemma", "protected theorem"}

QUALIFY_MAP = {
    "AffineSpace": "AddTorsor",
    "Injective": "Function.Injective",
    "Surjective": "Function.Surjective",
    "Bijective": "Function.Bijective",
    "Involutive": "Function.Involutive",
}

OPEN_QUALIFY_MAP = {
    "Finset": {
        "affineCombination": "Finset.affineCombination",
        "centroidWeights": "Finset.centroidWeights",
        "univ": "Finset.univ",
    },
    "Set": {
        "range": "Set.range",
        "univ": "Set.univ",
    },
}

# When true, wrap each generated theorem in `namespace Formalization`.
# In that mode, colliding theorem names are no longer skipped.
NAMESPACE_FORMALIZATION = False

# Theorems in this list are skipped because their recreated names collide with
# existing imported declarations.
COLLIDING_THEOREM_NAMES = {
    "map_vadd",
}

# Generated names that often appear bare inside theorem statements/proofs.
STATIC_NAMESPACE_NAMES = {"mk", "toEquiv"}

# If a proof body starts with `by`, these can appear as tactic commands and
# should not be namespace-prefixed when they are the first token on a line.
TACTIC_COMMANDS = {
    "aesop",
    "all_goals",
    "apply",
    "assumption",
    "calc",
    "case",
    "cases",
    "change",
    "constructor",
    "convert",
    "done",
    "dsimp",
    "exact",
    "ext",
    "fail_if_success",
    "first",
    "have",
    "induction",
    "infer_instance",
    "intro",
    "intros",
    "let",
    "native_decide",
    "omega",
    "rcases",
    "refine",
    "repeat",
    "revert",
    "rfl",
    "rintro",
    "rw",
    "show",
    "simpa",
    "simp",
    "skip",
    "symm",
    "trans",
    "trivial",
    "unfold",
}


@dataclass(frozen=True)
class VarBlock:
    text: str


@dataclass
class Decl:
    kind: str
    name: str
    namespace_path: tuple[str, ...]
    open_namespaces: tuple[str, ...]
    text: str
    var_blocks: list[VarBlock]
    order: int

    @property
    def is_theorem_like(self) -> bool:
        return self.kind in THEOREM_KINDS

    @property
    def is_referencable(self) -> bool:
        return self.kind != "instance"

    @property
    def full_name(self) -> str:
        if not self.namespace_path:
            return self.name
        return ".".join([*self.namespace_path, self.name])


def normalize_theorem_keyword(text: str) -> str:
    text = re.sub(r"^protected\s+theorem\b", "theorem", text, count=1, flags=re.MULTILINE)
    text = re.sub(r"^lemma\b", "theorem", text, count=1, flags=re.MULTILINE)
    return text


def qualify_common_names(text: str) -> str:
    for bare, qualified in QUALIFY_MAP.items():
        text = re.sub(
            rf"(?<![\w.']){re.escape(bare)}(?![\w'])",
            qualified,
            text,
        )
    return text


def split_statement_and_body(text: str) -> tuple[str, str]:
    idx = text.find(":=")
    if idx == -1:
        return text.rstrip(), ""
    head = text[:idx].rstrip()
    body = text[idx + 2 :].lstrip()
    return head, body


def is_toplevel_break(stripped: str) -> bool:
    if not stripped:
        return False
    if stripped.startswith(("/-", "/--", "/-!", "@[")):
        return True
    if stripped.startswith(("namespace ", "section", "end", "variable ", "open ", "open scoped")):
        return True
    return DECL_START_RE.match(stripped) is not None


def collect_block(lines: list[str], start: int) -> tuple[str, int]:
    end = start + 1
    while end < len(lines):
        line = lines[end]
        stripped = line.strip()
        if stripped and not line.startswith(" "):
            if is_toplevel_break(stripped):
                break
        end += 1
    return "".join(lines[start:end]).rstrip() + "\n", end


def collect_variable_block(lines: list[str], start: int) -> tuple[str, int]:
    end = start + 1
    while end < len(lines):
        line = lines[end]
        if line.startswith("  ") or line.startswith("    "):
            end += 1
            continue
        if not line.strip():
            break
        if line.startswith(" "):
            end += 1
            continue
        break
    return "".join(lines[start:end]).rstrip() + "\n", end


def skip_comment(lines: list[str], start: int) -> int:
    if "-/" in lines[start]:
        return start + 1
    i = start + 1
    while i < len(lines):
        if "-/" in lines[i]:
            return i + 1
        i += 1
    return i


def current_namespace_path(scope_stack: list[tuple[str, str]]) -> tuple[str, ...]:
    return tuple(name for kind, name in scope_stack if kind == "namespace")


def ordered_unique_var_blocks(blocks: list[VarBlock]) -> list[VarBlock]:
    seen: set[str] = set()
    ordered: list[VarBlock] = []
    for block in blocks:
        if block.text in seen:
            continue
        seen.add(block.text)
        ordered.append(block)
    return ordered


def parse_open_namespaces(stripped: str) -> tuple[str, ...]:
    if not stripped.startswith("open ") or stripped.startswith("open scoped"):
        return ()
    remainder = stripped[len("open ") :]
    if remainder.endswith(" in"):
        remainder = remainder[: -len(" in")].rstrip()
    if not remainder:
        return ()
    return tuple(part for part in remainder.split() if part)


def parse_source_file(source_path: Path) -> list[Decl]:
    lines = source_path.read_text(encoding="utf-8").splitlines(keepends=True)
    global_var_blocks: list[VarBlock] = []
    active_var_blocks: list[tuple[int, VarBlock]] = []
    global_open_namespaces: list[str] = []
    active_open_namespaces: list[tuple[int, tuple[str, ...]]] = []
    pending_one_shot_opens: tuple[str, ...] = ()
    decls: list[Decl] = []
    scope_stack: list[tuple[str, str]] = []
    order = 0
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        if not stripped:
            i += 1
            continue
        if stripped.startswith("/-"):
            i = skip_comment(lines, i)
            continue
        if stripped.startswith("@["):
            i += 1
            continue
        if stripped.startswith("namespace "):
            scope_stack.append(("namespace", stripped.split()[1]))
            i += 1
            continue
        if stripped.startswith("section"):
            name = stripped.split(maxsplit=1)[1] if " " in stripped else ""
            scope_stack.append(("section", name))
            i += 1
            continue
        if stripped.startswith("end"):
            if scope_stack:
                scope_stack.pop()
            while active_var_blocks and active_var_blocks[-1][0] > len(scope_stack):
                active_var_blocks.pop()
            while active_open_namespaces and active_open_namespaces[-1][0] > len(scope_stack):
                active_open_namespaces.pop()
            i += 1
            continue
        if stripped.startswith("open "):
            open_namespaces = parse_open_namespaces(stripped)
            if stripped.endswith(" in"):
                pending_one_shot_opens = open_namespaces
            elif not scope_stack:
                global_open_namespaces.extend(open_namespaces)
            else:
                active_open_namespaces.append((len(scope_stack), open_namespaces))
            i += 1
            continue
        if stripped.startswith("variable "):
            block_text, i = collect_variable_block(lines, i)
            block = VarBlock(block_text)
            if not scope_stack:
                global_var_blocks.append(block)
            else:
                active_var_blocks.append((len(scope_stack), block))
            continue
        if DECL_START_RE.match(stripped):
            text, i = collect_block(lines, i)
            first_line = text.splitlines()[0].strip()
            match = DECL_START_RE.match(first_line)
            if match is None:
                continue
            decls.append(
                Decl(
                    kind=match.group("kind"),
                    name=match.group("name"),
                    namespace_path=current_namespace_path(scope_stack),
                    open_namespaces=tuple(
                        global_open_namespaces
                        + [
                            namespace
                            for _, open_group in active_open_namespaces
                            for namespace in open_group
                        ]
                        + list(pending_one_shot_opens)
                    ),
                    text=text,
                    var_blocks=global_var_blocks + [block for _, block in active_var_blocks],
                    order=order,
                )
            )
            pending_one_shot_opens = ()
            order += 1
            continue
        i += 1
    return decls


def choose_best_decl_name(
    previous_decls: list[Decl],
    current_decl: Decl,
) -> dict[str, str]:
    chosen: dict[str, Decl] = {}
    for decl in previous_decls:
        if not decl.is_referencable:
            continue
        bare = decl.name
        current = chosen.get(bare)
        if current is None:
            chosen[bare] = decl
            continue
        current_same_ns = current.namespace_path == current_decl.namespace_path
        candidate_same_ns = decl.namespace_path == current_decl.namespace_path
        if candidate_same_ns and not current_same_ns:
            chosen[bare] = decl
            continue
    replacements: dict[str, str] = {}
    for bare, decl in chosen.items():
        if bare != decl.full_name:
            replacements[bare] = decl.full_name
    if current_decl.namespace_path:
        prefix = ".".join(current_decl.namespace_path)
        replacements[current_decl.namespace_path[-1]] = prefix
        for name in STATIC_NAMESPACE_NAMES:
            replacements[name] = f"{prefix}.{name}"
    for namespace in current_decl.open_namespaces:
        replacements.update(OPEN_QUALIFY_MAP.get(namespace, {}))
    return replacements


def prefixed_names(previous_decls: list[Decl], current_decl: Decl) -> list[tuple[str, str]]:
    replacements = choose_best_decl_name(previous_decls, current_decl)
    return sorted(replacements.items(), key=lambda item: len(item[0]), reverse=True)


def prefix_names_in_fragment(
    fragment: str,
    replacements: list[tuple[str, str]],
    *,
    skip_first_tactic_token: bool,
) -> str:
    protected_span: tuple[int, int] | None = None
    if skip_first_tactic_token:
        match = re.match(r"\s*([A-Za-z_][\w'.₀₁₂₃₄₅₆₇₈₉ₗ]*)", fragment)
        if match and match.group(1) in TACTIC_COMMANDS:
            protected_span = (match.start(1), match.end(1))

    for bare, qualified in replacements:
        pattern = re.compile(rf"(?<![\w.']){re.escape(bare)}(?![\w'])")

        def repl(match: re.Match[str], *, _qualified: str = qualified) -> str:
            if protected_span is not None and protected_span[0] <= match.start() < protected_span[1]:
                return match.group(0)
            return _qualified

        fragment = pattern.sub(repl, fragment)
    return fragment


def rewrite_body(body: str, replacements: list[tuple[str, str]]) -> str:
    body = qualify_common_names(body)
    if not body.lstrip().startswith("by"):
        return prefix_names_in_fragment(body, replacements, skip_first_tactic_token=False)

    lines = body.splitlines(keepends=True)
    rewritten: list[str] = []
    for index, line in enumerate(lines):
        newline = "\n" if line.endswith("\n") else ""
        content = line[:-1] if newline else line
        stripped = content.lstrip()
        indent = content[: len(content) - len(stripped)]
        if index == 0 and stripped.startswith("by"):
            if stripped == "by":
                rewritten.append(line)
                continue
            rest = stripped[2:].lstrip()
            rest_rewritten = prefix_names_in_fragment(rest, replacements, skip_first_tactic_token=True)
            rewritten.append(f"{indent}by {rest_rewritten}{newline}")
            continue
        rewritten_fragment = prefix_names_in_fragment(stripped, replacements, skip_first_tactic_token=True)
        rewritten.append(f"{indent}{rewritten_fragment}{newline}")
    return "".join(rewritten)


def rewrite_decl_text(decl: Decl, previous_decls: list[Decl]) -> str:
    text = normalize_theorem_keyword(decl.text)
    statement, body = split_statement_and_body(text)
    replacements = prefixed_names(previous_decls, decl)
    statement = qualify_common_names(statement)
    match = DECL_START_RE.match(statement)
    if match is not None:
        head = statement[: match.end("name")]
        tail = statement[match.end("name") :]
        statement = head + prefix_names_in_fragment(
            tail,
            replacements,
            skip_first_tactic_token=False,
        )
    else:
        statement = prefix_names_in_fragment(statement, replacements, skip_first_tactic_token=False)
    if not body:
        return statement
    return f"{statement} := {rewrite_body(body, replacements)}"


def rewrite_var_block(block: VarBlock) -> str:
    return qualify_common_names(block.text)


def theorem_filename(decl: Decl, name_counts: dict[str, int]) -> str:
    stem = decl.name
    if name_counts.get(decl.name, 0) > 1 and decl.namespace_path:
        stem = decl.full_name
    return f"{stem}.lean"


def iter_target_theorems(decls: list[Decl]) -> list[Decl]:
    skipped_names = set() if NAMESPACE_FORMALIZATION else COLLIDING_THEOREM_NAMES
    return [
        decl
        for decl in decls
        if decl.is_theorem_like and decl.name not in skipped_names
    ]


def output_text_for_theorem(target: Decl, previous_decls: list[Decl]) -> str:
    parts = ["import Mathlib\n\n"]
    for block in ordered_unique_var_blocks(target.var_blocks):
        parts.append(rewrite_var_block(block))
        parts.append("\n")
    if NAMESPACE_FORMALIZATION:
        parts.append("namespace Formalization\n\n")
    parts.append(rewrite_decl_text(target, previous_decls))
    parts.append("\n")
    if NAMESPACE_FORMALIZATION:
        parts.append("\nend Formalization\n")
    return "".join(parts)


def find_mathlib_root(path: Path) -> Path:
    resolved = path.resolve()
    for candidate in [resolved, *resolved.parents]:
        if candidate.name == "Mathlib":
            return candidate
    raise ValueError(f"{path} is not inside a Mathlib directory")


def source_files_from_input(source: Path) -> list[Path]:
    source = source.resolve()
    if source.is_file():
        if source.suffix != ".lean":
            raise ValueError(f"{source} is not a .lean file")
        return [source]
    if source.is_dir():
        return sorted(source.rglob("*.lean"))
    raise ValueError(f"{source} does not exist")


def output_dir_for_source(source_file: Path, output_root: Path) -> Path:
    mathlib_root = find_mathlib_root(source_file)
    relative = source_file.resolve().relative_to(mathlib_root)
    return output_root / relative


def generate_for_source_file(source_file: Path, output_root: Path) -> tuple[int, int]:
    decls = parse_source_file(source_file)
    target_theorems = iter_target_theorems(decls)
    name_counts: dict[str, int] = {}
    for decl in target_theorems:
        name_counts[decl.name] = name_counts.get(decl.name, 0) + 1

    output_dir = output_dir_for_source(source_file, output_root)
    output_dir.mkdir(parents=True, exist_ok=True)

    generated = 0
    skipped = 0
    for theorem in target_theorems:
        destination = output_dir / theorem_filename(theorem, name_counts)
        if destination.exists():
            skipped += 1
            continue
        previous_decls = [decl for decl in decls if decl.order < theorem.order]
        destination.write_text(
            output_text_for_theorem(theorem, previous_decls),
            encoding="utf-8",
        )
        generated += 1
    return generated, skipped


def generate(source: Path, output_root: Path) -> tuple[int, int, int]:
    generated = 0
    skipped = 0
    files_processed = 0
    for source_file in source_files_from_input(source):
        gen, skip = generate_for_source_file(source_file, output_root)
        generated += gen
        skipped += skip
        files_processed += 1
    return generated, skipped, files_processed


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate theorem recreations for a mathlib file or directory."
    )
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--output-root", type=Path, default=RECREATIONS_ROOT)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    generated, skipped, files_processed = generate(args.source, args.output_root)
    print(
        f"Processed {files_processed} source file(s); "
        f"generated {generated} theorem file(s); skipped {skipped} existing file(s)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
