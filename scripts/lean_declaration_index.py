#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Fully-qualified Lean declaration names read straight from source text.

`verify_claims.resolve_declaration` answers "does this name sit near this
line", which is the right question for a claim locator.  Comparator selection
asks a different question: "is this fully-qualified theorem name actually
declared inside this package".  A name-anywhere-in-the-repository match
answers that question wrongly, because every package in this corpus restates
theorems that also live in the library modules it imports.  So this module
tracks the namespace stack and reports the qualified names a file declares.

Stdlib only, no Lean, no network.
"""

from __future__ import annotations

from pathlib import Path

DECLARATION_KEYWORDS = frozenset(
    {
        "theorem",
        "lemma",
        "def",
        "abbrev",
        "instance",
        "structure",
        "inductive",
        "example",
        "class",
        "axiom",
    }
)

DECLARATION_MODIFIERS = frozenset(
    {
        "private",
        "protected",
        "noncomputable",
        "partial",
        "unsafe",
        "scoped",
        "local",
        "nonrec",
    }
)

_NAME_TRAILERS = ":{(,)}"

# How far below its keyword a wrapped declaration name may sit.
NAME_WRAP_WINDOW = 3


def strip_attributes(text: str) -> str:
    """Drop leading `@[...]` attribute blocks from one source line."""
    stripped = text.lstrip()
    while stripped.startswith("@["):
        close = stripped.find("]")
        if close == -1:
            return ""
        stripped = stripped[close + 1 :].lstrip()
    return stripped


def _declared_name(lines: list[str], index: int) -> str | None:
    """Return the bare name introduced at `index`, following a wrapped name.

    Declarations in this corpus routinely put `theorem` on its own line with
    the name indented beneath it, which is exactly the shape a naive matcher
    reports as a missing declaration.
    """
    line = lines[index]
    if line[:1] in (" ", "\t"):
        return None
    tokens = strip_attributes(line).split()
    cursor = 0
    while cursor < len(tokens) and tokens[cursor] in DECLARATION_MODIFIERS:
        cursor += 1
    if cursor >= len(tokens) or tokens[cursor] not in DECLARATION_KEYWORDS:
        return None
    if cursor + 1 < len(tokens):
        return tokens[cursor + 1].strip(_NAME_TRAILERS) or None
    for probe in range(index + 1, min(len(lines), index + 4)):
        following = lines[probe].split()
        if following:
            return following[0].strip(_NAME_TRAILERS) or None
    return None


def qualified_declarations(path: Path) -> dict[str, int]:
    """Map every fully-qualified declaration in `path` to its 1-based line."""
    try:
        lines = path.read_text(errors="replace").splitlines()
    except OSError:
        return {}
    namespaces: list[str] = []
    found: dict[str, int] = {}
    for index, raw in enumerate(lines):
        tokens = raw.split()
        if tokens and tokens[0] == "namespace" and len(tokens) > 1:
            namespaces.append(tokens[1])
            continue
        if tokens and tokens[0] == "end":
            if len(tokens) > 1 and namespaces and namespaces[-1] == tokens[1]:
                namespaces.pop()
            continue
        name = _declared_name(lines, index)
        if name is None:
            continue
        prefix = ".".join(namespaces)
        qualified = f"{prefix}.{name}" if prefix else name
        found.setdefault(qualified, index + 1)
    return found


def declaration_keyword_line(path: Path, name: str, line: int) -> int | None:
    """Return the keyword line of the declaration `name` reported at `line`.

    A declaration keyword frequently sits on its own line with the name
    indented beneath it, so the line a locator records (where the name is)
    and the line the keyword occupies are not always the same.
    """
    parts = name.split(".")
    spellings = {".".join(parts[cut:]) for cut in range(len(parts))}
    for qualified, keyword_line in qualified_declarations(path).items():
        tail = qualified.split(".")
        if not ({".".join(tail[cut:]) for cut in range(len(tail))} & spellings):
            continue
        if keyword_line <= line <= keyword_line + NAME_WRAP_WINDOW:
            return keyword_line
    return None


def module_path(root: Path, module: str) -> Path:
    """Resolve a Lean module name to its path inside `root`."""
    return root / (module.replace(".", "/") + ".lean")


def imported_modules(path: Path) -> list[str]:
    """List the modules a Lean file imports."""
    try:
        lines = path.read_text(errors="replace").splitlines()
    except OSError:
        return []
    modules: list[str] = []
    for raw in lines:
        tokens = raw.split()
        if not tokens:
            continue
        if tokens[0] == "import" and len(tokens) > 1:
            modules.append(tokens[1])
            continue
        if tokens[0] in {"namespace", "theorem", "lemma", "def", "open"}:
            break
    return modules


def resolve_within(
    root: Path,
    seeds: list[Path],
    name: str,
    *,
    max_modules: int = 64,
) -> tuple[str, int] | None:
    """Find `name` in `seeds`, then in the imports of `seeds` that live in `root`.

    Returns the relative module path and line, or None when the name is not
    declared anywhere reachable inside this tree.
    """
    queue: list[Path] = list(seeds)
    seen: set[Path] = set()
    visited = 0
    while queue and visited < max_modules:
        current = queue.pop(0)
        if current in seen:
            continue
        seen.add(current)
        if not current.is_file():
            continue
        visited += 1
        declarations = qualified_declarations(current)
        line = declarations.get(name)
        if line is None:
            parts = name.split(".")
            for cut in range(1, len(parts)):
                line = declarations.get(".".join(parts[cut:]))
                if line is not None:
                    break
        if line is not None:
            try:
                relative = current.relative_to(root).as_posix()
            except ValueError:
                relative = current.as_posix()
            return relative, line
        for module in imported_modules(current):
            candidate = module_path(root, module)
            if candidate.is_file():
                queue.append(candidate)
    return None
