#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep every declaration head reachable from the declaration atlas.

Two name-parsing defects have already reached the tracked atlas, and both
failed the same way: a declaration existed in Lean, was absent from
``docs/declaration_atlas.json``, and so every correct citation of it looked
fabricated to the corpus checks.

  * ``DECL_RE`` once closed the name with ``\\b``, truncating
    ``integerGreedyRemainder_lt_of_get?_eq_false`` and ``half_pow_term'``.
  * ``DECL_RE`` may span a newline, but the builder applied it one line at a
    time, so a declaration whose name sat on the line *after* its keyword was
    never matched at all.

This contract pins both shapes against synthetic fixtures and against the real
source, so a future rewrite of the head pattern cannot silently drop
declarations again.
"""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
ATLAS = ROOT / "docs" / "declaration_atlas.json"


def load_builder():
    """Import the atlas builder by path; ``scripts`` is not a package."""
    spec = importlib.util.spec_from_file_location(
        "build_declaration_atlas",
        ROOT / "scripts" / "build_declaration_atlas.py",
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def heads(builder, source: str) -> list[tuple[int, str, str]]:
    """Run the builder's own scan over ``source``, one-based line numbers."""
    lines = source.splitlines()
    is_code = builder.code_lines(lines)
    found = []
    for index in range(len(lines)):
        if not is_code[index]:
            continue
        head = builder.declaration_head(lines, index)
        if head is not None:
            found.append((index + 1, head[0], head[1]))
    return found


def wrapped_source_heads(builder) -> list[tuple[str, int, str]]:
    """Every ``(module, line, name)`` whose name is not on the keyword line."""
    wrapped = []
    for path in builder.source_paths():
        rel = path.relative_to(ROOT).as_posix()
        lines = path.read_text(encoding="utf-8").splitlines()
        is_code = builder.code_lines(lines)
        for index in range(len(lines)):
            if not is_code[index] or builder.DECL_RE.match(lines[index]):
                continue
            head = builder.declaration_head(lines, index)
            if head is not None:
                wrapped.append((rel, index + 1, head[1]))
    return wrapped


def check_fixtures(builder) -> int:
    """Pin the accepted and rejected head shapes.  Returns the fixture count."""
    accepted: list[tuple[str, str, list[tuple[int, str, str]]]] = [
        (
            "single line",
            "theorem foo_bar {n : ℕ} : n = n := rfl\n",
            [(1, "theorem", "foo_bar")],
        ),
        (
            "wrapped theorem",
            "theorem\n    wrapped_name {n : ℕ} :\n    n = n := rfl\n",
            [(1, "theorem", "wrapped_name")],
        ),
        (
            "wrapped noncomputable def with a dotted name",
            "noncomputable def\n    Namespace.wrappedDef (h : True) :\n    True := h\n",
            [(1, "def", "Namespace.wrappedDef")],
        ),
        (
            "attribute on its own line before a wrapped head",
            "@[simp]\ntheorem\n    attributed_wrapped : True := trivial\n",
            [(2, "theorem", "attributed_wrapped")],
        ),
        (
            "attribute sharing the keyword line",
            "@[simp] theorem\n    inline_attributed : True := trivial\n",
            [(1, "theorem", "inline_attributed")],
        ),
        (
            "blank line between keyword and name",
            "lemma\n\n    spaced_name : True := trivial\n",
            [(1, "lemma", "spaced_name")],
        ),
        (
            "line comment between keyword and name",
            "lemma\n    -- why this shape\n    commented_name : True := trivial\n",
            [(1, "lemma", "commented_name")],
        ),
        (
            "name ending in a prime",
            "theorem half_pow_term' : True := trivial\n",
            [(1, "theorem", "half_pow_term'")],
        ),
        (
            "name containing a question mark",
            "theorem integerGreedyRemainder_lt_of_get?_eq_false : True := trivial\n",
            [(1, "theorem", "integerGreedyRemainder_lt_of_get?_eq_false")],
        ),
        (
            "wrapped name ending in a prime",
            "lemma\n    wrapped_term' : True := trivial\n",
            [(1, "lemma", "wrapped_term'")],
        ),
    ]
    rejected: list[tuple[str, str]] = [
        (
            "anonymous wrapped instance has no name to record",
            "noncomputable local instance\n    {α : Type*} (C : ℕ) :\n"
            "    Decidable True :=\n  Classical.propDecidable _\n",
        ),
        (
            "prose inside a docstring is not a declaration",
            "/-- The wrapped\ntheorem says that everything is fine. -/\n",
        ),
        (
            "prose inside a nested block comment is not a declaration",
            "/- outer /- inner\nlemma used by the caller -/ still inside -/\n",
        ),
        (
            "keyword-only line at end of file",
            "theorem\n",
        ),
        (
            "name beyond the lookahead window is not claimed",
            "theorem\n\n\n\n    far_away_name : True := trivial\n",
        ),
        (
            "binders on the continuation line do not become a name",
            "def\n    (n : ℕ) : ℕ := n\n",
        ),
    ]

    for label, source, expected in accepted:
        assert heads(builder, source) == expected, f"accepted fixture failed: {label}"
    for label, source in rejected:
        assert heads(builder, source) == [], f"rejected fixture failed: {label}"

    genuine_doc = [
        "/-- The statement attached to `documented`. -/",
        "theorem documented : True := trivial",
    ]
    assert builder.preceding_docstring(genuine_doc, 1) == (
        "The statement attached to `documented`."
    )
    crossed_boundary = [
        "/-- This belongs only to `first`. -/",
        "theorem first : True := trivial",
        "",
        "/-! ## A section boundary -/",
        "",
        "lemma second : True := trivial",
    ]
    assert builder.preceding_docstring(crossed_boundary, 5) is None, (
        "docstring scanner crossed an intervening section comment and declaration"
    )
    return len(accepted) + len(rejected) + 2


def main() -> int:
    builder = load_builder()
    fixture_count = check_fixtures(builder)

    atlas = json.loads(ATLAS.read_text(encoding="utf-8"))
    indexed = {
        (str(row["module"]), int(row["line"]), str(row["name"]))
        for row in atlas["declarations"]
    }

    # Real wrapped heads must be in the tracked atlas, otherwise a citation of
    # a declaration that genuinely exists resolves to nothing.
    wrapped = wrapped_source_heads(builder)
    assert wrapped, "no wrapped declaration head found; the guard would be vacuous"
    missing = [entry for entry in wrapped if entry not in indexed]
    assert not missing, f"wrapped declarations absent from the atlas: {missing}"

    # The line-at-a-time matcher that dropped them must still fail on them, or
    # this contract is no longer testing anything.
    for module, line, name in wrapped:
        source_line = (ROOT / module).read_text(encoding="utf-8").splitlines()[line - 1]
        assert not builder.DECL_RE.match(source_line), (
            f"{module}:{line}:{name} is no longer a wrapped head; "
            "repoint this contract at a declaration whose name still wraps"
        )

    # The earlier truncation bug: identifier tails survive into the atlas.
    names = {str(row["name"]) for row in atlas["declarations"]}
    assert any(name.endswith("'") for name in names), "atlas lost prime-suffixed names"
    assert any("?" in name for name in names), "atlas lost `?`-bearing names"

    half_pow = next(
        row
        for row in atlas["declarations"]
        if row["module"] == "Erdos249257/GcdMomentCalculus.lean"
        and row["name"] == "half_pow_term'"
    )
    assert "docstring" not in half_pow, (
        "half_pow_term' inherited an earlier declaration's docstring"
    )

    print(
        "test_declaration_head_contract: "
        f"{fixture_count} head fixtures pinned; "
        f"{len(wrapped)} wrapped declaration(s) resolve in the atlas "
        f"({', '.join(f'{module}:{line}' for module, line, _ in wrapped)}); "
        "prime and `?` identifier tails intact"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
