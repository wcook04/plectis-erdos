#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Verify that every Erdős Problem Note source link names a real declaration.

The problem notes cover the expansion library ``ErdosProblems``, which is an
active research surface: later waves add theorems and move lines.  A note that
linked the working tree would therefore decay the moment the next wave landed.

Each note instead resolves its links against one pinned commit, declared once in
``paper/problem-note-preamble.tex``.  This program reads that snapshot out of Git
-- never the working tree -- and requires that every authored ``(file, line,
declaration)`` triple names exactly that declaration at exactly that line in the
pinned snapshot.  A link can then be wrong only if it was wrong when written.

Run from the repository root:

    python3 scripts/check_problem_note_sources.py

``--list`` prints the resolved link inventory instead of only a verdict.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PREAMBLE = ROOT / "paper" / "problem-note-preamble.tex"
CONTRACT = ROOT / "docs" / "publication_contract.json"
NOTE_ARTIFACT_CLASS = "problem_note"
LIBRARY_PREFIX = "ErdosProblems"

COMMIT_RE = re.compile(r"\\newcommand\{\\commit\}\{([0-9a-f]{40})\}")
COMMENT_RE = re.compile(r"(?<!\\)%.*$")
LINK_RE = re.compile(
    r"""\\lword\{(?P<word_file>[^{}]+)\}\{(?P<word_line>\d+)\}
            \{(?P<word_decl>[^{}]+)\}\{
        |\\(?:lref|lrefx)\{(?P<ref_file>[^{}]+)\}\{(?P<ref_line>\d+)\}
            \{(?P<ref_decl>[^{}]+)\}
        |\\lloc\{(?P<loc_file>[^{}]+)\}\{(?P<loc_line>\d+)\}""",
    re.X,
)
# A Lean declaration head: the keyword, optional modifiers, then the name.
DECL_KEYWORDS = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "structure",
    "instance",
    "example",
)


def strip_comments(text: str) -> str:
    return "\n".join(COMMENT_RE.sub("", line) for line in text.splitlines())


def note_sources() -> list[str]:
    """Return the registered problem-note manuscript paths, in contract order."""
    contract = json.loads(CONTRACT.read_text(encoding="utf-8"))
    return [
        row["source_path"]
        for row in contract.get("artifacts", [])
        if row.get("artifact_class") == NOTE_ARTIFACT_CLASS
    ]


def pinned_commit() -> str:
    match = COMMIT_RE.search(PREAMBLE.read_text(encoding="utf-8"))
    if match is None:
        raise SystemExit(
            f"{PREAMBLE.relative_to(ROOT)}: no pinned \\commit is declared"
        )
    return match.group(1)


def snapshot_lines(commit: str, relative: str, cache: dict[str, list[str]]) -> list[str]:
    if relative in cache:
        return cache[relative]
    completed = subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        cache[relative] = []
    else:
        cache[relative] = completed.stdout.splitlines()
    return cache[relative]


ATTRIBUTE_RE = re.compile(r"^\s*@\[[^\]]*\]\s*")


def declares(line: str, name: str) -> bool:
    """True when this source line is the declaration head for ``name``."""
    # A declaration head may carry attributes, as in `@[simp] theorem foo`.
    stripped = ATTRIBUTE_RE.sub("", line).strip()
    for keyword in DECL_KEYWORDS:
        for prefix in ("", "private ", "protected ", "noncomputable ", "nonrec "):
            head = f"{prefix}{keyword} "
            if stripped.startswith(head):
                rest = stripped[len(head) :].lstrip()
                if re.match(rf"{re.escape(name)}(?![A-Za-z0-9_'])", rest):
                    return True
    return False


def links(text: str) -> list[tuple[str, int, str | None]]:
    found: list[tuple[str, int, str | None]] = []
    for match in LINK_RE.finditer(strip_comments(text)):
        if match.group("word_file"):
            found.append(
                (match.group("word_file"), int(match.group("word_line")), match.group("word_decl"))
            )
        elif match.group("ref_file"):
            found.append(
                (match.group("ref_file"), int(match.group("ref_line")), match.group("ref_decl"))
            )
        else:
            found.append((match.group("loc_file"), int(match.group("loc_line")), None))
    return found


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--list",
        action="store_true",
        help="print every resolved link rather than only the verdict",
    )
    args = parser.parse_args()

    sources = note_sources()
    if not sources:
        print("check_problem_note_sources: no problem notes are registered")
        return 0

    commit = pinned_commit()
    if (
        subprocess.run(
            ["git", "cat-file", "-e", f"{commit}^{{commit}}"],
            cwd=ROOT,
            capture_output=True,
            check=False,
        ).returncode
        != 0
    ):
        print(f"check_problem_note_sources: pinned commit is absent: {commit}")
        return 1

    cache: dict[str, list[str]] = {}
    errors: list[str] = []
    checked = 0

    for source in sources:
        path = ROOT / source
        if not path.is_file():
            errors.append(f"{source}: registered problem note is missing")
            continue
        found = links(path.read_text(encoding="utf-8"))
        if not found:
            errors.append(f"{source}: authored no formal source links")
        for file_name, line_number, declaration in found:
            checked += 1
            relative = f"{LIBRARY_PREFIX}/{file_name}"
            lines = snapshot_lines(commit, relative, cache)
            if not lines:
                errors.append(
                    f"{source}: {relative} is absent from the pinned snapshot"
                )
                continue
            if not 1 <= line_number <= len(lines):
                errors.append(
                    f"{source}: {relative}:{line_number} is outside the pinned "
                    f"snapshot ({len(lines)} lines)"
                )
                continue
            line = lines[line_number - 1]
            if declaration is None:
                if not line.strip():
                    errors.append(
                        f"{source}: {relative}:{line_number} is blank in the "
                        "pinned snapshot"
                    )
                continue
            if not declares(line, declaration):
                errors.append(
                    f"{source}: {relative}:{line_number} does not declare "
                    f"{declaration!r}; the pinned line reads {line.strip()[:72]!r}"
                )
            elif args.list:
                print(f"  {declaration}  <-  {relative}:{line_number}")

    if errors:
        print(f"check_problem_note_sources: {len(errors)} failure(s)")
        for error in errors:
            print(f"  FAIL {error}")
        return 1

    print(
        f"check_problem_note_sources: {checked} link(s) across {len(sources)} note(s) "
        f"resolve at {commit[:12]}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
