#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Verify that every Erdős Problem Note source link names a real declaration.

The problem notes cover the expansion library ``ErdosProblems``, which is an
active research surface: later waves add theorems and move lines.  A note that
linked the working tree would therefore decay the moment the next wave landed.

Each note instead resolves its links against an immutable commit.  The corpus
default is declared in ``paper/problem-note-preamble.tex``; a note may override
that pin with ``\\renewcommand{\\commit}{...}`` when one problem advances on a
disjoint source branch.  This program reads each selected snapshot out of Git
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
INDEX_SOURCE = ROOT / "docs" / "problem_index_source.json"
NOTE_ARTIFACT_CLASS = "problem_note"
LIBRARY_PREFIX = "ErdosProblems"
# A note may also cite the reviewed #249/#257 corpus directly.  The expansion
# library is where problem-owned work lands, but the headline theorems for
# several problems live in the older reviewed library, and a note that could
# not name them would have to paraphrase a checked statement instead of
# linking it.  A link is read as library-qualified when its first path
# segment names a sibling library; otherwise it stays relative to
# ``ErdosProblems``, which is what every existing note writes.
SIBLING_LIBRARIES = ("Erdos249257",)

COMMIT_RE = re.compile(r"\\newcommand\{\\commit\}\{([0-9a-f]{40})\}")
NOTE_COMMIT_RE = re.compile(r"\\renewcommand\{\\commit\}\{([0-9a-f]{40})\}")
COMMENT_RE = re.compile(r"(?<!\\)%.*$")
LINK_RE = re.compile(
    r"""\\[lm]word\{(?P<word_file>[^{}]+)\}\{(?P<word_line>\d+)\}
            \{(?P<word_decl>[^{}]+)\}\{
        |\\(?:lref|lrefx|mref)\{(?P<ref_file>[^{}]+)\}\{(?P<ref_line>\d+)\}
            \{(?P<ref_decl>[^{}]+)\}
        |\\[lm]loc\{(?P<loc_file>[^{}]+)\}\{(?P<loc_line>\d+)\}""",
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


def note_pinned_commit(note_text: str, default_commit: str) -> str:
    """Return a note-local source pin, falling back to the corpus default."""
    match = NOTE_COMMIT_RE.search(strip_comments(note_text))
    return default_commit if match is None else match.group(1)


def snapshot_lines(
    commit: str,
    relative: str,
    cache: dict[tuple[str, str], list[str]],
) -> list[str]:
    key = (commit, relative)
    if key in cache:
        return cache[key]
    completed = subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        cache[key] = []
    else:
        cache[key] = completed.stdout.splitlines()
    return cache[key]


def library_relative(file_name: str) -> str:
    """Repository path for a link target named in a note.

    Unqualified names stay relative to the expansion library; a name whose
    first segment is a sibling library is already repository-relative.
    """
    head = file_name.split("/", 1)[0]
    if head in SIBLING_LIBRARIES:
        return file_name
    return f"{LIBRARY_PREFIX}/{file_name}"


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


def note_for_problem() -> list[tuple[dict, str]]:
    """Pair each indexed problem with its registered note source path."""
    index = json.loads(INDEX_SOURCE.read_text(encoding="utf-8"))
    contract = json.loads(CONTRACT.read_text(encoding="utf-8"))
    by_id = {row["id"]: row for row in contract.get("artifacts", [])}
    pairs = []
    for row in index["problems"]:
        artifact = by_id.get(row["note_artifact_id"])
        if artifact is not None:
            pairs.append((row, artifact["source_path"]))
    return pairs


def declarations_in(text: str) -> list[str]:
    """Every declaration name a Lean source declares, in file order."""
    names: list[str] = []
    for line in text.splitlines():
        stripped = ATTRIBUTE_RE.sub("", line).strip()
        for keyword in DECL_KEYWORDS:
            for prefix in ("", "private ", "protected ", "noncomputable ", "nonrec "):
                head = f"{prefix}{keyword} "
                if stripped.startswith(head):
                    match = re.match(
                        r"([A-Za-z_][A-Za-z0-9_'.]*)", stripped[len(head) :].lstrip()
                    )
                    if match:
                        names.append(match.group(1))
                    break
            else:
                continue
            break
    return names


def coverage_report(default_commit: str) -> tuple[list[str], list[str]]:
    """Report how much of each problem's current source its note reaches.

    A note pins its links to one commit, so it cannot break when the library
    moves.  The cost of that safety is that it can fall silently behind.  This
    measures the gap in the only terms that matter to a reader: how many of the
    declarations that exist *now* the note actually mentions, and whether the
    modules have changed at all since the note was pinned.
    """
    lines: list[str] = []
    failures: list[str] = []
    index = json.loads(INDEX_SOURCE.read_text(encoding="utf-8"))
    floor = index.get("note_coverage_floor", 0.0)
    for row, source in note_for_problem():
        note_text = (ROOT / source).read_text(encoding="utf-8")
        commit = note_pinned_commit(note_text, default_commit)
        linked = {declaration for _f, _l, declaration in links(note_text) if declaration}
        modules = [row["principal_module"], *row.get("companion_modules", [])]
        current: list[str] = []
        moved: list[str] = []
        for module in modules:
            relative = "/".join(module.split(".")) + ".lean"
            path = ROOT / relative
            if not path.is_file():
                failures.append(f"{row['problem_id']}: {relative} is missing")
                continue
            live = path.read_text(encoding="utf-8")
            current.extend(declarations_in(live))
            pinned = subprocess.run(
                ["git", "show", f"{commit}:{relative}"],
                cwd=ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
            if pinned.returncode != 0 or pinned.stdout != live:
                moved.append(relative)
        if not current:
            continue
        covered = [name for name in current if name in linked]
        ratio = len(covered) / len(current)
        status = "behind" if moved else "current"
        lines.append(
            f"  {row['problem_id']}: {len(covered)}/{len(current)} declarations "
            f"linked ({ratio:.0%}), source {status}"
        )
        if moved:
            lines.append(f"      moved since the pin: {', '.join(sorted(moved))}")
            missing = [name for name in current if name not in linked]
            if missing:
                head = ", ".join(missing[:6])
                more = "" if len(missing) <= 6 else f", and {len(missing) - 6} more"
                lines.append(f"      not reached by the note: {head}{more}")
        if ratio < floor:
            failures.append(
                f"{row['problem_id']}: note reaches {ratio:.0%} of current "
                f"declarations, below the {floor:.0%} floor; rewrite the note "
                f"and repin, or lower note_coverage_floor deliberately"
            )
        # The floor is measured against this checkout, which is what the notes
        # are built from.  The library is also developed on another branch, and
        # a note can be current here while that branch has already moved on.
        # That gap is reported and never gated: failing on someone else's
        # branch would make this check red through no fault of this tree.
        upstream = index.get("upstream_ref")
        if upstream:
            ahead = 0
            for module in modules:
                relative = "/".join(module.split(".")) + ".lean"
                shown = subprocess.run(
                    ["git", "show", f"{upstream}:{relative}"],
                    cwd=ROOT,
                    capture_output=True,
                    text=True,
                    check=False,
                )
                if shown.returncode == 0:
                    ahead += len(declarations_in(shown.stdout))
            if ahead > len(current):
                lines.append(
                    f"      upstream {upstream} is {ahead - len(current)} "
                    f"declaration(s) ahead of this checkout"
                )
    return lines, failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--list",
        action="store_true",
        help="print every resolved link rather than only the verdict",
    )
    parser.add_argument(
        "--coverage",
        action="store_true",
        help="also report, and gate on, how much of the current source each note reaches",
    )
    args = parser.parse_args()

    sources = note_sources()
    if not sources:
        print("check_problem_note_sources: no problem notes are registered")
        return 0

    default_commit = pinned_commit()
    cache: dict[tuple[str, str], list[str]] = {}
    errors: list[str] = []
    checked = 0
    resolved_commits: set[str] = set()

    for source in sources:
        path = ROOT / source
        if not path.is_file():
            errors.append(f"{source}: registered problem note is missing")
            continue
        note_text = path.read_text(encoding="utf-8")
        commit = note_pinned_commit(note_text, default_commit)
        resolved_commits.add(commit)
        if (
            subprocess.run(
                ["git", "cat-file", "-e", f"{commit}^{{commit}}"],
                cwd=ROOT,
                capture_output=True,
                text=True,
                check=False,
            ).returncode
            != 0
        ):
            errors.append(f"{source}: pinned commit is absent: {commit}")
            continue
        found = links(note_text)
        if not found:
            errors.append(f"{source}: authored no formal source links")
        for file_name, line_number, declaration in found:
            checked += 1
            relative = library_relative(file_name)
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

    report: list[str] = []
    if args.coverage:
        report, coverage_failures = coverage_report(default_commit)
        errors.extend(coverage_failures)

    if errors:
        print(f"check_problem_note_sources: {len(errors)} failure(s)")
        for error in errors:
            print(f"  FAIL {error}")
        for line in report:
            print(line)
        return 1

    print(
        f"check_problem_note_sources: {checked} link(s) across {len(sources)} note(s) "
        f"resolve against {len(resolved_commits)} pinned commit(s)"
    )
    for line in report:
        print(line)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
