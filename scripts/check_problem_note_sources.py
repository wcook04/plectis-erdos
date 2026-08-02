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

    python3 scripts/check_problem_note_sources.py --coverage

``--list`` prints the resolved link inventory instead of only a verdict.
``--coverage`` additionally requires module-qualified links to the configured
headline declarations and gates the fraction of current declarations reached.
"""

from __future__ import annotations

import argparse
import json
import math
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

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
NOTE_COMMIT_RE = re.compile(
    r"\\renewcommand\{\\commit\}\{([0-9a-f]{40})\}"
)
COMMIT_SHORT_RE = re.compile(
    r"\\newcommand\{\\commitshort\}\{([0-9a-f]{12})\}"
)
NOTE_COMMIT_SHORT_RE = re.compile(
    r"\\renewcommand\{\\commitshort\}\{([0-9a-f]{12})\}"
)
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


def strip_lean_comments(text: str) -> str:
    """Remove nested Lean comments while preserving source line boundaries."""
    output: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    while index < len(text):
        if block_depth:
            if text.startswith("/-", index):
                block_depth += 1
                output.extend((" ", " "))
                index += 2
            elif text.startswith("-/", index):
                block_depth -= 1
                output.extend((" ", " "))
                index += 2
            else:
                character = text[index]
                output.append("\n" if character == "\n" else " ")
                index += 1
            continue

        character = text[index]
        if in_string:
            output.append(character)
            index += 1
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                in_string = False
            continue

        if text.startswith("/-", index):
            block_depth = 1
            output.extend((" ", " "))
            index += 2
        elif text.startswith("--", index):
            while index < len(text) and text[index] != "\n":
                output.append(" ")
                index += 1
        else:
            output.append(character)
            index += 1
            if character == '"':
                in_string = True
    return "".join(output)


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


def pinned_commitshort() -> str:
    match = COMMIT_SHORT_RE.search(PREAMBLE.read_text(encoding="utf-8"))
    if match is None:
        raise SystemExit(
            f"{PREAMBLE.relative_to(ROOT)}: no pinned \\commitshort is declared"
        )
    return match.group(1)


def note_pinned_commit(note_text: str, default_commit: str) -> str:
    """Return a note-local source pin, falling back to the corpus default."""
    match = NOTE_COMMIT_RE.search(strip_comments(note_text))
    return default_commit if match is None else match.group(1)


def note_pinned_commitshort(note_text: str, default_commitshort: str) -> str:
    """Return a note-local display pin, falling back to the corpus default."""
    match = NOTE_COMMIT_SHORT_RE.search(strip_comments(note_text))
    return default_commitshort if match is None else match.group(1)


def source_pin_failure(
    source: str,
    note_text: str,
    default_commit: str,
    default_commitshort: str,
) -> str | None:
    """Reject a displayed short pin that does not name the effective commit."""
    commit = note_pinned_commit(note_text, default_commit)
    commitshort = note_pinned_commitshort(note_text, default_commitshort)
    expected = commit[:12]
    if commitshort == expected:
        return None
    return (
        f"{source}: displayed \\commitshort {commitshort} does not match "
        f"the effective \\commit prefix {expected}"
    )


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


def module_relative(module_name: str) -> str:
    """Repository path for a dotted Lean module name."""
    return "/".join(module_name.split(".")) + ".lean"


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
    # Lean also permits the declaration keyword and name on consecutive
    # lines. Authored links point at the name line in that layout.
    if re.match(rf"{re.escape(name)}(?![A-Za-z0-9_'])\s*:", stripped):
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
    for line in strip_lean_comments(text).splitlines():
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


DeclarationKey = tuple[str, str]


def linked_declaration_keys(note_text: str) -> set[DeclarationKey]:
    """Module-qualified declarations linked by one problem note."""
    return {
        (library_relative(file_name), declaration)
        for file_name, _line, declaration in links(note_text)
        if declaration is not None
    }


def declarations_for_module(relative: str, text: str) -> list[DeclarationKey]:
    """Module-qualified declarations parsed from one live Lean source."""
    return [(relative, name) for name in declarations_in(text)]


def validated_coverage_floor(
    owner: dict[str, Any], *, label: str = "note_coverage_floor"
) -> tuple[float | None, list[str]]:
    """Return a finite coverage floor in `(0, 1]`, or a validation failure."""
    value = owner.get("note_coverage_floor")
    if (
        isinstance(value, bool)
        or not isinstance(value, (int, float))
        or not math.isfinite(float(value))
        or not 0 < float(value) <= 1
    ):
        return None, [
            f"{label} must be a finite number in the interval (0, 1]"
        ]
    return float(value), []


def required_note_declaration_failures(
    row: dict[str, Any],
    current: set[DeclarationKey],
    linked: set[DeclarationKey],
) -> list[str]:
    """Validate and enforce the problem's module-qualified headline anchors."""
    failures: list[str] = []
    raw_anchors = row.get("required_note_declarations")
    if not isinstance(raw_anchors, list) or not raw_anchors:
        return [
            f"{row['problem_id']}: required_note_declarations must be a nonempty list"
        ]

    allowed_modules = {
        module_relative(module)
        for module in [row["principal_module"], *row.get("companion_modules", [])]
    }
    seen: set[DeclarationKey] = set()
    for anchor in raw_anchors:
        if not isinstance(anchor, dict):
            failures.append(
                f"{row['problem_id']}: required note declaration must be an object"
            )
            continue
        module = anchor.get("module")
        declaration = anchor.get("declaration")
        if not isinstance(module, str) or not module:
            failures.append(
                f"{row['problem_id']}: required note declaration has invalid module"
            )
            continue
        if not isinstance(declaration, str) or not declaration:
            failures.append(
                f"{row['problem_id']}: required note declaration has invalid declaration"
            )
            continue
        key = (module_relative(module), declaration)
        if key in seen:
            failures.append(
                f"{row['problem_id']}: duplicate required note declaration "
                f"{key[0]}::{key[1]}"
            )
            continue
        seen.add(key)
        if key[0] not in allowed_modules:
            failures.append(
                f"{row['problem_id']}: required note declaration module "
                f"{key[0]} is outside the indexed problem modules"
            )
        elif key not in current:
            failures.append(
                f"{row['problem_id']}: required note declaration "
                f"{key[0]}::{key[1]} is absent from current source"
            )
        elif key not in linked:
            failures.append(
                f"{row['problem_id']}: note does not link required headline "
                f"declaration {key[0]}::{key[1]}"
            )
    return failures


def coverage_report(default_commit: str) -> tuple[list[str], list[str]]:
    """Report how much of each problem's current source its note reaches.

    A note pins its links to one commit, so it cannot break when the library
    moves.  The cost of that safety is that it can fall silently behind.  This
    measures the gap in the only terms that matter to a reader: whether every
    configured headline declaration is linked, how many declarations that
    exist *now* the note mentions, and whether the modules have changed at all
    since the note was pinned.
    """
    lines: list[str] = []
    failures: list[str] = []
    index = json.loads(INDEX_SOURCE.read_text(encoding="utf-8"))
    floor, floor_failures = validated_coverage_floor(index)
    failures.extend(floor_failures)
    for row, source in note_for_problem():
        note_text = (ROOT / source).read_text(encoding="utf-8")
        commit = note_pinned_commit(note_text, default_commit)
        linked = linked_declaration_keys(note_text)
        modules = [row["principal_module"], *row.get("companion_modules", [])]
        current: list[DeclarationKey] = []
        moved: list[str] = []
        for module in modules:
            relative = module_relative(module)
            path = ROOT / relative
            if not path.is_file():
                failures.append(f"{row['problem_id']}: {relative} is missing")
                continue
            live = path.read_text(encoding="utf-8")
            current.extend(declarations_for_module(relative, live))
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
        current_set = set(current)
        failures.extend(
            required_note_declaration_failures(row, current_set, linked)
        )
        covered = [key for key in current if key in linked]
        ratio = len(covered) / len(current)
        status = "behind" if moved else "current"
        lines.append(
            f"  {row['problem_id']}: {len(covered)}/{len(current)} declarations "
            f"linked ({ratio:.0%}), source {status}"
        )
        if moved:
            lines.append(f"      moved since the pin: {', '.join(sorted(moved))}")
            missing = [key for key in current if key not in linked]
            if missing:
                head = ", ".join(
                    f"{relative}::{name}" for relative, name in missing[:6]
                )
                more = "" if len(missing) <= 6 else f", and {len(missing) - 6} more"
                lines.append(f"      not reached by the note: {head}{more}")
        row_floor = floor
        if "note_coverage_floor" in row:
            row_floor, row_floor_failures = validated_coverage_floor(
                row,
                label=f"{row['problem_id']}.note_coverage_floor",
            )
            failures.extend(row_floor_failures)
        if row_floor is not None and ratio < row_floor:
            failures.append(
                f"{row['problem_id']}: note reaches {ratio:.0%} of current "
                f"declarations, below the {row_floor:.0%} floor; rewrite the note "
                f"and repin, or lower its note_coverage_floor deliberately"
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
                relative = module_relative(module)
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
    default_commitshort = pinned_commitshort()
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
        pin_failure = source_pin_failure(
            source, note_text, default_commit, default_commitshort
        )
        if pin_failure is not None:
            errors.append(pin_failure)
        commit = note_pinned_commit(note_text, default_commit)
        resolved_commits.add(commit)
        if (
            subprocess.run(
                ["git", "cat-file", "-e", f"{commit}^{{commit}}"],
                cwd=ROOT,
                capture_output=True,
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
