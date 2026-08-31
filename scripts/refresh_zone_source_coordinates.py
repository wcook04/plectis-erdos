#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Refresh authored semantic-zone Lean coordinates from the declaration atlas.

Every file under ``docs/semantic/zones/`` pins Lean source coordinates by hand.
Each ``statement_nodes[].evidence[]`` row and each ``declaration_roles[]`` row
carries a ``module`` / ``declaration`` / ``line`` triple, and nothing kept those
line numbers current.  ``refresh_source_coordinates.py`` owns ``docs/claims.json``
and the two authored papers; ``refresh_reasoning_source_coordinates.py`` owns the
``\\lean`` citations in the reasoning parts.  Neither has ever opened a zone
file, so the zones were the one pinned-coordinate surface in this repository
with no refresher at all.

A hand-pinned coordinate with no refresher rots, and these did.  When this tool
was written, 3722 of the 149090 pinned rows, spread over 39 of the 94 zones,
named a line the declaration had moved off.  That is what made
``test_cyclotomic_semantic_digest.py`` fail with ``stale Z35 source coordinate
for binaryCyclotomicLayer_dvd_mersenneLayer: 1375 != 1416``; the Z35 row was one
of 134 stale rows in that file alone.  The generated zones Z19-Z27, which
``build_expansion_semantic_zones.py`` re-derives from the atlas, had zero.  The
rot is exactly the hand-authored half.

The declaration atlas is the authority here, as it already is for claims and for
the papers.  Two kinds of pin exist and they are not treated the same.

*Declaration pins* resolve in the atlas under the module they name.  Their line
is rewritten to the atlas line -- but only after the named declaration is found
in the declaration head starting at that line in the working-tree Lean source.
A coordinate is never moved onto a line that does not carry its declaration.

*Location pins* name a construct the atlas does not index: an anonymous
``instance``, a bare ``example``, a ``local instance``.  There is no authority to
compute a line for them, so, exactly as the reasoning refresher does with its
deliberately unnamed location citations, they stay authored and are checked
instead.  The pinned line must still begin a Lean construct once comments are
blanked.  When one does not, this tool names it and fails.  It does not leave the
stale number sitting there unexamined, which is the failure mode that produced
the rot in the first place.

``UNLOCATABLE_PINS`` carries the location pins that were already broken on the
day the refresher was written, one argued line each.  It is checked in both
directions -- an entry that no longer exists, or that now validates, is itself an
error -- so it cannot quietly grow into an allowlist.

Writing is surgical.  Only the digits of a ``line`` value are replaced; no zone
file is re-serialised, because 27 of the 94 do not round-trip through
``json.dumps`` under any setting and reformatting them would bury a coordinate
change under a whole-file diff.  Every edited file is re-parsed and compared
against the intended document before it is written.
"""

from __future__ import annotations

import argparse
import copy
import json
import re
import sys
from collections import defaultdict
from pathlib import Path
from typing import Iterator

from refresh_reasoning_source_coordinates import strip_lean_comments

ROOT = Path(__file__).resolve().parent.parent
ZONES = ROOT / "docs" / "semantic" / "zones"
ATLAS = ROOT / "docs" / "declaration_atlas.json"

# How many lines a declaration head may span.  The atlas points at the line the
# declaration keyword sits on, and a long binder list can push the name onto a
# following line -- `diagonalAdjacentSuffixResidue_powerTwo_oddDepth_central_iff_halfWordBand`
# is written under a bare `theorem`.  Four lines covers every declaration the
# zones cite; the sweep that fixed this defect verified all 144477 of them.
DECLARATION_HEAD_LINES = 4

DECLARATION_KEY = re.compile(r'"declaration"\s*:\s*"((?:[^"\\]|\\.)*)"')
JSON_STRING = re.compile(r'"(?:[^"\\]|\\.)*"')
LINE_VALUE = re.compile(r"\s*:\s*(-?\d+)")

# A Lean construct opener, after modifiers, at the start of a comment-stripped
# line.  `example` and `instance` are here because the location pins name them;
# the atlas does not index either.
CONSTRUCT_OPENER = re.compile(
    r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*"
    r"(?:(?:private|protected|noncomputable|nonrec|local|scoped|unsafe|partial|"
    r"irreducible)[ \t]+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|inductive|coinductive|instance|"
    r"axiom|constant|opaque|example|macro|notation|syntax)"
    r"(?![A-Za-z0-9_'])"
)

# A pin whose name encodes its own line, e.g. `example@79`.  Name and coordinate
# have to agree or one of them is lying.
SELF_DATED_PIN = re.compile(r"@(\d+)$")

# Location pins that already pointed at nothing when this refresher was written.
# Each is a real authored-classification defect that a coordinate refresher
# cannot repair, because there is no name for it to resolve: the fix is a
# decision about what the zone meant, not a line number. Keyed by
# (zone, module, declaration), so a repair anywhere else still fails loudly.
UNLOCATABLE_PINS: dict[tuple[str, str, str], str] = {
    ("Z01", "Erdos249257/CertificateKernel.lean", "is"): (
        "prose fragment, not a declaration; the atlas has no `is` anywhere and "
        "the pin lands mid-inequality"
    ),
    ("Z01", "Erdos249257/CertificateKernel.lean", "makes"): (
        "prose fragment, not a declaration; the pin lands on a `show` tactic"
    ),
    ("Z01", "Erdos249257/CertificateKernel.lean", "of"): (
        "prose fragment, not a declaration; the pin lands inside a docstring"
    ),
    ("Z01", "Erdos249257/CertificateKernel.lean", "closes"): (
        "prose fragment, not a declaration; the pin lands on a `norm_num`"
    ),
    ("Z05", "Erdos249257/DiagonalFreshLossBridge.lean", "anonymousInstance2"): (
        "positional name for an unindexed anonymous instance; the module now "
        "holds three of them and the zone pins two, so which construct this row "
        "follows is an authored decision"
    ),
    ("Z08", "Erdos249257/FirstHarmonicPivot.lean", "anonymousInstance1"): (
        "positional name for an unindexed anonymous instance; the pin lands on a "
        "`have` inside a proof"
    ),
    ("Z08", "Erdos249257/FirstHarmonicPivot.lean", "anonymousInstance2"): (
        "positional name for an unindexed anonymous instance; the pin lands on a "
        "`have` inside a proof"
    ),
    ("Z09", "Erdos249257/TotientMahlerDefect.lean", "of"): (
        "prose fragment, not a declaration; the pin lands on a blank line"
    ),
    ("Z10", "Erdos249257/DyadicPrefixCompression.lean", "invariant"): (
        "prose fragment, not a declaration; the pin lands on the word "
        "`inductive invariant` inside a docstring"
    ),
    (
        "Z12",
        "Erdos249257/GreedyAchievementSet.lean",
        "instDecidableHalfSecondChannelSeparatedRat",
    ): (
        "Lean's generated name for an anonymous instance, which the atlas does "
        "not index; the pin lands mid-expression"
    ),
    (
        "Z14",
        "Erdos249257/HalfFinalMiddlePhaseSieve.lean",
        "four_coeff_lower_le_binaryCoeffTail",
    ): (
        "the declaration exists, but in Erdos249257/HalfCylinderMiddleCarryLowerBound.lean; "
        "moving a citation between modules is an authored decision, and this "
        "repository deliberately refuses to guess it"
    ),
    (
        "Z14",
        "Erdos249257/HalfFinalMiddlePhaseSieve.lean",
        "truncatedMersenneWeight_two_three_six_seven_le_target",
    ): (
        "the declaration exists, but in Erdos249257/HalfCylinderMiddleCarryLowerBound.lean; "
        "moving a citation between modules is an authored decision"
    ),
    (
        "Z14",
        "Erdos249257/HalfFinalMiddlePhaseSieve.lean",
        "seamMiddleBranch_nextRemainder_add_belowPulse_eq",
    ): (
        "the declaration exists, but in Erdos249257/HalfCylinderMiddleCarryLowerBound.lean; "
        "moving a citation between modules is an authored decision"
    ),
}


class ZoneCoordinateError(RuntimeError):
    """A zone coordinate cannot be refreshed or verified."""


class Atlas:
    """Declaration lookup, resolving names the way the semantic corpus does."""

    def __init__(self, payload: dict) -> None:
        rows = payload.get("declarations")
        if not isinstance(rows, list):
            raise ZoneCoordinateError("declaration atlas has no declarations list")
        self.by_module_name: dict[tuple[str, str], list[dict]] = defaultdict(list)
        for row in rows:
            self.by_module_name[(row["module"], row["name"])].append(row)

    def find(self, module: str, name: str) -> dict | None:
        """Resolve a cited declaration inside the module it names.

        This mirrors ``build_semantic_corpus.find_declaration`` exactly, including
        its refusal to fall back on a bare name found in some other module. A
        refresher that resolved more widely than the corpus would write
        coordinates the corpus then reports as unresolved.
        """
        if not module or not name:
            return None
        rows = self.by_module_name.get((module, name))
        if rows:
            return rows[0]
        if "." in name:
            rows = self.by_module_name.get((module, name.rsplit(".", 1)[-1]))
            if rows:
                return rows[0]
        return None


class Sources:
    """Comment-stripped working-tree Lean sources, read once each."""

    def __init__(self) -> None:
        self._lines: dict[str, list[str] | None] = {}

    def lines(self, module: str) -> list[str] | None:
        if module not in self._lines:
            path = ROOT / module
            if path.is_file():
                text = strip_lean_comments(path.read_text(encoding="utf-8"))
                self._lines[module] = text.splitlines()
            else:
                self._lines[module] = None
        return self._lines[module]

    def declares_at(self, module: str, line: int, name: str) -> bool:
        """Is ``name`` written in the declaration head that starts at ``line``?"""
        lines = self.lines(module)
        if lines is None or not 1 <= line <= len(lines):
            return False
        token = re.compile(
            r"(?<![A-Za-z0-9_'])" + re.escape(name) + r"(?![A-Za-z0-9_'])"
        )
        window = lines[line - 1 : line - 1 + DECLARATION_HEAD_LINES]
        return any(token.search(candidate) for candidate in window)

    def opens_construct_at(self, module: str, line: int) -> bool:
        """Does ``line`` begin a Lean construct outside every comment?"""
        lines = self.lines(module)
        if lines is None or not 1 <= line <= len(lines):
            return False
        return CONSTRUCT_OPENER.match(lines[line - 1]) is not None


def pinned_rows(node: object, container: str = "") -> Iterator[tuple[str, dict]]:
    """Yield every ``declaration``-bearing row in document order.

    Document order is what lets the textual rewrite below line each parsed row up
    with its own ``"line"`` token, so the walk must not impose an order of its
    own: dictionaries are visited in key order and lists in element order.
    """
    if isinstance(node, dict):
        if "declaration" in node:
            yield container, node
            return
        for key, value in node.items():
            yield from pinned_rows(value, key)
    elif isinstance(node, list):
        for value in node:
            yield from pinned_rows(value, container)


def line_value_span(text: str, cursor: int) -> tuple[int, int] | None:
    """Span of the ``line`` number in the object whose row starts at ``cursor``.

    ``cursor`` sits just past a ``"declaration"`` key, so the scan starts at
    relative depth zero inside that object and stops at the ``}`` closing it.
    """
    depth = 0
    index = cursor
    length = len(text)
    while index < length:
        char = text[index]
        if char == '"':
            match = JSON_STRING.match(text, index)
            if match is None:
                raise ZoneCoordinateError("unterminated string in zone JSON")
            if depth == 0 and match.group(0) == '"line"':
                value = LINE_VALUE.match(text, match.end())
                if value is None:
                    raise ZoneCoordinateError("zone row has a non-integer line value")
                return value.span(1)
            index = match.end()
            continue
        if char in "{[":
            depth += 1
        elif char in "}]":
            if depth == 0:
                return None
            depth -= 1
        index += 1
    raise ZoneCoordinateError("zone row is not closed")


class Report:
    def __init__(self) -> None:
        self.rewritten: list[str] = []
        self.declaration_pins = 0
        self.location_pins = 0
        self.broken: list[str] = []
        self.repaired_exemptions: list[str] = []
        self.pinned: set[tuple[str, str, str]] = set()


def plan_zone(path: Path, atlas: Atlas, sources: Sources, report: Report) -> str:
    """Return the zone file's refreshed text, editing only ``line`` values."""
    raw = path.read_text(encoding="utf-8")
    document = json.loads(raw)
    zone = str(document.get("zone_id") or path.stem)
    intended = copy.deepcopy(document)

    rows = list(pinned_rows(intended))
    keys = list(DECLARATION_KEY.finditer(raw))
    if len(keys) != len(rows):
        raise ZoneCoordinateError(
            f"{path.relative_to(ROOT)}: found {len(keys)} textual declaration "
            f"rows but {len(rows)} parsed ones; the surgical rewrite cannot "
            "line them up and will not guess"
        )

    edits: list[tuple[int, int, str]] = []
    for key, (container, row) in zip(keys, rows):
        if json.loads(f'"{key.group(1)}"') != row.get("declaration"):
            raise ZoneCoordinateError(
                f"{path.relative_to(ROOT)}: textual and parsed declaration rows "
                "disagree; the surgical rewrite cannot line them up"
            )
        module = str(row.get("module") or "")
        name = str(row.get("declaration") or "")
        where = f"{zone} {container or 'row'} {module}::{name}"
        current = row.get("line")
        exemption = (zone, module, name)
        report.pinned.add(exemption)

        found = atlas.find(module, name)
        if found is not None:
            report.declaration_pins += 1
            target = found["line"]
            if not sources.declares_at(found["module"], target, found["name"]):
                raise ZoneCoordinateError(
                    f"{where}: the atlas puts {found['name']} at "
                    f"{found['module']}:{target}, but that declaration head does "
                    "not name it; refusing to pin a coordinate onto a line that "
                    "does not carry its declaration"
                )
            if exemption in UNLOCATABLE_PINS:
                report.repaired_exemptions.append(
                    f"{where}: recorded as unlocatable but now resolves in the atlas"
                )
            if current != target:
                span = line_value_span(raw, key.end())
                if span is None:
                    raise ZoneCoordinateError(f"{where}: row has no line coordinate")
                edits.append((span[0], span[1], str(target)))
                row["line"] = target
            continue

        report.location_pins += 1
        self_dated = SELF_DATED_PIN.search(name)
        dated_disagrees = self_dated is not None and int(self_dated.group(1)) != current
        located = (
            isinstance(current, int)
            and sources.opens_construct_at(module, current)
            and not dated_disagrees
        )
        if located:
            if exemption in UNLOCATABLE_PINS:
                report.repaired_exemptions.append(
                    f"{where}: recorded as unlocatable but its pin now validates"
                )
            continue
        if exemption in UNLOCATABLE_PINS:
            continue
        report.broken.append(
            f"{where}: pinned at line {current}, which the atlas cannot resolve "
            "and which no longer begins a Lean construct"
        )

    if not edits:
        return raw

    updated = raw
    for begin, end, value in sorted(edits, reverse=True):
        updated = f"{updated[:begin]}{value}{updated[end:]}"
    if json.loads(updated) != intended:
        raise ZoneCoordinateError(
            f"{path.relative_to(ROOT)}: the surgical rewrite did not reproduce the "
            "intended document; refusing to write"
        )
    report.rewritten.append(path.relative_to(ROOT).as_posix())
    return updated


def render() -> tuple[dict[Path, str], Report]:
    atlas = Atlas(json.loads(ATLAS.read_text(encoding="utf-8")))
    sources = Sources()
    report = Report()
    rendered: dict[Path, str] = {}
    for path in sorted(ZONES.glob("*.json")):
        rendered[path] = plan_zone(path, atlas, sources, report)
    for exemption in sorted(UNLOCATABLE_PINS):
        if exemption not in report.pinned:
            report.repaired_exemptions.append(
                f"{exemption[0]} {exemption[1]}::{exemption[2]}: recorded as "
                "unlocatable but the zone no longer pins it"
            )
    return rendered, report


def describe(report: Report) -> str:
    return (
        f"{report.declaration_pins} declaration pins refreshed from the atlas, "
        f"{report.location_pins} authored location pins checked, "
        f"{len(UNLOCATABLE_PINS)} recorded unlocatable pin(s)"
    )


def complain(report: Report) -> int:
    """Report pins the refresher cannot stand behind, loudly."""
    failed = 0
    if report.broken:
        print(
            "zone coordinates pin declarations that cannot be located at all:",
            file=sys.stderr,
        )
        for message in report.broken:
            print(f"  {message}", file=sys.stderr)
        print(
            "  repair the zone row, or record it in UNLOCATABLE_PINS in "
            "scripts/refresh_zone_source_coordinates.py with the reason",
            file=sys.stderr,
        )
        failed = 1
    if report.repaired_exemptions:
        print("recorded unlocatable pins that are no longer unlocatable:", file=sys.stderr)
        for message in report.repaired_exemptions:
            print(f"  {message}", file=sys.stderr)
        print(
            "  drop each from UNLOCATABLE_PINS; an exemption that no longer "
            "describes anything is how an argued list turns into an allowlist",
            file=sys.stderr,
        )
        failed = 1
    return failed


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="report stale zone coordinates without writing anything",
    )
    args = parser.parse_args(argv)

    try:
        rendered, report = render()
    except (ZoneCoordinateError, OSError, ValueError) as exc:
        print(f"refresh_zone_source_coordinates: {exc}", file=sys.stderr)
        return 2

    if complain(report):
        return 1

    if args.check:
        if report.rewritten:
            print("zone source coordinates are stale: " + ", ".join(report.rewritten))
            return 1
        print(f"zone source coordinates current: {describe(report)}")
        return 0

    for path, text in rendered.items():
        if text != path.read_text(encoding="utf-8"):
            path.write_text(text, encoding="utf-8")
    if report.rewritten:
        print(f"refreshed zone source coordinates in {len(report.rewritten)} zone(s): {describe(report)}")
    else:
        print(f"zone source coordinates were already current: {describe(report)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
