#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Tests for the systems paper's generated record counts."""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import build_systems_paper_counts as counts  # noqa: E402


def require(condition: bool, message: str) -> None:
    """Keep the tests active under ``python3 -O``."""
    if not condition:
        raise AssertionError(message)


def main() -> int:
    text = counts.PAPER.read_text(encoding="utf-8")
    if counts.VERSION_TWO in text:
        from test_systems_paper_pipeline import run_counts
        return run_counts()
    require(counts.errors(text) == [], f"the committed paper disagrees with the checkout: {counts.errors(text)}")
    checks = 1

    stated = counts.region_values(text, counts.BEGIN, counts.END)
    # A changed ledger count, a changed frontier count and a missing macro are each rejected.
    for name in ("LedgerRows", "LeanModules", "Claims", "Returns", "Contrasts"):
        mutated = text.replace(rf"\newcommand{{\{name}}}{{{stated[name]}}}",
                               rf"\newcommand{{\{name}}}{{{stated[name]}0}}", 1)
        require(mutated != text, f"mutation of {name} did not apply")
        require(any(f"\\{name}:" in e for e in counts.errors(mutated)), f"a stale {name} was accepted")
        checks += 1
    frontier = counts.region_values(text, counts.FRONTIER_BEGIN, counts.FRONTIER_END)
    mutated = text.replace(rf"\newcommand{{\AFIdle}}{{{frontier['AFIdle']}}}", r"\newcommand{\AFIdle}{0}", 1)
    require(any("AFIdle" in e for e in counts.errors(mutated)), "a stale frontier count was accepted")
    checks += 1
    dropped = text.replace(rf"\newcommand{{\Claims}}{{{stated['Claims']}}}" + "\n", "", 1)
    require(any("\\Claims:" in e for e in counts.errors(dropped)), "a missing macro was accepted")
    checks += 1

    # The journal counts stop at the named head, so appending events moves nothing;
    # a head naming no event is refused.
    events = counts.research_record.read_events(counts.research_record.journal_path(counts.ROOT))
    first = events[0]["event_sha"][: counts.HEAD_LENGTH]
    early = counts.journal_values(counts.ROOT, first)
    require(early["JournalHead"] == first and early["Rounds"] <= 1, "the journal prefix is not honoured")
    try:
        counts.journal_values(counts.ROOT, "f" * counts.HEAD_LENGTH)
    except counts.CountError:
        pass
    else:
        raise AssertionError("a journal head naming no event was accepted")
    checks += 2

    require(counts.word_list([5, 6, 8]) == "five, six and eight", "word list")
    require(counts.word_list([13]) == "13" and counts.word(7) == "seven", "word rendering")
    checks += 2

    # The sentence after the relation counts must agree with them, in both directions.
    want = counts.region_values(counts._expected_region(str(counts.ROOT), stated["JournalHead"]),
                                counts.BEGIN, counts.END)
    every_row = want["Relations"] == want["RelationsAttested"]
    prose = " ".join(text.split())
    wrong = (prose.replace(counts.RELATIONS_ALL, "Some rows are attested; the atlas "
                           + counts.RELATIONS_SOME) if every_row
             else prose.replace(counts.RELATIONS_SOME, "rows. " + counts.RELATIONS_ALL))
    require(wrong != prose, "the relation sentence mutation did not apply")
    require(any("relation row" in e for e in counts.errors(wrong)), "a relation sentence contradicting the counts was accepted")
    checks += 1

    # A ledger whose Comparator rows do not cover its exact and specialising rows is refused.
    with tempfile.TemporaryDirectory() as tmp:
        docs = Path(tmp) / "docs"
        docs.mkdir()
        ledger = json.loads((counts.ROOT / "docs" / "paper_lean_coverage.json").read_text(encoding="utf-8"))
        ledger["summary"]["comparator"]["pending"] = ledger["summary"]["comparator"].get("pending", 0) + 1
        (docs / "paper_lean_coverage.json").write_text(json.dumps(ledger), encoding="utf-8")
        try:
            counts.ledger_values(Path(tmp))
        except counts.CountError:
            pass
        else:
            raise AssertionError("a ledger with uncovered Comparator rows was accepted")
    checks += 1

    region = counts.render({"A": 1_234, "B": "x"})
    require(region.splitlines()[1] == r"\newcommand{\A}{1,234}", "integers render with separators")
    require(counts.replace_region(f"a\n{counts.BEGIN}\nold\n{counts.END}\nb", region).count(counts.BEGIN) == 1,
            "replace_region keeps one region")
    checks += 2
    print(f"systems-paper record counts tests: {checks} checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
