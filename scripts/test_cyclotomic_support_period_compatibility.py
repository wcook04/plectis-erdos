#!/usr/bin/env python3
"""Assure the source-current #249 cyclotomic support/period boundary."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "ErdosProblems" / "Erdos249" / "CyclotomicAnchoredKill.lean"
PAPER = ROOT / "paper" / "erdos-249-binary-totient-series.tex"
THEOREM = (
    "exists_unbounded_binaryCyclotomicSupport_with_periodLock_of_not_irrational"
)


def theorem_block() -> str:
    source = SOURCE.read_text(encoding="utf-8")
    pattern = re.compile(
        rf"\btheorem\s+{re.escape(THEOREM)}\b(?P<body>.*?)(?=\n/--|\n(?:theorem|lemma|def)\s)",
        re.DOTALL,
    )
    matches = list(pattern.finditer(source))
    assert len(matches) == 1, THEOREM
    return matches[0].group(0)


def test_source_states_the_conditional_conjunction_without_an_endpoint() -> None:
    block = theorem_block()
    assert "hrat : ¬ Irrational" in block
    assert "UnboundedPrimeDivisorSupply binaryCyclotomicLayer h" in block
    assert "totientTail (N + h) - totientTail N" in block
    assert "binaryCyclotomicLayer_unboundedPrimeDivisorSupply" in block
    assert "eventual_period_of_not_irrational" in block


def test_individual_paper_preserves_the_no_go_boundary() -> None:
    paper = PAPER.read_text(encoding="utf-8")
    assert THEOREM in paper
    assert "unbounded support cannot be the missing contradiction" in paper
    assert "neither constructs a rational example" in paper
    assert "Erd\\H{o}s \\#249 remains open" in paper


if __name__ == "__main__":
    test_source_states_the_conditional_conjunction_without_an_endpoint()
    test_individual_paper_preserves_the_no_go_boundary()
    print("cyclotomic support/period boundary: ok")
