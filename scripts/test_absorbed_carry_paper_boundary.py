#!/usr/bin/env python3
"""Assure the #269 absorbed-carry bridge and its paper boundary."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "ErdosProblems" / "Erdos269" / "RestrictedFloorSum.lean"
PAPER = ROOT / "paper" / "erdos-269-three-prime-running-lcm.tex"
THEOREM = "no_positive_absorbedCarry_of_cofinalLocalWindowEscape"
PIN = "c5e7698474b32428e6a46ed4e7770d393b6f9dc8"


def theorem_block() -> str:
    source = SOURCE.read_text(encoding="utf-8")
    pattern = re.compile(
        rf"\btheorem\s+{re.escape(THEOREM)}\b(?P<body>.*?)(?=\nend\s)",
        re.DOTALL,
    )
    matches = list(pattern.finditer(source))
    assert len(matches) == 1, THEOREM
    return matches[0].group(0)


def test_source_keeps_every_conditional_bridge_hypothesis() -> None:
    block = theorem_block()
    for fragment in (
        "hescape : CofinalLocalWindowEscape b m shortBound",
        "hBcoprime : Nat.Coprime B 30",
        "hsmooth : smoothFactor ≠ 0",
        "hfactor : ∀ n, c n = smoothFactor * d n",
        "hrec : ∀ n",
        "hpos : ∀ n, 0 < d n",
        "hbound : ∀ n, Int.natAbs (d n) ≤ shortBound B n",
        "no_positive_reducedCarry_of_cofinalLocalWindowEscape",
        "integralCarry_cancel_commonFactor",
    ):
        assert fragment in block


def test_individual_paper_is_pinned_and_does_not_promote_the_bridge() -> None:
    paper = PAPER.read_text(encoding="utf-8")
    assert rf"\renewcommand{{\commit}}{{{PIN}}}" in paper
    assert THEOREM in paper
    assert "does not prove that" in paper
    assert "is not an irrationality theorem" in paper
    assert "endpoint remains open" in paper


if __name__ == "__main__":
    test_source_keeps_every_conditional_bridge_hypothesis()
    test_individual_paper_is_pinned_and_does_not_promote_the_bridge()
    print("absorbed-carry paper boundary: ok")
