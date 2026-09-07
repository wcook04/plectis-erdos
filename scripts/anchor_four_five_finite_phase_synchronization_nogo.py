#!/usr/bin/env python3
"""Exact audit for the finite-phase synchronization no-go at 1/465.

The script checks concrete synchronized instances.  The universal and
infinitely-many statements are algebraic consequences proved in the companion
note; this finite audit is not their authority.
"""

from __future__ import annotations

import json
import math
from fractions import Fraction


TARGET = Fraction(1, 465)


def greedy_prefix(depth: int) -> tuple[list[int], Fraction]:
    residual = TARGET
    selected: list[int] = []
    for rank in range(1, depth + 1):
        weight = Fraction(1, (1 << rank) - 1)
        if residual >= weight:
            residual -= weight
            selected.append(rank)
    assert residual > 0
    return selected, residual


def synchronized_receipt(depth: int) -> dict[str, object]:
    selected, residual = greedy_prefix(depth)
    height = math.lcm(20, *selected)

    assert height % 20 == 0
    assert pow(2, height, 465) == 1
    for rank in selected:
        assert height % rank == 0
        assert pow(2, height, (1 << rank) - 1) == 1

    selected_mass = TARGET - residual
    target_phase = TARGET
    selected_phase = sum(
        (
            Fraction(pow(2, height % rank), (1 << rank) - 1)
            for rank in selected
        ),
        start=Fraction(0),
    )
    assert selected_phase == selected_mass
    assert selected_phase < target_phase

    # Verify both sufficient large-height inequalities using exact integer
    # comparisons.  For the named cutoffs the first synchronization height is
    # already sufficient.
    power = 1 << height
    assert power * residual > 1
    assert Fraction(2, (power << 1) - 1) < residual

    quotient_numerator = ((power - 1) * residual.numerator)
    assert quotient_numerator % residual.denominator == 0
    quotient = quotient_numerator // residual.denominator
    assert quotient > 0

    phase_margin = selected_phase - (quotient + target_phase - 1)
    assert phase_margin == 1 - power * residual
    assert phase_margin < 0

    # Avoid serializing the enormous synchronized quotient.  Its sign and
    # exact identity have already been checked above.
    return {
        "cutoff": depth,
        "selected": selected,
        "synchronization_height": height,
        "target_phase": str(target_phase),
        "selected_phase": str(selected_phase),
        "phase_shortfall": str(target_phase - selected_phase),
        "residual": str(residual),
        "quotient_positive": True,
        "dyadic_cutoff_violated": True,
        "phase_inequality_violated": True,
    }


def main() -> None:
    receipts = [synchronized_receipt(depth) for depth in (9, 20)]
    print(
        json.dumps(
            {
                "target": "1/465",
                "receipts": receipts,
                "claim_status": "exact finite audit of an algebraic theorem",
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
