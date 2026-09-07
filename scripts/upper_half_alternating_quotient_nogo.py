#!/usr/bin/env python3
"""Exact audit for UpperHalfAlternatingQuotientNogo.md."""

from __future__ import annotations

import json
from fractions import Fraction


DENOMINATOR = 465


def mersenne(rank: int) -> int:
    return (1 << rank) - 1


def alternating_cell(selected_rank: int, jump: int) -> tuple[int, int]:
    """Return the quotient and remainder in (5)--(6)."""
    quotient_length, tail = divmod(selected_rank, jump)
    alternating = sum(
        (-1) ** (term - 1) * (1 << (selected_rank - term * jump))
        for term in range(1, quotient_length + 1)
    )
    if quotient_length % 2 == 0 and tail > 0:
        quotient = alternating
        remainder = (1 << tail) - 2
    else:
        quotient = alternating - 1
        if quotient_length % 2 == 0:
            remainder = 1 << jump
        else:
            remainder = (1 << jump) - (1 << tail) - 1
    return quotient, remainder


def pulse_division(pulse_rank: int, selected_rank: int) -> tuple[int, Fraction]:
    """Return the integer and fractional terms in (9)."""
    quotient_length, tail = divmod(pulse_rank, selected_rank)
    integer_pulse = (1 << tail) * sum(
        1 << (term * selected_rank) for term in range(quotient_length)
    )
    fractional_residue = Fraction(mersenne(tail), mersenne(selected_rank))
    return integer_pulse, fractional_residue


def check_alternating_cells(depth: int = 160) -> int:
    checked = 0
    for selected_rank in range(2, depth + 1):
        for jump in range(1, selected_rank):
            quotient, remainder = alternating_cell(selected_rank, jump)
            divisor = (1 << jump) + 1
            numerator = mersenne(selected_rank) - 1
            assert quotient == numerator // divisor
            assert remainder == numerator % divisor
            if jump < selected_rank < 2 * jump:
                height = selected_rank - jump
                assert quotient == mersenne(height)
                assert (
                    mersenne(selected_rank) - quotient
                    == (1 << height) * mersenne(jump)
                )
            checked += 1
    return checked


def check_pulse_divisions(depth: int = 80) -> int:
    checked = 0
    for pulse_rank in range(1, depth + 1):
        for selected_rank in range(1, depth + 1):
            integer_pulse, fractional_residue = pulse_division(
                pulse_rank,
                selected_rank,
            )
            assert (
                Fraction(mersenne(pulse_rank), mersenne(selected_rank))
                == integer_pulse + fractional_residue
            )
            if pulse_rank % selected_rank == 0:
                assert fractional_residue == 0
            checked += 1
    return checked


def reachable_counterexample() -> dict[str, object]:
    target = Fraction(81, DENOMINATOR)
    residual = target
    selected: list[int] = []
    unsafe_skips: list[int] = []

    for rank in range(1, 6):
        weight = Fraction(1, mersenne(rank))
        if weight <= residual:
            residual -= weight
            selected.append(rank)
        elif residual >= Fraction(1, 1 << rank):
            unsafe_skips.append(rank)

    assert selected == [3]
    assert unsafe_skips == [5]
    assert residual == Fraction(34, 1085)
    assert Fraction(1, 1 << 5) < residual < Fraction(1, mersenne(5))

    selected_rank = 3
    unsafe_rank = 5
    jump = unsafe_rank - selected_rank
    height = selected_rank - jump
    quotient = (
        mersenne(selected_rank) - 1
    ) // ((1 << jump) + 1)
    pre_numerator = 81
    post_numerator = (
        mersenne(selected_rank) * pre_numerator - DENOMINATOR
    )
    least_representative = post_numerator - quotient * pre_numerator
    complement = (quotient + 1) * pre_numerator - post_numerator

    assert (jump, height, quotient) == (2, 1, 1)
    assert post_numerator == 102
    assert least_representative == 21
    assert complement == 60
    assert least_representative not in (81,)
    assert complement not in (81,)

    pulse = mersenne(jump) * target
    assert Fraction(1, 1 << height) < pulse
    assert pulse < Fraction(1, 1 << height) * (1 + target)

    return {
        "target": "81/465",
        "selected_ranks_through_5": selected,
        "dyadically_unsafe_skips_through_5": unsafe_skips,
        "cell": {
            "selected_rank": selected_rank,
            "unsafe_rank": unsafe_rank,
            "jump": jump,
            "height": height,
            "quotient": quotient,
        },
        "unreduced_numerators": {
            "pre_selection": pre_numerator,
            "post_selection": post_numerator,
            "least_representative": least_representative,
            "complement": complement,
        },
        "selected_divisor_mass_before_rank_3": 0,
        "claim_status": "exact reachable counterexample for source-independent closure",
    }


def check_fixed_source_congruence_vacuity() -> dict[str, object]:
    """Check the finite support fact used after (17)."""
    residual = Fraction(1, DENOMINATOR)
    product = 1
    selected: list[int] = []
    for rank in range(1, 26):
        weight = Fraction(1, mersenne(rank))
        if weight <= residual:
            residual -= weight
            product *= mersenne(rank)
            selected.append(rank)

    assert selected == [9, 13, 14, 17, 19, 21, 22, 23, 24, 25]
    assert product % DENOMINATOR == 0
    assert mersenne(14) % 3 == 0
    assert mersenne(24) % 5 == 0
    assert mersenne(25) % 31 == 0
    return {
        "selected_ranks_through_25": selected,
        "prefix_product_divisible_by_465": True,
    }


def main() -> None:
    result = reachable_counterexample()
    result["alternating_cells_checked"] = check_alternating_cells()
    result["pulse_divisions_checked"] = check_pulse_divisions()
    result["fixed_1_over_465_finite_check"] = (
        check_fixed_source_congruence_vacuity()
    )
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
