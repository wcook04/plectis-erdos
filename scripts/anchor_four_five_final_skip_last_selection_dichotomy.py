#!/usr/bin/env python3
"""Exact audit for the final-skip last-selection dichotomy at x = 1/465."""

from __future__ import annotations

from fractions import Fraction


def source_pair(rank: int) -> int:
    return {0: 3, 5: 2, 7: 3, 9: 3}.get(rank % 10, 0)


def initial_orbit(
    depth: int = 20,
) -> tuple[list[int], dict[int, tuple[int, int]]]:
    loads = [0] * (2 * depth + 1)
    remainder = 0
    bits: list[int] = []
    selected_data: dict[int, tuple[int, int]] = {}
    selected_count = 0
    for rank in range(1, depth + 1):
        pulse = source_pair(rank)
        divisor_load = 2 * loads[2 * rank - 1] + loads[2 * rank]
        pre_remainder = 4 * remainder + pulse - divisor_load
        weight = (1 << (2 * rank)) // ((1 << rank) - 1)
        bit = int(pre_remainder >= weight)
        remainder = pre_remainder - bit * weight
        bits.append(bit)
        if bit:
            selected_data[rank] = (remainder, selected_count)
            selected_count += 1
            for multiple in range(2 * rank, 2 * depth + 1, rank):
                loads[multiple] += 1
    return bits, selected_data


def phase(depth: int, denominator: int) -> Fraction:
    return Fraction(pow(4, depth, denominator), denominator)


def resolvent(depth: int, support: set[int]) -> Fraction:
    return sum(
        (phase(depth, (1 << rank) - 1) for rank in support),
        Fraction(),
    )


def divisor_load(rank: int, support: set[int]) -> int:
    odd = sum((2 * rank - 1) % selected == 0 for selected in support)
    even = sum((2 * rank) % selected == 0 for selected in support)
    return 2 * odd + even


def audit_tail_transport() -> None:
    support = {9, 13, 14, 17, 19, 21, 22, 23}
    for selected_rank, final_rank in [(23, 24), (23, 40), (29, 61)]:
        active = {rank for rank in support if rank <= selected_rank}
        gap = final_rank - selected_rank
        source_prefix = sum(
            Fraction(source_pair(selected_rank + step), 4**step)
            for step in range(1, gap + 1)
        )
        source_tail_identity = (
            Fraction(pow(4, selected_rank, 465), 465)
            - Fraction(pow(4, final_rank, 465), 465 * 4**gap)
        )
        assert source_prefix == source_tail_identity

        load_prefix = sum(
            Fraction(divisor_load(selected_rank + step, active), 4**step)
            for step in range(1, gap + 1)
        )
        assert load_prefix == (
            resolvent(selected_rank, active)
            - resolvent(final_rank, active) / 4**gap
        )


def audit_anchor_gap() -> None:
    lower = Fraction((1 << 8) - 1, (1 << 9) - 1) + Fraction(
        (1 << 12) - 1,
        (1 << 13) - 1,
    )
    upper = Fraction(464, 465) + Fraction(1, 4**13)
    assert lower == Fraction(4_181_250, 4_185_601)
    assert lower - upper == Fraction(
        145_113_321_685_039,
        130_614_281_644_277_760,
    )
    assert lower > upper

    repeat_upper = Fraction(464, 465) + Fraction(15, 4**13)
    assert lower - repeat_upper == Fraction(
        145_086_073_422_529,
        130_614_281_644_277_760,
    )
    assert lower > repeat_upper


def main() -> None:
    bits, selected_data = initial_orbit()
    assert bits[8] == 1
    assert bits[12] == 1
    assert bits[17] == 0
    selected = [rank for rank, bit in enumerate(bits, 1) if bit]
    assert selected == [9, 13, 14, 17, 19]
    assert all(
        remainder > selected_before
        for remainder, selected_before in selected_data.values()
    )
    audit_tail_transport()
    audit_anchor_gap()
    print(
        "final-skip last-selection dichotomy PASS: initial anchors, exact "
        "source/resolvent plateau tails, strict anchor-deficit gap, and "
        "small-margin repeat gap"
    )


if __name__ == "__main__":
    main()
