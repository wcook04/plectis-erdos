#!/usr/bin/env python3
"""Exact audit for PeriodTwentyBufferedComparatorNoGo.md."""

from __future__ import annotations

import json
from fractions import Fraction
from math import gcd, isqrt


DENOMINATOR = 465
TARGET_NUMERATOR = 64
TARGET = Fraction(TARGET_NUMERATOR, DENOMINATOR)


def weight(rank: int) -> Fraction:
    return Fraction(1, (1 << rank) - 1)


def quotient(horizon: int, rank: int) -> int:
    return (1 << horizon) // ((1 << rank) - 1)


def source_period(numerator: int) -> tuple[int, ...]:
    remainder = numerator
    bits: list[int] = []
    for _ in range(20):
        remainder *= 2
        bit, remainder = divmod(remainder, DENOMINATOR)
        bits.append(bit)
    assert remainder == numerator
    return tuple(bits)


def shifted_target(horizon: int) -> tuple[int, int]:
    source = (TARGET_NUMERATOR * (1 << horizon)) // DENOMINATOR
    shift = 2 * isqrt(horizon) + 5
    return source - shift, shift


def quotient_greedy_remainder(horizon: int) -> tuple[tuple[int, ...], int]:
    remainder, _ = shifted_target(horizon)
    support: list[int] = []
    for rank in range(1, horizon + 1):
        coin = quotient(horizon, rank)
        if coin <= remainder:
            remainder -= coin
            support.append(rank)
    return tuple(support), remainder


def real_greedy_prefix(limit: int) -> tuple[int, ...]:
    remainder = TARGET
    support: list[int] = []
    for rank in range(1, limit + 1):
        coin = weight(rank)
        if coin <= remainder:
            remainder -= coin
            support.append(rank)
    return tuple(support)


def main() -> None:
    assert gcd(TARGET_NUMERATOR, DENOMINATOR) == 1

    base_period = source_period(1)
    shifted_period = source_period(TARGET_NUMERATOR)
    assert "".join(map(str, base_period)) == "00000000100011001111"
    assert "".join(map(str, shifted_period)) == "00100011001111000000"
    assert sum(base_period) == sum(shifted_period) == 7

    rank_three_gap = weight(3) - TARGET
    tail_three_upper = Fraction(13, 96)
    fatal_gap_lower = TARGET - tail_three_upper
    assert rank_three_gap == Fraction(17, 3255)
    assert fatal_gap_lower == Fraction(11, 4960)
    assert rank_three_gap > 0
    assert fatal_gap_lower > 0

    real_support = real_greedy_prefix(256)
    assert real_support == tuple(range(4, 257))

    samples: list[dict[str, int | str]] = []
    for horizon in range(8, 257):
        target, shift = shifted_target(horizon)
        support, remainder = quotient_greedy_remainder(horizon)
        assert target >= 0
        assert all(rank >= 4 for rank in support)

        # Integer form of r_N > 2^N * 11/4960 - S_N - 1.
        # Multiplication by 4960 avoids any floating-point comparison.
        assert 4960 * (remainder + shift + 1) > 11 * (1 << horizon)

        if horizon in {8, 20, 40, 80, 160, 256}:
            samples.append(
                {
                    "horizon": horizon,
                    "terminal_remainder": str(remainder),
                    "shift": shift,
                    "first_selected_rank": support[0] if support else -1,
                }
            )

    print(
        json.dumps(
            {
                "status": "exact cross-target falsifier",
                "target": "64/465",
                "base_period": "".join(map(str, base_period)),
                "shifted_period": "".join(map(str, shifted_period)),
                "period_popcount": 7,
                "real_greedy_word": "000 followed by all ones",
                "rank_three_gap": str(rank_three_gap),
                "fatal_gap_lower": str(fatal_gap_lower),
                "quotient_lower_bound": "r_N > 11*2^N/4960 - S_N - 1",
                "audited_horizons": "8..256",
                "samples": samples,
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
