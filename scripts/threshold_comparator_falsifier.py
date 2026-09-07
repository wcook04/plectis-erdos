#!/usr/bin/env python3
"""Exact scans for the threshold-comparator recut calculations.

The scan uses the recurrence for the integer quotient weights and directed
fixed-point bounds for their fractional remainders.  It proves only the
finite rows requested on the command line.
"""

from __future__ import annotations

import argparse
import json
from math import isqrt


def source_count(horizon: int) -> int:
    return 2 * (horizon // 6) + int(horizon % 6 >= 5)


def update_quotients(previous: list[int], horizon: int) -> list[int]:
    """Return a[d]=floor(2^horizon/(2^d-1)), with an unused index zero."""
    current = [0] + [value << 1 for value in previous[1:]]
    current.append(2 if horizon == 1 else 1)
    for divisor in range(2, isqrt(horizon) + 1):
        if horizon % divisor:
            continue
        current[divisor] += 1
        paired = horizon // divisor
        if paired != divisor and paired < horizon:
            current[paired] += 1
    return current


def lex_least_crossing(weights: list[int], target: int) -> tuple[list[int], int]:
    tail = sum(weights[1:])
    deficit = target
    bits = [0] * len(weights)
    for rank in range(1, len(weights)):
        tail -= weights[rank]
        if tail < deficit:
            bits[rank] = 1
            deficit -= weights[rank]
    if deficit > 0:
        raise AssertionError(f"threshold not crossed; deficit={deficit}")
    return bits, -deficit


def first_lex_change(old: list[int], new: list[int]) -> tuple[int, int, int] | None:
    for rank in range(1, len(old)):
        if old[rank] != new[rank]:
            return rank, old[rank], new[rank]
    return None


def scaled_fraction_bounds(
    horizon: int, support: list[int], precision: int
) -> tuple[int, int]:
    """Bounds scale*sum {2^N/(2^d-1)} by exact integer arithmetic."""
    lower = 0
    upper = 0
    for rank in support:
        if rank == 1:
            continue
        exponent = precision + horizon % rank
        blocks, shift = divmod(exponent, rank)
        quotient = 0
        for block in range(blocks):
            quotient |= 1 << (shift + block * rank)
        lower += quotient
        upper += quotient + 1
    return lower, upper


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=5000)
    parser.add_argument("--precision", type=int, default=128)
    args = parser.parse_args()
    if args.depth < 100 or args.precision < 32:
        raise SystemExit("depth must be at least 100 and precision at least 32")

    scale = 1 << args.precision
    quotients = [0]
    previous_original: list[int] | None = None
    previous_doubled: list[int] | None = None
    original_reversals: list[tuple[int, int, int, int]] = []
    doubled_reversals: list[tuple[int, int, int, int]] = []
    original_fraction_failures: list[int] = []
    doubled_feasibility_failures: list[int] = []
    exact_representation_failures: list[tuple[int, int]] = []
    maximum_allowance_excess = (-10**9, 0)
    minimum_doubled_margin: tuple[int, int] | None = None

    for horizon in range(1, args.depth + 1):
        quotients = update_quotients(quotients, horizon)
        target_prefix = (1 << horizon) // 21
        count = source_count(horizon)

        original_weights = [0] + [
            quotients[rank] - 1 + int(2 * rank <= horizon)
            for rank in range(1, horizon + 1)
        ]
        original, original_overshoot = lex_least_crossing(
            original_weights, target_prefix - count - 3
        )
        if previous_original is not None:
            change = first_lex_change(previous_original, original)
            if change is not None and change[1:] != (0, 1):
                original_reversals.append((horizon, *change))
        previous_original = original
        original_support = [
            rank for rank in range(1, horizon + 1) if original[rank]
        ]
        original_upper = sum(2 * rank > horizon for rank in original_support)
        original_q = count + 3 - original_upper - original_overshoot
        _, original_fraction_upper = scaled_fraction_bounds(
            horizon, original_support, args.precision
        )
        if original_fraction_upper > original_q * scale:
            original_fraction_failures.append(horizon)

        doubled_weights = [0] + [
            2 * quotients[rank] - int(2 * rank > horizon)
            for rank in range(1, horizon + 1)
        ]
        doubled, doubled_overshoot = lex_least_crossing(
            doubled_weights, 2 * target_prefix - count - 4
        )
        if previous_doubled is not None:
            change = first_lex_change(previous_doubled, doubled)
            if change is not None and change[1:] != (0, 1):
                doubled_reversals.append((horizon, *change))
        previous_doubled = doubled
        doubled_support = [
            rank for rank in range(1, horizon + 1) if doubled[rank]
        ]
        doubled_upper = sum(2 * rank > horizon for rank in doubled_support)
        doubled_q_numerator = count + 4 - doubled_overshoot - doubled_upper
        if doubled_q_numerator % 2:
            raise AssertionError(f"nonintegral doubled Q at N={horizon}")
        doubled_q = doubled_q_numerator // 2
        _, doubled_fraction_upper = scaled_fraction_bounds(
            horizon, doubled_support, args.precision
        )
        source_remainder = pow(2, horizon, 21)
        directed_margin = (
            (21 * doubled_q + source_remainder) * scale
            - 21 * doubled_fraction_upper
        )
        if directed_margin < 0:
            doubled_feasibility_failures.append(horizon)
        if minimum_doubled_margin is None or directed_margin < minimum_doubled_margin[0]:
            minimum_doubled_margin = (directed_margin, horizon)

        allowance = 2 * isqrt(horizon) + 5
        capacity = target_prefix - allowance
        if capacity >= 0:
            selected: list[int] = []
            for rank in range(1, horizon + 1):
                if quotients[rank] <= capacity:
                    selected.append(rank)
                    capacity -= quotients[rank]
            if capacity:
                exact_representation_failures.append((horizon, capacity))
            upper = sum(2 * rank > horizon for rank in selected)
            maximum_allowance_excess = max(
                maximum_allowance_excess,
                (upper - count, horizon),
            )

    assert minimum_doubled_margin is not None
    print(
        json.dumps(
            {
                "depth": args.depth,
                "precision": args.precision,
                "original_first_lex_reversals": original_reversals[:10],
                "original_F_le_Q_directed_failures": original_fraction_failures[:10],
                "doubled_first_lex_reversals": doubled_reversals[:10],
                "doubled_feasibility_directed_failures": doubled_feasibility_failures[:10],
                "minimum_doubled_margin_horizon": minimum_doubled_margin[1],
                "allowance_exact_representation_failures": exact_representation_failures[:10],
                "maximum_allowance_upper_excess": maximum_allowance_excess[0],
                "maximum_allowance_upper_excess_horizon": maximum_allowance_excess[1],
                "claim_status": "exact finite computation only",
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
