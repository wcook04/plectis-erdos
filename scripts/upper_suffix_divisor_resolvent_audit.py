#!/usr/bin/env python3
"""Exact finite audit for the upper-suffix divisor resolvent at 1/465.

Greedy decisions are certified by directed dyadic intervals.  All subsequent
states use integer arithmetic.  The script checks the quotient-tail identity,
the current-bit cancellation, and the first failure of eight-step solvency.
It supplies finite evidence only; the infinite resolvent identity is proved in
the companion note.
"""

from __future__ import annotations

import argparse
import json


DENOMINATOR = 465
PERIOD = 20
PERIOD_NUMERATOR = ((1 << PERIOD) - 1) // DENOMINATOR


def target_bit(rank: int) -> int:
    shift = PERIOD - 1 - ((rank - 1) % PERIOD)
    return (PERIOD_NUMERATOR >> shift) & 1


def exact_greedy_bits(depth: int) -> list[int]:
    """Certify the greedy prefix by directed dyadic residual bounds."""
    precision = 2 * depth + 64
    scale = 1 << precision
    lower = scale // DENOMINATOR
    upper = (scale + DENOMINATOR - 1) // DENOMINATOR
    bits = [0] * (depth + 1)
    for rank in range(1, depth + 1):
        weight_floor = scale // ((1 << rank) - 1)
        if lower >= weight_floor + 1:
            lower -= weight_floor + 1
            upper -= weight_floor
            bits[rank] = 1
        elif upper <= weight_floor:
            continue
        else:
            raise AssertionError(
                f"directed interval is undecided at rank {rank}"
            )
    return bits


def proper_divisor_pulses(bits: list[int]) -> list[int]:
    depth = len(bits) - 1
    pulses = [0] * (depth + 1)
    for divisor in range(1, depth + 1):
        if bits[divisor]:
            for multiple in range(2 * divisor, depth + 1, divisor):
                pulses[multiple] += 1
    return pulses


def quotient_defects(bits: list[int], pulses: list[int]) -> list[int]:
    depth = len(bits) - 1
    defects = [0] * (depth + 1)
    for rank in range(1, depth + 1):
        defects[rank] = (
            2 * defects[rank - 1]
            + target_bit(rank)
            - pulses[rank]
            - bits[rank]
        )
        if defects[rank] < 0:
            raise AssertionError(f"negative quotient defect at rank {rank}")
    return defects


def resolvent_row(
    base: int,
    length: int,
    bits: list[int],
    pulses: list[int],
    defects: list[int],
) -> list[dict[str, int]]:
    value = -defects[base]
    hole = 0
    rows: list[dict[str, int]] = []
    for delay in range(1, length + 1):
        rank = base + delay
        hole = 2 * hole + 1 - bits[rank]
        value = 2 * value + 1 - target_bit(rank) + pulses[rank]
        if value != hole - defects[rank]:
            raise AssertionError(
                f"resolvent cancellation failed at M={base}, n={rank}"
            )
        rows.append(
            {
                "rank": rank,
                "bit": bits[rank],
                "target_bit": target_bit(rank),
                "proper_divisor_pulse": pulses[rank],
                "D": value,
                "Q": defects[rank],
            }
        )
    return rows


def quotient_tail_check(
    horizon: int,
    bits: list[int],
    defects: list[int],
) -> None:
    middle = horizon // 2
    target = (1 << horizon) // DENOMINATOR
    head = sum(
        bits[rank] * ((1 << horizon) // ((1 << rank) - 1))
        for rank in range(1, middle + 1)
    )
    suffix = sum(
        bits[rank] << (horizon - rank)
        for rank in range(middle + 1, horizon + 1)
    )
    if target - head != suffix + defects[horizon]:
        raise AssertionError(f"quotient-tail identity failed at N={horizon}")


def audit(depth: int, window: int, delay_search: int) -> dict[str, object]:
    if depth < 1310:
        raise ValueError("depth must be at least 1310")
    bits = exact_greedy_bits(depth)
    pulses = proper_divisor_pulses(bits)
    defects = quotient_defects(bits, pulses)

    for horizon in (40, 100, 1000, 1306, min(depth, 5000)):
        quotient_tail_check(horizon, bits, defects)

    first_failure: dict[str, object] | None = None
    maximum_delay = (0, 0, 0)
    for base in range(20, depth - delay_search + 1):
        rows = resolvent_row(base, delay_search, bits, pulses, defects)
        first_nonnegative = next(
            (index for index, row in enumerate(rows, start=1) if row["D"] >= 0),
            None,
        )
        if first_nonnegative is not None:
            maximum_delay = max(
                maximum_delay,
                (first_nonnegative, base, defects[base]),
            )
        if (
            first_failure is None
            and all(row["D"] < 0 for row in rows[:window])
        ):
            first_failure = {
                "base": base,
                "initial_Q": defects[base],
                "window": window,
                "first_nonnegative_delay": first_nonnegative,
                "rows_through_first_nonnegative": (
                    rows[:first_nonnegative]
                    if first_nonnegative is not None
                    else rows
                ),
            }

    if first_failure is None:
        raise AssertionError("the expected fixed-window failure was not found")
    if (
        first_failure["base"] != 1298
        or first_failure["initial_Q"] != 2
        or first_failure["first_nonnegative_delay"] != 10
    ):
        raise AssertionError(f"unexpected first failure: {first_failure}")

    return {
        "target": "1/465",
        "depth": depth,
        "method": "directed dyadic greedy certification and exact integer recurrences",
        "first_fixed_window_failure": first_failure,
        "maximum_payment_delay": maximum_delay[0],
        "maximum_delay_base": maximum_delay[1],
        "maximum_delay_initial_Q": maximum_delay[2],
        "maximum_Q": max(defects),
        "quotient_tail_sample_horizons": [
            40,
            100,
            1000,
            1306,
            min(depth, 5000),
        ],
        "claim_status": "exact finite audit only",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=5000)
    parser.add_argument("--window", type=int, default=8)
    parser.add_argument("--delay-search", type=int, default=64)
    args = parser.parse_args()
    if args.window < 1 or args.delay_search < args.window:
        raise SystemExit("require 1 <= window <= delay-search")
    print(
        json.dumps(
            audit(args.depth, args.window, args.delay_search),
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
