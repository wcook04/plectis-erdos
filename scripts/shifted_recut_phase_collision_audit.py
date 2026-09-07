#!/usr/bin/env python3
"""Exact audit for shifted quotient recuts and their pulse margins.

The script uses integer arithmetic only.  It checks the first-difference
identity from ``ShiftedRecutPhaseCollision.md`` for the target ``1/21`` and
contrasts it with the eventual pure-extension orbit at ``1/7``.  Every
reported range is finite evidence; the deductions are proved in the note.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from math import isqrt


def safety(horizon: int) -> int:
    return 2 * isqrt(horizon) + 5


def quotient_weight(horizon: int, rank: int) -> int:
    return (1 << horizon) // ((1 << rank) - 1)


@dataclass(frozen=True)
class Row:
    horizon: int
    bits: tuple[int, ...]
    pre_remainders: tuple[int, ...]
    remainder: int


def shifted_row(horizon: int, numerator: int, denominator: int) -> Row | None:
    capacity = ((numerator << horizon) // denominator) - safety(horizon)
    if capacity < 0:
        return None
    bits: list[int] = []
    pre_remainders: list[int] = []
    for rank in range(1, horizon + 1):
        pre_remainders.append(capacity)
        weight = quotient_weight(horizon, rank)
        take = int(weight <= capacity)
        bits.append(take)
        if take:
            capacity -= weight
    return Row(
        horizon,
        tuple(bits),
        tuple(pre_remainders),
        capacity,
    )


def target_pulse(horizon: int, numerator: int, denominator: int) -> int:
    old = (numerator << horizon) // denominator
    new = (numerator << (horizon + 1)) // denominator
    return new - 2 * old


def audit_target(depth: int, numerator: int, denominator: int) -> dict[str, object]:
    previous: Row | None = None
    recut_count = 0
    extension_count = 0
    first_extension = 0
    last_recut = 0
    maximum_lag = (-1, 0, 0)
    minimum_collision_slack: tuple[int, int, int] | None = None
    maximum_recut_remainder = (0, 0)

    for horizon in range(1, depth + 1):
        current = shifted_row(horizon, numerator, denominator)
        if current is None:
            continue
        if previous is None:
            previous = current
            continue

        old_horizon = previous.horizon
        if horizon != old_horizon + 1:
            previous = current
            continue

        first_difference = next(
            (
                rank
                for rank in range(1, horizon)
                if previous.bits[rank - 1] != current.bits[rank - 1]
            ),
            None,
        )
        full_pulse = sum(
            previous.bits[rank - 1]
            for rank in range(1, horizon)
            if horizon % rank == 0
        )
        fresh_allowance = (
            target_pulse(old_horizon, numerator, denominator)
            + 2 * safety(old_horizon)
            - safety(horizon)
            - full_pulse
        )

        if first_difference is None:
            extension_count += 1
            if first_extension == 0:
                first_extension = horizon
            if current.bits[-1] != 1:
                raise AssertionError(
                    f"pure extension did not append one at N={horizon}"
                )
            predicted = 2 * previous.remainder + fresh_allowance - 1
            if current.remainder != predicted:
                raise AssertionError(
                    f"pure-extension remainder recurrence failed at N={horizon}"
                )
        else:
            rank = first_difference
            recut_count += 1
            last_recut = horizon
            if previous.bits[rank - 1] != 0 or current.bits[rank - 1] != 1:
                raise AssertionError(
                    f"lexicographic direction failed at N={horizon}, d={rank}"
                )
            prefix_pulse = sum(
                previous.bits[e - 1]
                for e in range(1, rank)
                if horizon % e == 0
            )
            local_allowance = (
                target_pulse(old_horizon, numerator, denominator)
                + 2 * safety(old_horizon)
                - safety(horizon)
                - prefix_pulse
            )
            old_weight = quotient_weight(old_horizon, rank)
            shortfall = old_weight - previous.pre_remainders[rank - 1]
            coin_pulse = int(horizon % rank == 0)
            slack = local_allowance - coin_pulse - 2 * shortfall
            if shortfall <= 0 or slack < 0:
                raise AssertionError(
                    f"recut collision identity failed at N={horizon}, d={rank}"
                )
            if previous.remainder >= old_weight:
                raise AssertionError(
                    f"recut remainder bound failed at N={horizon}, d={rank}"
                )
            maximum_lag = max(
                maximum_lag,
                (horizon - rank, horizon, rank),
            )
            maximum_recut_remainder = max(
                maximum_recut_remainder,
                (previous.remainder, old_horizon),
            )
            candidate = (slack, horizon, rank)
            if minimum_collision_slack is None or candidate < minimum_collision_slack:
                minimum_collision_slack = candidate

        previous = current

    return {
        "target": f"{numerator}/{denominator}",
        "depth": depth,
        "recut_count": recut_count,
        "extension_count": extension_count,
        "first_extension_horizon": first_extension or None,
        "last_recut_horizon": last_recut or None,
        "maximum_recut_lag": maximum_lag[0],
        "maximum_recut_lag_horizon": maximum_lag[1],
        "maximum_recut_lag_rank": maximum_lag[2],
        "minimum_collision_slack": (
            minimum_collision_slack[0] if minimum_collision_slack else None
        ),
        "minimum_collision_slack_horizon": (
            minimum_collision_slack[1] if minimum_collision_slack else None
        ),
        "minimum_collision_slack_rank": (
            minimum_collision_slack[2] if minimum_collision_slack else None
        ),
        "maximum_old_remainder_at_recut": maximum_recut_remainder[0],
        "maximum_old_remainder_horizon": maximum_recut_remainder[1],
    }


def verify_one_seventh_tail_start(depth: int) -> dict[str, object]:
    if depth < 11:
        raise ValueError("the 1/7 tail certificate begins at horizon 11")
    for horizon in range(11, depth + 1):
        row = shifted_row(horizon, 1, 7)
        assert row is not None
        expected = (0, 0, 0) + (1,) * (horizon - 3)
        if row.bits != expected:
            raise AssertionError(
                f"1/7 was not the pure cofinite word at N={horizon}"
            )
        lower_bound_numerator = (1 << horizon) - 105 * (safety(horizon) + 1)
        if lower_bound_numerator <= 0:
            raise AssertionError(
                f"analytic 1/7 remainder lower bound was not positive at N={horizon}"
            )
        if 105 * row.remainder < lower_bound_numerator:
            raise AssertionError(
                f"1/7 remainder lower bound failed at N={horizon}"
            )
    return {
        "start_horizon": 11,
        "last_horizon": depth,
        "word_from_start": "000 followed by ones",
        "proved_lower_bound": "r_N >= 2^N/105 - S_N - 1",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=2000)
    parser.add_argument("--counter-depth", type=int, default=300)
    args = parser.parse_args()
    if args.depth < 20 or args.counter_depth < 11:
        raise SystemExit("depth must be at least 20 and counter-depth at least 11")
    result = {
        "method": "exact integer shifted quotient greedy",
        "one_twenty_one": audit_target(args.depth, 1, 21),
        "one_seventh": audit_target(args.counter_depth, 1, 7),
        "one_seventh_tail_certificate": verify_one_seventh_tail_start(
            args.counter_depth
        ),
        "claim_status": "finite audit of exact deductions in the companion note",
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
