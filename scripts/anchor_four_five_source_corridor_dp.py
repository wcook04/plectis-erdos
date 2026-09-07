#!/usr/bin/env python3
"""Exact finite audit of the source-clock corridor for ``x = 1/465``.

This retains the complete Boolean prefix in every state.  No states are
merged merely because their terminal quotient defects agree.  The audit is
finite evidence only; in particular it does not prove that the endpoint
interval and common-prefix properties persist at every rank.
"""

from __future__ import annotations

import argparse
from math import isqrt


DENOMINATOR = 465


def proper_divisors(n: int) -> tuple[int, ...]:
    result: list[int] = []
    for divisor in range(1, isqrt(n) + 1):
        if n % divisor:
            continue
        other = n // divisor
        if divisor < n:
            result.append(divisor)
        if other != divisor and other < n:
            result.append(other)
    return tuple(result)


def audit(horizon: int) -> dict[str, object]:
    # A state is (complete Boolean prefix as a bitset, terminal Q_n).
    states: list[tuple[int, int]] = [(0, 0)]
    remainder = 1
    maximum_variable_suffix = 0

    for rank in range(1, horizon + 1):
        remainder *= 2
        target_bit, remainder = divmod(remainder, DENOMINATOR)
        corridor_ceiling = rank // 20
        divisors = proper_divisors(rank)
        next_states: list[tuple[int, int]] = []

        for bits, previous_defect in states:
            proper_divisor_count = sum(
                (bits >> (divisor - 1)) & 1 for divisor in divisors
            )
            before_terminal_bit = (
                2 * previous_defect + target_bit - proper_divisor_count
            )
            for selected in (0, 1):
                defect = before_terminal_bit - selected
                if 0 <= defect <= corridor_ceiling:
                    next_states.append(
                        (bits | (selected << (rank - 1)), defect)
                    )

        states = next_states
        endpoint_map = {defect: bits for bits, defect in states}
        expected_endpoints = set(range(corridor_ceiling + 1))
        assert len(states) == corridor_ceiling + 1
        assert set(endpoint_map) == expected_endpoints

        common_mask = (1 << (rank // 2)) - 1
        common_prefix = states[0][0] & common_mask
        assert all((bits & common_mask) == common_prefix for bits, _ in states)

        variable_mask = 0
        reference = states[0][0]
        for bits, _ in states[1:]:
            variable_mask |= bits ^ reference
        if variable_mask:
            first_variable_rank = (variable_mask & -variable_mask).bit_length()
            maximum_variable_suffix = max(
                maximum_variable_suffix, rank - first_variable_rank + 1
            )

    return {
        "target": "1/465",
        "horizon": horizon,
        "corridor": "0 <= Q_n <= floor(n/20) at every intermediate rank",
        "state_semantics": "complete Boolean prefix; no endpoint-only merging",
        "terminal_state_count": len(states),
        "terminal_endpoints": (0, horizon // 20),
        "endpoint_interval_exact_at_every_audited_rank": True,
        "one_complete_prefix_per_endpoint_at_every_audited_rank": True,
        "common_prefix_through_floor_half_at_every_audited_rank": True,
        "maximum_observed_variable_suffix_length": maximum_variable_suffix,
        "status": "finite exact evidence, not an all-depth theorem",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--horizon", type=int, default=3_000)
    args = parser.parse_args()
    if args.horizon < 1:
        raise SystemExit("--horizon must be positive")
    print(audit(args.horizon))


if __name__ == "__main__":
    main()
