#!/usr/bin/env python3
"""Exact anatomy audit for the first frozen-margin quotient crossing at 1/2.

This is deliberately not another survival-horizon sweep.  It replays the
certified half-greedy word only far enough to inspect actual skipped ranks
``n``.  For each such rank it iterates the exact integer recurrence

    M(n, 0) = -(Q_n - 1),
    M(n, J + 1) = 2 M(n, J) + f(n + J + 1),

where ``f(m)`` is the number of already-selected proper divisors of ``m``.
At the first nonnegative value it records the last negative state, the
closing divisor pulse, and the selected divisors which pay that pulse.

On a bounded prefix the script also evaluates the Mersenne quotients
directly and asserts the all-horizon quotient-lift identity.  All arithmetic
is integer-exact; no floating point values are used or emitted.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from math import isqrt
from pathlib import Path
from typing import Any


def _first_counterexample(
    current: dict[str, Any] | None, condition: bool, witness: dict[str, Any]
) -> dict[str, Any] | None:
    return current if current is not None or condition else witness


def _selected_divisors(
    m: int, n: int, selected: bytearray
) -> list[int]:
    """Selected proper divisors of m belonging to the prefix through n-1."""
    divisors: list[int] = []
    for d in range(1, isqrt(m) + 1):
        if m % d:
            continue
        other = m // d
        if d < n and selected[d]:
            divisors.append(d)
        if other != d and other < n and selected[other]:
            divisors.append(other)
    divisors.sort()
    return divisors


def _direct_quotient(selected: bytearray, n: int, row: int) -> int:
    return sum(
        (1 << row) // ((1 << d) - 1)
        for d in range(2, n)
        if selected[d]
    )


def analyze(max_n: int, slack_bits: int, quotient_check_max_n: int) -> dict[str, Any]:
    if max_n < 32:
        raise ValueError("--max-n must be at least 32")
    if slack_bits < 128:
        raise ValueError("--slack-bits must be at least 128")

    maximum_horizon = 2 * (max_n - 1).bit_length()
    max_rank = max_n + maximum_horizon + 2
    precision = 2 * max_rank + slack_bits
    scale = 1 << precision
    lower = scale // 2
    upper = lower

    selected = bytearray(max_rank + 1)
    skipped = bytearray(max_rank + 1)
    proper_divisor_pulse = [0] * (max_rank + 1)
    integer_carry = [0] * (max_rank + 1)
    orbit_trace = hashlib.sha256()

    for rank in range(1, max_rank + 1):
        denominator = (1 << rank) - 1
        weight_floor = scale // denominator
        pulse = proper_divisor_pulse[rank]

        if lower >= weight_floor + 1:
            take = True
            lower -= weight_floor + 1
            upper -= weight_floor
        elif upper <= weight_floor:
            take = False
        else:
            raise AssertionError(
                f"ambiguous branch at rank {rank}; increase --slack-bits"
            )

        if take:
            selected[rank] = 1
            for multiple in range(2 * rank, max_rank + 1, rank):
                proper_divisor_pulse[multiple] += 1
        else:
            skipped[rank] = 1

        if rank == 1:
            integer_carry[rank] = 1
        else:
            integer_carry[rank] = (
                2 * integer_carry[rank - 1] - pulse - (1 if take else 0)
            )
        orbit_trace.update(
            f"{rank}:{1 if take else 0}:{pulse}:{integer_carry[rank]};".encode()
        )

    crossing_count = 0
    first_crossing_failure: dict[str, Any] | None = None
    maximum_crossing: dict[str, Any] | None = None
    pre_margin_counts: Counter[int] = Counter()
    closing_pulse_counts: Counter[int] = Counter()
    overshoot_counts: Counter[int] = Counter()
    crossing_length_counts: Counter[int] = Counter()
    initial_margin_counts: Counter[int] = Counter()
    endpoint_mod_six_counts: Counter[int] = Counter()
    future_skip_count_at_crossing: Counter[int] = Counter()
    crossing_endpoint_branch_counts: Counter[str] = Counter()
    closing_pair_counts: Counter[str] = Counter()
    quotient_checks = 0
    quotient_check_failure: dict[str, Any] | None = None

    first_pre_margin_not_minus_one: dict[str, Any] | None = None
    first_closing_pulse_not_two: dict[str, Any] | None = None
    first_endpoint_not_divisible_by_six: dict[str, Any] | None = None
    first_half_divisor_failure: dict[str, Any] | None = None
    first_small_pair_failure: dict[str, Any] | None = None
    first_more_than_two_future_skips: dict[str, Any] | None = None
    first_more_than_four_future_skips: dict[str, Any] | None = None
    first_crossing_endpoint_is_take: dict[str, Any] | None = None
    first_pulse_divisor_mismatch: dict[str, Any] | None = None
    first_skip_capacity_identity_failure: dict[str, Any] | None = None
    largest_second_selected_divisor: dict[str, Any] | None = None
    largest_second_divisor_ratio_numerator: dict[str, Any] | None = None
    maximum_future_skip_count: dict[str, Any] | None = None
    sample_exceptional_crossings: list[dict[str, Any]] = []

    for n in range(2, max_n + 1):
        if not skipped[n]:
            continue
        binary_length = (n - 1).bit_length()
        horizon = min(n, 2 * binary_length)
        margin = -(integer_carry[n] - 1)
        if margin > 0:
            raise AssertionError(f"skipped rank {n} has positive initial margin")
        initial_margin_counts[margin] += 1

        crossing: dict[str, Any] | None = None
        for length in range(1, horizon + 1):
            endpoint = n + length
            before = margin
            pulse = proper_divisor_pulse[endpoint]
            margin = 2 * before + pulse

            if n <= quotient_check_max_n:
                quotient = _direct_quotient(selected, n, endpoint)
                target = (1 << length) * ((1 << (n - 1)) - 1)
                quotient_margin = quotient - target
                quotient_checks += 1
                if quotient_margin != margin and quotient_check_failure is None:
                    quotient_check_failure = {
                        "rank": n,
                        "length": length,
                        "endpoint": endpoint,
                        "recurrence_margin": margin,
                        "quotient_margin": quotient_margin,
                    }

            if margin < 0:
                continue

            divisors = _selected_divisors(endpoint, n, selected)
            if len(divisors) != pulse and first_pulse_divisor_mismatch is None:
                first_pulse_divisor_mismatch = {
                    "rank": n,
                    "length": length,
                    "endpoint": endpoint,
                    "pulse": pulse,
                    "selected_divisors": divisors,
                }
            if before < 0 and pulse < -2 * before:
                raise AssertionError(f"invalid first-crossing arithmetic at rank {n}")

            future_skips = [
                rank
                for rank in range(n + 1, endpoint + 1)
                if skipped[rank]
            ]
            skip_capacity = sum(
                1 << (endpoint - rank) for rank in future_skips
            )
            centered_endpoint_carry = integer_carry[endpoint] - 1
            capacity_margin = skip_capacity - centered_endpoint_carry
            if (
                capacity_margin != margin
                and first_skip_capacity_identity_failure is None
            ):
                first_skip_capacity_identity_failure = {
                    "rank": n,
                    "length": length,
                    "endpoint": endpoint,
                    "frozen_margin": margin,
                    "skip_capacity_margin": capacity_margin,
                }

            crossing = {
                "rank": n,
                "length": length,
                "binary_length": binary_length,
                "endpoint": endpoint,
                "pre_margin": before,
                "required_pulse": max(0, -2 * before),
                "closing_pulse": pulse,
                "overshoot": margin,
                "selected_divisors": divisors,
                "future_skip_count": len(future_skips),
                "future_skips": future_skips,
                "future_skip_capacity": skip_capacity,
                "centered_endpoint_carry": centered_endpoint_carry,
                "endpoint_branch": "skip" if skipped[endpoint] else "take",
            }
            break

        if crossing is None:
            if first_crossing_failure is None:
                first_crossing_failure = {
                    "rank": n,
                    "horizon": horizon,
                    "terminal_margin": margin,
                }
            continue

        crossing_count += 1
        length = int(crossing["length"])
        endpoint = int(crossing["endpoint"])
        before = int(crossing["pre_margin"])
        pulse = int(crossing["closing_pulse"])
        overshoot = int(crossing["overshoot"])
        divisors = list(crossing["selected_divisors"])
        crossing_length_counts[length] += 1
        pre_margin_counts[before] += 1
        closing_pulse_counts[pulse] += 1
        overshoot_counts[overshoot] += 1
        endpoint_mod_six_counts[endpoint % 6] += 1
        future_skip_count = int(crossing["future_skip_count"])
        future_skip_count_at_crossing[future_skip_count] += 1
        crossing_endpoint_branch_counts[str(crossing["endpoint_branch"])] += 1
        if len(divisors) >= 2:
            pair = f"{divisors[0]},{divisors[1]}"
            closing_pair_counts[pair] += 1
            second = divisors[1]
            if (
                largest_second_selected_divisor is None
                or second > largest_second_selected_divisor["second_selected_divisor"]
            ):
                largest_second_selected_divisor = {
                    "rank": n,
                    "endpoint": endpoint,
                    "second_selected_divisor": second,
                    "selected_divisors": divisors,
                }
            if (
                largest_second_divisor_ratio_numerator is None
                or second * largest_second_divisor_ratio_numerator["rank"]
                > largest_second_divisor_ratio_numerator["second_selected_divisor"] * n
            ):
                largest_second_divisor_ratio_numerator = {
                    "rank": n,
                    "endpoint": endpoint,
                    "second_selected_divisor": second,
                    "ratio": f"{second}/{n}",
                    "selected_divisors": divisors,
                }

        witness = {
            "rank": n,
            "length": length,
            "endpoint": endpoint,
            "pre_margin": before,
            "closing_pulse": pulse,
            "overshoot": overshoot,
            "selected_divisors": divisors,
        }
        first_pre_margin_not_minus_one = _first_counterexample(
            first_pre_margin_not_minus_one, before == -1, witness
        )
        first_closing_pulse_not_two = _first_counterexample(
            first_closing_pulse_not_two, pulse == 2, witness
        )
        first_endpoint_not_divisible_by_six = _first_counterexample(
            first_endpoint_not_divisible_by_six, endpoint % 6 == 0, witness
        )
        first_half_divisor_failure = _first_counterexample(
            first_half_divisor_failure,
            endpoint % 2 == 0
            and endpoint // 2 < n
            and bool(selected[endpoint // 2]),
            witness,
        )
        first_small_pair_failure = _first_counterexample(
            first_small_pair_failure,
            sum(1 for d in divisors if d <= 12) >= 2,
            witness,
        )
        first_more_than_two_future_skips = _first_counterexample(
            first_more_than_two_future_skips,
            future_skip_count <= 2,
            crossing,
        )
        first_more_than_four_future_skips = _first_counterexample(
            first_more_than_four_future_skips,
            future_skip_count <= 4,
            crossing,
        )
        first_crossing_endpoint_is_take = _first_counterexample(
            first_crossing_endpoint_is_take,
            bool(skipped[endpoint]),
            crossing,
        )

        if (
            (before != -1 or pulse != 2 or endpoint % 6 != 0)
            and len(sample_exceptional_crossings) < 20
        ):
            sample_exceptional_crossings.append(witness)

        if maximum_crossing is None or length > maximum_crossing["length"]:
            maximum_crossing = crossing
        if (
            maximum_future_skip_count is None
            or future_skip_count > maximum_future_skip_count["future_skip_count"]
        ):
            maximum_future_skip_count = crossing

    def counter_dict(counter: Counter[int]) -> dict[str, int]:
        return {str(key): counter[key] for key in sorted(counter)}

    return {
        "schema": "erdos257_selected_first_window_quotient_crossing_v1",
        "target": "1/2",
        "range": {
            "min_skipped_rank": 2,
            "max_skipped_rank": max_n,
            "orbit_max_rank": max_rank,
        },
        "arithmetic": {
            "orbit_decisions": "forced integer dyadic enclosure",
            "crossing_recurrence": "integer exact",
            "quotient_cross_checks": quotient_checks,
            "quotient_check_max_n": quotient_check_max_n,
            "first_quotient_lift_failure": quotient_check_failure,
            "first_pulse_divisor_mismatch": first_pulse_divisor_mismatch,
            "first_skip_capacity_identity_failure": (
                first_skip_capacity_identity_failure
            ),
        },
        "crossings": {
            "analyzed_skipped_ranks": crossing_count,
            "status": "falsified" if first_crossing_failure else "not_falsified",
            "claim": "every skipped n crosses by 2*ceil(log2 n)",
            "first_counterexample": first_crossing_failure,
            "maximum_minimal_crossing": maximum_crossing,
            "length_distribution": counter_dict(crossing_length_counts),
            "initial_margin_distribution": counter_dict(initial_margin_counts),
            "pre_margin_distribution": counter_dict(pre_margin_counts),
            "closing_pulse_distribution": counter_dict(closing_pulse_counts),
            "overshoot_distribution": counter_dict(overshoot_counts),
            "endpoint_mod_six_distribution": counter_dict(endpoint_mod_six_counts),
            "future_skip_count_at_crossing": counter_dict(
                future_skip_count_at_crossing
            ),
            "crossing_endpoint_branch_distribution": dict(
                sorted(crossing_endpoint_branch_counts.items())
            ),
            "most_common_smallest_divisor_pairs": [
                {"pair": pair, "count": count}
                for pair, count in closing_pair_counts.most_common(20)
            ],
            "largest_second_selected_divisor": largest_second_selected_divisor,
            "largest_second_divisor_relative_to_rank": (
                largest_second_divisor_ratio_numerator
            ),
            "maximum_future_skip_count": maximum_future_skip_count,
        },
        "candidate_lemmas": {
            "pre_margin_is_minus_one": {
                "status": (
                    "falsified"
                    if first_pre_margin_not_minus_one
                    else "not_falsified"
                ),
                "first_counterexample": first_pre_margin_not_minus_one,
            },
            "closing_pulse_is_two": {
                "status": (
                    "falsified" if first_closing_pulse_not_two else "not_falsified"
                ),
                "first_counterexample": first_closing_pulse_not_two,
            },
            "closing_endpoint_divisible_by_six": {
                "status": (
                    "falsified"
                    if first_endpoint_not_divisible_by_six
                    else "not_falsified"
                ),
                "first_counterexample": first_endpoint_not_divisible_by_six,
            },
            "endpoint_half_is_selected": {
                "status": (
                    "falsified" if first_half_divisor_failure else "not_falsified"
                ),
                "first_counterexample": first_half_divisor_failure,
            },
            "two_selected_divisors_at_most_twelve_close": {
                "status": (
                    "falsified" if first_small_pair_failure else "not_falsified"
                ),
                "first_counterexample": first_small_pair_failure,
            },
            "crossing_by_second_future_skip": {
                "status": (
                    "falsified"
                    if first_more_than_two_future_skips
                    else "not_falsified"
                ),
                "first_counterexample": first_more_than_two_future_skips,
            },
            "crossing_by_fourth_future_skip": {
                "status": (
                    "falsified"
                    if first_more_than_four_future_skips
                    else "not_falsified"
                ),
                "first_counterexample": first_more_than_four_future_skips,
            },
            "crossing_endpoint_is_an_actual_skip": {
                "status": (
                    "falsified"
                    if first_crossing_endpoint_is_take
                    else "not_falsified"
                ),
                "first_counterexample": first_crossing_endpoint_is_take,
            },
            "unconditional_first_crossing_arithmetic": {
                "status": "proved_by_integer_order",
                "claim": (
                    "if the last pre-crossing margin is negative, "
                    "closing_pulse >= -2*pre_margin, hence closing_pulse >= 2"
                ),
            },
        },
        "sample_exceptional_crossings": sample_exceptional_crossings,
        "orbit_trace_sha256": orbit_trace.hexdigest(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=10_000)
    parser.add_argument("--slack-bits", type=int, default=256)
    parser.add_argument("--quotient-check-max-n", type=int, default=384)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    result = analyze(args.max_n, args.slack_bits, args.quotient_check_max_n)
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
