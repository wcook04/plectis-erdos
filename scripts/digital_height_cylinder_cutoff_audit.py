#!/usr/bin/env python3
"""Exact receipts for digital height and LCM-lift cutoff stability."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import lcm


def weight(rank: int) -> Fraction:
    return Fraction(1, (1 << rank) - 1)


def cylinder(a: int, b: int) -> Fraction:
    return weight(a) * weight(b)


def digital_height(coefficient: int, a: int, b: int) -> int:
    if coefficient <= 0:
        raise ValueError("coefficient must be positive")
    return a + b - (coefficient.bit_length() - 1)


def power_block_law(a: int, b: int, exponent: int) -> bool:
    left = (1 << exponent) * cylinder(a, b)
    comparison_rank = a + b - exponent
    if comparison_rank < 1:
        raise ValueError("comparison rank must be positive")
    analytic = (1 << a) + (1 << b) > (1 << exponent) + 1
    return (left > weight(comparison_rank)) == analytic


def lcm_lift(endpoint: int, stop: int) -> tuple[int, int]:
    if not 2 <= endpoint < stop - 1:
        raise ValueError("need 2 <= endpoint < stop-1")
    lifted_rank = lcm(endpoint, stop - 1)
    coefficient = (
        ((1 << lifted_rank) - 1) // ((1 << endpoint) - 1)
        - ((1 << lifted_rank) - 1) // ((1 << (stop - 1)) - 1)
    )
    assert coefficient > 0
    assert coefficient * weight(lifted_rank) == (
        weight(endpoint) - weight(stop - 1)
    )
    return lifted_rank, coefficient


def exhaustive_lift_checks(maximum_stop: int) -> dict[str, object]:
    power_law_checks = 0
    lift_checks = 0
    minimum_height_gain = None
    minimum_height_receipt = None
    for a in range(2, maximum_stop + 1):
        for b in range(2, maximum_stop + 1):
            for exponent in range(0, a + b):
                if not power_block_law(a, b, exponent):
                    raise AssertionError("power-block law failed")
                power_law_checks += 1

    for stop in range(4, maximum_stop + 1):
        for endpoint in range(2, stop - 1):
            lifted_rank, coefficient = lcm_lift(endpoint, stop)
            assert coefficient < (1 << (lifted_rank - 1))
            height = digital_height(
                coefficient,
                stop,
                lifted_rank,
            )
            assert height >= stop + 2
            lift_mass = coefficient * cylinder(stop, lifted_rank)
            assert lift_mass == (
                cylinder(endpoint, stop)
                - cylinder(stop - 1, stop)
            )
            assert lift_mass < weight(stop + 1)
            gain = height - stop
            if minimum_height_gain is None or gain < minimum_height_gain:
                minimum_height_gain = gain
                minimum_height_receipt = {
                    "stop": stop,
                    "endpoint": endpoint,
                    "L": lifted_rank,
                    "A": coefficient,
                    "effective_height": height,
                    "height_gain": gain,
                }
            lift_checks += 1
    return {
        "maximum_stop": maximum_stop,
        "power_block_equivalence_checks": power_law_checks,
        "lcm_lift_checks": lift_checks,
        "minimum_lift_height_gain": minimum_height_receipt,
    }


def first_lift_receipt() -> dict[str, object]:
    stop = 11
    endpoint = 2
    lifted_rank, coefficient = lcm_lift(endpoint, stop)
    assert (lifted_rank, coefficient) == (10, 340)
    block_mass = coefficient * cylinder(stop, lifted_rank)
    doubled_mass = 2 * block_mass
    assert weight(13) < block_mass < weight(12)
    assert weight(12) < doubled_mass < weight(11)

    binary_exponents = [
        exponent
        for exponent in range(coefficient.bit_length())
        if (coefficient >> exponent) & 1
    ]
    assert binary_exponents == [2, 4, 6, 8]
    power_blocks = []
    for exponent in binary_exponents:
        first_rank = stop + lifted_rank - exponent
        mass = (1 << exponent) * cylinder(stop, lifted_rank)
        assert weight(first_rank) < mass < weight(first_rank - 1)
        assert first_rank >= stop + 2
        power_blocks.append(
            {
                "coefficient": 1 << exponent,
                "exponent": exponent,
                "first_affordable_atom_rank": first_rank,
            }
        )

    doubled_coefficient = 2 * coefficient
    assert doubled_coefficient == 680
    assert digital_height(
        doubled_coefficient, stop, lifted_rank
    ) == stop + 1

    return {
        "single_lift": {
            "stop_n": stop,
            "endpoint_e": endpoint,
            "L": lifted_rank,
            "A": coefficient,
            "binary": format(coefficient, "b"),
            "effective_height": digital_height(
                coefficient, stop, lifted_rank
            ),
            "mass_between_weights": "w_13 < A*M(11,10) < w_12",
            "binary_power_blocks": power_blocks,
        },
        "two_identical_lifts": {
            "coefficient": doubled_coefficient,
            "binary": format(doubled_coefficient, "b"),
            "effective_height": digital_height(
                doubled_coefficient, stop, lifted_rank
            ),
            "mass_between_weights": "w_12 < 2*A*M(11,10) < w_11",
            "forced_boolean_atom_rank": 12,
            "reason": (
                "strict superincreasingness makes the tail after rank 12 "
                "smaller than w_12, while every atom below rank 12 "
                "is larger than the whole mass"
            ),
        },
        "reachable_second_generation_pair": second_generation_receipt(),
    }


def second_generation_receipt() -> dict[str, object]:
    # The first e=2 lift consists of 340 copies of M(11,10), all of stop 21.
    # Pairing two such copies at stop 21 and choosing endpoint 10 gives an
    # exact power-of-two lift.
    lifted_rank, coefficient = lcm_lift(10, 21)
    assert (lifted_rank, coefficient) == (20, 1024)
    single = coefficient * cylinder(21, lifted_rank)
    doubled = 2 * single
    assert weight(31) < single < weight(30)
    assert weight(30) < doubled < weight(29)
    return {
        "source_cohort": "340 copies of M(11,10) from the first e=2 lift",
        "available_pair_rewrites": 170,
        "chosen_second_collision_endpoint": 10,
        "L": lifted_rank,
        "A": coefficient,
        "single_block_cutoff": 31,
        "doubled_block_forced_cutoff": 30,
        "single_mass_between_weights": "w_31 < 1024*M(21,20) < w_30",
        "double_mass_between_weights": "w_30 < 2048*M(21,20) < w_29",
        "reachability_boundary": (
            "two such blocks occur under any schedule which applies the "
            "endpoint-10 pair rewrite at least twice; this is not asserted "
            "for every possible whole-cohort cleaning rule"
        ),
    }


def coalescence_checks(limit: int) -> dict[str, object]:
    checks = 0
    sharp_examples = []
    for first in range(1, limit + 1):
        for second in range(1, limit + 1):
            largest_log = max(
                first.bit_length() - 1,
                second.bit_length() - 1,
            )
            combined_log = (first + second).bit_length() - 1
            assert combined_log <= largest_log + 1
            if combined_log == largest_log + 1:
                sharp_examples.append((first, second))
            checks += 1
    assert (340, 340) in sharp_examples
    return {
        "coefficient_limit": limit,
        "pair_checks": checks,
        "height_loss_bound": 1,
        "first_lift_pair_is_sharp": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--maximum-stop", type=int, default=60)
    parser.add_argument("--coefficient-limit", type=int, default=700)
    args = parser.parse_args()
    if args.maximum_stop < 11 or args.coefficient_limit < 340:
        raise SystemExit("ranges must include the first lift")
    output = {
        "power_block_law": (
            "2^j*M(a,b)>w_(a+b-j) iff "
            "2^a+2^b>2^j+1"
        ),
        "lift_cutoff": (
            "A<2^(L-1), so H(A*M(n,L))>=n+2; "
            "in fact A*M(n,L)<w_(n+1)"
        ),
        "exhaustive_checks": exhaustive_lift_checks(args.maximum_stop),
        "first_lift_cross_cohort_counterexample": first_lift_receipt(),
        "coalescence": coalescence_checks(args.coefficient_limit),
        "claim_status": (
            "exact algebraic theorems plus finite arithmetic receipts; "
            "normalizing either doubled block forces its one-rank cutoff "
            "loss; the displayed second-generation block is reachable from "
            "one M(2,3) under the specified legal pairwise schedule, not "
            "under every possible whole-cohort rule"
        ),
    }
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
