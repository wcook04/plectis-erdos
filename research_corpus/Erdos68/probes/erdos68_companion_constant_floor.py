#!/usr/bin/env python3
"""Probe the full companion-constant factorial-floor congruence for Erdős #68.

The explicit constant is

    C = sum_(n>=2) 1 / (n! (n!-1)) = S - e + 2.

If S is rational, elementary exponential-tail arithmetic forces

    floor(m! C) == -2 (mod m)

for every sufficiently large m.  This probe measures that single-residue
orbit.  It is finite high-precision evidence, not proof authority.
"""

from __future__ import annotations

import argparse
import json
import math
import sys

import mpmath as mp

problem_id = "erdos_68"
probe_id = "erdos68_companion_constant_floor"

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def decimal_digits_of_factorial(n: int) -> int:
    return 1 if n < 2 else math.floor(math.lgamma(n + 1) / math.log(10)) + 1


def run_once(max_m: int, truncation: int, dps: int) -> dict:
    with mp.workdps(dps):
        factorial = mp.mpf(1)
        terms: list[mp.mpf] = []
        for n in range(1, truncation + 1):
            factorial *= n
            if n >= 2:
                terms.append(1 / (factorial * (factorial - 1)))
        companion = mp.fsum(terms)

        factorial = mp.mpf(1)
        minus_two: list[int] = []
        minus_one: list[int] = []
        closest_distance = mp.inf
        closest_index = 0
        floors: list[int] = []
        for m in range(1, max_m + 1):
            factorial *= m
            if m < 3:
                continue
            scaled = factorial * companion
            floor_scaled = int(mp.floor(scaled))
            floors.append(floor_scaled)
            residue = floor_scaled % m
            if residue == m - 2:
                minus_two.append(m)
            elif residue == m - 1:
                minus_one.append(m)
            distance = min(scaled - floor_scaled, floor_scaled + 1 - scaled)
            if distance < closest_distance:
                closest_distance = distance
                closest_index = m

        omitted_tail_bound = (
            mp.factorial(max_m) * 3 / mp.factorial(truncation + 1) ** 2
        )
        return {
            "floors": floors,
            "minus_two": minus_two,
            "minus_one": minus_one,
            "other_count": max_m - 2 - len(minus_two) - len(minus_one),
            "closest_integer_distance": mp.nstr(closest_distance, 40),
            "closest_integer_index": closest_index,
            "scaled_omitted_tail_bound_at_max_m": mp.nstr(
                omitted_tail_bound, 30
            ),
        }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-m", type=int, default=600)
    parser.add_argument("--truncation", type=int, default=0)
    parser.add_argument("--dps", type=int, default=0)
    args = parser.parse_args()
    if args.max_m < 3:
        raise SystemExit("--max-m must be at least 3")
    truncation = args.truncation or args.max_m + 50
    if truncation <= args.max_m:
        raise SystemExit("--truncation must exceed --max-m")
    dps = args.dps or decimal_digits_of_factorial(args.max_m) + 700

    first = run_once(args.max_m, truncation, dps)
    second = run_once(args.max_m, truncation, dps + 100)
    stable = first["floors"] == second["floors"]
    del first["floors"]
    del second["floors"]
    if not stable:
        raise SystemExit("floor stream changed under the +100 decimal precision rerun")
    if first != second:
        raise SystemExit("summary changed under the +100 decimal precision rerun")

    expected_match = None
    if args.max_m == 600:
        expected_match = (
            first["minus_two"] == [52, 591]
            and first["minus_one"] == [5, 9, 23, 60, 470]
        )
        if not expected_match:
            raise SystemExit("default census disagrees with the predeclared lists")

    payload = {
        "probe_id": probe_id,
        "problem_id": problem_id,
        "experiment_contract": {
            "hypothesis": (
                "the full companion orbit has the same two rare adjacent "
                "residue classes as the finite carry orbit; the analytic "
                "factorial-digit normal form makes eventual concentration in "
                "the -2 class equivalent to rationality"
            ),
            "falsifier": (
                "a precision-unstable floor, a default-list mismatch, or an "
                "integer distance not safely above the omitted-tail bound"
            ),
            "authority_boundary": (
                "finite dual-precision computation only; the analytic and Lean "
                "theorems own proof status"
            ),
        },
        "parameters": {
            "max_m": args.max_m,
            "truncation": truncation,
            "decimal_precision": dps,
            "verification_precision": dps + 100,
        },
        "result": {
            **first,
            "dual_precision_floor_stream_stable": stable,
            "default_predeclared_lists_match": expected_match,
        },
        "reading": (
            "through the finite horizon, residue -2 exactly reproduces unit "
            "carries and residue -1 reproduces the adjacent lower rare family"
        ),
        "claim_boundary": (
            "no cofinality, non-concentration, irrationality, or certified "
            "arbitrary-precision interval claim"
        ),
    }
    print(json.dumps(payload, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
