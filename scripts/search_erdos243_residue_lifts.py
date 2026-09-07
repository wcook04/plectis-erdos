#!/usr/bin/env python3
"""Exact residue lifting for the constant-negative Erdős #243 obstruction.

Normalize the common scale to ``E = -1`` and ``C_0 = 1``.  The forced update is

    a_{n+1} = ((n+1) a_n^2 - (n+2) a_n + (n+3)) / (n+2).

Survival through ``H`` updates depends only on ``a_0 mod (H+1)!``.  More
precisely, at step ``n`` we retain ``a_n`` modulo

    (H+1)! / (n+1)!,

check divisibility by ``n+2``, divide exactly, and reduce to the next modulus.
This avoids constructing the double-exponential integer orbit.  The compatible
classes form a finite-horizon/profinite tree, but the Lean theorem
``no_constantNegative_orbit`` proves that no fixed natural seed survives every
horizon as a genuine constant-negative orbit.
"""

from __future__ import annotations

import argparse
import json
import math


problem_id = "erdos_243"


def forced_numerator(index: int, a: int) -> int:
    return (index + 1) * a * a - (index + 2) * a + (index + 3)


def survives_modular(seed: int, horizon: int) -> bool:
    """Decide the first ``horizon`` divisibility conditions exactly."""
    modulus = math.factorial(horizon + 1)
    a = seed % modulus
    for index in range(horizon):
        divisor = index + 2
        next_modulus = modulus // divisor
        numerator = forced_numerator(index, a)
        if numerator % divisor:
            return False
        a = (numerator // divisor) % next_modulus if next_modulus > 1 else 0
        modulus = next_modulus
    return True


def completed_modular(seed: int, horizon: int) -> int:
    """Count successful updates, using only the finite-horizon modulus."""
    modulus = math.factorial(horizon + 1)
    a = seed % modulus
    for index in range(horizon):
        divisor = index + 2
        next_modulus = modulus // divisor
        numerator = forced_numerator(index, a)
        if numerator % divisor:
            return index
        a = (numerator // divisor) % next_modulus if next_modulus > 1 else 0
        modulus = next_modulus
    return horizon


def scan_seeds(max_seed: int, horizon: int, keep: int) -> dict[str, object]:
    counts: dict[int, int] = {}
    leaders: list[tuple[int, int]] = []
    for seed in range(2, max_seed + 1):
        completed = completed_modular(seed, horizon)
        counts[completed] = counts.get(completed, 0) + 1
        leaders.append((completed, seed))
        leaders.sort(key=lambda item: (item[0], -item[1]), reverse=True)
        del leaders[keep:]
    return {
        "max_seed": max_seed,
        "horizon": horizon,
        "seed_count": max(0, max_seed - 1),
        "completed_step_counts": {str(key): counts[key] for key in sorted(counts)},
        "max_completed_steps": leaders[0][0] if leaders else 0,
        "leaders": [
            {"seed": seed, "completed_steps": completed}
            for completed, seed in leaders
        ],
    }


def lift_levels(max_horizon: int, sample_limit: int) -> list[dict[str, object]]:
    modulus = 1
    residues = [0]
    levels: list[dict[str, object]] = []
    for horizon in range(1, max_horizon + 1):
        lift_factor = horizon + 1
        next_modulus = modulus * lift_factor
        candidates = (
            residue + lift * modulus
            for residue in residues
            for lift in range(lift_factor)
        )
        residues = [
            candidate
            for candidate in candidates
            if survives_modular(candidate, horizon)
        ]
        residues.sort()
        modulus = next_modulus
        common = math.gcd(len(residues), modulus)
        levels.append(
            {
                "horizon": horizon,
                "modulus": modulus,
                "residue_count": len(residues),
                "density": {
                    "numerator": len(residues) // common,
                    "denominator": modulus // common,
                },
                "smallest_residues": residues[:sample_limit],
            }
        )
    return levels


def assert_packet_fixtures(levels: list[dict[str, object]]) -> list[str]:
    if not levels or levels[0]["smallest_residues"] != [1]:
        raise AssertionError("the first condition must be the odd residue mod 2")
    if not survives_modular(1501, 17):
        raise AssertionError("a0=1501 must survive the first 17 updates")
    if survives_modular(1501, 18):
        raise AssertionError("a0=1501 must fail the eighteenth update")
    for level in levels:
        horizon = int(level["horizon"])
        for residue in level["smallest_residues"]:
            if not survives_modular(int(residue), horizon):
                raise AssertionError((horizon, residue))
    return [
        "horizon_one_is_the_odd_class_mod_two",
        "a0_1501_survives_17_but_not_18_updates",
        "reported_sample_residues_recheck_exactly",
    ]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-horizon", type=int, default=8)
    parser.add_argument("--sample-limit", type=int, default=12)
    parser.add_argument("--scan-max-seed", type=int, default=5000)
    parser.add_argument("--scan-horizon", type=int, default=25)
    parser.add_argument("--keep", type=int, default=12)
    parser.add_argument("--allow-large-residue-enumeration", action="store_true")
    parser.add_argument("--assert-packet", action="store_true")
    args = parser.parse_args()
    if args.max_horizon < 1:
        parser.error("--max-horizon must be positive")
    if args.sample_limit < 0:
        parser.error("--sample-limit must be nonnegative")
    if args.scan_max_seed < 1 or args.scan_horizon < 1 or args.keep < 1:
        parser.error("scan bounds and --keep must be positive")
    if args.max_horizon > 10 and not args.allow_large_residue_enumeration:
        parser.error(
            "full residue enumeration grows quickly; pass "
            "--allow-large-residue-enumeration explicitly above horizon 10"
        )

    levels = lift_levels(args.max_horizon, args.sample_limit)
    result: dict[str, object] = {
        "schema": "erdos243-constant-negative-residue-lifts/1",
        "claim_ceiling": (
            "finite_exact_residue_classes_not_an_infinite_natural_orbit; "
            "all_fixed_natural_constant_negative_seeds_are_lean_excluded"
        ),
        "normalization": {"centered_state": -1, "initial_tail_state": 1},
        "max_horizon": args.max_horizon,
        "levels": levels,
        "bounded_seed_scan": scan_seeds(args.scan_max_seed, args.scan_horizon, args.keep),
    }
    if args.assert_packet:
        result["packet_assertions"] = assert_packet_fixtures(levels)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
