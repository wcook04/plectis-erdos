#!/usr/bin/env python3
"""Exact alive-cylinder discriminator for the 1/21 nested-height producer.

The older denominator census samples rational targets first and then retains
the ones whose greedy orbit survives.  This probe samples the survival
cylinders directly.  A Boolean word ``A <= N`` and a residual

    0 <= r <= 2^-N < sum_(k>N) 1/(2^k-1)

define the exact target ``sum_(a in A) 1/(2^a-1) + r``.  Strict
superincreasingness makes its greedy prefix exactly ``A`` through rank ``N``.
The executable nevertheless verifies every take and skip by integer
cross-multiplication.

For each exact cylinder state it reconstructs the binary quotient defect,
strict records, and height, then tests the phase-matched nested-height law

    2*(Q_(2d-1)-Q_(d-1)) + Q_d <= H(d) + H(d/2).

This is a target-space breadth test, not an all-depth theorem.  In particular,
finite survival is an input to every sampled state, so a clean receipt cannot
be used as a membership proof.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from math import gcd
from pathlib import Path
import platform
import random
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[5]
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/"
    "NewtonNestedHeightFrontier.md"
)


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def canonical_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def update_minimum(
    summary: dict[str, Any],
    margin: int,
    witness: dict[str, Any],
) -> None:
    summary["row_count"] += 1
    if margin < 0:
        summary["violation_count"] += 1
        if len(summary["violations"]) < 12:
            summary["violations"].append(witness)
    if margin == 0:
        summary["equality_count"] += 1
        if len(summary["equalities"]) < 12:
            summary["equalities"].append(witness)
    old = summary["minimum_margin"]
    if old is None or margin < old:
        summary["minimum_margin"] = margin
        summary["minimum_witness"] = witness


def empty_metric() -> dict[str, Any]:
    return {
        "row_count": 0,
        "minimum_margin": None,
        "minimum_witness": None,
        "violation_count": 0,
        "equality_count": 0,
        "violations": [],
        "equalities": [],
    }


def support_word(
    rng: random.Random,
    depth: int,
    density_numerator: int,
    density_denominator: int,
) -> bytearray:
    bits = bytearray(depth + 1)
    for rank in range(2, depth + 1):
        bits[rank] = (
            rng.randrange(density_denominator) < density_numerator
        )
    return bits


def residual_numerator(
    rng: random.Random,
    residual_bits: int,
    mode: int,
) -> int:
    scale = 1 << residual_bits
    if mode == 0:
        return 0
    if mode == 1:
        return scale // 2
    if mode == 2:
        return scale
    return rng.randrange(scale + 1)


def build_receipt(args: argparse.Namespace) -> dict[str, Any]:
    if args.depth < 2 * args.max_midpoint:
        raise ValueError("depth must cover every tested successor 2d")
    if args.residual_bits < 2:
        raise ValueError("residual-bits must be at least two")
    if args.samples < 1:
        raise ValueError("samples must be positive")

    script_path = Path(__file__).resolve()
    rng = random.Random(args.seed)
    profiles = ((1, 20), (1, 10), (1, 5), (1, 3), (1, 2), (2, 3), (4, 5), (9, 10))

    odd_lcm = 1
    for rank in range(2, args.depth + 1):
        odd_lcm = lcm(odd_lcm, (1 << rank) - 1)
    full_denominator = odd_lcm << (args.depth + args.residual_bits)
    coin_numerators = [0] * (args.depth + 1)
    for rank in range(1, args.depth + 1):
        coin_numerators[rank] = full_denominator // ((1 << rank) - 1)

    metrics = {
        "nested_height": empty_metric(),
        "quarter_gain_split": empty_metric(),
        "half_gain_residue_split": empty_metric(),
        "causal_height_plus_two": empty_metric(),
    }
    profile_counts: Counter[str] = Counter()
    residual_mode_counts: Counter[str] = Counter()
    prefix_failures: list[dict[str, Any]] = []
    negative_defect_failures: list[dict[str, Any]] = []
    invalid_digit_failures: list[dict[str, Any]] = []
    trace = hashlib.sha256()
    selected_targets = 0
    strict_record_count = 0

    for sample in range(args.samples):
        profile = profiles[sample % len(profiles)]
        bits = support_word(rng, args.depth, *profile)
        mode = sample % 4
        z = residual_numerator(rng, args.residual_bits, mode)
        profile_name = f"{profile[0]}/{profile[1]}"
        residual_name = ("zero", "half", "upper", "random")[mode]
        profile_counts[profile_name] += 1
        residual_mode_counts[residual_name] += 1

        numerator = z * odd_lcm
        for rank in range(2, args.depth + 1):
            if bits[rank]:
                numerator += coin_numerators[rank]
        if not 0 <= numerator < full_denominator:
            raise AssertionError("constructed cylinder target left [0,1)")

        greedy_remainder = numerator
        for rank in range(1, args.depth + 1):
            coin = coin_numerators[rank]
            actual_take = coin <= greedy_remainder
            expected_take = bool(bits[rank])
            if actual_take != expected_take:
                prefix_failures.append(
                    {
                        "sample": sample,
                        "rank": rank,
                        "expected_take": expected_take,
                        "actual_take": actual_take,
                    }
                )
                break
            if actual_take:
                greedy_remainder -= coin
        if greedy_remainder != z * odd_lcm:
            prefix_failures.append(
                {
                    "sample": sample,
                    "rank": args.depth,
                    "terminal_remainder_mismatch": True,
                }
            )

        loads = [0] * (args.depth + 1)
        for divisor in range(2, args.depth + 1):
            if bits[divisor]:
                for multiple in range(divisor, args.depth + 1, divisor):
                    loads[multiple] += 1

        defects = [0] * (args.depth + 1)
        heights = [1] * (args.depth + 1)
        digits = [0] * (args.depth + 1)
        records = [False] * (args.depth + 1)
        binary_remainder = numerator
        maximum = 0
        for rank in range(1, args.depth + 1):
            binary_remainder *= 2
            digit, binary_remainder = divmod(
                binary_remainder, full_denominator
            )
            digits[rank] = digit
            if digit not in (0, 1):
                invalid_digit_failures.append(
                    {"sample": sample, "rank": rank, "digit": digit}
                )
                break
            heights[rank] = maximum + 1
            defect = 2 * defects[rank - 1] + digit - loads[rank]
            if defect < 0:
                negative_defect_failures.append(
                    {"sample": sample, "rank": rank, "defect": defect}
                )
                break
            defects[rank] = defect
            if defect > maximum:
                maximum = defect
                records[rank] = True
                strict_record_count += 1

        sample_had_row = False
        for d in range(4, args.max_midpoint + 1, 2):
            record_rank = 2 * d - 1
            if (
                not records[record_rank]
                or heights[d] < 4
                or digits[2 * d] != digits[d]
            ):
                continue
            sample_had_row = True
            gain = defects[record_rank] - defects[d - 1]
            block = 2 * gain + defects[d]
            witness = {
                "sample": sample,
                "midpoint": d,
                "support_card": sum(bits),
                "residual_mode": residual_name,
                "density_profile": profile_name,
                "H_d": heights[d],
                "H_half": heights[d // 2],
                "Q_record": defects[record_rank],
                "Q_d_pred": defects[d - 1],
                "Q_d": defects[d],
            }
            margins = {
                "nested_height": heights[d] + heights[d // 2] - block,
                "quarter_gain_split": heights[d // 2] - gain,
                "half_gain_residue_split": heights[d] - gain - defects[d],
                "causal_height_plus_two": heights[d] + 2 - block,
            }
            for name, margin in margins.items():
                update_minimum(
                    metrics[name], margin, {**witness, "margin": margin}
                )
            trace.update(
                (
                    f"{sample}:{d}:{defects[record_rank]}:"
                    f"{defects[d - 1]}:{defects[d]}:"
                    f"{heights[d]}:{heights[d // 2]}\n"
                ).encode()
            )
        if sample_had_row:
            selected_targets += 1

    return {
        "schema": "erdos257_nested_height_alive_cylinder_probe_v1",
        "claim_ceiling": (
            "Exact finite target-space discrimination only. Every target is "
            "constructed inside a certified greedy survival cylinder; the "
            "receipt does not prove nested height at all depths, 1/21 "
            "membership, or Erdős #257."
        ),
        "authority": {
            "script_ref": str(script_path.relative_to(REPO_ROOT)),
            "script_sha256": hashlib.sha256(script_path.read_bytes()).hexdigest(),
            "analysis_ref": ANALYSIS_REF,
            "python_version": platform.python_version(),
            "floating_point_used": False,
            "exact_arithmetic": (
                "one common integer denominator; greedy comparisons, binary "
                "digits, carries, records, and margins are all integral"
            ),
        },
        "parameters": {
            "depth": args.depth,
            "max_midpoint": args.max_midpoint,
            "samples": args.samples,
            "seed": args.seed,
            "residual_bits": args.residual_bits,
            "residual_interval": "0 <= r <= 2^-depth < mersenneTail(depth)",
            "density_profiles": [f"{a}/{b}" for a, b in profiles],
            "common_denominator_bit_length": full_denominator.bit_length(),
        },
        "coverage": {
            "profile_counts": dict(sorted(profile_counts.items())),
            "residual_mode_counts": dict(sorted(residual_mode_counts.items())),
            "targets_with_applicable_rows": selected_targets,
            "strict_record_count": strict_record_count,
            "row_trace_sha256": trace.hexdigest(),
        },
        "exact_checks": {
            "greedy_prefix_failure_count": len(prefix_failures),
            "greedy_prefix_failures": prefix_failures[:12],
            "invalid_binary_digit_count": len(invalid_digit_failures),
            "invalid_binary_digits": invalid_digit_failures[:12],
            "negative_defect_count": len(negative_defect_failures),
            "negative_defects": negative_defect_failures[:12],
        },
        "metrics": metrics,
        "route_decision": {
            "supporting_evidence": (
                "The coupled nested-height law can now be tested on arbitrary "
                "certified alive cylinders, rather than only a denominator grid."
            ),
            "contrary_evidence": (
                "A clean finite receipt remains survival-conditioned and so "
                "cannot supply the all-depth induction needed for membership."
            ),
            "next_proof_boundary": (
                "Either prove a source-specific implication from the 1/21 "
                "periodic digits before assuming survival, or treat nested "
                "height as an alive-prefix diagnostic and return to the "
                "noncircular 1/2 full-shell boundary charge."
            ),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=80)
    parser.add_argument("--max-midpoint", type=int, default=36)
    parser.add_argument("--samples", type=int, default=10_000)
    parser.add_argument("--seed", type=int, default=257_202_608_23)
    parser.add_argument("--residual-bits", type=int, default=32)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    receipt = build_receipt(args)
    rendered = canonical_json(receipt)
    if args.output is not None:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
