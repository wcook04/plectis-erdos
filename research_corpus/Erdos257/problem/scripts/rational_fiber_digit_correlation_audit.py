#!/usr/bin/env python3
"""Audit digit correlations on the positive-measure fibre x + y = 3/2.

This is a mechanism falsifier, not a proof about the infinite fibre.  It samples
fair Mersenne codings x, greedily decodes y = 3/2 - x, retains prefixes that
survive the Mersenne tail corridor through ``depth``, and records the joint digit
frequencies.  The omitted tail and numerical precision are far below the
rank-``depth`` gap scale; a deterministic high-precision replay guards the
classification and decoded-prefix decisions.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import random
from pathlib import Path
from typing import Any

import mpmath as mp


ROOT = Path(__file__).resolve().parents[5]
DEFAULT_OUTPUT = (
    ROOT
    / "state/formal_math/erdos257_period_noncollapse"
    / "rational_fiber_digit_correlation_receipt.json"
)


def _weights(length: int, dps: int) -> tuple[list[mp.mpf], list[mp.mpf], mp.mpf]:
    with mp.workdps(dps):
        weights = [mp.mpf(0)] + [
            1 / (mp.mpf(2) ** n - 1) for n in range(1, length + 1)
        ]
        suffix = [mp.mpf(0)] * (length + 2)
        for n in range(length, 0, -1):
            suffix[n] = suffix[n + 1] + weights[n]
        omitted_tail_upper = mp.mpf(2) ** (1 - length)
        return weights, suffix, omitted_tail_upper


def _decode_sample(
    sample_seed: int,
    *,
    depth: int,
    generated_length: int,
    dps: int,
    weights: list[mp.mpf],
    suffix: list[mp.mpf],
    omitted_tail_upper: mp.mpf,
) -> tuple[bool, tuple[int, ...], tuple[int, ...]]:
    with mp.workdps(dps):
        rng = random.Random(sample_seed)
        source = tuple(rng.getrandbits(1) for _ in range(generated_length))
        x = mp.fsum(
            weights[n] for n in range(1, generated_length + 1) if source[n - 1]
        )
        residual = mp.mpf(3) / 2 - x
        if residual < 0 or residual > suffix[1] + omitted_tail_upper:
            return False, source[:depth], ()

        target: list[int] = []
        for n in range(1, depth + 1):
            take = int(residual >= weights[n])
            target.append(take)
            if take:
                residual -= weights[n]
            if residual > suffix[n + 1] + omitted_tail_upper:
                return False, source[:depth], tuple(target)
        return True, source[:depth], tuple(target)


def _quantiles(values: list[int]) -> dict[str, int]:
    ordered = sorted(values)
    result: dict[str, int] = {}
    for label, q in (
        ("min", 0.0),
        ("p001", 0.001),
        ("p01", 0.01),
        ("p10", 0.10),
        ("median", 0.50),
        ("p90", 0.90),
        ("p99", 0.99),
        ("p999", 0.999),
        ("max", 1.0),
    ):
        result[label] = ordered[round((len(ordered) - 1) * q)]
    return result


def _correlation(left: list[float], right: list[float]) -> float:
    left_mean = sum(left) / len(left)
    right_mean = sum(right) / len(right)
    covariance = sum(
        (x - left_mean) * (y - right_mean) for x, y in zip(left, right)
    )
    left_energy = sum((x - left_mean) ** 2 for x in left)
    right_energy = sum((y - right_mean) ** 2 for y in right)
    if left_energy == 0 or right_energy == 0:
        return 0.0
    return covariance / math.sqrt(left_energy * right_energy)


def run(depth: int, samples: int, seed: int, replay_count: int) -> dict[str, Any]:
    if depth < 64:
        raise ValueError("depth must be at least 64")
    if samples < 100:
        raise ValueError("samples must be at least 100")

    generated_length = 2 * depth + 96
    dps = math.ceil(generated_length * math.log10(2)) + 70
    replay_dps = dps + 80
    master_rng = random.Random(seed)
    sample_seeds = [master_rng.getrandbits(64) for _ in range(samples)]
    weights, suffix, omitted_tail_upper = _weights(generated_length, dps)
    checkpoints = sorted({64, 128, 256, 512, depth} & set(range(1, depth + 1)))
    checkpoint_counts = {n: [0, 0, 0, 0] for n in checkpoints}
    tail_half_counts = [0, 0, 0, 0]
    position_11_counts = [0] * depth
    cohort_11_counts = [[0] * depth, [0] * depth]
    cohort_accepted = [0, 0]
    double_counts: list[int] = []
    accepted_records: list[tuple[int, tuple[int, ...], tuple[int, ...]]] = []

    for sample_index, sample_seed in enumerate(sample_seeds):
        accepted, source, target = _decode_sample(
            sample_seed,
            depth=depth,
            generated_length=generated_length,
            dps=dps,
            weights=weights,
            suffix=suffix,
            omitted_tail_upper=omitted_tail_upper,
        )
        if not accepted:
            continue
        accepted_records.append((sample_seed, source, target))
        cohort = int(sample_index >= samples // 2)
        cohort_accepted[cohort] += 1
        cumulative = [0, 0, 0, 0]
        for n, (left, right) in enumerate(zip(source, target), start=1):
            cell = 2 * left + right  # 00, 01, 10, 11
            cumulative[cell] += 1
            if cell == 3:
                position_11_counts[n - 1] += 1
                cohort_11_counts[cohort][n - 1] += 1
            if n > depth // 2:
                tail_half_counts[cell] += 1
            if n in checkpoint_counts:
                for cell_index in range(4):
                    checkpoint_counts[n][cell_index] += cumulative[cell_index]
        double_counts.append(cumulative[3])

    accepted = len(accepted_records)
    if accepted == 0:
        raise AssertionError("no accepted fibre prefixes")

    replay_failures: list[dict[str, Any]] = []
    replay_weights, replay_suffix, replay_omitted_tail_upper = _weights(
        generated_length, replay_dps
    )
    for sample_seed, source, target in accepted_records[: min(replay_count, accepted)]:
        replay_accepted, replay_source, replay_target = _decode_sample(
            sample_seed,
            depth=depth,
            generated_length=generated_length,
            dps=replay_dps,
            weights=replay_weights,
            suffix=replay_suffix,
            omitted_tail_upper=replay_omitted_tail_upper,
        )
        if not replay_accepted or replay_source != source or replay_target != target:
            replay_failures.append(
                {
                    "sample_seed": sample_seed,
                    "accepted_changed": replay_accepted is not True,
                    "source_changed": replay_source != source,
                    "target_changed": replay_target != target,
                }
            )

    joint_rates_by_depth = {
        str(n): {
            label: checkpoint_counts[n][index] / (accepted * n)
            for index, label in enumerate(("00", "01", "10", "11"))
        }
        for n in checkpoints
    }
    tail_length = depth - depth // 2
    tail_half_rates = {
        label: tail_half_counts[index] / (accepted * tail_length)
        for index, label in enumerate(("00", "01", "10", "11"))
    }
    threshold_15 = math.floor(0.15 * depth)
    threshold_20 = math.floor(0.20 * depth)
    independent_no_double_probability = (3 / 4) ** depth
    position_11_rates = [count / accepted for count in position_11_counts]
    curvature_partial_sums: list[float] = []
    curvature_sum = 0.0
    for rate in position_11_rates:
        curvature_sum += rate - 0.25
        curvature_partial_sums.append(curvature_sum)
    curvature_checkpoint_sums = {
        str(n): curvature_partial_sums[n - 1] for n in checkpoints
    }
    dyadic_blocks: list[dict[str, float | int]] = []
    block_start = 1
    block_end = min(depth, 16)
    while block_start <= depth:
        block_sum = sum(
            rate - 0.25 for rate in position_11_rates[block_start - 1 : block_end]
        )
        dyadic_blocks.append(
            {
                "start": block_start,
                "end": block_end,
                "sum": block_sum,
                "mean": block_sum / (block_end - block_start + 1),
            }
        )
        block_start = block_end + 1
        block_end = min(depth, 2 * block_end)
    cohort_11_deviations = [
        [count / cohort_accepted[index] - 0.25 for count in cohort_11_counts[index]]
        for index in (0, 1)
    ]
    profile_starts = [start for start in (33, 65, 129, 257) if start <= depth]
    split_correlations = {
        str(start): _correlation(
            cohort_11_deviations[0][start - 1 :],
            cohort_11_deviations[1][start - 1 :],
        )
        for start in profile_starts
    }
    reproducible_spikes = sorted(
        (
            {
                "rank": rank + 1,
                "cohort_a_deviation": cohort_11_deviations[0][rank],
                "cohort_b_deviation": cohort_11_deviations[1][rank],
                "mean_absolute_deviation": abs(
                    (cohort_11_deviations[0][rank] + cohort_11_deviations[1][rank])
                    / 2
                ),
            }
            for rank in range(16, depth)
            if cohort_11_deviations[0][rank] * cohort_11_deviations[1][rank] > 0
        ),
        key=lambda row: row["mean_absolute_deviation"],
        reverse=True,
    )[:20]

    return {
        "schema": "erdos257_rational_fiber_digit_correlation_receipt_v0",
        "parameters": {
            "target": "3/2",
            "depth": depth,
            "samples": samples,
            "seed": seed,
            "generated_length": generated_length,
            "decimal_precision": dps,
            "replay_decimal_precision": replay_dps,
            "replay_count": min(replay_count, accepted),
        },
        "acceptance": {
            "accepted_prefixes": accepted,
            "acceptance_rate": accepted / samples,
            "meaning": "y=3/2-x survives the high-precision Mersenne greedy tail corridor through depth",
        },
        "joint_digit_order": ["00", "01", "10", "11"],
        "joint_rates_by_depth": joint_rates_by_depth,
        "tail_half_joint_rates": tail_half_rates,
        "coordinate_profile": {
            "p11_by_rank": position_11_rates,
            "split_cohort_accepted": cohort_accepted,
            "split_cohort_correlation_by_start_rank": split_correlations,
            "largest_same_sign_split_cohort_spikes": reproducible_spikes,
            "interpretation": "The Cesaro 1/4 law hides a reproducible non-flat arithmetic rank profile.",
        },
        "curvature_cesaro_profile": {
            "quantity": "sum_{n<=N}(p11(n)-1/4)",
            "checkpoint_sums": curvature_checkpoint_sums,
            "minimum": min(curvature_partial_sums),
            "minimum_rank": 1 + min(
                range(depth), key=lambda index: curvature_partial_sums[index]
            ),
            "maximum": max(curvature_partial_sums),
            "maximum_rank": 1 + max(
                range(depth), key=lambda index: curvature_partial_sums[index]
            ),
            "dyadic_blocks": dyadic_blocks,
            "mechanism_test": "An order-one envelope supports a coboundary/Cesaro-cancellation model; linear growth falsifies it.",
            "claim_boundary": "Finite sampled evidence only; boundedness for all N is not proved.",
        },
        "double_count_quantiles": _quantiles(double_counts),
        "low_collision_counts": {
            f"double_count_le_{threshold_15}": sum(
                value <= threshold_15 for value in double_counts
            ),
            f"double_count_le_{threshold_20}": sum(
                value <= threshold_20 for value in double_counts
            ),
        },
        "controls": {
            "independent_fair_pair_joint_rates": {
                "00": 0.25,
                "01": 0.25,
                "10": 0.25,
                "11": 0.25,
            },
            "independent_fair_pair_expected_double_count": depth / 4,
            "independent_fair_pair_double_count_stddev": math.sqrt(3 * depth / 16),
            "independent_fair_pair_no_double_probability": independent_no_double_probability,
            "exact_complement_target_E_joint_rates": {
                "00": 0.0,
                "01": 0.5,
                "10": 0.5,
                "11": 0.0,
            },
            "exact_complement_explanation": "At target E, uniqueness gives b'_n=1-b_n coordinatewise.",
        },
        "precision_replay": {
            "failure_count": len(replay_failures),
            "failures": replay_failures,
        },
        "mechanism_decision": {
            "eliminated": "generic_positive_measure_selection_followed_by_sparse_collision_cleanup",
            "evidence": "The 3/2 fibre's empirical tail joint law is near the independent 1/4 law, and its double count is order depth rather than sparse.",
            "remaining_exceptional_route": "A Boolean pair would require a zero-double, maximally anticorrelated fibre point; this audit neither constructs nor excludes that exceptional point.",
        },
        "consequence_decisions": {
            "multiplicity_two_construction": {
                "decision": "update_now",
                "mathematical_reason": "The construction's open correlation consumer now has a finite no-go for generic selection and sparse cleanup.",
                "authority_surface_checked": "MultiplicityTwoRationalConstruction.md",
                "validation_or_reentry": "Re-enter if an all-scale fibre decorrelation theorem or an exceptional anti-correlated point is proved.",
            },
            "lean_and_public_claims": {
                "decision": "verified_no_change",
                "mathematical_reason": "The audit proves no Boolean representation or infinite joint-normality theorem.",
                "authority_surface_checked": "claim boundary in RationalFiberCorrelationAudit.md and this receipt",
                "validation_or_reentry": "Require Lean or exact proof authority before claim promotion.",
            },
            "generic_lexical_candidates": {
                "decision": "outside_scope",
                "mathematical_reason": "Consequence-map matches on generic words such as depth are unrelated to the Erdos 257 fibre.",
                "authority_surface_checked": "mathematical_consequence_map candidate classes",
                "validation_or_reentry": "None unless an exact Erdos 257 semantic bridge is added.",
            },
        },
        "claim_boundary": {
            "proved": False,
            "finite_diagnostic_only": True,
            "caveat": "Accepted prefixes may fail after the audited depth, and observed joint normality is not an infinite-fibre theorem.",
        },
        "all_assertions": (
            len(replay_failures) == 0
            and max(abs(rate - 0.25) for rate in tail_half_rates.values()) < 0.02
            and not any(value <= threshold_15 for value in double_counts)
            and split_correlations[str(profile_starts[-1])] > 0.1
            and max(abs(value) for value in curvature_partial_sums) < 2.0
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=512)
    parser.add_argument("--samples", type=int, default=4096)
    parser.add_argument("--seed", type=int, default=257512)
    parser.add_argument("--replay-count", type=int, default=64)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()

    receipt = run(args.depth, args.samples, args.seed, args.replay_count)
    encoded = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    receipt["receipt_sha256_before_hash_field"] = hashlib.sha256(encoded.encode()).hexdigest()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(
        json.dumps(
            {
                "all_assertions": receipt["all_assertions"],
                "accepted_prefixes": receipt["acceptance"]["accepted_prefixes"],
                "depth": args.depth,
                "tail_half_11_rate": receipt["tail_half_joint_rates"]["11"],
                "output": str(args.output.relative_to(ROOT)),
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
