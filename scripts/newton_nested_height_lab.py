#!/usr/bin/env python3
"""Search for proof structure at the live Erdős-257 boundary.

This lab deliberately combines three different experiments.

1.  At an even strict-record successor ``2d`` it tests the coupled nested-
    height inequality

        f(2d) - f(d) + Q(2d)
          <= H(d) + H(d/2) + t(2d) - t(d).                 (NH)

    The old midpoint-service law follows immediately because ``H`` is
    nondecreasing.  The lab also tests two tempting summands of (NH)
    separately, so a larger census can falsify a fake decomposed proof while
    retaining the coupled statement.

2.  It constructs exact rational targets whose greedy word follows a chosen
    canonical prefix, enters a genuine Mersenne tail gap at a prescribed
    rank, and then takes every later coin.  These are boundary countermodels:
    (NH) fails after the fatal gap, proving that a carry-only argument cannot
    establish it.

3.  For the independent ``1/2`` quotient-row route, it verifies the exact
    last strict-core coin ``2^(R+1)+4`` and tests the separate fringe
    conjecture that the greedy remainder lies below that coin.  Conditional
    on this still-open fringe bound, the advertised core bound reduces to
    excluding only the three values immediately below the coin.

All arithmetic used for witnesses is exact.  A finite pass is conjecture
discrimination, never an all-depth proof or a solution of Erdős 257.
"""

from __future__ import annotations

import argparse
from array import array
import base64
from collections import Counter
from fractions import Fraction
import hashlib
import json
from math import gcd
from pathlib import Path
import platform
from typing import Any, Callable

from euler_midpoint_service_lab import (
    CANONICAL_PATH,
    OrbitArrays,
    bit_from_packed,
    interval_tables,
    midpoint_rows,
    reconstruct_orbit,
    replay_rational_target,
    target_digits,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/"
    "NewtonNestedHeightFrontier.md"
)


def canonical_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def load_canonical_bits(ranks: int) -> bytearray:
    receipt = json.loads(CANONICAL_PATH.read_text())
    available = int(receipt["parameters"]["ranks"])
    if not 1 <= ranks <= available:
        raise ValueError(f"canonical ranks must lie in [1,{available}]")
    packed_block = receipt["packed_itinerary"]
    packed = base64.b64decode(packed_block["data_base64"])
    digest = hashlib.sha256(packed).hexdigest()
    if digest != packed_block["sha256"] or digest != receipt["itinerary_sha256"]:
        raise AssertionError("canonical packed-itinerary digest mismatch")
    bits = bytearray(ranks + 1)
    for rank in range(1, ranks + 1):
        bits[rank] = bit_from_packed(packed, rank)
    return bits


def nested_row(row: dict[str, Any], orbit: OrbitArrays) -> dict[str, Any]:
    midpoint = int(row["midpoint"])
    quarter_height = int(orbit.heights[midpoint // 2])
    record_gain = int(row["record_defect"]) - int(
        row["half_predecessor_defect"]
    )
    digit_correction = int(row["successor_digit"]) - int(row["half_digit"])
    nested_budget = int(row["half_height"]) + quarter_height + digit_correction
    return {
        **row,
        "quarter_height": quarter_height,
        "record_gain": record_gain,
        "nested_height_budget": nested_budget,
        "nested_height_margin": nested_budget - int(row["service"]),
        "split_quarter_gain_margin": quarter_height - record_gain,
        "split_half_gain_residue_margin": (
            int(row["half_height"])
            - record_gain
            - int(row["half_defect"])
        ),
    }


def metric_summary(
    tagged_rows: list[tuple[str, dict[str, Any]]],
    metric: str,
) -> dict[str, Any]:
    if not tagged_rows:
        return {
            "row_count": 0,
            "minimum_margin": None,
            "violation_count": 0,
            "equality_count": 0,
            "violations": [],
        }
    values = [int(row[metric]) for _, row in tagged_rows]
    violations = [item for item in tagged_rows if int(item[1][metric]) < 0]
    equalities = [item for item in tagged_rows if int(item[1][metric]) == 0]
    return {
        "row_count": len(tagged_rows),
        "target_count": len({target for target, _ in tagged_rows}),
        "minimum_margin": min(values),
        "violation_count": len(violations),
        "equality_count": len(equalities),
        "violations": [
            {
                "target": target,
                **{
                    key: row[key]
                    for key in (
                        "successor",
                        "midpoint",
                        "half_height",
                        "quarter_height",
                        "record_gain",
                        "half_defect",
                        "new_layer_service",
                        "successor_defect",
                        metric,
                    )
                },
            }
            for target, row in violations[:20]
        ],
        "equalities": [
            {
                "target": target,
                "successor": row["successor"],
                "midpoint": row["midpoint"],
                "half_height": row["half_height"],
                "quarter_height": row["quarter_height"],
                "service": row["service"],
            }
            for target, row in equalities[:20]
        ],
    }


def canonical_nested_height(ranks: int) -> dict[str, Any]:
    bits = load_canonical_bits(ranks)
    orbit = reconstruct_orbit(bits, target_digits(1, 21, ranks), ranks)
    rows = [nested_row(row, orbit) for row in midpoint_rows(orbit, ranks)]
    selected = [
        ("1/21", row)
        for row in rows
        if int(row["midpoint"]) % 2 == 0
        and bool(row["phase_matched"])
        and int(row["half_height"]) >= 4
    ]
    return {
        "ranks": ranks,
        "strict_record_count": len(orbit.strict_records),
        "selected_even_midpoint_record_count": len(selected),
        "nested_height": metric_summary(selected, "nested_height_margin"),
        "quarter_gain_split": metric_summary(
            selected, "split_quarter_gain_margin"
        ),
        "half_gain_residue_split": metric_summary(
            selected, "split_half_gain_residue_margin"
        ),
        "last_selected_row": selected[-1][1] if selected else None,
    }


def rational_nested_height_census(
    ranks: int,
    max_denominator: int,
) -> dict[str, Any]:
    tables = interval_tables(ranks, 2 * ranks + 192)
    statuses: Counter[str] = Counter()
    alive = 0
    enumerated = 0
    selected: list[tuple[str, dict[str, Any]]] = []

    for denominator in range(2, max_denominator + 1):
        for numerator in range(1, denominator):
            if gcd(numerator, denominator) != 1:
                continue
            enumerated += 1
            status, payload = replay_rational_target(
                numerator, denominator, ranks, tables
            )
            statuses[status] += 1
            if status != "alive_through_cap":
                continue
            if isinstance(payload, int):
                raise AssertionError("alive orbit unexpectedly returned a rank")
            alive += 1
            target = f"{numerator}/{denominator}"
            for base_row in midpoint_rows(payload, ranks):
                row = nested_row(base_row, payload)
                if (
                    int(row["midpoint"]) % 2 == 0
                    and bool(row["phase_matched"])
                    and int(row["half_height"]) >= 4
                ):
                    selected.append((target, row))

    return {
        "parameters": {
            "ranks": ranks,
            "max_denominator": max_denominator,
            "selection": (
                "certified alive-through-cap rational targets; strict-record "
                "successor 2d with d even, endpoint digits equal, H(d)>=4"
            ),
        },
        "enumerated_target_count": enumerated,
        "alive_target_count": alive,
        "orbit_status_counts": dict(sorted(statuses.items())),
        "nested_height": metric_summary(selected, "nested_height_margin"),
        "quarter_gain_split": metric_summary(
            selected, "split_quarter_gain_margin"
        ),
        "half_gain_residue_split": metric_summary(
            selected, "split_half_gain_residue_margin"
        ),
        "selection_warning": (
            "The cohort is survivor-conditioned. Exact fatal-gap splices below "
            "test the missing boundary rather than treating this census as proof."
        ),
    }


def tail_upper_bound(death_rank: int) -> Fraction:
    """Strict rational upper bound for sum_(k>n) 1/(2^k-1)."""

    n = death_rank
    first_geometric_column = Fraction(1, 1 << n)
    later_columns = (
        Fraction(4, 3)
        * Fraction(1, 1 << (2 * (n + 1)))
        * Fraction(1, 1 - Fraction(1, 1 << (n + 1)))
    )
    return first_geometric_column + later_columns


def exact_gap_splice(death_rank: int, depth_multiplier: int) -> dict[str, Any]:
    depth = death_rank * depth_multiplier
    canonical = load_canonical_bits(death_rank - 1)
    prefix_value = sum(
        (
            Fraction(1, (1 << rank) - 1)
            for rank in range(1, death_rank)
            if canonical[rank]
        ),
        Fraction(),
    )
    death_coin = Fraction(1, (1 << death_rank) - 1)
    upper = tail_upper_bound(death_rank)
    if not upper < death_coin:
        raise AssertionError("tail upper bound did not expose a gap")
    gap_residual = (upper + death_coin) / 2
    target = prefix_value + gap_residual

    bits = bytearray(depth + 1)
    loads = array("I", [0]) * (depth + 1)
    defects = [0] * (depth + 1)
    heights = [0] * (depth + 1)
    digits = bytearray(depth + 1)
    strict_records: list[int] = []
    maximum = 0
    residual = target
    binary_remainder = target.numerator

    for rank in range(1, depth + 1):
        coin = Fraction(1, (1 << rank) - 1)
        if residual >= coin:
            bits[rank] = 1
            residual -= coin
            for multiple in range(rank, depth + 1, rank):
                loads[multiple] += 1
        binary_remainder *= 2
        digits[rank], binary_remainder = divmod(
            binary_remainder, target.denominator
        )
        heights[rank] = maximum + 1
        defect = 2 * defects[rank - 1] + digits[rank] - loads[rank]
        if defect < 0:
            raise AssertionError("exact gap splice produced negative defect")
        defects[rank] = defect
        if defect > maximum:
            maximum = defect
            strict_records.append(rank)

    if any(bits[rank] != canonical[rank] for rank in range(1, death_rank)):
        raise AssertionError("gap splice did not preserve the canonical prefix")
    if bits[death_rank] != 0:
        raise AssertionError("prescribed fatal rank was not skipped")
    if any(bits[rank] != 1 for rank in range(death_rank + 1, depth + 1)):
        raise AssertionError("fatal gap did not force the terminal all-take run")

    orbit = OrbitArrays(bits, loads, defects, heights, digits, strict_records)
    selected: list[tuple[str, dict[str, Any]]] = []
    for base_row in midpoint_rows(orbit, depth):
        row = nested_row(base_row, orbit)
        if (
            int(row["midpoint"]) % 2 == 0
            and bool(row["phase_matched"])
            and int(row["half_height"]) >= 4
        ):
            selected.append(("gap_splice", row))
    violations = [row for _, row in selected if row["nested_height_margin"] < 0]
    return {
        "death_rank": death_rank,
        "depth": depth,
        "target_numerator_bit_length": target.numerator.bit_length(),
        "target_denominator_bit_length": target.denominator.bit_length(),
        "gap_certificate": {
            "tail_upper_is_below_death_coin": upper < death_coin,
            "gap_residual_is_above_tail_upper": gap_residual > upper,
            "gap_residual_is_below_death_coin": gap_residual < death_coin,
        },
        "canonical_prefix_preserved_through": death_rank - 1,
        "fatal_skip_bit": bits[death_rank],
        "all_later_bits_are_one": all(
            bits[rank] == 1 for rank in range(death_rank + 1, depth + 1)
        ),
        "first_post_gap_strict_record": next(
            (rank for rank in strict_records if rank >= death_rank), None
        ),
        "selected_nested_row_count": len(selected),
        "nested_violation_count": len(violations),
        "first_nested_violation": violations[0] if violations else None,
    }


def integer_greedy_remainder(
    target: int,
    weights: list[int],
) -> int:
    remainder = target
    for weight in weights:
        if weight <= remainder:
            remainder -= weight
    return remainder


def half_three_state_audit(through: int) -> dict[str, Any]:
    if through < 4:
        raise ValueError("half audit must reach R=4")
    coarse_bound_failures: list[dict[str, Any]] = []
    fringe_failures: list[dict[str, Any]] = []
    three_state_hits: list[dict[str, Any]] = []
    last_coin_failures: list[dict[str, Any]] = []
    tight: tuple[int, int, int] | None = None  # core, bound, R
    perturbed_exact_counts = {0: 0, 1: 0, 2: 0}
    perturbed_smallest_residue: dict[int, tuple[int, int] | None] = {
        0: None,
        1: None,
        2: None,
    }

    for r in range(4, through + 1):
        endpoint = 2 * r
        power = 1 << endpoint
        half_power = 1 << (r + 1)
        weights = [power // ((1 << d) - 1) for d in range(2, r)]
        last_coin = weights[-1]
        if last_coin != half_power + 4:
            last_coin_failures.append(
                {"R": r, "actual": last_coin, "expected": half_power + 4}
            )
        core = integer_greedy_remainder((1 << (endpoint - 1)) - 1, weights)
        if not core < last_coin:
            fringe_failures.append(
                {"R": r, "core_minus_last_coin": core - last_coin}
            )
        if core > half_power:
            coarse_bound_failures.append(
                {
                    "R": r,
                    "core_minus_bound": core - half_power,
                    "core": core,
                }
            )
            if core - half_power in (1, 2, 3):
                three_state_hits.append(
                    {"R": r, "core_minus_bound": core - half_power}
                )
        if tight is None or core * tight[1] > tight[0] * half_power:
            tight = (core, half_power, r)

        target_half = 1 << (endpoint - 1)
        for perturbation in (0, 1, 2):
            residue = integer_greedy_remainder(
                target_half + perturbation, weights
            )
            if residue == 0:
                perturbed_exact_counts[perturbation] += 1
            best = perturbed_smallest_residue[perturbation]
            if best is None or residue < best[0]:
                perturbed_smallest_residue[perturbation] = (residue, r)

    if tight is None:
        raise AssertionError("half audit produced no rows")
    core, bound, tight_r = tight
    return {
        "rows_tested": through - 3,
        "max_R": through,
        "exact_last_strict_core_coin": "q_(2R)(R-1)=2^(R+1)+4 for R>=4",
        "last_coin_identity_failures": last_coin_failures,
        "open_fringe_candidate": (
            "A_R < 2^(R+1)+4. This does not follow from one-copy greedy "
            "without an additional boundary/capacity argument. Conditional "
            "on it, A_R<=2^(R+1) is exactly the exclusion of the next three "
            "integer states."
        ),
        "fringe_candidate_failures": fringe_failures[:20],
        "fringe_candidate_failure_count": len(fringe_failures),
        "coarse_bound_failures": coarse_bound_failures[:20],
        "coarse_bound_failure_count": len(coarse_bound_failures),
        "conditional_three_state_hits": three_state_hits[:20],
        "conditional_three_state_hit_count": len(three_state_hits),
        "tightest_normalized_row": {
            "R": tight_r,
            "scaled_floor_parts_per_billion": (core * 1_000_000_000) // bound,
            "bound_minus_core_exact_if_63_bits": (
                bound - core if (bound - core).bit_length() <= 63 else None
            ),
            "bound_minus_core_bit_length": (bound - core).bit_length(),
        },
        "near_half_core_exact_subset_control": {
            "targets": "2^(2R-1)+j for j=0,1,2 using only ranks 2,...,R-1",
            "exact_zero_residue_counts": perturbed_exact_counts,
            "smallest_positive_residues": {
                str(j): {
                    "residue": best[0],
                    "R": best[1],
                }
                for j, best in perturbed_smallest_residue.items()
                if best is not None
            },
            "status": "finite control only",
        },
    }


def build_receipt(args: argparse.Namespace) -> dict[str, Any]:
    script_path = Path(__file__).resolve()
    return {
        "schema": "erdos257_newton_nested_height_lab_v1",
        "claim_status": (
            "exact identities, exact boundary countermodels, and finite "
            "conjecture discrimination; Erdos 257 remains unproved"
        ),
        "authority": {
            "script_ref": str(script_path.relative_to(REPO_ROOT)),
            "script_sha256": hashlib.sha256(script_path.read_bytes()).hexdigest(),
            "analysis_ref": ANALYSIS_REF,
            "python_version": platform.python_version(),
            "floating_point_used_for_witnesses": False,
        },
        "exact_algebra": {
            "nested_height_candidate": (
                "f(2d)-f(d)+Q_(2d) <= H(d)+H(d/2)+t_(2d)-t_d"
            ),
            "phase_neutral_form": (
                "2*(Q_(2d-1)-Q_(d-1))+Q_d <= H(d)+H(d/2)"
            ),
            "implication": (
                "nested height and monotonicity H(d/2)<=H(d) imply the "
                "even-midpoint service law and hence DRMH at the plateau"
            ),
            "half_three_state_decomposition": (
                "q_(2R)(R-1)=2^(R+1)+4. The separately open fringe bound "
                "A_R<2^(R+1)+4 would reduce A_R<=2^(R+1) to three integers"
            ),
        },
        "canonical_twenty_one": canonical_nested_height(args.canonical_ranks),
        "rational_survivor_census": rational_nested_height_census(
            args.census_ranks, args.max_denominator
        ),
        "exact_fatal_gap_splices": [
            exact_gap_splice(death, args.gap_depth_multiplier)
            for death in args.fatal_death
        ],
        "half_quotient_three_state_audit": half_three_state_audit(
            args.half_through
        ),
        "proof_boundary": {
            "surviving_boundary": (
                "exclude a final Mersenne tail gap for one explicit rational "
                "target, equivalently kill the positive homogeneous carry mode"
            ),
            "not_claimed": [
                "the nested-height inequality at all depths for 1/21",
                "the fringe bound or three-state exclusion at all or "
                "cofinally many half rows",
                "1/21 or 1/2 achievement-set membership",
                "a proof or disproof of Erdos problem 257",
            ],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--canonical-ranks", type=int, default=2_000_002)
    parser.add_argument("--census-ranks", type=int, default=1_000)
    parser.add_argument("--max-denominator", type=int, default=101)
    parser.add_argument(
        "--fatal-death",
        type=int,
        action="append",
        default=None,
        help="prescribed exact tail-gap rank; repeatable (default: 40,80,140,200)",
    )
    parser.add_argument("--gap-depth-multiplier", type=int, default=5)
    parser.add_argument("--half-through", type=int, default=1_400)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.fatal_death is None:
        args.fatal_death = [40, 80, 140, 200]
    receipt = build_receipt(args)
    rendered = canonical_json(receipt)
    if args.output is not None:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
