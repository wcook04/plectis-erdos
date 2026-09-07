#!/usr/bin/env python3
"""Probe the doubled-midpoint service law behind Erdős problem 257.

For a greedy Mersenne-weight itinerary ``b_n`` and target binary digits
``t_n``, put

    f(n) = sum_{a|n} b_a,
    Q_n = 2 Q_{n-1} + t_n - f(n),
    H(d) = 1 + max_{0 <= k < d} Q_k.

At an even strict-record successor ``2d`` define the new divisor service

    g_d = f(2d) - f(d).

This script tests the exact midpoint inequality

    g_d + Q_{2d} <= 2 H(d) + t_{2d} - t_d.                 (EM)

It has two deliberately different experiments:

* decode the canonical two-million-rank 1/21 itinerary and reconstruct every
  term in (EM), independently of the quotient-greedy replay;
* run a directed-interval census of unrelated rational targets, looking both
  for counterexamples and for the hypotheses which discriminate them.

The computation is a conjecture discriminator.  It never promotes a finite
check to an all-depth theorem or to a solution of Erdős 257.
"""

from __future__ import annotations

import argparse
from array import array
import base64
from collections import Counter
from dataclasses import dataclass
from math import gcd
import hashlib
import json
from pathlib import Path
import platform
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[3]
CANONICAL_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "twenty_one_computational_structure_receipt_2000002_v1.json"
)
CANONICAL_PATH = REPO_ROOT / CANONICAL_REF
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/"
    "EulerMidpointServiceLaw.md"
)
WORD_1_OVER_21 = "000011"


def canonical_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def bit_from_packed(packed: bytes, rank: int) -> int:
    return (packed[(rank - 1) // 8] >> ((rank - 1) % 8)) & 1


def target_digits(numerator: int, denominator: int, ranks: int) -> bytearray:
    digits = bytearray(ranks + 1)
    remainder = numerator
    for rank in range(1, ranks + 1):
        remainder *= 2
        digits[rank], remainder = divmod(remainder, denominator)
        if digits[rank] not in (0, 1):
            raise AssertionError("target must lie strictly between zero and one")
    return digits


@dataclass
class OrbitArrays:
    bits: bytearray
    loads: array
    defects: array
    heights: array
    digits: bytearray
    strict_records: list[int]


def reconstruct_orbit(
    bits: bytearray,
    digits: bytearray,
    ranks: int,
) -> OrbitArrays:
    """Reconstruct divisor loads, defects, heights, and strict records."""

    if len(bits) <= ranks or len(digits) <= ranks:
        raise ValueError("orbit arrays do not cover requested ranks")
    loads = array("I", [0]) * (ranks + 1)
    for divisor in range(1, ranks + 1):
        if bits[divisor]:
            for multiple in range(divisor, ranks + 1, divisor):
                loads[multiple] += 1

    defects = array("I", [0]) * (ranks + 1)
    heights = array("I", [0]) * (ranks + 1)
    strict_records: list[int] = []
    maximum = 0
    for rank in range(1, ranks + 1):
        # H(rank) sees Q_0,...,Q_(rank-1).
        heights[rank] = maximum + 1
        defect = 2 * defects[rank - 1] + digits[rank] - loads[rank]
        if defect < 0:
            raise AssertionError(f"negative defect at rank {rank}")
        defects[rank] = defect
        if defect > maximum:
            maximum = defect
            strict_records.append(rank)
    return OrbitArrays(bits, loads, defects, heights, digits, strict_records)


def midpoint_rows(orbit: OrbitArrays, ranks: int) -> list[dict[str, Any]]:
    """Return exact rows for strict records with even successors in range."""

    rows: list[dict[str, Any]] = []
    for record_rank in orbit.strict_records:
        successor = record_rank + 1
        if successor > ranks or successor % 2:
            continue
        midpoint = successor // 2
        record_defect = int(orbit.defects[record_rank])
        half_height = int(orbit.heights[midpoint])
        half_predecessor_defect = int(orbit.defects[midpoint - 1])
        half_defect = int(orbit.defects[midpoint])
        successor_defect = int(orbit.defects[successor])
        half_load = int(orbit.loads[midpoint])
        successor_load = int(orbit.loads[successor])
        new_layer_service = successor_load - half_load
        previous_layer_service = (
            half_load - int(orbit.loads[midpoint // 2])
            if midpoint % 2 == 0
            else None
        )
        half_digit = int(orbit.digits[midpoint])
        successor_digit = int(orbit.digits[successor])

        service = new_layer_service + successor_defect
        corrected_budget = 2 * half_height + successor_digit - half_digit
        block_increment = (
            2 * (record_defect - half_predecessor_defect) + half_defect
        )
        identity_right = block_increment + successor_digit - half_digit
        if service != identity_right:
            raise AssertionError("midpoint cancellation identity failed")

        rows.append(
            {
                "record_rank": record_rank,
                "successor": successor,
                "midpoint": midpoint,
                "record_defect": record_defect,
                "half_height": half_height,
                "half_predecessor_defect": half_predecessor_defect,
                "half_defect": half_defect,
                "successor_defect": successor_defect,
                "half_load": half_load,
                "successor_load": successor_load,
                "new_layer_service": new_layer_service,
                "previous_layer_service": previous_layer_service,
                "half_digit": half_digit,
                "successor_digit": successor_digit,
                "phase_matched": half_digit == successor_digit,
                "service": service,
                "corrected_budget": corrected_budget,
                "service_margin": corrected_budget - service,
                "block_increment": block_increment,
                "phase_neutral_margin": 2 * half_height - block_increment,
                "drmh_margin": 2 * half_height - (record_defect + 1),
            }
        )
    return rows


def summarize_rows(rows: list[dict[str, Any]]) -> dict[str, Any]:
    if not rows:
        return {
            "row_count": 0,
            "violation_count": 0,
            "equality_count": 0,
            "minimum_margin": None,
            "violations": [],
            "equalities": [],
        }
    violations = [row for row in rows if int(row["service_margin"]) < 0]
    equalities = [row for row in rows if int(row["service_margin"]) == 0]
    minimum = min(int(row["service_margin"]) for row in rows)
    return {
        "row_count": len(rows),
        "violation_count": len(violations),
        "equality_count": len(equalities),
        "minimum_margin": minimum,
        "violations": violations[:50],
        "equalities": equalities[:50],
    }


def canonical_twenty_one_experiment(
    canonical_ranks: int | None,
) -> dict[str, Any]:
    receipt = json.loads(CANONICAL_PATH.read_text())
    packed_block = receipt["packed_itinerary"]
    packed = base64.b64decode(packed_block["data_base64"])
    digest = hashlib.sha256(packed).hexdigest()
    if digest != packed_block["sha256"] or digest != receipt["itinerary_sha256"]:
        raise AssertionError("canonical packed-itinerary digest mismatch")
    receipt_ranks = int(receipt["parameters"]["ranks"])
    ranks = receipt_ranks if canonical_ranks is None else canonical_ranks
    if ranks < 20 or ranks > receipt_ranks:
        raise ValueError(f"canonical ranks must lie in [20,{receipt_ranks}]")

    bits = bytearray(ranks + 1)
    for rank in range(1, ranks + 1):
        bits[rank] = bit_from_packed(packed, rank)
    digits = target_digits(1, 21, ranks)
    if "".join(str(digits[rank]) for rank in range(1, 7)) != WORD_1_OVER_21:
        raise AssertionError("1/21 source period drifted")
    orbit = reconstruct_orbit(bits, digits, ranks)
    rows = midpoint_rows(orbit, ranks)
    if not rows:
        raise AssertionError("canonical orbit has no even record successors")
    if any(not bool(row["phase_matched"]) for row in rows):
        raise AssertionError("canonical even record successor lost phase match")
    if any(int(row["successor"]) % 20 for row in rows):
        raise AssertionError("canonical post-seed record phase lock drifted")
    if any(int(row["service_margin"]) < 0 for row in rows):
        raise AssertionError("canonical orbit violates midpoint service law")

    split_violations = [
        row
        for row in rows
        if int(row["new_layer_service"]) > int(row["half_height"])
    ]
    tight = sorted(rows, key=lambda row: int(row["service_margin"]))[:12]
    maximum_service_excess = max(
        int(row["service"]) - int(row["half_height"]) for row in rows
    )
    maximum_service_excess_rows = [
        row
        for row in rows
        if int(row["service"]) - int(row["half_height"])
        == maximum_service_excess
    ]
    return {
        "ranks": ranks,
        "selected_count": sum(bits),
        "maximum_defect": max(orbit.defects),
        "strict_record_count": len(orbit.strict_records),
        "even_record_successor_count": len(rows),
        "all_even_successors_are_multiples_of_20": all(
            int(row["successor"]) % 20 == 0 for row in rows
        ),
        "all_even_successors_phase_match": all(
            bool(row["phase_matched"]) for row in rows
        ),
        "service_law": summarize_rows(rows),
        "naive_split_g_le_H_violation_count": len(split_violations),
        "naive_split_g_le_H_first_violations": split_violations[:12],
        "maximum_service_excess_over_half_height": maximum_service_excess,
        "maximum_service_excess_rows": maximum_service_excess_rows,
        "tightest_service_rows": tight,
        "last_service_row": rows[-1],
    }


def interval_tables(
    ranks: int, precision_bits: int
) -> tuple[int, list[int], list[int], list[int], list[int]]:
    """Return rigorous dyadic coin and infinite-tail enclosures."""

    scale = 1 << precision_bits
    weight_lower = [0] * (ranks + 1)
    weight_upper = [0] * (ranks + 1)
    for rank in range(1, ranks + 1):
        denominator = (1 << rank) - 1
        weight_lower[rank] = scale // denominator
        weight_upper[rank] = (scale + denominator - 1) // denominator

    tail_lower = [0] * (ranks + 1)
    tail_upper = [0] * (ranks + 1)
    tail_lower[ranks] = scale >> ranks
    correction_denominator = 3 * (1 << (2 * ranks))
    tail_upper[ranks] = tail_lower[ranks] + (
        2 * scale + correction_denominator - 1
    ) // correction_denominator
    for rank in range(ranks - 1, -1, -1):
        tail_lower[rank] = tail_lower[rank + 1] + weight_lower[rank + 1]
        tail_upper[rank] = tail_upper[rank + 1] + weight_upper[rank + 1]
    return scale, weight_lower, weight_upper, tail_lower, tail_upper


def replay_rational_target(
    numerator: int,
    denominator: int,
    ranks: int,
    tables: tuple[int, list[int], list[int], list[int], list[int]],
) -> tuple[str, OrbitArrays | int]:
    """Certify one finite rational greedy orbit by directed intervals."""

    scale, weight_lower, weight_upper, tail_lower, tail_upper = tables
    residual_lower = scale * numerator // denominator
    residual_upper = (scale * numerator + denominator - 1) // denominator
    bits = bytearray(ranks + 1)
    loads = array("I", [0]) * (ranks + 1)
    digits = bytearray(ranks + 1)
    defects = array("I", [0]) * (ranks + 1)
    heights = array("I", [0]) * (ranks + 1)
    strict_records: list[int] = []
    maximum = 0
    remainder = numerator

    for rank in range(1, ranks + 1):
        took = False
        if residual_lower >= weight_upper[rank]:
            took = True
            bits[rank] = 1
            residual_lower -= weight_upper[rank]
            residual_upper -= weight_lower[rank]
            for multiple in range(rank, ranks + 1, rank):
                loads[multiple] += 1
        elif residual_upper <= weight_lower[rank]:
            pass
        else:
            return "ambiguous_decision", rank

        remainder *= 2
        digits[rank], remainder = divmod(remainder, denominator)
        heights[rank] = maximum + 1
        defect = 2 * defects[rank - 1] + digits[rank] - loads[rank]
        if defect < 0:
            raise AssertionError(
                f"negative defect for {numerator}/{denominator} at {rank}"
            )
        defects[rank] = defect
        if defect > maximum:
            maximum = defect
            strict_records.append(rank)

        if residual_upper <= 0:
            return "finite", rank
        if not took:
            if residual_lower > tail_upper[rank]:
                return "fatal_gap", rank
            if residual_upper > tail_lower[rank]:
                return "ambiguous_tail", rank

    return (
        "alive_through_cap",
        OrbitArrays(bits, loads, defects, heights, digits, strict_records),
    )


def examples_with_target(
    rows: Iterable[tuple[str, dict[str, Any]]], limit: int = 50
) -> list[dict[str, Any]]:
    result: list[dict[str, Any]] = []
    for target, row in rows:
        result.append({"target": target, **row})
        if len(result) >= limit:
            break
    return result


def rational_census(ranks: int, max_denominator: int) -> dict[str, Any]:
    if ranks < 20:
        raise ValueError("census ranks must be at least 20")
    if max_denominator < 3:
        raise ValueError("maximum denominator must be at least 3")
    tables = interval_tables(ranks, 2 * ranks + 192)
    statuses: Counter[str] = Counter()
    status_max_rank: dict[str, int] = {}
    enumerated = 0
    alive = 0
    tagged_rows: list[tuple[str, dict[str, Any]]] = []

    for denominator in range(2, max_denominator + 1):
        for numerator in range(1, denominator):
            if gcd(numerator, denominator) != 1:
                continue
            enumerated += 1
            status, payload = replay_rational_target(
                numerator, denominator, ranks, tables
            )
            statuses[status] += 1
            if isinstance(payload, int):
                status_max_rank[status] = max(
                    status_max_rank.get(status, 0), payload
                )
                continue
            alive += 1
            target = f"{numerator}/{denominator}"
            for row in midpoint_rows(payload, ranks):
                tagged_rows.append((target, row))

    phase_rows = [item for item in tagged_rows if item[1]["phase_matched"]]
    phase_h4_rows = [
        item for item in phase_rows if int(item[1]["half_height"]) >= 4
    ]
    mod4_phase_h4_rows = [
        item
        for item in phase_h4_rows
        if int(item[1]["successor"]) % 4 == 0
    ]
    mod20_rows = [
        item for item in tagged_rows if int(item[1]["successor"]) % 20 == 0
    ]
    mod20_h4_rows = [
        item for item in mod20_rows if int(item[1]["half_height"]) >= 4
    ]
    mod20_phase_h4_rows = [
        item for item in mod20_h4_rows if item[1]["phase_matched"]
    ]
    corrected_h4_rows = [
        item for item in tagged_rows if int(item[1]["half_height"]) >= 4
    ]

    def tagged_summary(
        items: list[tuple[str, dict[str, Any]]]
    ) -> dict[str, Any]:
        margins = [int(row["service_margin"]) for _, row in items]
        violations = [item for item in items if int(item[1]["service_margin"]) < 0]
        equalities = [item for item in items if int(item[1]["service_margin"]) == 0]
        return {
            "row_count": len(items),
            "target_count": len({target for target, _ in items}),
            "minimum_margin": min(margins) if margins else None,
            "violation_count": len(violations),
            "violation_half_height_counts": dict(sorted(Counter(
                int(row["half_height"]) for _, row in violations
            ).items())),
            "equality_count": len(equalities),
            "violations": examples_with_target(violations),
            "equalities": examples_with_target(equalities),
        }

    naive_split_violations = [
        item
        for item in tagged_rows
        if int(item[1]["new_layer_service"]) > int(item[1]["half_height"])
    ]
    return {
        "parameters": {
            "ranks": ranks,
            "max_denominator": max_denominator,
            "precision_bits": 2 * ranks + 192,
            "cohort": "all reduced fractions 0<a/q<1 with q<=max_denominator",
        },
        "enumerated_target_count": enumerated,
        "orbit_status_counts": dict(sorted(statuses.items())),
        "orbit_status_max_rank": status_max_rank,
        "alive_target_count": alive,
        "even_strict_record_row_count": len(tagged_rows),
        "all_corrected_rows": tagged_summary(tagged_rows),
        "corrected_rows_with_H_at_least_4": tagged_summary(corrected_h4_rows),
        "phase_matched_rows": tagged_summary(phase_rows),
        "phase_matched_rows_with_H_at_least_4": tagged_summary(phase_h4_rows),
        "successor_multiple_of_4_phase_matched_rows_with_H_at_least_4": (
            tagged_summary(mod4_phase_h4_rows)
        ),
        "successor_multiple_of_20_rows": tagged_summary(mod20_rows),
        "successor_multiple_of_20_rows_with_H_at_least_4": tagged_summary(
            mod20_h4_rows
        ),
        "successor_multiple_of_20_phase_matched_rows_with_H_at_least_4": (
            tagged_summary(mod20_phase_h4_rows)
        ),
        "naive_split_g_le_H_violation_count": len(naive_split_violations),
        "naive_split_g_le_H_examples": examples_with_target(
            naive_split_violations
        ),
    }


def build_receipt(
    canonical_ranks: int | None,
    census_ranks: int,
    max_denominator: int,
) -> dict[str, Any]:
    script_path = Path(__file__).resolve()
    return {
        "schema": "erdos257_euler_midpoint_service_lab_v1",
        "claim_status": (
            "exact finite falsification evidence plus an exact algebraic "
            "reduction; the midpoint service law remains unproved"
        ),
        "authority": {
            "script_ref": str(script_path.relative_to(REPO_ROOT)),
            "script_sha256": hashlib.sha256(script_path.read_bytes()).hexdigest(),
            "analysis_ref": ANALYSIS_REF,
            "canonical_itinerary_ref": CANONICAL_REF,
            "method": (
                "packed-itinerary decoding, exact integer divisor convolution, "
                "exact defect recurrence, and certified directed-dyadic "
                "rational greedy replay"
            ),
            "floating_point_used": False,
            "python_version": platform.python_version(),
        },
        "exact_algebra": {
            "definitions": (
                "f(n)=sum_(a|n)b_a; Q_n=2Q_(n-1)+t_n-f(n); "
                "H(d)=1+max_(0<=k<d)Q_k; g_d=f(2d)-f(d)"
            ),
            "candidate_EM": (
                "g_d+Q_(2d) <= 2H(d)+t_(2d)-t_d at an even strict-record "
                "successor 2d"
            ),
            "cancellation_identity": (
                "g_d+Q_(2d)=2(Q_(2d-1)-Q_(d-1))+Q_d+t_(2d)-t_d"
            ),
            "phase_neutral_form": (
                "2(Q_(2d-1)-Q_(d-1))+Q_d <= 2H(d)"
            ),
            "proved_implication": (
                "EM implies Q_(2d-1)+1 <= 2H(d), hence the DRMH plateau "
                "inequality at that record"
            ),
        },
        "canonical_twenty_one": canonical_twenty_one_experiment(
            canonical_ranks
        ),
        "rational_control_census": rational_census(
            census_ranks, max_denominator
        ),
        "proof_boundary": {
            "not_claimed": [
                "EM for every future phase-matched record",
                "the all-depth 1/21 record phase lock",
                "DRMH at all depths",
                "1/21 achievement-set membership",
                "a decision of Erdos problem 257",
            ],
            "next_proof_target": (
                "Prove the even-midpoint service lemma: at a strict-record "
                "successor 2d with d even, matching endpoint digits, and "
                "H(d)>=4, prove the phase-neutral block-increment bound for "
                "the actual greedy dynamics. Then prove only the weaker 1/21 "
                "record four-lock (every later successor is divisible by 4); "
                "the period-six source then supplies matching endpoint digits."
            ),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--canonical-ranks",
        type=int,
        default=None,
        help="prefix of the canonical packed 1/21 orbit (default: all)",
    )
    parser.add_argument("--census-ranks", type=int, default=1_000)
    parser.add_argument("--max-denominator", type=int, default=101)
    parser.add_argument(
        "--output",
        type=Path,
        help="optional JSON output path; stdout is always emitted",
    )
    args = parser.parse_args()
    receipt = build_receipt(
        args.canonical_ranks, args.census_ranks, args.max_denominator
    )
    rendered = canonical_json(receipt)
    if args.output is not None:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
