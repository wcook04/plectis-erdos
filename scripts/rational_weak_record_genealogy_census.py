#!/usr/bin/env python3
"""Exact rational-target census for shifted weak-record genealogy.

The denominator-21 computation suggests comparing defect density along a
strict-record/weak-record divisor edge.  The unshifted candidate uses Q/n;
the carry coordinate which occurs in the membership theorem is instead
(Q+1)/n.  This script tests both versions on every eligible edge and also
tests the stronger multiplicative running-maximum envelope from which the
shifted edge law would follow.

Only targets whose exact interval orbit is certified alive through the depth
cap enter the genealogy census.  A finite census is a falsification control,
not a theorem about all rational targets or all ranks.
"""

from __future__ import annotations

import argparse
import base64
from fractions import Fraction
import hashlib
import json
from math import gcd
from pathlib import Path
import platform
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
DEFAULT_RANKS = 1_000
DEFAULT_MAX_DENOMINATOR = 101
CONTROL_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "rational_record_genealogy_control_receipt.json"
)
CONTROL_PATH = REPO_ROOT / CONTROL_REF
TWENTY_ONE_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "twenty_one_computational_structure_receipt.json"
)
TWENTY_ONE_PATH = REPO_ROOT / TWENTY_ONE_REF
RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "rational_weak_record_genealogy_census_receipt.json"
)
DEFAULT_RECEIPT = REPO_ROOT / RECEIPT_REF
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/"
    "TwentyOneRecordAncestorInheritance.md"
)
PMRMH_COUNTEREXAMPLE_SUPPORT = (
    2, 3, 4, 7, 9, 11, 15, 16, 22, 44, 45, 46, 47, 48
)
PMRMH_COUNTEREXAMPLE_BASE = 22
PMRMH_COUNTEREXAMPLE_QUOTIENT = 2
PMRMH_COUNTEREXAMPLE_EXTENSION_START = 100


def canonical_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def canonical_payload_sha256(payload: dict[str, Any]) -> str:
    encoded = json.dumps(
        payload, separators=(",", ":"), sort_keys=True
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def exact_pmrmh_support_counterexample() -> dict[str, Any]:
    """Return a fully exact representability falsifier for PMRMH.

    For a support ``A`` representing ``x``, its target defect is

      Q_k = floor(sum_{d in A} 2^(k mod d)/(2^d-1)).

    The displayed finite support is its own exact greedy expansion, yet its
    positive-base multiplicative running maximum fails at 44 = 2 * 22.
    The same integer heights survive adjoining every rank at least 100, so
    the failure is not an artefact of finite support.
    """

    support = list(PMRMH_COUNTEREXAMPLE_SUPPORT)
    target = sum((Fraction(1, (1 << d) - 1) for d in support), Fraction())

    remainder = target
    replayed: list[int] = []
    for rank in range(1, support[-1] + 1):
        weight = Fraction(1, (1 << rank) - 1)
        if weight <= remainder:
            replayed.append(rank)
            remainder -= weight
    if replayed != support or remainder != 0:
        raise AssertionError("PMRMH support does not replay exactly")

    def tail(rank: int) -> Fraction:
        return sum(
            (
                Fraction(1 << (rank % divisor), (1 << divisor) - 1)
                for divisor in support
            ),
            Fraction(),
        )

    def defect(rank: int) -> int:
        value = tail(rank)
        return value.numerator // value.denominator

    def target_floor_defect(rank: int) -> int:
        target_floor = (
            (1 << rank) * target.numerator // target.denominator
        )
        prefix_numerator = sum(
            sum(rank_index % divisor == 0 for divisor in support)
            * (1 << (rank - rank_index))
            for rank_index in range(1, rank + 1)
        )
        return target_floor - prefix_numerator

    def height(horizon: int) -> tuple[int, int, Fraction]:
        rows = [(defect(rank), rank, tail(rank)) for rank in range(horizon)]
        maximum_defect, witness_rank, witness_tail = max(rows)
        return maximum_defect + 1, witness_rank, witness_tail

    base = PMRMH_COUNTEREXAMPLE_BASE
    quotient = PMRMH_COUNTEREXAMPLE_QUOTIENT
    multiple = quotient * base
    base_height, base_witness, base_tail = height(base)
    multiple_height, multiple_witness, multiple_tail = height(multiple)
    margin = quotient * base_height - multiple_height
    if (base_height, multiple_height, margin) != (2, 5, -1):
        raise AssertionError("PMRMH counterexample heights drifted")
    for rank in range(multiple):
        if target_floor_defect(rank) != defect(rank):
            raise AssertionError("target-floor and divisor-tail defects differ")

    extension_start = PMRMH_COUNTEREXAMPLE_EXTENSION_START

    def extension_upper_bound(rank: int) -> Fraction:
        # For d > rank, 2^rank/(2^d-1) < 2^(rank-d+1).
        # Summing d >= extension_start gives 2^(rank+2-extension_start).
        return Fraction(1, 1 << (extension_start - rank - 2))

    for rank in range(multiple):
        if not tail(rank) + extension_upper_bound(rank) < (
            2 if rank < base else 5
        ):
            raise AssertionError("infinite extension can change an upper floor")
    if not tail(base_witness) >= 1 or not tail(multiple_witness) >= 4:
        raise AssertionError("counterexample lower floor witness drifted")

    return {
        "id": "PMRMH_EXACT_REPRESENTATION_FALSIFIER",
        "support_ranks": support,
        "support_cardinality": len(support),
        "exact_rational_target": {
            "numerator": target.numerator,
            "denominator": target.denominator,
        },
        "exact_greedy_replay": {
            "selected_ranks": replayed,
            "terminal_rank": support[-1],
            "terminal_remainder_numerator": remainder.numerator,
            "terminal_remainder_denominator": remainder.denominator,
            "matches_declared_support": replayed == support,
        },
        "tail_identity_used": (
            "Q_k=floor(T_k), where T_k=sum_{d in A} "
            "2^(k mod d)/(2^d-1), for an exactly represented target"
        ),
        "target_floor_defect_crosscheck_rank_count": multiple,
        "positive_base_violation": {
            "base_horizon": base,
            "base_height": base_height,
            "base_floor_witness_rank": base_witness,
            "base_floor_witness_tail": {
                "numerator": base_tail.numerator,
                "denominator": base_tail.denominator,
            },
            "quotient": quotient,
            "multiple_horizon": multiple,
            "multiple_height": multiple_height,
            "multiple_floor_witness_rank": multiple_witness,
            "multiple_floor_witness_tail": {
                "numerator": multiple_tail.numerator,
                "denominator": multiple_tail.denominator,
            },
            "integer_margin": margin,
        },
        "infinite_support_extension": {
            "support": "A_* union {d : d>=100}",
            "extension_start": extension_start,
            "per_rank_strict_upper_bound": (
                "sum_{d>=100} 2^k/(2^d-1) < 2^(k+2-100)"
            ),
            "base_height_remains": base_height,
            "multiple_height_remains": multiple_height,
            "integer_margin_remains": margin,
        },
        "classification": (
            "PMRMH is neither support-universal nor implied by exact greedy "
            "representability; an all-depth proof for 1/21 must use "
            "additional arithmetic of that actual orbit"
        ),
    }


def interval_tables(ranks: int, precision_bits: int) -> tuple[
    int, list[int], list[int], list[int], list[int]
]:
    """Return scale, coin bounds, and rigorous tail bounds.

    For k>R,

      sum 1/(2^k-1) = 2^-R + correction,
      0 < correction < (2/3) 4^-R.

    Adding the individually rounded coins backwards gives certified bounds
    for every tail after ranks 0..R.
    """

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
        tail_lower[rank] = (
            tail_lower[rank + 1] + weight_lower[rank + 1]
        )
        tail_upper[rank] = (
            tail_upper[rank + 1] + weight_upper[rank + 1]
        )
    return scale, weight_lower, weight_upper, tail_lower, tail_upper


def replay_target(
    numerator: int,
    denominator: int,
    ranks: int,
    scale: int,
    weight_lower: list[int],
    weight_upper: list[int],
    tail_lower: list[int],
    tail_upper: list[int],
) -> dict[str, Any]:
    common = gcd(numerator, denominator)
    numerator //= common
    denominator //= common
    target = f"{numerator}/{denominator}"
    residual_lower = scale * numerator // denominator
    residual_upper = (
        scale * numerator + denominator - 1
    ) // denominator

    bits = bytearray(ranks + 1)
    selected_divisor_counts = [0] * (ranks + 1)
    defects = [0] * (ranks + 1)
    strict_records: list[int] = []
    weak_records: list[int] = []
    running_max_plus_one = [1] * (ranks + 2)
    maximum_defect = 0
    binary_remainder = numerator

    for rank in range(1, ranks + 1):
        took = False
        if residual_lower >= weight_upper[rank]:
            took = True
            bits[rank] = 1
            residual_lower -= weight_upper[rank]
            residual_upper -= weight_lower[rank]
            for multiple in range(rank, ranks + 1, rank):
                selected_divisor_counts[multiple] += 1
        elif residual_upper <= weight_lower[rank]:
            pass
        else:
            return {
                "target": target,
                "orbit_status": "ambiguous_decision",
                "status_rank": rank,
            }

        binary_remainder *= 2
        target_bit = binary_remainder // denominator
        binary_remainder %= denominator
        defect = (
            2 * defects[rank - 1]
            + target_bit
            - selected_divisor_counts[rank]
        )
        if defect < 0:
            raise AssertionError(f"negative defect for {target} at {rank}")
        defects[rank] = defect
        if defect > maximum_defect:
            maximum_defect = defect
            strict_records.append(rank)
            weak_records.append(rank)
        elif defect == maximum_defect and maximum_defect > 0:
            weak_records.append(rank)
        running_max_plus_one[rank + 1] = maximum_defect + 1

        if residual_upper <= 0:
            return {
                "target": target,
                "orbit_status": "finite",
                "status_rank": rank,
            }
        if not took:
            if residual_lower > tail_upper[rank]:
                return {
                    "target": target,
                    "orbit_status": "fatal_gap",
                    "status_rank": rank,
                }
            if residual_upper > tail_lower[rank]:
                return {
                    "target": target,
                    "orbit_status": "ambiguous_tail",
                    "status_rank": rank,
                }

    all_edge_count = 0
    raw_all_edge_violations: list[dict[str, Any]] = []
    shifted_all_edge_violations: list[dict[str, Any]] = []
    raw_chosen_violations: list[dict[str, Any]] = []
    shifted_chosen_violations: list[dict[str, Any]] = []
    parentless_after_first: list[int] = []
    chosen_edge_count = 0
    shifted_equality_count = 0

    for record_index, rank in enumerate(strict_records):
        eligible = [
            weak_rank
            for weak_rank in weak_records
            if weak_rank < rank and (rank + 1) % (weak_rank + 1) == 0
        ]
        if record_index > 0 and not eligible:
            parentless_after_first.append(rank)
        for weak_rank in eligible:
            quotient = (rank + 1) // (weak_rank + 1)
            raw_margin = quotient * defects[weak_rank] - defects[rank]
            shifted_margin = (
                quotient * (defects[weak_rank] + 1) - (defects[rank] + 1)
            )
            edge = {
                "record_rank": rank,
                "record_defect": defects[rank],
                "weak_record_rank": weak_rank,
                "weak_record_defect": defects[weak_rank],
                "successor_quotient": quotient,
                "raw_margin": raw_margin,
                "shifted_margin": shifted_margin,
            }
            all_edge_count += 1
            if raw_margin < 0:
                raw_all_edge_violations.append(edge)
            if shifted_margin < 0:
                shifted_all_edge_violations.append(edge)
            if shifted_margin == 0:
                shifted_equality_count += 1

        if eligible:
            weak_rank = max(eligible)
            quotient = (rank + 1) // (weak_rank + 1)
            raw_margin = quotient * defects[weak_rank] - defects[rank]
            shifted_margin = (
                quotient * (defects[weak_rank] + 1) - (defects[rank] + 1)
            )
            chosen = {
                "record_rank": rank,
                "record_defect": defects[rank],
                "weak_record_rank": weak_rank,
                "weak_record_defect": defects[weak_rank],
                "successor_quotient": quotient,
                "raw_margin": raw_margin,
                "shifted_margin": shifted_margin,
            }
            chosen_edge_count += 1
            if raw_margin < 0:
                raw_chosen_violations.append(chosen)
            if shifted_margin < 0:
                shifted_chosen_violations.append(chosen)

    multiplicative_pair_count = 0
    multiplicative_equality_count = 0
    multiplicative_minimum_margin: int | None = None
    multiplicative_violations: list[dict[str, int]] = []
    positive_multiplicative_pair_count = 0
    positive_multiplicative_equality_count = 0
    positive_multiplicative_minimum_margin: int | None = None
    positive_multiplicative_violations: list[dict[str, int]] = []
    for divisor in range(1, (ranks + 1) // 2 + 1):
        divisor_height = running_max_plus_one[divisor]
        for multiple in range(2 * divisor, ranks + 2, divisor):
            quotient = multiple // divisor
            margin = (
                quotient * divisor_height
                - running_max_plus_one[multiple]
            )
            multiplicative_pair_count += 1
            if (
                multiplicative_minimum_margin is None
                or margin < multiplicative_minimum_margin
            ):
                multiplicative_minimum_margin = margin
            if margin == 0:
                multiplicative_equality_count += 1
            if margin < 0:
                violation = {
                    "divisor_horizon": divisor,
                    "multiple_horizon": multiple,
                    "quotient": quotient,
                    "divisor_height": divisor_height,
                    "multiple_height": running_max_plus_one[multiple],
                    "margin": margin,
                }
                multiplicative_violations.append(violation)
            if divisor_height >= 2:
                positive_multiplicative_pair_count += 1
                if (
                    positive_multiplicative_minimum_margin is None
                    or margin < positive_multiplicative_minimum_margin
                ):
                    positive_multiplicative_minimum_margin = margin
                if margin == 0:
                    positive_multiplicative_equality_count += 1
                if margin < 0:
                    positive_multiplicative_violations.append(violation)

    second_record_anchor_rank = (
        strict_records[1] if len(strict_records) >= 2 else None
    )
    second_record_anchor_violations = (
        [
            rank
            for rank in strict_records[2:]
            if (rank + 1) % (second_record_anchor_rank + 1) != 0
        ]
        if second_record_anchor_rank is not None
        else []
    )

    packed = bytearray((ranks + 7) // 8)
    for rank in range(1, ranks + 1):
        if bits[rank]:
            packed[(rank - 1) // 8] |= 1 << ((rank - 1) % 8)
    return {
        "target": target,
        "orbit_status": "alive_through_cap",
        "selected_count": sum(bits),
        "packed_itinerary_sha256": hashlib.sha256(packed).hexdigest(),
        "maximum_defect": maximum_defect,
        "strict_record_count": len(strict_records),
        "weak_record_count": len(weak_records),
        "chosen_edge_count": chosen_edge_count,
        "all_eligible_edge_count": all_edge_count,
        "parentless_after_first_record_ranks": parentless_after_first,
        "raw_chosen_violation_count": len(raw_chosen_violations),
        "raw_chosen_violations": raw_chosen_violations,
        "shifted_chosen_violation_count": len(shifted_chosen_violations),
        "shifted_chosen_violations": shifted_chosen_violations,
        "raw_all_edge_violation_count": len(raw_all_edge_violations),
        "raw_all_edge_violations": raw_all_edge_violations,
        "shifted_all_edge_violation_count": len(shifted_all_edge_violations),
        "shifted_all_edge_violations": shifted_all_edge_violations,
        "shifted_all_edge_equality_count": shifted_equality_count,
        "multiplicative_pair_count": multiplicative_pair_count,
        "multiplicative_minimum_margin": multiplicative_minimum_margin,
        "multiplicative_equality_count": multiplicative_equality_count,
        "multiplicative_violation_count": len(multiplicative_violations),
        "multiplicative_violations": multiplicative_violations,
        "positive_multiplicative_pair_count": (
            positive_multiplicative_pair_count
        ),
        "positive_multiplicative_minimum_margin": (
            positive_multiplicative_minimum_margin
        ),
        "positive_multiplicative_equality_count": (
            positive_multiplicative_equality_count
        ),
        "positive_multiplicative_violation_count": len(
            positive_multiplicative_violations
        ),
        "positive_multiplicative_violations": (
            positive_multiplicative_violations
        ),
        "second_record_anchor_rank": second_record_anchor_rank,
        "second_record_anchor_successor": (
            second_record_anchor_rank + 1
            if second_record_anchor_rank is not None
            else None
        ),
        "second_record_anchor_tested_later_record_count": max(
            0, len(strict_records) - 2
        ),
        "second_record_anchor_violation_count": len(
            second_record_anchor_violations
        ),
        "second_record_anchor_violation_ranks": (
            second_record_anchor_violations
        ),
    }


def build_receipt(ranks: int, max_denominator: int) -> dict[str, Any]:
    if ranks < 100:
        raise ValueError("ranks must be at least 100")
    if max_denominator < 21:
        raise ValueError("max denominator must include 21")
    precision_bits = 2 * ranks + 192
    tables = interval_tables(ranks, precision_bits)
    status_counts: dict[str, int] = {}
    status_max_rank: dict[str, int] = {}
    alive_rows: list[dict[str, Any]] = []
    enumerated_count = 0
    for denominator in range(2, max_denominator + 1):
        for numerator in range(1, denominator):
            if gcd(numerator, denominator) != 1:
                continue
            enumerated_count += 1
            row = replay_target(
                numerator, denominator, ranks, *tables
            )
            status = str(row["orbit_status"])
            status_counts[status] = status_counts.get(status, 0) + 1
            if "status_rank" in row:
                status_max_rank[status] = max(
                    status_max_rank.get(status, 0), int(row["status_rank"])
                )
            if status == "alive_through_cap":
                alive_rows.append(row)

    if not alive_rows:
        raise AssertionError("empty alive cohort")
    by_target = {str(row["target"]): row for row in alive_rows}
    if "1/21" not in by_target:
        raise AssertionError("1/21 missing from alive cohort")

    control = json.loads(CONTROL_PATH.read_text())
    one_twenty_one = by_target["1/21"]
    twenty_one = json.loads(TWENTY_ONE_PATH.read_text())
    canonical_packed = base64.b64decode(
        twenty_one["packed_itinerary"]["data_base64"]
    )
    prefix_byte_count = (ranks + 7) // 8
    canonical_prefix = bytearray(canonical_packed[:prefix_byte_count])
    if ranks % 8:
        canonical_prefix[-1] &= (1 << (ranks % 8)) - 1
    if (
        one_twenty_one["packed_itinerary_sha256"]
        != hashlib.sha256(canonical_prefix).hexdigest()
    ):
        raise AssertionError("1/21 itinerary disagrees with canonical source")

    raw_chosen_examples = [
        {"target": row["target"], **edge}
        for row in alive_rows
        for edge in row["raw_chosen_violations"]
    ]
    shifted_chosen_examples = [
        {"target": row["target"], **edge}
        for row in alive_rows
        for edge in row["shifted_chosen_violations"]
    ]
    raw_all_edge_examples = [
        {"target": row["target"], **edge}
        for row in alive_rows
        for edge in row["raw_all_edge_violations"]
    ]
    shifted_all_edge_examples = [
        {"target": row["target"], **edge}
        for row in alive_rows
        for edge in row["shifted_all_edge_violations"]
    ]
    parentless_examples = [
        {"target": row["target"], "record_rank": rank}
        for row in alive_rows
        for rank in row["parentless_after_first_record_ranks"]
    ]
    multiplicative_examples = [
        {"target": row["target"], **violation}
        for row in alive_rows
        for violation in row["multiplicative_violations"]
    ]
    positive_multiplicative_examples = [
        {"target": row["target"], **violation}
        for row in alive_rows
        for violation in row["positive_multiplicative_violations"]
    ]
    pmrmh_support_counterexample = exact_pmrmh_support_counterexample()

    compact_rows = []
    for row in alive_rows:
        compact = dict(row)
        compact.pop("raw_chosen_violations")
        compact.pop("shifted_chosen_violations")
        compact.pop("raw_all_edge_violations")
        compact.pop("shifted_all_edge_violations")
        compact.pop("multiplicative_violations")
        compact.pop("positive_multiplicative_violations")
        compact_rows.append(compact)

    payload: dict[str, Any] = {
        "schema": "rational_weak_record_genealogy_census_v3",
        "parameters": {
            "ranks": ranks,
            "max_denominator": max_denominator,
            "precision_bits": precision_bits,
            "target_cohort": (
                "all reduced fractions 0<a/q<1 with 2<=q<=max_denominator"
            ),
        },
        "authority": {
            "script_ref": str(Path(__file__).resolve().relative_to(REPO_ROOT)),
            "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "analysis_ref": ANALYSIS_REF,
            "canonical_control_ref": CONTROL_REF,
            "canonical_control_payload_sha256": control[
                "canonical_payload_sha256"
            ],
            "canonical_twenty_one_ref": TWENTY_ONE_REF,
            "canonical_twenty_one_payload_sha256": twenty_one[
                "receipt_payload_sha256"
            ],
            "method": (
                "certified dyadic interval greedy replay, rigorous finite-"
                "rank tail bounds, exact target binary digits, exact divisor "
                "convolution, and exhaustive eligible weak-divisor edges"
            ),
            "floating_point_used": False,
            "python_version": platform.python_version(),
        },
        "cohort_summary": {
            "enumerated_reduced_target_count": enumerated_count,
            "orbit_status_counts": status_counts,
            "orbit_status_max_rank": status_max_rank,
            "alive_target_count": len(alive_rows),
        },
        "raw_normalized_candidate": {
            "id": "WGN",
            "statement": (
                "Q_n/(n+1) <= Q_r/(r+1) on a chosen weak-divisor edge"
            ),
            "chosen_edge_count": sum(
                int(row["chosen_edge_count"]) for row in alive_rows
            ),
            "violation_count": len(raw_chosen_examples),
            "target_violation_count": len({
                str(row["target"])
                for row in alive_rows
                if row["raw_chosen_violation_count"]
            }),
            "violation_examples": raw_chosen_examples[:200],
        },
        "shifted_normalized_candidate": {
            "id": "SWGN",
            "statement": (
                "(Q_n+1)/(n+1) <= (Q_r+1)/(r+1) on the largest eligible "
                "weak-divisor edge"
            ),
            "chosen_edge_count": sum(
                int(row["chosen_edge_count"]) for row in alive_rows
            ),
            "violation_count": len(shifted_chosen_examples),
            "target_violation_count": len({
                str(row["target"])
                for row in alive_rows
                if row["shifted_chosen_violation_count"]
            }),
            "violations": shifted_chosen_examples,
        },
        "shifted_edgewise_candidate": {
            "id": "SEWGN",
            "statement": (
                "(Q_n+1)/(n+1) <= (Q_r+1)/(r+1) on every eligible strict-"
                "record/weak-record successor-divisor edge"
            ),
            "eligible_edge_count": sum(
                int(row["all_eligible_edge_count"]) for row in alive_rows
            ),
            "raw_edge_violation_count": len(raw_all_edge_examples),
            "shifted_violation_count": len(shifted_all_edge_examples),
            "shifted_target_violation_count": len({
                str(example["target"])
                for example in shifted_all_edge_examples
            }),
            "shifted_equality_count": sum(
                int(row["shifted_all_edge_equality_count"])
                for row in alive_rows
            ),
            "raw_violation_examples": raw_all_edge_examples[:200],
            "shifted_violations": shifted_all_edge_examples,
        },
        "multiplicative_running_max_candidate": {
            "id": "MRMH",
            "definition": (
                "H(m)=1+max_{0<=k<m} Q_k, so a strict record n has "
                "H(n+1)=Q_n+1 and a weak record r has H(r+1)=Q_r+1"
            ),
            "statement": (
                "H(q*d) <= q*H(d) for every integer q>=2 and every tested "
                "horizon d with q*d at most the rank cap plus one"
            ),
            "implication": (
                "At a strict-record/weak-record successor-divisor edge, set "
                "d=r+1 and q*d=n+1; MRMH then gives SEWGN immediately."
            ),
            "direct_all_depth_consequence_if_proved": (
                "Fix any base d with H(d)>=2.  For N+1>d, take "
                "q=ceil((N+1)/d).  Monotonicity of H and PMRMH give "
                "Q_N+1<=H(q*d)<=q*H(d)=O(N).  Thus PMRMH for the actual "
                "1/21 carry is itself a global linear-defect producer and "
                "needs neither record genealogy nor a phase-lock theorem."
            ),
            "tested_pair_count": sum(
                int(row["multiplicative_pair_count"]) for row in alive_rows
            ),
            "minimum_integer_margin": min(
                int(row["multiplicative_minimum_margin"])
                for row in alive_rows
                if row["multiplicative_minimum_margin"] is not None
            ),
            "equality_count": sum(
                int(row["multiplicative_equality_count"])
                for row in alive_rows
            ),
            "violation_count": len(multiplicative_examples),
            "target_violation_count": len({
                str(example["target"])
                for example in multiplicative_examples
            }),
            "violations": multiplicative_examples,
            "unrestricted_falsifier_classification": (
                "Every unrestricted violation has H(d)=1, q=2, and margin "
                "-1; these occur before a positive weak-record plateau."
            ),
            "positive_base_subcandidate": {
                "id": "PMRMH",
                "hypothesis": "H(d)>=2",
                "statement": "H(q*d) <= q*H(d) for every tested q>=2",
                "implication": (
                    "Every weak record in the genealogy has positive defect, "
                    "so its successor d satisfies H(d)=Q_r+1>=2.  PMRMH "
                    "therefore implies SEWGN on every eligible edge."
                ),
                "direct_consequence": (
                    "At any one fixed positive base, PMRMH bounds every later "
                    "rank after rounding its horizon up to a multiple of that "
                    "base; the edge implication is not needed for this "
                    "stronger use."
                ),
                "tested_pair_count": sum(
                    int(row["positive_multiplicative_pair_count"])
                    for row in alive_rows
                ),
                "minimum_integer_margin": min(
                    int(row["positive_multiplicative_minimum_margin"])
                    for row in alive_rows
                    if row["positive_multiplicative_minimum_margin"] is not None
                ),
                "equality_count": sum(
                    int(row["positive_multiplicative_equality_count"])
                    for row in alive_rows
                ),
                "violation_count": len(positive_multiplicative_examples),
                "target_violation_count": len({
                    str(example["target"])
                    for example in positive_multiplicative_examples
                }),
                "violations": positive_multiplicative_examples,
            },
            "exact_representation_falsifier": pmrmh_support_counterexample,
            "selectivity_conclusion": (
                "The positive-base law is not a consequence of Boolean "
                "support, infinite support, exact representation, or exact "
                "greedy replay.  Its zero failures in the bounded rational "
                "cohort and on 1/21 therefore measure target-specific "
                "arithmetic rather than a universal tail identity."
            ),
        },
        "weak_parent_existence_control": {
            "target_with_parentless_later_record_count": len({
                str(example["target"]) for example in parentless_examples
            }),
            "parentless_later_record_count": len(parentless_examples),
            "examples": parentless_examples[:200],
            "interpretation": (
                "Parent existence is a logically separate clause; the "
                "density inequality is tested only when an edge exists."
            ),
        },
        "second_record_fixed_anchor_control": {
            "id": "SRFA",
            "statement": (
                "The successor of the second strict record divides every "
                "later strict-record successor."
            ),
            "eligible_target_count": sum(
                row["second_record_anchor_rank"] is not None
                for row in alive_rows
            ),
            "passing_target_count": sum(
                row["second_record_anchor_rank"] is not None
                and row["second_record_anchor_violation_count"] == 0
                for row in alive_rows
            ),
            "violating_target_count": sum(
                row["second_record_anchor_violation_count"] > 0
                for row in alive_rows
            ),
            "violation_count": sum(
                int(row["second_record_anchor_violation_count"])
                for row in alive_rows
            ),
            "violation_examples": [
                {
                    "target": row["target"],
                    "anchor_rank": row["second_record_anchor_rank"],
                    "anchor_successor": row[
                        "second_record_anchor_successor"
                    ],
                    "violation_ranks": row[
                        "second_record_anchor_violation_ranks"
                    ],
                }
                for row in alive_rows
                if row["second_record_anchor_violation_count"] > 0
            ][:200],
            "one_twenty_one": {
                "anchor_rank": one_twenty_one[
                    "second_record_anchor_rank"
                ],
                "anchor_successor": one_twenty_one[
                    "second_record_anchor_successor"
                ],
                "tested_later_record_count": one_twenty_one[
                    "second_record_anchor_tested_later_record_count"
                ],
                "violation_count": one_twenty_one[
                    "second_record_anchor_violation_count"
                ],
            },
            "interpretation": (
                "This preselected fixed-anchor law is stronger than merely "
                "having some weak divisor parent and is tested cross-target "
                "to measure source specificity."
            ),
        },
        "one_twenty_one_control": one_twenty_one,
        "alive_target_rows": compact_rows,
        "finite_interpretation": (
            "The +1 shift is selected before seeing the census because Q+1 "
            "is the native normalized carry in the checked membership "
            "theorems.  Zero finite violations would open a broader survivor-"
            "genealogy mechanism; any violation is an exact falsifier."
        ),
        "nonclaims": [
            "The finite alive cohort does not prove survival beyond the cap.",
            "The census does not prove SWGN or SEWGN at all depths.",
            "The census does not prove the multiplicative envelope MRMH.",
            "The census does not prove weak-parent existence at all depths.",
            "The census does not prove the second-record fixed-anchor law.",
            "The census does not prove 1/21 membership or decide Erdos 257.",
        ],
    }
    payload["canonical_payload_sha256"] = canonical_payload_sha256(payload)
    return payload


def resolve_path(value: str | None) -> Path:
    if value is None:
        return DEFAULT_RECEIPT
    path = Path(value)
    return path if path.is_absolute() else REPO_ROOT / path


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ranks", type=int, default=DEFAULT_RANKS)
    parser.add_argument(
        "--max-denominator", type=int, default=DEFAULT_MAX_DENOMINATOR
    )
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--write", nargs="?", const=None, metavar="PATH")
    action.add_argument("--check", nargs="?", const=None, metavar="PATH")
    args = parser.parse_args()
    payload = build_receipt(args.ranks, args.max_denominator)
    rendered = canonical_json(payload)
    argv = __import__("sys").argv
    if args.write is not None or "--write" in argv:
        path = resolve_path(args.write)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(rendered)
        print(canonical_json({
            "status": "written",
            "path": str(path.relative_to(REPO_ROOT)),
            "canonical_payload_sha256": payload[
                "canonical_payload_sha256"
            ],
        }), end="")
        return 0
    if args.check is not None or "--check" in argv:
        path = resolve_path(args.check)
        if path.read_text() != rendered:
            raise AssertionError(f"receipt drift: {path}")
        print(canonical_json({
            "status": "matched",
            "path": str(path.relative_to(REPO_ROOT)),
            "canonical_payload_sha256": payload[
                "canonical_payload_sha256"
            ],
        }), end="")
        return 0
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
