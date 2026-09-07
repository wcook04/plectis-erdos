#!/usr/bin/env python3
"""Test weak-record divisor genealogy from the persisted 1/21 itinerary.

This is the first downstream consumer of the canonical packed itinerary.  It
reconstructs selected-divisor loads and the denominator-21 binary carry defect
without replaying the expensive quotient recurrence.
"""

from __future__ import annotations

import argparse
import base64
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import platform
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
SOURCE_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "twenty_one_computational_structure_receipt.json"
)
SOURCE_PATH = REPO_ROOT / SOURCE_REF
CONTROL_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "rational_record_genealogy_control_receipt.json"
)
CONTROL_PATH = REPO_ROOT / CONTROL_REF
RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "twenty_one_weak_record_genealogy_receipt.json"
)
DEFAULT_RECEIPT = REPO_ROOT / RECEIPT_REF
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/"
    "TwentyOneRecordAncestorInheritance.md"
)


def canonical_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def canonical_payload_sha256(payload: dict[str, Any]) -> str:
    encoded = json.dumps(
        payload, separators=(",", ":"), sort_keys=True
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def validate_payload_digest(payload: dict[str, Any], field: str) -> None:
    claimed = payload[field]
    digest_payload = dict(payload)
    digest_payload.pop(field)
    computed = canonical_payload_sha256(digest_payload)
    if claimed != computed:
        raise AssertionError(
            f"payload digest mismatch: claimed={claimed} computed={computed}"
        )


def target_bit(rank: int) -> int:
    return int(rank % 6 in (5, 0))


def build_receipt(source_path: Path = SOURCE_PATH) -> dict[str, Any]:
    source = json.loads(source_path.read_text())
    validate_payload_digest(source, "receipt_payload_sha256")
    if source["schema"] != "twenty_one_computational_structure_lab_v1":
        raise AssertionError("packed-itinerary source is not schema v1")
    packed_metadata = source["packed_itinerary"]
    packed = base64.b64decode(packed_metadata["data_base64"])
    if len(packed) != int(packed_metadata["byte_length"]):
        raise AssertionError("packed-itinerary byte length mismatch")
    packed_sha256 = hashlib.sha256(packed).hexdigest()
    if packed_sha256 != packed_metadata["sha256"]:
        raise AssertionError("packed-itinerary digest mismatch")

    ranks = int(source["parameters"]["ranks"])
    bits = bytearray(ranks + 1)
    for rank in range(1, ranks + 1):
        bits[rank] = (
            packed[(rank - 1) // 8] >> ((rank - 1) % 8)
        ) & 1
    if sum(bits) != int(source["selected_count"]):
        raise AssertionError("decoded selected count mismatch")

    selected_divisor_counts = [0] * (ranks + 1)
    for divisor in range(1, ranks + 1):
        if not bits[divisor]:
            continue
        for multiple in range(divisor, ranks + 1, divisor):
            selected_divisor_counts[multiple] += 1

    defects = [0] * (ranks + 1)
    strict_record_ranks: list[int] = []
    weak_record_ranks: list[int] = []
    strict_source_by_defect: dict[int, int] = {}
    maximum_defect = 0
    running_max_plus_one = [1] * (ranks + 2)
    for rank in range(1, ranks + 1):
        defects[rank] = (
            2 * defects[rank - 1]
            + target_bit(rank)
            - selected_divisor_counts[rank]
        )
        if defects[rank] < 0:
            raise AssertionError(f"negative reconstructed defect at rank {rank}")
        if defects[rank] > maximum_defect:
            maximum_defect = defects[rank]
            strict_record_ranks.append(rank)
            weak_record_ranks.append(rank)
            strict_source_by_defect[maximum_defect] = rank
        elif defects[rank] == maximum_defect and maximum_defect > 0:
            weak_record_ranks.append(rank)
        running_max_plus_one[rank + 1] = maximum_defect + 1

    expected_strict_rows = [
        (int(row["rank"]), int(row["defect"]))
        for row in source["strict_record_rows"]
    ]
    reconstructed_strict_rows = [
        (rank, defects[rank]) for rank in strict_record_ranks
    ]
    if reconstructed_strict_rows != expected_strict_rows:
        raise AssertionError("strict-record reconstruction mismatch")

    rows: list[dict[str, Any]] = []
    for rank in strict_record_ranks:
        eligible = [
            weak_rank
            for weak_rank in weak_record_ranks
            if weak_rank < rank and (rank + 1) % (weak_rank + 1) == 0
        ]
        eligible_edge_rows = []
        for weak_rank in eligible:
            weak_defect = defects[weak_rank]
            quotient = (rank + 1) // (weak_rank + 1)
            eligible_edge_rows.append(
                {
                    "weak_parent_rank": weak_rank,
                    "weak_parent_defect": weak_defect,
                    "weak_parent_successor": weak_rank + 1,
                    "successor_quotient": quotient,
                    "plateau_source_strict_record_rank": (
                        strict_source_by_defect[weak_defect]
                    ),
                    "normalized_margin": (
                        quotient * weak_defect - defects[rank]
                    ),
                }
            )
        parent_rank = max(eligible, default=None)
        parent_defect = defects[parent_rank] if parent_rank is not None else None
        parent_plateau_source = (
            strict_source_by_defect[parent_defect]
            if parent_defect is not None
            else None
        )
        parent_successor_quotient = (
            (rank + 1) // (parent_rank + 1)
            if parent_rank is not None
            else None
        )
        rows.append(
            {
                "strict_record_rank": rank,
                "strict_record_defect": defects[rank],
                "weak_parent_rank": parent_rank,
                "weak_parent_defect": parent_defect,
                "weak_parent_successor": (
                    parent_rank + 1 if parent_rank is not None else None
                ),
                "weak_parent_successor_quotient": (
                    parent_successor_quotient
                ),
                "parent_plateau_source_strict_record_rank": (
                    parent_plateau_source
                ),
                "plateau_source_successor_at_most_half_child": (
                    parent_plateau_source + 1 <= (rank + 1) // 2
                    if parent_plateau_source is not None
                    else None
                ),
                "wgp4_margin": (
                    4 * parent_defect - defects[rank]
                    if parent_defect is not None
                    else None
                ),
                "normalized_weak_parent_margin": (
                    parent_successor_quotient * parent_defect - defects[rank]
                    if parent_successor_quotient is not None
                    and parent_defect is not None
                    else None
                ),
                "eligible_weak_parent_edges": eligible_edge_rows,
            }
        )

    parentless_after_seed = [
        row
        for row in rows
        if int(row["strict_record_rank"]) > 6 and row["weak_parent_rank"] is None
    ]
    violations = [
        row
        for row in rows
        if row["wgp4_margin"] is not None and int(row["wgp4_margin"]) < 0
    ]
    normalized_violations = [
        row
        for row in rows
        if row["normalized_weak_parent_margin"] is not None
        and int(row["normalized_weak_parent_margin"]) < 0
    ]
    all_eligible_edge_rows = [
        {
            "strict_record_rank": int(row["strict_record_rank"]),
            "strict_record_defect": int(row["strict_record_defect"]),
            **edge,
        }
        for row in rows
        for edge in row["eligible_weak_parent_edges"]
    ]
    edgewise_normalized_violations = [
        edge
        for edge in all_eligible_edge_rows
        if int(edge["normalized_margin"]) < 0
    ]
    half_index_failures = [
        row
        for row in rows
        if row["plateau_source_successor_at_most_half_child"] is False
    ]
    if (
        parentless_after_seed
        or violations
        or normalized_violations
        or edgewise_normalized_violations
        or half_index_failures
    ):
        raise AssertionError("weak-record polynomial genealogy candidate failed")

    parented_rows = [row for row in rows if row["weak_parent_rank"] is not None]
    adjacent_strict_record_density_rows = []
    for previous, current in zip(rows, rows[1:]):
        previous_rank = int(previous["strict_record_rank"])
        previous_defect = int(previous["strict_record_defect"])
        current_rank = int(current["strict_record_rank"])
        current_defect = int(current["strict_record_defect"])
        adjacent_strict_record_density_rows.append(
            {
                "previous_record_rank": previous_rank,
                "previous_record_defect": previous_defect,
                "current_record_rank": current_rank,
                "current_record_defect": current_defect,
                "density_monotonicity_integer_margin": (
                    previous_defect * (current_rank + 1)
                    - current_defect * (previous_rank + 1)
                ),
            }
        )
    global_density_monotonicity_violations = [
        row
        for row in adjacent_strict_record_density_rows
        if int(row["density_monotonicity_integer_margin"]) < 0
    ]
    if not global_density_monotonicity_violations:
        raise AssertionError(
            "expected global record-density monotonicity counterexample"
        )
    if int(global_density_monotonicity_violations[0]["current_record_rank"]) != 839:
        raise AssertionError("unexpected first global density counterexample")
    sharp_row = max(
        parented_rows,
        key=lambda row: (
            Fraction(
                int(row["strict_record_defect"]),
                int(row["weak_parent_defect"]),
            ),
            -int(row["strict_record_rank"]),
        ),
    )
    sharp_ratio = Fraction(
        int(sharp_row["strict_record_defect"]),
        int(sharp_row["weak_parent_defect"]),
    )
    if sharp_ratio != Fraction(7, 2) or sharp_row["strict_record_rank"] != 779:
        raise AssertionError("unexpected sharp weak-parent ratio")

    multiplicative_pair_count = 0
    multiplicative_equality_count = 0
    multiplicative_minimum_margin: int | None = None
    multiplicative_violations: list[dict[str, int]] = []
    positive_multiplicative_pair_count = 0
    positive_multiplicative_equality_count = 0
    positive_multiplicative_minimum_margin: int | None = None
    positive_multiplicative_violations: list[dict[str, int]] = []
    doubling_pair_count = 0
    doubling_equality_count = 0
    doubling_minimum_margin: int | None = None
    doubling_minimum_margin_examples: list[dict[str, int]] = []
    doubling_violations: list[dict[str, int]] = []
    positive_doubling_pair_count = 0
    positive_doubling_equality_count = 0
    positive_doubling_minimum_margin: int | None = None
    positive_doubling_minimum_margin_examples: list[dict[str, int]] = []
    positive_doubling_violations: list[dict[str, int]] = []
    for divisor in range(1, (ranks + 1) // 2 + 1):
        divisor_height = running_max_plus_one[divisor]
        for multiple in range(2 * divisor, ranks + 2, divisor):
            quotient = multiple // divisor
            margin = (
                quotient * divisor_height
                - running_max_plus_one[multiple]
            )
            pair = {
                "divisor_horizon": divisor,
                "multiple_horizon": multiple,
                "quotient": quotient,
                "divisor_height": divisor_height,
                "multiple_height": running_max_plus_one[multiple],
                "margin": margin,
            }
            multiplicative_pair_count += 1
            if (
                multiplicative_minimum_margin is None
                or margin < multiplicative_minimum_margin
            ):
                multiplicative_minimum_margin = margin
            if margin == 0:
                multiplicative_equality_count += 1
            if margin < 0:
                multiplicative_violations.append(pair)
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
                    positive_multiplicative_violations.append(pair)
            if quotient == 2:
                doubling_pair_count += 1
                if (
                    doubling_minimum_margin is None
                    or margin < doubling_minimum_margin
                ):
                    doubling_minimum_margin = margin
                    doubling_minimum_margin_examples = [pair]
                elif (
                    margin == doubling_minimum_margin
                    and len(doubling_minimum_margin_examples) < 200
                ):
                    doubling_minimum_margin_examples.append(pair)
                if margin == 0:
                    doubling_equality_count += 1
                if margin < 0:
                    doubling_violations.append(pair)
                if divisor_height >= 2:
                    positive_doubling_pair_count += 1
                    if (
                        positive_doubling_minimum_margin is None
                        or margin < positive_doubling_minimum_margin
                    ):
                        positive_doubling_minimum_margin = margin
                        positive_doubling_minimum_margin_examples = [pair]
                    elif (
                        margin == positive_doubling_minimum_margin
                        and len(positive_doubling_minimum_margin_examples) < 200
                    ):
                        positive_doubling_minimum_margin_examples.append(pair)
                    if margin == 0:
                        positive_doubling_equality_count += 1
                    if margin < 0:
                        positive_doubling_violations.append(pair)

    dyadic_anchor_rows: list[dict[str, int]] = []
    dyadic_horizon = 20
    while 2 * dyadic_horizon <= ranks + 1:
        base_height = running_max_plus_one[dyadic_horizon]
        doubled_height = running_max_plus_one[2 * dyadic_horizon]
        dyadic_anchor_rows.append({
            "base_horizon": dyadic_horizon,
            "base_height": base_height,
            "doubled_horizon": 2 * dyadic_horizon,
            "doubled_height": doubled_height,
            "integer_margin": 2 * base_height - doubled_height,
        })
        dyadic_horizon *= 2

    plateau_starts = [1] + [rank + 1 for rank in strict_record_ranks]
    plateau_heights = [1] + [defects[rank] + 1 for rank in strict_record_ranks]
    plateaus = [
        {
            "start": start,
            "end": (
                plateau_starts[index + 1] - 1
                if index + 1 < len(plateau_starts)
                else ranks + 1
            ),
            "height": plateau_heights[index],
        }
        for index, start in enumerate(plateau_starts)
    ]

    doubling_plateau_start_of = [1] * (ranks + 2)
    for plateau in plateaus:
        fill_start = int(plateau["start"])
        fill_end = min(int(plateau["end"]), ranks + 1)
        if fill_end >= fill_start:
            doubling_plateau_start_of[fill_start : fill_end + 1] = [fill_start] * (
                fill_end - fill_start + 1
            )

    doubling_plateau_min_margin: dict[int, int] = {}
    doubling_plateau_argmin: dict[int, int] = {}
    for divisor in range(1, (ranks + 1) // 2 + 1):
        multiple = 2 * divisor
        margin = (
            2 * running_max_plus_one[divisor]
            - running_max_plus_one[multiple]
        )
        owner = doubling_plateau_start_of[multiple]
        current = doubling_plateau_min_margin.get(owner)
        if current is None or margin < current:
            doubling_plateau_min_margin[owner] = margin
            doubling_plateau_argmin[owner] = divisor

    doubling_plateau_reduction_rows: list[dict[str, Any]] = []
    doubling_plateau_reduction_mismatches: list[dict[str, int]] = []
    for index, plateau in enumerate(plateaus):
        start = int(plateau["start"])
        half = (start + 1) // 2
        representative_margin = (
            2 * running_max_plus_one[half]
            - running_max_plus_one[min(2 * half, ranks + 1)]
        )
        row = {
            "plateau_start": start,
            "record_rank": start - 1 if start > 1 else None,
            "plateau_height": int(plateau["height"]),
            "half_horizon": half,
            "half_height": running_max_plus_one[half],
            "integer_margin": representative_margin,
        }
        empirical_minimum = doubling_plateau_min_margin.get(start)
        empirical_argmin = doubling_plateau_argmin.get(start)
        if empirical_minimum != representative_margin:
            doubling_plateau_reduction_mismatches.append(
                {
                    "plateau_start": start,
                    "representative_margin": representative_margin,
                    "empirical_minimum": empirical_minimum,
                    "empirical_argmin": empirical_argmin,
                }
            )
        doubling_plateau_reduction_rows.append(row)

    doubling_plateau_reduction_violations = [
        row
        for row in doubling_plateau_reduction_rows
        if int(row["integer_margin"]) < 0
    ]
    doubling_plateau_positive_rows = [
        row
        for row in doubling_plateau_reduction_rows
        if int(row["integer_margin"]) >= 1
    ]
    doubling_plateau_min_positive_margin = min(
        (int(row["integer_margin"]) for row in doubling_plateau_positive_rows),
        default=None,
    )
    doubling_plateau_tight_positive_rows = [
        row
        for row in doubling_plateau_positive_rows
        if int(row["integer_margin"])
        == doubling_plateau_min_positive_margin
    ]

    record_edge_damping_rows: list[dict[str, Any]] = []
    previous_record_rank: int | None = None
    for rank in strict_record_ranks:
        record_edge_damping_rows.append(
            {
                "record_rank": rank,
                "defect": defects[rank],
                "selected_divisor_load": selected_divisor_counts[rank],
                "take_bit": target_bit(rank),
                "damping_delta": (
                    1
                    + selected_divisor_counts[rank]
                    - target_bit(rank)
                ),
                "previous_record_rank": previous_record_rank,
            }
        )
        previous_record_rank = rank

    zero_damping_edges = [
        row
        for row in record_edge_damping_rows
        if int(row["damping_delta"]) == 0
    ]
    zero_damping_all_unselected = all(
        bits[int(row["record_rank"])] == 0 for row in zero_damping_edges
    )

    # Pure chain arithmetic: from the halving anchor, apply the exact
    # consecutive-record edge bound W <- 2W + 2 - delta and test whether the
    # resulting worst case still respects each plateau-start row.
    chain_arithmetic_rows: list[dict[str, int]] = []
    for index in range(1, len(plateau_starts)):
        start = plateau_starts[index]
        height = plateau_heights[index]
        half = (start + 1) // 2
        anchor_index = -1
        for j, record_rank in enumerate(strict_record_ranks):
            if record_rank + 1 <= half:
                anchor_index = j
            else:
                break
        if anchor_index < 0:
            worst = 0
            anchor_height = 1
        else:
            anchor_rank = strict_record_ranks[anchor_index]
            worst = defects[anchor_rank]
            anchor_height = defects[anchor_rank] + 1
            for j in range(anchor_index + 1, index):
                record_rank = strict_record_ranks[j]
                worst = (
                    2 * worst
                    + 2
                    - (
                        1
                        + selected_divisor_counts[record_rank]
                        - target_bit(record_rank)
                    )
                )
        bound_margin = 2 * anchor_height - (worst + 1)
        chain_arithmetic_rows.append(
            {
                "plateau_start": start,
                "plateau_height": height,
                "anchor_height": anchor_height,
                "chain_worst_plus_one": worst + 1,
                "chain_bound_margin": bound_margin,
                "chain_edge_count": max(index - 1 - anchor_index, 0),
            }
        )
    chain_arithmetic_proved_rows = [
        row for row in chain_arithmetic_rows if row["chain_bound_margin"] >= 0
    ]
    chain_arithmetic_failed_rows = [
        row
        for row in chain_arithmetic_rows
        if row["chain_bound_margin"] < 0
    ]

    def subadditivity_violations(
        minimum_height: int,
    ) -> list[dict[str, int]]:
        found: list[dict[str, int]] = []
        for left_index, left in enumerate(plateaus):
            if int(left["height"]) < minimum_height:
                continue
            for right in plateaus[left_index:]:
                if int(right["height"]) < minimum_height:
                    continue
                total = min(
                    int(left["end"]) + int(right["end"]), ranks + 1
                )
                if total < int(left["start"]) + int(right["start"]):
                    continue
                left_horizon = max(
                    int(left["start"]), total - int(right["end"])
                )
                right_horizon = total - left_horizon
                margin = (
                    int(left["height"])
                    + int(right["height"])
                    - running_max_plus_one[total]
                )
                if margin < 0:
                    found.append({
                        "left_horizon": left_horizon,
                        "left_height": int(left["height"]),
                        "right_horizon": right_horizon,
                        "right_height": int(right["height"]),
                        "sum_horizon": total,
                        "sum_height": running_max_plus_one[total],
                        "integer_margin": margin,
                    })
        return found

    def first_subadditivity_violation(
        minimum_height: int,
    ) -> dict[str, int] | None:
        candidates: list[dict[str, int]] = []
        for total, total_height in zip(
            plateau_starts[1:], plateau_heights[1:]
        ):
            for left_index, left in enumerate(plateaus):
                if int(left["height"]) < minimum_height:
                    continue
                for right in plateaus[left_index:]:
                    if int(right["height"]) < minimum_height:
                        continue
                    if int(left["height"]) + int(right["height"]) >= total_height:
                        continue
                    left_horizon = max(
                        int(left["start"]), total - int(right["end"])
                    )
                    if left_horizon > int(left["end"]):
                        continue
                    right_horizon = total - left_horizon
                    if not (
                        int(right["start"])
                        <= right_horizon
                        <= int(right["end"])
                    ):
                        continue
                    candidates.append({
                        "left_horizon": left_horizon,
                        "left_height": int(left["height"]),
                        "right_horizon": right_horizon,
                        "right_height": int(right["height"]),
                        "sum_horizon": total,
                        "sum_height": total_height,
                        "integer_margin": (
                            int(left["height"])
                            + int(right["height"])
                            - total_height
                        ),
                    })
            if candidates:
                return min(
                    candidates,
                    key=lambda row: (
                        int(row["sum_horizon"]),
                        int(row["left_horizon"]),
                    ),
                )
        return None

    subadditive_violations = subadditivity_violations(1)
    positive_subadditive_violations = subadditivity_violations(2)
    first_subadditive_violation = first_subadditivity_violation(1)
    first_positive_subadditive_violation = first_subadditivity_violation(2)
    if (
        doubling_violations
        or positive_doubling_violations
        or not subadditive_violations
        or not positive_subadditive_violations
    ):
        raise AssertionError("unexpected doubling/subadditivity classification")

    fixed_anchor_rank = 19
    fixed_anchor_successor = fixed_anchor_rank + 1
    if strict_record_ranks[:2] != [6, fixed_anchor_rank]:
        raise AssertionError("unexpected fixed-anchor seed records")
    if defects[fixed_anchor_rank] != 2:
        raise AssertionError("unexpected fixed-anchor defect")
    fixed_anchor_later_records = [
        rank for rank in strict_record_ranks if rank > fixed_anchor_rank
    ]
    fixed_anchor_phase_violations = [
        {
            "strict_record_rank": rank,
            "strict_record_defect": defects[rank],
            "successor": rank + 1,
            "successor_residue_mod_anchor": (
                (rank + 1) % fixed_anchor_successor
            ),
        }
        for rank in fixed_anchor_later_records
        if (rank + 1) % fixed_anchor_successor != 0
    ]

    control = json.loads(CONTROL_PATH.read_text())
    validate_payload_digest(control, "canonical_payload_sha256")
    source_display = (
        str(source_path.relative_to(REPO_ROOT))
        if source_path.is_relative_to(REPO_ROOT)
        else str(source_path)
    )
    payload: dict[str, Any] = {
        "schema": "twenty_one_weak_record_genealogy_v2",
        "parameters": {
            "ranks": ranks,
            "seed_record_rank": 6,
            "multiplicative_defect_factor": 4,
        },
        "authority": {
            "script_ref": str(Path(__file__).resolve().relative_to(REPO_ROOT)),
            "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "analysis_ref": ANALYSIS_REF,
            "packed_itinerary_source_ref": source_display,
            "packed_itinerary_source_payload_sha256": source[
                "receipt_payload_sha256"
            ],
            "packed_itinerary_sha256": packed_sha256,
            "cross_target_control_ref": CONTROL_REF,
            "cross_target_control_payload_sha256": control[
                "canonical_payload_sha256"
            ],
            "method": (
                "decode persisted itinerary, reconstruct selected-divisor "
                "convolution and carry defect, then mine weak running-maximum "
                "divisor parents"
            ),
            "quotient_replay_used": False,
            "floating_point_used": False,
            "python_version": platform.python_version(),
        },
        "selected_count": sum(bits),
        "strict_record_count": len(strict_record_ranks),
        "weak_record_count": len(weak_record_ranks),
        "record_rows": rows,
        "weak_record_genealogy_candidate": {
            "id": "WGP4",
            "statement": (
                "Every strict record n>6 has an earlier weak record r with "
                "r+1 dividing n+1 and Q_n <= 4*Q_r."
            ),
            "weak_record_definition": (
                "Q_r equals the running maximum max_{k<=r} Q_k; equality "
                "with an earlier strict record is allowed"
            ),
            "finite_status": f"verified_on_the_packed_{ranks}_rank_orbit",
            "tested_nonseed_record_count": len(rows) - 1,
            "parentless_after_seed_violation_count": len(parentless_after_seed),
            "parentless_after_seed_violations": parentless_after_seed,
            "factor_four_violation_count": len(violations),
            "factor_four_violations": violations,
            "sharp_finite_ratio": {
                "numerator": sharp_ratio.numerator,
                "denominator": sharp_ratio.denominator,
                "record_rank": int(sharp_row["strict_record_rank"]),
                "weak_parent_rank": int(sharp_row["weak_parent_rank"]),
                "plateau_source_strict_record_rank": int(
                    sharp_row["parent_plateau_source_strict_record_rank"]
                ),
            },
            "all_depth_consequence_if_proved": (
                "A weak parent r has Q_r=Q_s for the strict record s that "
                "created its plateau.  Since s+1<=r+1<=(n+1)/2, recursive "
                "WGP4 descent gives Q_n=O((n+1)^2) at strict records and "
                "therefore everywhere.  The Lean-checked subexponential-"
                "defect theorem then yields 1/21 membership and infinite "
                "support."
            ),
            "falsifiers": [
                "a strict record above rank six with no weak divisor parent",
                "a weak-parent edge with Q_child > 4*Q_parent",
            ],
        },
        "normalized_weak_record_genealogy_candidate": {
            "id": "WGN",
            "statement": (
                "For every strict record n>6, the weak divisor parent r "
                "may be chosen so Q_n/(n+1) <= Q_r/(r+1), equivalently "
                "Q_n <= ((n+1)/(r+1))*Q_r."
            ),
            "finite_status": f"verified_on_the_packed_{ranks}_rank_orbit",
            "tested_nonseed_record_count": len(rows) - 1,
            "violation_count": len(normalized_violations),
            "violations": normalized_violations,
            "minimum_integer_margin": min(
                int(row["normalized_weak_parent_margin"])
                for row in parented_rows
            ),
            "equality_record_ranks": [
                int(row["strict_record_rank"])
                for row in parented_rows
                if int(row["normalized_weak_parent_margin"]) == 0
            ],
            "all_depth_consequence_if_proved": (
                "If weak parent r lies on the plateau created by strict "
                "record s, then Q_r=Q_s and s<=r.  WGN gives "
                "Q_n/(n+1)<=Q_r/(r+1)<=Q_s/(s+1).  Recursive descent to "
                "the seed (6,1) yields Q_n<= (n+1)/7 at every strict "
                "record and hence Q_N<= (N+1)/7 everywhere.  This linear "
                "bound is subexponential and proves 1/21 membership with "
                "infinite support via the checked Lean consumer."
            ),
            "proof_advantage": (
                "WGN replaces the arbitrary factor four by the exact "
                "successor quotient, so its invariant is normalized defect "
                "density rather than absolute defect growth."
            ),
            "falsifiers": [
                "a strict record above rank six with no weak divisor parent",
                "a weak-parent edge where normalized defect density increases",
            ],
        },
        "edgewise_normalized_weak_record_candidate": {
            "id": "EWGN",
            "statement": (
                "For every strict record n and every earlier weak record r "
                "with r+1 dividing n+1, Q_n/(n+1) <= Q_r/(r+1)."
            ),
            "finite_status": "verified_on_every_eligible_edge_in_the_packed_orbit",
            "eligible_edge_count": len(all_eligible_edge_rows),
            "strict_records_with_an_eligible_edge": sum(
                bool(row["eligible_weak_parent_edges"]) for row in rows
            ),
            "violation_count": len(edgewise_normalized_violations),
            "violations": edgewise_normalized_violations,
            "minimum_integer_margin": min(
                int(edge["normalized_margin"])
                for edge in all_eligible_edge_rows
            ),
            "equality_edges": [
                edge
                for edge in all_eligible_edge_rows
                if int(edge["normalized_margin"]) == 0
            ],
            "proof_decomposition": {
                "existence_clause": (
                    "Every strict record after the seed has at least one "
                    "earlier weak-record successor dividing its successor."
                ),
                "edge_clause": (
                    "Normalized defect density does not increase along any "
                    "eligible weak-divisor edge."
                ),
                "consequence": (
                    "The two clauses imply WGN without a parent-selection "
                    "rule and hence the explicit linear defect bound."
                ),
            },
            "all_depth_consequence_if_proved": (
                "Together with weak-divisor-parent existence after rank six, "
                "EWGN recursively bounds Q_n/(n+1) by Q_6/7=1/7 and proves "
                "Q_N<=(N+1)/7, hence 1/21 membership and infinite support."
            ),
            "falsifier": (
                "an eligible strict-record/weak-record divisor edge on which "
                "normalized defect density increases"
            ),
        },
        "global_record_density_monotonicity_control": {
            "statement": (
                "Normalized defect Q_n/(n+1) is nonincreasing along all "
                "successive strict records, without a divisor condition."
            ),
            "status": "falsified_on_actual_denominator_21_orbit",
            "tested_adjacent_record_edge_count": len(
                adjacent_strict_record_density_rows
            ),
            "violation_count": len(global_density_monotonicity_violations),
            "violations": global_density_monotonicity_violations,
            "all_adjacent_rows": adjacent_strict_record_density_rows,
            "first_witness": global_density_monotonicity_violations[0],
            "consequence": (
                "EWGN is not inherited from a global record-density trend; "
                "the weak-record successor divisibility condition is "
                "essential to the surviving finite mechanism."
            ),
        },
        "multiplicative_running_max_candidate": {
            "definition": (
                "H(m)=1+max_{0<=k<m} Q_k; at strict n, H(n+1)=Q_n+1, "
                "and at weak r, H(r+1)=Q_r+1"
            ),
            "unrestricted": {
                "id": "MRMH",
                "statement": "H(q*d) <= q*H(d) for every q>=2",
                "tested_pair_count": multiplicative_pair_count,
                "minimum_integer_margin": multiplicative_minimum_margin,
                "equality_count": multiplicative_equality_count,
                "violation_count": len(multiplicative_violations),
                "violations": multiplicative_violations,
            },
            "positive_base": {
                "id": "PMRMH",
                "hypothesis": "H(d)>=2",
                "statement": "H(q*d) <= q*H(d) for every q>=2",
                "tested_pair_count": positive_multiplicative_pair_count,
                "minimum_integer_margin": (
                    positive_multiplicative_minimum_margin
                ),
                "equality_count": positive_multiplicative_equality_count,
                "violation_count": len(positive_multiplicative_violations),
                "violations": positive_multiplicative_violations,
                "edge_implication": (
                    "A positive weak-record parent has H(r+1)=Q_r+1>=2. "
                    "With d=r+1 and q*d=n+1, PMRMH gives the shifted "
                    "edge law (Q_n+1)/(n+1)<=(Q_r+1)/(r+1)."
                ),
                "direct_all_depth_consequence_if_proved": (
                    "For the actual 1/21 carry, fix d=20 where H(20)=3. "
                    "Given N>=20, let q=ceil((N+1)/20).  Then "
                    "Q_N+1<=H(20*q)<=3*q<=3*(N+20)/20.  This global "
                    "linear bound is subexponential and reaches the checked "
                    "membership and infinite-support consumers without any "
                    "record-parent or phase-lock hypothesis."
                ),
            },
            "finite_status": f"tested_on_every_multiplicative_horizon_pair_through_{ranks + 1}",
        },
        "doubling_running_max_candidate": {
            "id": "DRMH",
            "statement": "H(2*d) <= 2*H(d)",
            "all_base": {
                "tested_pair_count": doubling_pair_count,
                "minimum_integer_margin": doubling_minimum_margin,
                "minimum_margin_examples": doubling_minimum_margin_examples,
                "equality_count": doubling_equality_count,
                "violation_count": len(doubling_violations),
                "violations": doubling_violations,
            },
            "positive_base": {
                "hypothesis": "H(d)>=2",
                "tested_pair_count": positive_doubling_pair_count,
                "minimum_integer_margin": positive_doubling_minimum_margin,
                "minimum_margin_examples": (
                    positive_doubling_minimum_margin_examples
                ),
                "equality_count": positive_doubling_equality_count,
                "violation_count": len(positive_doubling_violations),
                "violations": positive_doubling_violations,
            },
            "dyadic_anchor_20_rows": dyadic_anchor_rows,
            "direct_all_depth_consequence_if_proved": (
                "Starting from H(20)=3, iteration gives "
                "H(20*2^j)<=3*2^j.  Every horizon can be rounded upward "
                "to the next 20*2^j, giving a global linear defect bound "
                "and hence 1/21 membership with infinite support.  No "
                "quotient q other than two is needed."
            ),
            "finite_status": f"tested_at_every_doubling_pair_through_{ranks + 1}",
        },
        "doubling_plateau_reduction_candidate": {
            "statement": (
                "(DRMH) for every d is equivalent to (DRMH) at the "
                "plateau-start halves d=ceil(s/2): on the d-range that "
                "maps into one plateau [s,s'), H(2d) is constant while "
                "H(d) is nondecreasing, so the margin 2H(d)-H(2d) is "
                "minimized at d=ceil(s/2)."
            ),
            "reduction_row_count": len(doubling_plateau_reduction_rows),
            "rows": doubling_plateau_reduction_rows,
            "lossless_representative_mismatch_count": len(
                doubling_plateau_reduction_mismatches
            ),
            "lossless_representative_mismatches": (
                doubling_plateau_reduction_mismatches
            ),
            "violation_count": len(doubling_plateau_reduction_violations),
            "violations": doubling_plateau_reduction_violations,
            "minimum_positive_integer_margin": (
                doubling_plateau_min_positive_margin
            ),
            "tight_positive_rows": doubling_plateau_tight_positive_rows,
            "later_record_successor_residues_mod_20": sorted({
                int(row["plateau_start"]) % 20
                for row in doubling_plateau_reduction_rows
                if int(row["record_rank"] or 0) > 19
            }),
            "consequence_for_all_depth_proof": (
                "The million-pair audit surface collapses to one "
                "inequality per strict record: Q_n+1 <= 2*H((n+1)/2).  "
                "With FAPL20 every later record successor s is 0 mod 20, "
                "so the check points are s/2 = 0 mod 10.  The minimum "
                "positive margin is attained exactly at records 19 and "
                "139 with margin one, so no uniform slack above one "
                "exists and an all-depth proof must be sharp at those "
                "two seams."
            ),
            "falsifier": (
                "a plateau start s with H(s) > 2*H(ceil(s/2)), or a "
                "representative whose margin exceeds the empirical "
                "per-plateau doubling minimum"
            ),
            "finite_status": (
                f"reduced_surface_verified_losslessly_through_{ranks + 1}"
            ),
        },
        "record_edge_damping_candidate": {
            "definition": (
                "On a consecutive-record edge r -> n with no record "
                "between, exact carry algebra gives "
                "Q_n+1 <= 2*(Q_r+1) - delta_n with damping "
                "delta_n = 1 + f_n - t_n >= 0."
            ),
            "edge_count": len(record_edge_damping_rows),
            "rows": record_edge_damping_rows,
            "zero_damping_edge_count": len(zero_damping_edges),
            "zero_damping_edges": [
                {
                    "record_rank": int(row["record_rank"]),
                    "selected": bits[int(row["record_rank"])] == 1,
                    "take_bit": int(row["take_bit"]),
                }
                for row in zero_damping_edges
            ],
            "zero_damping_all_unselected": zero_damping_all_unselected,
            "chain_arithmetic": {
                "method": (
                    "from each row's halving anchor, iterate the exact "
                    "worst-case edge bound W <- 2W + 2 - delta over the "
                    "records up to the row; the row is chain-proved when "
                    "the resulting worst case respects "
                    "H(s) <= 2*H(ceil(s/2))"
                ),
                "proved_row_count": len(chain_arithmetic_proved_rows),
                "failed_row_count": len(chain_arithmetic_failed_rows),
                "minimum_chain_bound_margin": min(
                    (
                        int(row["chain_bound_margin"])
                        for row in chain_arithmetic_rows
                    ),
                    default=None,
                ),
                "failures": chain_arithmetic_failed_rows[:64],
            },
            "interpretation": (
                "Per-record supply discipline alone does not prove the "
                "reduced doubling rows: only a small minority of rows is "
                "chain-proved and the worst-case chain margin becomes "
                "strongly negative.  The all-depth content of (DRMH) lives "
                "in sustained inter-record divisor-load accumulation, i.e. "
                "in the windowed sum of f_k - t_k with exponential weights, "
                "not in the per-record deltas."
            ),
            "falsifier": (
                "a zero-damping edge at a selected rank, or a chain-proved "
                "row whose actual margin violates the reduction"
            ),
            "finite_status": (
                f"edge_table_complete_through_{ranks}"
            ),
        },
        "running_max_subadditivity_control": {
            "statement": "H(a+b) <= H(a)+H(b)",
            "status": "falsified_on_actual_denominator_21_orbit",
            "first_violation": first_subadditive_violation,
            "strongest_plateau_pair_violation": min(
                subadditive_violations,
                key=lambda row: int(row["integer_margin"]),
            ),
            "violating_plateau_pair_count": len(subadditive_violations),
            "positive_base_restriction": {
                "hypothesis": "H(a)>=2 and H(b)>=2",
                "status": "falsified_on_actual_denominator_21_orbit",
                "first_violation": first_positive_subadditive_violation,
                "strongest_plateau_pair_violation": min(
                    positive_subadditive_violations,
                    key=lambda row: int(row["integer_margin"]),
                ),
                "violating_plateau_pair_count": len(
                    positive_subadditive_violations
                ),
            },
            "interpretation": (
                "DRMH cannot be obtained by first proving ordinary or "
                "positive-base subadditivity of H and then specializing "
                "a=b=d; both proposed stronger laws already fail exactly."
            ),
        },
        "fixed_anchor_phase_lock_candidate": {
            "id": "FAPL20",
            "anchor_record_rank": fixed_anchor_rank,
            "anchor_successor": fixed_anchor_successor,
            "anchor_defect": defects[fixed_anchor_rank],
            "anchor_running_max_plus_one": running_max_plus_one[
                fixed_anchor_successor
            ],
            "statement": (
                "Every strict record n>19 satisfies n+1 divisible by 20, "
                "so the fixed weak record r=19 is an eligible parent."
            ),
            "tested_later_record_count": len(fixed_anchor_later_records),
            "violation_count": len(fixed_anchor_phase_violations),
            "violations": fixed_anchor_phase_violations,
            "observed_successor_residues_mod_20": sorted({
                (rank + 1) % fixed_anchor_successor
                for rank in fixed_anchor_later_records
            }),
            "consequence_with_sewgn_if_proved": (
                "SEWGN on the fixed edge from r=19 gives "
                "Q_n+1<=((n+1)/20)*(Q_19+1)=3*(n+1)/20 at every later "
                "strict record, hence globally.  This alternate linear "
                "route needs no recursive parent descent."
            ),
            "falsifier": (
                "a later strict record rank n with n not congruent to 19 "
                "modulo 20"
            ),
            "finite_status": f"tested_on_all_strict_records_through_{ranks}",
        },
        "control_interpretation": (
            "Allowing tied running maxima repairs the finite-support-shift "
            "failure of strict GP4 on the ten-target control panel.  The "
            "stronger normalized inequality holds on nine targets without "
            "exception; 1/5 has one finite-seed failure at rank 29."
        ),
        "nonclaims": [
            "WGP4 remains an all-depth conjecture, not a proof.",
            "WGN remains an all-depth conjecture, not a proof.",
            "EWGN remains an all-depth conjecture, not a proof.",
            "DRMH remains an all-depth conjecture, not a proof.",
            "Global record-density monotonicity is explicitly falsified.",
            "The cross-target panel does not prove a universal rational theorem.",
            "This receipt does not decide Erdos Problem 257.",
        ],
    }
    payload["canonical_payload_sha256"] = canonical_payload_sha256(payload)
    return payload


def resolve_path(value: str | None) -> Path:
    if value is None:
        return DEFAULT_RECEIPT
    path = Path(value)
    return path if path.is_absolute() else REPO_ROOT / path


def resolve_source_path(value: str) -> Path:
    path = Path(value)
    return path if path.is_absolute() else REPO_ROOT / path


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", default=SOURCE_REF)
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--write", nargs="?", const=None, metavar="PATH")
    action.add_argument("--check", nargs="?", const=None, metavar="PATH")
    args = parser.parse_args()
    payload = build_receipt(resolve_source_path(args.source))
    rendered = canonical_json(payload)
    argv = __import__("sys").argv
    if args.write is not None or "--write" in argv:
        path = resolve_path(args.write)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(rendered)
        print(canonical_json({
            "status": "written",
            "path": str(path.relative_to(REPO_ROOT)),
            "canonical_payload_sha256": payload["canonical_payload_sha256"],
        }), end="")
        return 0
    if args.check is not None or "--check" in argv:
        path = resolve_path(args.check)
        if path.read_text() != rendered:
            raise AssertionError(f"receipt drift: {path}")
        print(canonical_json({
            "status": "matched",
            "path": str(path.relative_to(REPO_ROOT)),
            "canonical_payload_sha256": payload["canonical_payload_sha256"],
        }), end="")
        return 0
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
