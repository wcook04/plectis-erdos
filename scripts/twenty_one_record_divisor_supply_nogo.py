#!/usr/bin/env python3
"""Exact divisor-supply probes at denominator-21 defect records.

The strict-record reset experiment asks why the selected-divisor load at
``n + 1`` is large whenever the denominator-21 Lambert defect sets a new
record at ``n``.  This script independently reconstructs the rational greedy
word with exact dyadic interval enclosures and tests several tempting static
explanations of that load.

The output is a finite counterexample certificate for the static explanations
and a finite positive certificate for a dyadic record-inheritance candidate.
It neither proves nor disproves the all-depth record-reset and record-repair
conjectures.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from math import isqrt
from pathlib import Path
import platform
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
DEFAULT_RANKS = 10_080
DEFAULT_RECEIPT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "twenty_one_record_divisor_supply_nogo_receipt.json"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/"
    "TwentyOneRecordDivisorSupplyNoGo.md"
)
SOURCE_LAB_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/"
    "TwentyOneComputationalStructureLab.md"
)
MATURE_RECORD_START = 419


def canonical_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def canonical_payload_sha256(payload: dict[str, Any]) -> str:
    encoded = json.dumps(
        payload, separators=(",", ":"), sort_keys=True
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def target_bit(rank: int) -> int:
    return int(rank % 6 in (5, 0))


def divisors(value: int) -> list[int]:
    lower: list[int] = []
    upper: list[int] = []
    for divisor in range(1, isqrt(value) + 1):
        if value % divisor != 0:
            continue
        lower.append(divisor)
        if divisor * divisor != value:
            upper.append(value // divisor)
    return lower + upper[::-1]


def packed_itinerary_sha256(bits: bytearray, ranks: int) -> str:
    itinerary = bytearray((ranks + 7) // 8)
    for rank in range(1, ranks + 1):
        if bits[rank]:
            itinerary[(rank - 1) // 8] |= 1 << ((rank - 1) % 8)
    return hashlib.sha256(itinerary).hexdigest()


def first_pair_witness(
    rows: list[dict[str, Any]], state: str
) -> dict[str, Any] | None:
    for row in rows:
        for pair in row["proper_divisor_pairs"]:
            if pair["state"] == state:
                return {
                    "record_rank": row["record_rank"],
                    "successor": row["successor"],
                    "divisor_pair": [pair["lower"], pair["upper"]],
                    "pair_state": state,
                }
    return None


def first_row_witness(
    rows: list[dict[str, Any]], predicate: Any
) -> dict[str, Any] | None:
    for row in rows:
        if predicate(row):
            return row
    return None


def replay(ranks: int) -> dict[str, Any]:
    if ranks < DEFAULT_RANKS:
        raise ValueError(
            f"ranks must be at least {DEFAULT_RANKS} to cover the canonical "
            "counterexample set"
        )

    precision_bits = 2 * ranks + 160
    scale = 1 << precision_bits
    residual_lower = scale // 21
    residual_upper = (scale + 20) // 21
    bits = bytearray(ranks + 1)
    selected_divisor_counts = [0] * (ranks + 1)
    defects = [0] * (ranks + 1)
    strict_record_ranks: list[int] = []
    maximum_defect = 0

    for rank in range(1, ranks + 1):
        weight_floor = scale // ((1 << rank) - 1)
        if residual_lower >= weight_floor + 1:
            bits[rank] = 1
            residual_lower -= weight_floor + 1
            residual_upper -= weight_floor
            for multiple in range(rank, ranks + 1, rank):
                selected_divisor_counts[multiple] += 1
        elif residual_upper <= weight_floor:
            pass
        else:
            raise AssertionError(
                f"ambiguous exact greedy branch at rank {rank}"
            )

        defects[rank] = (
            2 * defects[rank - 1]
            + target_bit(rank)
            - selected_divisor_counts[rank]
        )
        if defects[rank] < 0:
            raise AssertionError(f"negative defect at rank {rank}")
        if defects[rank] > maximum_defect:
            maximum_defect = defects[rank]
            strict_record_ranks.append(rank)

    rows: list[dict[str, Any]] = []
    for record_rank in strict_record_ranks:
        if record_rank == ranks:
            continue
        successor = record_rank + 1
        successor_divisors = divisors(successor)
        root = isqrt(successor)
        proper_pairs: list[dict[str, Any]] = []
        for lower in successor_divisors:
            if lower * lower > successor:
                break
            upper = successor // lower
            if lower == 1 or upper == successor:
                continue
            proper_pairs.append(
                {
                    "lower": lower,
                    "upper": upper,
                    "state": f"{bits[lower]}{bits[upper]}",
                }
            )
        pair_state_counts = {
            state: sum(pair["state"] == state for pair in proper_pairs)
            for state in ("00", "01", "10", "11")
        }
        selected_divisors = [
            divisor for divisor in successor_divisors if bits[divisor]
        ]
        lower_selected = sum(divisor <= root for divisor in selected_divisors)
        upper_selected = len(selected_divisors) - lower_selected
        rows.append(
            {
                "record_rank": record_rank,
                "record_defect": defects[record_rank],
                "successor": successor,
                "successor_divisor_count": len(successor_divisors),
                "successor_selected_divisor_load": len(selected_divisors),
                "successor_defect": defects[successor],
                "selected_divisors": selected_divisors,
                "proper_divisor_pairs": proper_pairs,
                "proper_pair_state_counts": pair_state_counts,
                "selected_at_or_below_sqrt": lower_selected,
                "selected_above_sqrt": upper_selected,
            }
        )

    pair_00 = first_pair_witness(rows, "00")
    pair_11 = first_pair_witness(rows, "11")
    exact_half = first_row_witness(
        rows,
        lambda row: (
            2 * row["successor_selected_divisor_load"]
            != row["successor_divisor_count"]
        ),
    )
    half_lower_bound = first_row_witness(
        rows,
        lambda row: (
            2 * row["successor_selected_divisor_load"]
            < row["successor_divisor_count"]
        ),
    )
    mature_rows = [
        row for row in rows if row["record_rank"] >= MATURE_RECORD_START
    ]
    lower_side = first_row_witness(
        mature_rows,
        lambda row: (
            row["selected_at_or_below_sqrt"]
            < row["selected_above_sqrt"]
        ),
    )
    upper_side = first_row_witness(
        mature_rows,
        lambda row: (
            row["selected_above_sqrt"]
            < row["selected_at_or_below_sqrt"]
        ),
    )
    required_witnesses = {
        "proper_pair_at_least_one_selected": pair_00,
        "proper_pair_at_most_one_selected": pair_11,
        "successor_load_exactly_half_of_divisors": exact_half,
        "successor_load_at_least_half_of_divisors": half_lower_bound,
        "mature_record_load_lower_side_dominates": lower_side,
        "mature_record_load_upper_side_dominates": upper_side,
    }
    missing = [name for name, witness in required_witnesses.items() if witness is None]
    if missing:
        raise AssertionError(f"missing expected no-go witnesses: {missing}")

    strict_record_set = set(strict_record_ranks)
    inheritance_rows: list[dict[str, Any]] = []
    for parent_rank in strict_record_ranks:
        child_rank = 2 * parent_rank + 1
        child_successor = child_rank + 1
        if child_successor > ranks:
            continue
        parent_successor = parent_rank + 1
        inherited_load = selected_divisor_counts[parent_successor]
        required_load = defects[child_rank] + target_bit(child_successor)
        child_is_strict_record = child_rank in strict_record_set
        inheritance_rows.append(
            {
                "parent_record_rank": parent_rank,
                "parent_record_defect": defects[parent_rank],
                "parent_successor": parent_successor,
                "parent_successor_defect": defects[parent_successor],
                "inherited_selected_divisor_load": inherited_load,
                "child_rank": child_rank,
                "child_defect": defects[child_rank],
                "child_is_strict_record": child_is_strict_record,
                "child_successor": child_successor,
                "child_successor_target_bit": target_bit(child_successor),
                "inherited_repair_margin": inherited_load - required_load,
                "child_successor_selected_divisor_load": (
                    selected_divisor_counts[child_successor]
                ),
                "parent_successor_divides_child_successor": (
                    child_successor % parent_successor == 0
                ),
            }
        )
    inheritance_violations = [
        row
        for row in inheritance_rows
        if row["inherited_repair_margin"] < 0
    ]
    if inheritance_violations:
        raise AssertionError(
            "dyadic record-inheritance candidate unexpectedly failed"
        )
    if not inheritance_rows:
        raise AssertionError("no dyadic record-inheritance rows were tested")
    inherited_child_records = [
        row for row in inheritance_rows if row["child_is_strict_record"]
    ]
    for row in inherited_child_records:
        if not row["parent_successor_divides_child_successor"]:
            raise AssertionError("dyadic successor divisibility failed")
        if (
            row["child_successor_selected_divisor_load"]
            < row["inherited_selected_divisor_load"]
        ):
            raise AssertionError("selected divisor inheritance failed")

    dyadic_child_records = {
        int(row["child_rank"]) for row in inherited_child_records
    }
    root_record_ranks = [
        rank for rank in strict_record_ranks if rank not in dyadic_child_records
    ]

    payload: dict[str, Any] = {
        "schema": "twenty_one_record_divisor_supply_nogo_v1",
        "parameters": {
            "ranks": ranks,
            "precision_bits": precision_bits,
            "mature_record_start": MATURE_RECORD_START,
        },
        "authority": {
            "script_ref": str(Path(__file__).resolve().relative_to(REPO_ROOT)),
            "script_sha256": hashlib.sha256(
                Path(__file__).read_bytes()
            ).hexdigest(),
            "analysis_ref": ANALYSIS_REF,
            "motivating_analysis_ref": SOURCE_LAB_REF,
            "python_version": platform.python_version(),
            "method": (
                "exact dyadic interval reconstruction of the rational greedy "
                "word, followed by exact divisor enumeration"
            ),
            "floating_point_used": False,
        },
        "itinerary_sha256": packed_itinerary_sha256(bits, ranks),
        "strict_record_count": len(strict_record_ranks),
        "strict_record_rows": rows,
        "no_go_results": {
            name: {
                "status": "falsified_on_actual_denominator_21_orbit",
                "first_witness": witness,
            }
            for name, witness in required_witnesses.items()
        },
        "dyadic_record_inheritance_candidate": {
            "statement": (
                "If r is a strict record rank, then f(r+1) >= "
                "Q_(2r+1) + t_(2r+2)."
            ),
            "finite_status": "verified_on_every_tested_parent_record",
            "tested_parent_record_count": len(inheritance_rows),
            "minimum_inherited_repair_margin": min(
                int(row["inherited_repair_margin"])
                for row in inheritance_rows
            ),
            "violation_count": len(inheritance_violations),
            "violations": inheritance_violations,
            "rows": inheritance_rows,
            "strict_child_record_count": len(inherited_child_records),
            "strict_child_record_ranks": sorted(dyadic_child_records),
            "root_record_ranks_in_checked_range": root_record_ranks,
            "one_way_consequence": (
                "If 2r+1 is also a strict record, then r+1 divides 2r+2, "
                "so selected-divisor inclusion transfers the displayed "
                "inequality to RR at the child record."
            ),
        },
        "analytic_consequence": (
            "RB4/RR cannot be proved by static complement pairing, exact or "
            "lower half-density of selected successor divisors, or a fixed "
            "choice of the lower/upper square-root bank.  The surviving "
            "dyadic inheritance candidate does use the record condition: "
            "on every tested parent, the old load at r+1 already pays the "
            "repair bill at 2r+1, which proves RR for every tested record "
            "that is a dyadic child.  The all-depth dyadic inequality and "
            "the root records remain open."
        ),
        "nonclaims": [
            "The computation does not falsify RB4 or RR.",
            "The computation does not prove denominator-21 membership.",
            "The computation does not decide Erdos Problem 257.",
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
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--write", nargs="?", const=None, metavar="PATH")
    action.add_argument("--check", nargs="?", const=None, metavar="PATH")
    args = parser.parse_args()

    payload = replay(args.ranks)
    rendered = canonical_json(payload)
    if args.write is not None or "--write" in __import__("sys").argv:
        path = resolve_path(args.write)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(rendered)
        print(
            canonical_json(
                {
                    "status": "written",
                    "path": str(path.relative_to(REPO_ROOT)),
                    "canonical_payload_sha256": payload[
                        "canonical_payload_sha256"
                    ],
                }
            ),
            end="",
        )
        return 0
    if args.check is not None or "--check" in __import__("sys").argv:
        path = resolve_path(args.check)
        expected = path.read_text()
        if expected != rendered:
            raise AssertionError(f"receipt drift: {path}")
        print(
            canonical_json(
                {
                    "status": "matched",
                    "path": str(path.relative_to(REPO_ROOT)),
                    "canonical_payload_sha256": payload[
                        "canonical_payload_sha256"
                    ],
                }
            ),
            end="",
        )
        return 0
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
