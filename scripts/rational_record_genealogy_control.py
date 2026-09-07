#!/usr/bin/env python3
"""Exact cross-target control for strict-record divisor genealogy.

The denominator-21 genealogy candidate GP4 may be source-specific or may be a
generic artifact of pseudorandom-looking greedy words.  This script replays a
fixed rational control panel with certified dyadic interval comparisons,
builds the analogous binary-carry defect for each target, and tests the same
canonical divisor-parent rule.

It is a control experiment, not a universal rational-target census.
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
DEFAULT_RANKS = 10_080
PANEL = (
    (1, 21),
    (1, 5),
    (2, 21),
    (4, 21),
    (8, 21),
    (4, 9),
    (1, 465),
    (1, 2),
    (3, 11),
    (7, 31),
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/"
    "TwentyOneRecordAncestorInheritance.md"
)
RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "rational_record_genealogy_control_receipt.json"
)
DEFAULT_RECEIPT = REPO_ROOT / RECEIPT_REF
HISTORICAL_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "twenty_one_computational_structure_receipt_2000002.json"
)
HISTORICAL_PATH = REPO_ROOT / HISTORICAL_REF
NOGO_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "twenty_one_record_divisor_supply_nogo_receipt.json"
)
NOGO_PATH = REPO_ROOT / NOGO_REF


def canonical_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def canonical_payload_sha256(payload: dict[str, Any]) -> str:
    encoded = json.dumps(
        payload, separators=(",", ":"), sort_keys=True
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def pack_itinerary(bits: bytearray, ranks: int) -> bytes:
    packed = bytearray((ranks + 7) // 8)
    for rank in range(1, ranks + 1):
        if bits[rank]:
            packed[(rank - 1) // 8] |= 1 << ((rank - 1) % 8)
    return bytes(packed)


def replay_target(numerator: int, denominator: int, ranks: int) -> dict[str, Any]:
    common = gcd(numerator, denominator)
    numerator //= common
    denominator //= common
    precision_bits = 2 * ranks + 192
    scale = 1 << precision_bits
    residual_lower = scale * numerator // denominator
    residual_upper = (
        scale * numerator + denominator - 1
    ) // denominator
    bits = bytearray(ranks + 1)
    selected_divisor_counts = [0] * (ranks + 1)
    defects = [0] * (ranks + 1)
    target_bits = bytearray(ranks + 1)
    strict_records: list[int] = []
    weak_records: list[int] = []
    strict_source_by_defect: dict[int, int] = {}
    maximum_defect = 0
    binary_remainder = numerator

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
                f"ambiguous exact branch for {numerator}/{denominator} "
                f"at rank {rank}"
            )

        binary_remainder *= 2
        target_bits[rank] = binary_remainder // denominator
        binary_remainder %= denominator
        defect = (
            2 * defects[rank - 1]
            + target_bits[rank]
            - selected_divisor_counts[rank]
        )
        if defect < 0:
            raise AssertionError(
                f"negative carry defect for {numerator}/{denominator} "
                f"at rank {rank}"
            )
        defects[rank] = defect
        if defect > maximum_defect:
            maximum_defect = defect
            strict_records.append(rank)
            weak_records.append(rank)
            strict_source_by_defect[defect] = rank
        elif defect == maximum_defect and maximum_defect > 0:
            weak_records.append(rank)

    rows: list[dict[str, Any]] = []
    for index, rank in enumerate(strict_records):
        eligible = [
            prior
            for prior in strict_records[:index]
            if (rank + 1) % (prior + 1) == 0
        ]
        parent_rank = max(eligible, default=None)
        parent_defect = defects[parent_rank] if parent_rank is not None else None
        weak_eligible = [
            weak_rank
            for weak_rank in weak_records
            if weak_rank < rank and (rank + 1) % (weak_rank + 1) == 0
        ]
        weak_parent_rank = max(weak_eligible, default=None)
        weak_parent_defect = (
            defects[weak_parent_rank] if weak_parent_rank is not None else None
        )
        weak_parent_plateau_source = (
            strict_source_by_defect[weak_parent_defect]
            if weak_parent_defect is not None
            else None
        )
        rows.append(
            {
                "record_rank": rank,
                "record_defect": defects[rank],
                "successor": rank + 1,
                "canonical_parent_record_rank": parent_rank,
                "canonical_parent_record_defect": parent_defect,
                "canonical_parent_successor": (
                    parent_rank + 1 if parent_rank is not None else None
                ),
                "canonical_parent_successor_quotient": (
                    (rank + 1) // (parent_rank + 1)
                    if parent_rank is not None
                    else None
                ),
                "gp4_margin": (
                    4 * parent_defect - defects[rank]
                    if parent_defect is not None
                    else None
                ),
                "weak_parent_record_rank": weak_parent_rank,
                "weak_parent_record_defect": weak_parent_defect,
                "weak_parent_successor": (
                    weak_parent_rank + 1
                    if weak_parent_rank is not None
                    else None
                ),
                "weak_parent_successor_quotient": (
                    (rank + 1) // (weak_parent_rank + 1)
                    if weak_parent_rank is not None
                    else None
                ),
                "weak_parent_plateau_source_strict_record_rank": (
                    weak_parent_plateau_source
                ),
                "wgp4_margin": (
                    4 * weak_parent_defect - defects[rank]
                    if weak_parent_defect is not None
                    else None
                ),
                "normalized_weak_parent_margin": (
                    ((rank + 1) // (weak_parent_rank + 1))
                    * weak_parent_defect
                    - defects[rank]
                    if weak_parent_defect is not None
                    and weak_parent_rank is not None
                    else None
                ),
            }
        )
    parented_rows = [
        row for row in rows if row["canonical_parent_record_rank"] is not None
    ]
    gp4_violations = [
        row for row in parented_rows if int(row["gp4_margin"]) < 0
    ]
    weak_parented_rows = [
        row for row in rows if row["weak_parent_record_rank"] is not None
    ]
    wgp4_violations = [
        row for row in weak_parented_rows if int(row["wgp4_margin"]) < 0
    ]
    normalized_weak_parent_violations = [
        row
        for row in weak_parented_rows
        if int(row["normalized_weak_parent_margin"]) < 0
    ]
    weak_parentless_after_first_record = [
        row
        for row in rows[1:]
        if row["weak_parent_record_rank"] is None
    ]
    maximum_ratio_row = max(
        parented_rows,
        key=lambda row: Fraction(
            int(row["record_defect"]),
            int(row["canonical_parent_record_defect"]),
        ),
    )
    maximum_ratio = Fraction(
        int(maximum_ratio_row["record_defect"]),
        int(maximum_ratio_row["canonical_parent_record_defect"]),
    )
    maximum_weak_ratio_row = max(
        weak_parented_rows,
        key=lambda row: Fraction(
            int(row["record_defect"]),
            int(row["weak_parent_record_defect"]),
        ),
    )
    maximum_weak_ratio = Fraction(
        int(maximum_weak_ratio_row["record_defect"]),
        int(maximum_weak_ratio_row["weak_parent_record_defect"]),
    )
    packed = pack_itinerary(bits, ranks)
    return {
        "target": f"{numerator}/{denominator}",
        "parameters": {
            "ranks": ranks,
            "precision_bits": precision_bits,
        },
        "selected_count": sum(bits),
        "packed_itinerary_sha256": hashlib.sha256(packed).hexdigest(),
        "packed_itinerary_base64": base64.b64encode(packed).decode("ascii"),
        "strict_record_count": len(rows),
        "weak_record_count": len(weak_records),
        "maximum_defect": maximum_defect,
        "parentless_record_ranks": [
            int(row["record_rank"])
            for row in rows
            if row["canonical_parent_record_rank"] is None
        ],
        "maximum_canonical_parent_defect_ratio": {
            "numerator": maximum_ratio.numerator,
            "denominator": maximum_ratio.denominator,
            "witness_record_rank": int(maximum_ratio_row["record_rank"]),
        },
        "gp4_violation_count": len(gp4_violations),
        "gp4_violations": gp4_violations,
        "weak_parentless_after_first_record_ranks": [
            int(row["record_rank"])
            for row in weak_parentless_after_first_record
        ],
        "maximum_weak_parent_defect_ratio": {
            "numerator": maximum_weak_ratio.numerator,
            "denominator": maximum_weak_ratio.denominator,
            "witness_record_rank": int(
                maximum_weak_ratio_row["record_rank"]
            ),
        },
        "wgp4_violation_count": len(wgp4_violations),
        "wgp4_violations": wgp4_violations,
        "normalized_weak_parent_violation_count": len(
            normalized_weak_parent_violations
        ),
        "normalized_weak_parent_violations": (
            normalized_weak_parent_violations
        ),
        "strict_record_rows": rows,
    }


def build_receipt(ranks: int) -> dict[str, Any]:
    if ranks < DEFAULT_RANKS:
        raise ValueError(
            f"ranks must be at least {DEFAULT_RANKS} for the canonical control"
        )
    target_rows = [replay_target(p, q, ranks) for p, q in PANEL]
    by_target = {row["target"]: row for row in target_rows}

    historical = json.loads(HISTORICAL_PATH.read_text())
    expected_prefix = [
        (int(row["rank"]), int(row["defect"]))
        for row in historical["strict_record_rows"]
        if int(row["rank"]) <= ranks
    ]
    observed_prefix = [
        (int(row["record_rank"]), int(row["record_defect"]))
        for row in by_target["1/21"]["strict_record_rows"]
    ]
    if observed_prefix != expected_prefix:
        raise AssertionError("1/21 strict-record prefix mismatch")
    nogo = json.loads(NOGO_PATH.read_text())
    if (
        by_target["1/21"]["packed_itinerary_sha256"]
        != nogo["itinerary_sha256"]
    ):
        raise AssertionError("1/21 independent itinerary mismatch")

    support_1_21 = base64.b64decode(
        by_target["1/21"]["packed_itinerary_base64"]
    )
    support_4_21 = base64.b64decode(
        by_target["4/21"]["packed_itinerary_base64"]
    )
    differing_ranks = []
    for rank in range(1, ranks + 1):
        left = (support_1_21[(rank - 1) // 8] >> ((rank - 1) % 8)) & 1
        right = (support_4_21[(rank - 1) // 8] >> ((rank - 1) % 8)) & 1
        if left != right:
            differing_ranks.append(rank)
    if differing_ranks != [3]:
        raise AssertionError(
            f"unexpected 1/21 versus 4/21 support difference: {differing_ranks}"
        )
    if by_target["1/21"]["gp4_violation_count"] != 0:
        raise AssertionError("1/21 GP4 control unexpectedly failed")
    four_twenty_one_violations = by_target["4/21"]["gp4_violations"]
    if [row["record_rank"] for row in four_twenty_one_violations] != [419, 779]:
        raise AssertionError("unexpected 4/21 GP4 falsifier set")
    unexpected_wgp4_failures = [
        row["target"] for row in target_rows if row["wgp4_violation_count"]
    ]
    if unexpected_wgp4_failures:
        raise AssertionError(
            f"unexpected WGP4 panel failures: {unexpected_wgp4_failures}"
        )
    normalized_failure_map = {
        row["target"]: [
            int(violation["record_rank"])
            for violation in row["normalized_weak_parent_violations"]
        ]
        for row in target_rows
        if row["normalized_weak_parent_violation_count"]
    }
    if normalized_failure_map != {"1/5": [29]}:
        raise AssertionError(
            f"unexpected normalized weak-parent failures: {normalized_failure_map}"
        )

    maximum_panel_ratio, maximum_panel_ratio_target = max(
        (
            Fraction(
                row["maximum_canonical_parent_defect_ratio"]["numerator"],
                row["maximum_canonical_parent_defect_ratio"]["denominator"],
            ),
            row["target"],
        )
        for row in target_rows
    )

    for row in target_rows:
        row.pop("packed_itinerary_base64")
    payload: dict[str, Any] = {
        "schema": "rational_record_genealogy_control_v2",
        "parameters": {
            "ranks": ranks,
            "target_panel": [f"{p}/{q}" for p, q in PANEL],
        },
        "authority": {
            "script_ref": str(Path(__file__).resolve().relative_to(REPO_ROOT)),
            "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "analysis_ref": ANALYSIS_REF,
            "historical_twenty_one_receipt_ref": HISTORICAL_REF,
            "historical_twenty_one_receipt_payload_sha256": historical[
                "receipt_payload_sha256"
            ],
            "independent_twenty_one_receipt_ref": NOGO_REF,
            "independent_twenty_one_itinerary_sha256": nogo["itinerary_sha256"],
            "method": (
                "certified dyadic interval greedy replay plus exact target "
                "binary digits, selected-divisor convolution, and strict-"
                "record divisor genealogy"
            ),
            "floating_point_used": False,
            "python_version": platform.python_version(),
        },
        "target_rows": target_rows,
        "finite_shift_control": {
            "identity": "4/21 = 1/21 + 1/(2^3-1)",
            "support_difference_ranks": differing_ranks,
            "one_twenty_one_gp4_violation_count": by_target["1/21"][
                "gp4_violation_count"
            ],
            "four_twenty_one_gp4_violation_count": by_target["4/21"][
                "gp4_violation_count"
            ],
            "four_twenty_one_gp4_violation_ranks": [
                int(row["record_rank"]) for row in four_twenty_one_violations
            ],
            "one_twenty_one_wgp4_violation_count": by_target["1/21"][
                "wgp4_violation_count"
            ],
            "four_twenty_one_wgp4_violation_count": by_target["4/21"][
                "wgp4_violation_count"
            ],
            "four_twenty_one_maximum_ratio": by_target["4/21"][
                "maximum_canonical_parent_defect_ratio"
            ],
            "conclusion": (
                "GP4 is not a generic support-word or divisor-genealogy "
                "tautology: adding the single forced coin at rank three "
                "leaves the tail support identical but creates exact GP4 "
                "failures.  A proof for 1/21 must use its exact source bits."
            ),
        },
        "panel_summary": {
            "target_count": len(target_rows),
            "targets_with_gp4_violations": [
                row["target"]
                for row in target_rows
                if row["gp4_violation_count"] > 0
            ],
            "targets_with_wgp4_violations": [
                row["target"]
                for row in target_rows
                if row["wgp4_violation_count"] > 0
            ],
            "targets_with_later_parentless_weak_record": [
                row["target"]
                for row in target_rows
                if row["weak_parentless_after_first_record_ranks"]
            ],
            "targets_with_normalized_weak_parent_violations": (
                normalized_failure_map
            ),
            "normalized_weak_parent_interpretation": (
                "Nine targets satisfy defect-density monotonicity on every "
                "tested weak-parent edge.  Target 1/5 has one finite-seed "
                "failure at rank 29 and no later failure in the checked range."
            ),
            "maximum_panel_ratio": {
                "numerator": maximum_panel_ratio.numerator,
                "denominator": maximum_panel_ratio.denominator,
                "target": maximum_panel_ratio_target,
            },
            "interpretation": (
                "The panel is a falsification control, not evidence for a "
                "universal rational-target genealogy theorem."
            ),
        },
        "nonclaims": [
            "The target panel is finite and not a census of all rationals.",
            "The control does not prove GP4 for 1/21 at all depths.",
            "The control does not prove WGP4 for any target at all depths.",
            "The control does not prove normalized weak-parent monotonicity.",
            "The control does not decide Erdos Problem 257.",
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
    payload = build_receipt(args.ranks)
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
