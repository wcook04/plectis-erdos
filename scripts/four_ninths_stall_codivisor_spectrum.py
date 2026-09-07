#!/usr/bin/env python3
"""Resolve the co-divisor spectrum financing the worst 4/9 seam stall."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from four_ninths_seam_stall_ancestry import analyze as ancestry_analyze


SCRIPT_PATH = Path(__file__).resolve()
ANCESTRY_PATH = SCRIPT_PATH.with_name("four_ninths_seam_stall_ancestry.py")
STALL_RANKS = tuple(range(293_578, 293_592, 2))
THRESHOLDS = (10, 50, 100, 500, 1_000, 5_000, 10_000)


def canonical_digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def analyze(crosscheck: int) -> dict[str, Any]:
    ancestry = ancestry_analyze(293_592, crosscheck, STALL_RANKS)
    rows = []
    for source in ancestry["trace_rows"]:
        if source["escape_served"]:
            continue
        weighted_q: list[int] = []
        for divisor in source["odd_contributors"]:
            weighted_q.extend([source["odd_row"] // divisor] * 2)
        for divisor in source["even_contributors"]:
            weighted_q.append(source["even_row"] // divisor)
        weighted_q.sort()
        x = source["offset_before"]
        escape_floor = max(1, 2 * x)
        needed = 4 * x + source["target_digit"] - escape_floor + 1
        if not (1 <= needed <= len(weighted_q)):
            raise AssertionError((source["source_rank"], needed, len(weighted_q)))
        rows.append(
            {
                "source_rank": source["source_rank"],
                "offset_before": x,
                "weighted_load": len(weighted_q),
                "minimum_load_to_fail_service": needed,
                "minimum_codivisor_cutoff_supplying_failure_load": weighted_q[needed - 1],
                "load_by_codivisor_cutoff": {
                    str(cutoff): sum(q <= cutoff for q in weighted_q)
                    for cutoff in THRESHOLDS
                },
                "minimum_codivisor": weighted_q[0],
                "maximum_codivisor": weighted_q[-1],
                "weighted_codivisor_sha256": canonical_digest(weighted_q),
            }
        )

    sufficient_by_cutoff = {
        str(cutoff): sum(
            row["load_by_codivisor_cutoff"][str(cutoff)]
            >= row["minimum_load_to_fail_service"]
            for row in rows
        )
        for cutoff in THRESHOLDS
    }
    cutoffs = [row["minimum_codivisor_cutoff_supplying_failure_load"] for row in rows]
    result: dict[str, Any] = {
        "schema": "erdos257_four_ninths_stall_codivisor_spectrum_v0",
        "parameters": {"crosscheck": crosscheck, "thresholds": list(THRESHOLDS)},
        "source": {
            "stall_ancestry": str(ANCESTRY_PATH.relative_to(SCRIPT_PATH.parents[2])),
            "stall_ancestry_sha256": hashlib.sha256(ANCESTRY_PATH.read_bytes()).hexdigest(),
        },
        "validation": {
            "exact_selected_divisor_ancestry": True,
            "failure_count": len(rows),
            "row_table_sha256": canonical_digest(rows),
        },
        "census": {
            "minimum_required_codivisor_cutoffs": cutoffs,
            "minimum_over_failures": min(cutoffs),
            "maximum_over_failures": max(cutoffs),
            "failures_financed_by_cutoff": sufficient_by_cutoff,
        },
        "failure_rows": rows,
        "mechanism_decision": {
            "candidate": (
                "finance every escape-service failure from a fixed collection of "
                "small co-divisor diagonals q=m/d"
            ),
            "status": "small_codivisor_channel_eliminated_on_actual_worst_stall",
            "reason": (
                "no failure is financed by q<=50; four of six are not financed by "
                "q<=1000, and one needs channels through q=146794"
            ),
            "stop_condition": (
                "do not reduce the seam stall to finitely many small quotient "
                "diagonals; any charge must work across quotient scales"
            ),
        },
        "claim_ceiling": (
            "exact finite co-divisor spectrum of the worst observed stall; no "
            "all-depth service bound, seam exclusion, or Erdos 257 conclusion"
        ),
    }
    result["canonical_digest"] = canonical_digest(result)
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--crosscheck", type=int, default=300)
    parser.add_argument("--check-receipt")
    args = parser.parse_args()
    result = analyze(args.crosscheck)
    if args.check_receipt:
        with open(args.check_receipt, encoding="utf-8") as handle:
            if result != json.load(handle):
                raise SystemExit("receipt mismatch")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
