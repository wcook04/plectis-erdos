#!/usr/bin/env python3
"""Test whether worst seam-stall contributors arise at diagonal small margins."""

from __future__ import annotations

import argparse
import hashlib
import json
from array import array
from pathlib import Path
from typing import Any

from four_ninths_seam_stall_ancestry import analyze as ancestry_analyze


SCRIPT_PATH = Path(__file__).resolve()
ANCESTRY_PATH = SCRIPT_PATH.with_name("four_ninths_seam_stall_ancestry.py")
STALL_RANKS = tuple(range(293_578, 293_592, 2))


def canonical_digest(value: object) -> str:
    data = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(data).hexdigest()


def integer_digest(value: int) -> str:
    length = max(1, (value.bit_length() + 7) // 8)
    return hashlib.sha256(value.to_bytes(length, "big")).hexdigest()


def pair_pulse(rank: int) -> int:
    return (0, 1, 3)[rank % 3]


def analyze(limit: int, crosscheck: int) -> dict[str, Any]:
    ancestry = ancestry_analyze(293_592, crosscheck, STALL_RANKS)
    failure_rows = [
        row for row in ancestry["trace_rows"] if not row["escape_served"]
    ]
    cohort = sorted(
        {
            contributor
            for row in failure_rows
            for contributor in row["odd_contributors"] + row["even_contributors"]
        }
    )
    if limit < max(cohort):
        raise ValueError("--limit must reach every stall contributor")

    loads = array("H", [0]) * (2 * limit + 3)
    rho = 0
    selected = 0
    cohort_set = set(cohort)
    cohort_rows: list[dict[str, Any]] = []
    small_margin_events: list[dict[str, int]] = []
    maximum_gap_all: tuple[int, int, int, int] | None = None

    for rank in range(1, limit + 1):
        load = 2 * loads[2 * rank - 1] + loads[2 * rank]
        transported = 4 * rho + pair_pulse(rank) - load
        coin = (1 << rank) + 1
        take = transported >= coin
        rho = transported - coin if take else transported
        if rho < 0:
            raise AssertionError(("negative diagonal", rank, rho, load))
        if not take:
            continue

        selected += 1
        for multiple in range(2 * rank, 2 * limit + 3, rank):
            loads[multiple] += 1

        bit_length = rho.bit_length()
        gap = rank - bit_length
        small = 3 * rho < 2 * selected
        score = (gap, -rank, bit_length, selected)
        old_score = (
            (maximum_gap_all[0], -maximum_gap_all[1], maximum_gap_all[2], maximum_gap_all[3])
            if maximum_gap_all is not None
            else None
        )
        if old_score is None or score > old_score:
            maximum_gap_all = (gap, rank, bit_length, selected)
        if small:
            small_margin_events.append(
                {"rank": rank, "rho": rho, "selected_count": selected}
            )
        if rank in cohort_set:
            cohort_rows.append(
                {
                    "rank": rank,
                    "rho_bit_length": bit_length,
                    "dyadic_leading_zero_count": gap,
                    "selected_count": selected,
                    "three_rho_lt_two_selected": small,
                    "rho_sha256": integer_digest(rho),
                    "rho_low_64": rho & ((1 << 64) - 1),
                }
            )

    if maximum_gap_all is None:
        raise AssertionError("no selected diagonal ranks")
    if [row["rank"] for row in cohort_rows] != cohort:
        missing = sorted(cohort_set - {row["rank"] for row in cohort_rows})
        raise AssertionError(("stall contributor not selected on diagonal", missing))

    gap_histogram: dict[str, int] = {}
    for row in cohort_rows:
        key = str(row["dyadic_leading_zero_count"])
        gap_histogram[key] = gap_histogram.get(key, 0) + 1
    worst_cohort = max(
        cohort_rows,
        key=lambda row: (row["dyadic_leading_zero_count"], -row["rank"]),
    )
    result: dict[str, Any] = {
        "schema": "erdos257_four_ninths_stall_diagonal_charge_v0",
        "parameters": {"limit": limit, "crosscheck": crosscheck},
        "source": {
            "stall_ancestry": str(ANCESTRY_PATH.relative_to(SCRIPT_PATH.parents[2])),
            "stall_ancestry_sha256": hashlib.sha256(ANCESTRY_PATH.read_bytes()).hexdigest(),
        },
        "validation": {
            "exact_integer_diagonal": True,
            "every_stall_contributor_selected_on_diagonal": True,
            "contributor_count": len(cohort),
            "cohort_table_sha256": canonical_digest(cohort_rows),
        },
        "diagonal_census": {
            "selected_count_through_limit": selected,
            "small_two_thirds_margin_event_count": len(small_margin_events),
            "small_two_thirds_margin_events": small_margin_events,
            "maximum_dyadic_leading_zero_count": {
                "value": maximum_gap_all[0],
                "rank": maximum_gap_all[1],
                "rho_bit_length": maximum_gap_all[2],
                "selected_count": maximum_gap_all[3],
            },
        },
        "stall_contributor_census": {
            "count": len(cohort_rows),
            "small_two_thirds_margin_count": sum(
                row["three_rho_lt_two_selected"] for row in cohort_rows
            ),
            "dyadic_leading_zero_histogram": gap_histogram,
            "maximum_dyadic_leading_zero_witness": worst_cohort,
        },
        "mechanism_decision": {
            "candidate": (
                "charge seam-stall fresh contributors to the diagonal's selected "
                "two-thirds-small-margin events"
            ),
            "status": "eliminated_on_actual_stall_cohort",
            "stop_condition": (
                "do not charge seam-stall contributors to diagonal small-margin "
                "selection; seek a different reachability resource"
            ),
        },
        "claim_ceiling": (
            "exact finite diagonal charge comparison; no all-depth margin exclusion, "
            "seam exclusion, support construction, or Erdos 257 conclusion"
        ),
    }
    result["canonical_digest"] = canonical_digest(result)
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=146_794)
    parser.add_argument("--crosscheck", type=int, default=300)
    parser.add_argument("--check-receipt")
    args = parser.parse_args()
    result = analyze(args.limit, args.crosscheck)
    if args.check_receipt:
        with open(args.check_receipt, encoding="utf-8") as handle:
            if result != json.load(handle):
                raise SystemExit("receipt mismatch")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
