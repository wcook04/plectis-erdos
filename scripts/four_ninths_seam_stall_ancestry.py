#!/usr/bin/env python3
"""Trace selected-divisor ancestry of the exact worst 4/9 seam stall."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from array import array
from pathlib import Path
from typing import Any

from totient_four_ninths_even_cylinder_audit import (
    full_prefix_dp,
    initialize_cylinder,
    raw_carry,
    target_bit,
)


SCRIPT_PATH = Path(__file__).resolve()
AUDIT_PATH = SCRIPT_PATH.with_name("totient_four_ninths_even_cylinder_audit.py")
DEFAULT_TRACE_RANKS = tuple(range(293_578, 293_592, 2)) + (1_349_998,)


def canonical_digest(value: object) -> str:
    data = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(data).hexdigest()


def receipt_projection(result: dict[str, Any]) -> dict[str, Any]:
    """Compact ancestry receipt with full lists for the two decisive rows."""

    projection = {key: value for key, value in result.items() if key != "trace_rows"}
    projected_rows = []
    for row in result["trace_rows"]:
        contributors = {
            "odd": row["odd_contributors"],
            "even": row["even_contributors"],
        }
        item = {
            key: row[key]
            for key in (
                "source_rank",
                "offset_before",
                "offset_after_raw",
                "escape_served",
                "escape_deficit",
                "correction",
                "weighted_load",
            )
        }
        item["odd_contributor_count"] = len(row["odd_contributors"])
        item["even_contributor_count"] = len(row["even_contributors"])
        item["contributor_sha256"] = canonical_digest(contributors)
        if "new_vs_prior_transition" in row:
            item["new_contributor_count"] = len(row["new_vs_prior_transition"])
            item["reused_contributor_count"] = len(row["reused_vs_prior_transition"])
        if row["source_rank"] in (293_590, 1_349_998):
            item["odd_contributors"] = row["odd_contributors"]
            item["even_contributors"] = row["even_contributors"]
            if "new_vs_prior_transition" in row:
                item["new_vs_prior_transition"] = row["new_vs_prior_transition"]
                item["reused_vs_prior_transition"] = row["reused_vs_prior_transition"]
        projected_rows.append(item)
    projection["trace_rows"] = projected_rows
    return projection


def selected_proper_divisors(value: int, fixed: bytearray) -> list[int]:
    result: list[int] = []
    for divisor in range(1, math.isqrt(value) + 1):
        if value % divisor:
            continue
        quotient = value // divisor
        if divisor < value and fixed[divisor]:
            result.append(divisor)
        if quotient != divisor and quotient < value and fixed[quotient]:
            result.append(quotient)
    return sorted(result)


def analyze(horizon: int, crosscheck: int, trace_ranks: tuple[int, ...]) -> dict[str, Any]:
    if horizon < max(trace_ranks) + 2 or horizon % 2:
        raise ValueError("--horizon must be even and exceed every traced transition")
    if any(rank % 2 for rank in trace_ranks):
        raise ValueError("all trace ranks must be even")

    trace_set = set(trace_ranks)
    snapshots = full_prefix_dp(crosscheck)
    prefix_word, prefix_length, suffix_length, suffix_top = initialize_cylinder(
        snapshots
    )
    fixed = bytearray(horizon + 3)
    divisor_load = array("H", [0]) * (horizon + 3)

    def fix_rank(rank: int, bit: int) -> None:
        fixed[rank] = bit
        if bit:
            for multiple in range(2 * rank, horizon + 3, rank):
                divisor_load[multiple] += 1

    for rank in range(1, prefix_length + 1):
        fix_rank(rank, (prefix_word >> (rank - 1)) & 1)

    rows: list[dict[str, Any]] = []
    trace = hashlib.sha256()
    rank = 6
    while rank < horizon:
        boundary = 1 << (suffix_length - 1)
        bottom = suffix_top - raw_carry(rank)
        if not (bottom < boundary <= suffix_top):
            raise AssertionError((rank, bottom, boundary, suffix_top))
        old_offset = suffix_top - boundary

        g1, g2 = divisor_load[rank + 1], divisor_load[rank + 2]
        t1, t2 = target_bit(rank + 1), target_bit(rank + 2)
        correction = 2 * (t1 - g1) + (t2 - g2)
        next_carry = raw_carry(rank + 2)
        next_top = 4 * suffix_top + correction
        next_width = suffix_length + 2
        next_bottom = next_top - next_carry
        difference = next_top ^ next_bottom
        common = next_width - (difference.bit_length() if difference else 0)
        raw_offset = 4 * old_offset + correction

        if rank in trace_set:
            odd = selected_proper_divisors(rank + 1, fixed)
            even = selected_proper_divisors(rank + 2, fixed)
            if len(odd) != g1 or len(even) != g2:
                raise AssertionError(("load ancestry", rank, len(odd), g1, len(even), g2))
            weighted_load = 2 * len(odd) + len(even)
            target_digit = 2 * t1 + t2
            if correction != target_digit - weighted_load:
                raise AssertionError(("correction ancestry", rank))
            rows.append(
                {
                    "source_rank": rank,
                    "offset_before": old_offset,
                    "offset_after_raw": raw_offset,
                    "common_bits_stripped": common,
                    "escape_served": raw_offset >= max(1, 2 * old_offset),
                    "escape_deficit": max(1, 2 * old_offset) - raw_offset,
                    "target_digit": target_digit,
                    "correction": correction,
                    "odd_row": rank + 1,
                    "odd_contributors": odd,
                    "even_row": rank + 2,
                    "even_contributors": even,
                    "weighted_load": weighted_load,
                }
            )

        trace.update(f"{rank + 2}:{old_offset}:{correction}:{raw_offset}:{common};".encode())
        for offset in range(common):
            bit = (next_top >> (next_width - 1 - offset)) & 1
            prefix_length += 1
            fix_rank(prefix_length, bit)
        next_width -= common
        suffix_length = next_width
        suffix_top = next_top & ((1 << suffix_length) - 1 if suffix_length else 0)
        rank += 2
        if prefix_length < rank // 2 + 1:
            raise AssertionError(("first midpoint seam", rank, prefix_length, suffix_length))

    if {row["source_rank"] for row in rows} != trace_set:
        raise AssertionError("not every requested rank was traced")

    stall_rows = [row for row in rows if row["source_rank"] < 300_000]
    prior: set[int] = set()
    failure_union: set[int] = set()
    contributor_frequency: dict[int, int] = {}
    for row in stall_rows:
        contributors = set(row["odd_contributors"]) | set(row["even_contributors"])
        row["new_vs_prior_transition"] = sorted(contributors - prior)
        row["reused_vs_prior_transition"] = sorted(contributors & prior)
        prior |= contributors
        if not row["escape_served"]:
            failure_union |= contributors
            for contributor in contributors:
                contributor_frequency[contributor] = contributor_frequency.get(contributor, 0) + 1

    reused_failures = sorted(
        contributor for contributor, count in contributor_frequency.items() if count > 1
    )
    failure_rows = [row for row in stall_rows if not row["escape_served"]]
    result: dict[str, Any] = {
        "schema": "erdos257_four_ninths_seam_stall_ancestry_v0",
        "parameters": {
            "horizon": horizon,
            "crosscheck": crosscheck,
            "trace_ranks": list(trace_ranks),
        },
        "source": {
            "existing_cylinder_audit": str(AUDIT_PATH.relative_to(SCRIPT_PATH.parents[2])),
            "existing_cylinder_audit_sha256": hashlib.sha256(AUDIT_PATH.read_bytes()).hexdigest(),
        },
        "validation": {
            "exact_integer_recurrence": True,
            "load_ancestry_recounted_from_fixed_support": True,
            "midpoint_seam_seen": False,
            "trace_sha256": trace.hexdigest(),
        },
        "stall_summary": {
            "transition_count": len(stall_rows),
            "failure_count": len(failure_rows),
            "distinct_contributors_across_failures": len(failure_union),
            "contributors_reused_across_failures": reused_failures,
            "reused_contributor_count": len(reused_failures),
            "minimum_new_contributors_on_failure": min(
                len(row["new_vs_prior_transition"]) for row in failure_rows
            ),
        },
        "trace_rows": rows,
        "mechanism_decision": {
            "candidate": (
                "bound the reachable supply of fresh selected divisors capable of "
                "paying for consecutive escape-service failures"
            ),
            "status": "fresh_contributor_mechanism_measured",
            "stop_condition": (
                "use fixation/reachability history to bound fresh contributor supply; "
                "do not infer a bound from local divisor ancestry alone"
            ),
        },
        "claim_ceiling": (
            "exact ancestry of specified finite transitions; no uniform fresh-load "
            "budget, all-depth seam exclusion, or Erdos 257 conclusion"
        ),
    }
    result["canonical_digest"] = canonical_digest(result)
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--horizon", type=int, default=1_350_002)
    parser.add_argument("--crosscheck", type=int, default=300)
    parser.add_argument("--trace-rank", type=int, action="append")
    parser.add_argument("--check-receipt")
    args = parser.parse_args()
    trace_ranks = tuple(args.trace_rank) if args.trace_rank else DEFAULT_TRACE_RANKS
    result = analyze(args.horizon, args.crosscheck, trace_ranks)
    if args.check_receipt:
        with open(args.check_receipt, encoding="utf-8") as handle:
            if receipt_projection(result) != json.load(handle):
                raise SystemExit("receipt mismatch")
    print(json.dumps(receipt_projection(result), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
