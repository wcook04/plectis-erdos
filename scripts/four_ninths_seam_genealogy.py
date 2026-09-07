#!/usr/bin/env python3
"""Trace exact record genealogies in the 4/9 even-cylinder recurrence.

The existing cylinder audit proves finite exact transport while its midpoint
seam remains closed.  This companion does not extend that claim.  It records
which correction words create new suffix-width records, so bounded-memory
seam arguments can be proved or killed by exact witnesses.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from array import array
from collections import deque
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


def canonical_digest(value: object) -> str:
    data = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(data).hexdigest()


def receipt_projection(result: dict[str, Any]) -> dict[str, Any]:
    """Compact durable projection; full record lists remain reproducible."""

    omitted = {"suffix_width_records"}
    return {key: value for key, value in result.items() if key not in omitted}


def analyze(horizon: int, crosscheck: int) -> dict[str, Any]:
    if horizon < 100 or horizon % 2:
        raise ValueError("--horizon must be an even integer at least 100")
    if crosscheck < 6 or crosscheck % 2 or crosscheck > horizon:
        raise ValueError("--crosscheck must be even and lie in [6,horizon]")

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

    recent: deque[dict[str, int]] = deque(maxlen=256)
    width_records: list[dict[str, Any]] = []
    no_strip_records: list[dict[str, int]] = []
    max_width = suffix_length
    no_strip_run = 0
    max_no_strip_run = 0
    max_post_strip_width = 0
    max_log_excess: tuple[int, int, int] | None = None
    log_excess_records: list[dict[str, int]] = []
    common_strip_total = 0
    zero_common_count = 0
    correction_min: tuple[int, int] | None = None
    correction_max: tuple[int, int] | None = None
    trace = hashlib.sha256()

    rank = 6
    while rank < horizon:
        carry = raw_carry(rank)
        g1, g2 = divisor_load[rank + 1], divisor_load[rank + 2]
        c1 = target_bit(rank + 1) - g1
        c2 = target_bit(rank + 2) - g2
        correction = 2 * c1 + c2
        next_carry = raw_carry(rank + 2)
        next_top = 4 * suffix_top + correction
        next_width = suffix_length + 2
        if not (0 <= next_top - next_carry <= next_top < 1 << next_width):
            raise AssertionError((rank, suffix_length, suffix_top, correction))

        bottom = next_top - next_carry
        difference = next_top ^ bottom
        common = next_width - (difference.bit_length() if difference else 0)
        common_strip_total += common
        if common == 0:
            no_strip_run += 1
            zero_common_count += 1
        else:
            no_strip_run = 0

        for offset in range(common):
            bit = (next_top >> (next_width - 1 - offset)) & 1
            prefix_length += 1
            fix_rank(prefix_length, bit)
        next_width -= common
        suffix_length = next_width
        suffix_top = next_top & ((1 << suffix_length) - 1 if suffix_length else 0)
        rank += 2

        row = {
            "rank": rank,
            "width": suffix_length,
            "common_bits_stripped": common,
            "no_strip_run": no_strip_run,
            "correction": correction,
            "odd_load": g1,
            "even_load": g2,
            "carry": next_carry,
        }
        recent.append(row)
        trace.update(
            f"{rank}:{suffix_length}:{common}:{correction}:{g1}:{g2};".encode()
        )

        if correction_min is None or correction < correction_min[0]:
            correction_min = (correction, rank)
        if correction_max is None or correction > correction_max[0]:
            correction_max = (correction, rank)

        if common > 0:
            max_post_strip_width = max(max_post_strip_width, suffix_length)

        log_excess = suffix_length - 2 * rank.bit_length()
        if max_log_excess is None or log_excess > max_log_excess[0]:
            max_log_excess = (log_excess, rank, suffix_length)
            log_excess_records.append(
                {
                    "rank": rank,
                    "suffix_width": suffix_length,
                    "twice_rank_bit_length": 2 * rank.bit_length(),
                    "excess": log_excess,
                }
            )

        if no_strip_run > max_no_strip_run:
            max_no_strip_run = no_strip_run
            no_strip_records.append(
                {
                    "rank": rank,
                    "run_length": no_strip_run,
                    "suffix_width": suffix_length,
                }
            )

        if suffix_length > max_width:
            max_width = suffix_length
            boundary = 1 << (suffix_length - 1)
            reduced_bottom = suffix_top - next_carry
            if not (reduced_bottom < boundary <= suffix_top):
                raise AssertionError((rank, reduced_bottom, boundary, suffix_top))
            width_records.append(
                {
                    "rank": rank,
                    "suffix_width": suffix_length,
                    "carry": next_carry,
                    "boundary_below_top": suffix_top - boundary,
                    "boundary_above_bottom": boundary - reduced_bottom,
                    "no_strip_run": no_strip_run,
                    "correction_tail": list(recent)[-max(1, no_strip_run) :],
                }
            )

        if prefix_length < rank // 2 + 1:
            raise AssertionError(
                ("first midpoint seam", rank, prefix_length, suffix_length)
            )

        if rank <= crosscheck:
            expected_carry, expected = snapshots[rank]
            if expected_carry != next_carry or set(expected) != set(range(next_carry + 1)):
                raise AssertionError(("crosscheck", rank))

    assert correction_min is not None and correction_max is not None
    assert max_log_excess is not None
    key_ranks = {width_records[-1]["rank"], no_strip_records[-1]["rank"]}
    key_genealogies = []
    for row in width_records:
        if row["rank"] not in key_ranks:
            continue
        tail = row["correction_tail"]
        key_genealogies.append(
            {
                "rank": row["rank"],
                "suffix_width": row["suffix_width"],
                "starting_width": tail[0]["width"] - 2,
                "no_strip_run": row["no_strip_run"],
                "carry": row["carry"],
                "boundary_below_top": row["boundary_below_top"],
                "boundary_above_bottom": row["boundary_above_bottom"],
                "corrections": [item["correction"] for item in tail],
                "odd_loads": [item["odd_load"] for item in tail],
                "even_loads": [item["even_load"] for item in tail],
            }
        )
    width_record_summaries = [
        {key: value for key, value in row.items() if key != "correction_tail"}
        for row in width_records
    ]
    mechanism = {
        "candidate": "prove suffix_width <= 2*bit_length(rank)+5",
        "one_way_effect": (
            "this logarithmic envelope is eventually below rank/2, so it "
            "excludes the midpoint seam and inducts the 4/9 cylinder forever"
        ),
        "observed_maximum_no_strip_run": max_no_strip_run,
        "observed_log_envelope_constant": max_log_excess[0],
        "status": "finite_proof_target_opened",
        "stop_condition": (
            "seek an analytic correction-word proof of the logarithmic envelope; "
            "do not extend the horizon without a proposed smaller constant or a falsifier"
        ),
    }
    result: dict[str, Any] = {
        "schema": "erdos257_four_ninths_seam_genealogy_v0",
        "parameters": {"horizon": horizon, "crosscheck": crosscheck},
        "source": {
            "existing_cylinder_audit": str(AUDIT_PATH.relative_to(SCRIPT_PATH.parents[3])),
            "existing_cylinder_audit_sha256": hashlib.sha256(
                AUDIT_PATH.read_bytes()
            ).hexdigest(),
        },
        "validation": {
            "exact_integer_recurrence": True,
            "full_prefix_crosscheck": True,
            "midpoint_seam_seen": False,
            "trace_sha256": trace.hexdigest(),
        },
        "terminal": {
            "rank": rank,
            "prefix_length": prefix_length,
            "suffix_width": suffix_length,
        },
        "extremes": {
            "maximum_suffix_width": max_width,
            "maximum_no_strip_run": max_no_strip_run,
            "maximum_post_strip_width": max_post_strip_width,
            "maximum_log_envelope_excess": {
                "value": max_log_excess[0],
                "rank": max_log_excess[1],
                "suffix_width": max_log_excess[2],
            },
            "zero_common_strip_step_count": zero_common_count,
            "common_bits_stripped_total": common_strip_total,
            "minimum_correction": {"value": correction_min[0], "rank": correction_min[1]},
            "maximum_correction": {"value": correction_max[0], "rank": correction_max[1]},
        },
        "suffix_width_records": width_record_summaries,
        "no_strip_run_records": no_strip_records,
        "log_envelope_excess_records": log_excess_records,
        "key_correction_genealogies": key_genealogies,
        "mechanism_decision": mechanism,
        "claim_ceiling": (
            "exact finite genealogy of the existing 4/9 cylinder; no all-depth "
            "seam exclusion, rational representation, or Erdos 257 conclusion"
        ),
    }
    result["canonical_digest"] = canonical_digest(result)
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--horizon", type=int, default=10_000_000)
    parser.add_argument("--crosscheck", type=int, default=300)
    parser.add_argument("--check-receipt")
    args = parser.parse_args()
    result = analyze(args.horizon, args.crosscheck)
    if args.check_receipt:
        with open(args.check_receipt, encoding="utf-8") as handle:
            expected = json.load(handle)
        if receipt_projection(result) != expected:
            raise SystemExit("receipt mismatch")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
