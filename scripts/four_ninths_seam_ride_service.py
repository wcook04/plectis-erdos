#!/usr/bin/env python3
"""Measure service into multiplicative escape on exact 4/9 seam rides.

For a minimal suffix interval crossing its highest dyadic boundary, let ``x``
be the distance from that boundary to the upper endpoint.  On a two-row step
with no common-prefix strip, the exact recurrence is

    x' = 4*x + C.

For positive ``x``, the condition ``C >= -2*x`` forces ``x' >= 2*x``; at
``x = 0`` one additionally needs ``C >= 1`` to leave the zero trap.  Thus the
uniform escape-service condition is ``x' >= max(1, 2*x)``.  A consecutive
service tail cannot stay inside the linear carry corridor for more than
logarithmically many steps.  This script finds the last failure of that
condition in every maximal no-strip ride.  It tests a proof-sized mechanism;
a finite pass does not prove a uniform bound or resolve Erdos 257.
"""

from __future__ import annotations

import argparse
import hashlib
import json
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


def canonical_digest(value: object) -> str:
    data = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(data).hexdigest()


def receipt_projection(result: dict[str, Any]) -> dict[str, Any]:
    """The result is already a compact projection of the streamed census."""

    return result


def tail_start(offsets: list[int], factor: int) -> int:
    """First transition in the final tail satisfying x[k+1] >= factor*x[k]."""

    last_failure = -1
    for index, (before, after) in enumerate(zip(offsets, offsets[1:])):
        if after < factor * before:
            last_failure = index
    return last_failure + 1


def escape_tail_start(offsets: list[int]) -> int:
    """Final tail satisfying x[k+1] >= max(1, 2*x[k])."""

    last_failure = -1
    for index, (before, after) in enumerate(zip(offsets, offsets[1:])):
        if after < max(1, 2 * before):
            last_failure = index
    return last_failure + 1


def strict_growth_tail_start(offsets: list[int]) -> int:
    last_failure = -1
    for index, (before, after) in enumerate(zip(offsets, offsets[1:])):
        if after <= before:
            last_failure = index
    return last_failure + 1


def analyze(horizon: int, crosscheck: int) -> dict[str, Any]:
    if horizon < 100 or horizon % 2:
        raise ValueError("--horizon must be an even integer at least 100")
    if crosscheck < 6 or crosscheck % 2 or crosscheck > horizon:
        raise ValueError("--crosscheck must be even and lie in [6,horizon]")

    snapshots = full_prefix_dp(crosscheck)
    prefix_word, prefix_length, suffix_length, suffix_top = initialize_cylinder(
        snapshots
    )
    divisor_load = array("H", [0]) * (horizon + 3)

    def fix_rank(rank: int, bit: int) -> None:
        if bit:
            for multiple in range(2 * rank, horizon + 3, rank):
                divisor_load[multiple] += 1

    for rank in range(1, prefix_length + 1):
        fix_rank(rank, (prefix_word >> (rank - 1)) & 1)

    def state_offset() -> int:
        if suffix_length <= 0:
            raise AssertionError(("empty suffix", rank))
        boundary = 1 << (suffix_length - 1)
        bottom = suffix_top - raw_carry(rank)
        if not (bottom < boundary <= suffix_top):
            raise AssertionError(("nonminimal suffix", rank, bottom, boundary, suffix_top))
        return suffix_top - boundary

    active: dict[str, Any] | None = None
    trace = hashlib.sha256()
    run_trace = hashlib.sha256()
    run_count = 0
    extreme_runs: dict[str, dict[str, Any]] = {}
    strip_reset_count = 0
    maximum_strip_reset: tuple[int, int, int] | None = None
    maximum_post_strip_width: tuple[int, int, int, int] | None = None
    maximum_burden: tuple[int, int, int, int] | None = None

    def finish_run(run: dict[str, Any], end_rank: int) -> None:
        nonlocal run_count
        run["end_rank"] = end_rank
        offsets = run["offsets"]
        run["length"] = len(run["corrections"])
        run["strict_growth_tail_start"] = strict_growth_tail_start(offsets)
        run["doubling_tail_start"] = tail_start(offsets, 2)
        run["escape_tail_start"] = escape_tail_start(offsets)
        run["tripling_tail_start"] = tail_start(offsets, 3)
        run["doubling_tail_length"] = run["length"] - run["doubling_tail_start"]
        run["escape_tail_length"] = run["length"] - run["escape_tail_start"]
        run["maximum_offset"] = max(offsets)
        run_count += 1
        run_trace.update(
            json.dumps(run, sort_keys=True, separators=(",", ":")).encode()
        )
        for field in (
            "length",
            "strict_growth_tail_start",
            "doubling_tail_start",
            "escape_tail_start",
            "tripling_tail_start",
            "doubling_tail_length",
            "escape_tail_length",
        ):
            old = extreme_runs.get(field)
            score = (run[field], run["length"], -run["start_rank"])
            old_score = (
                (old[field], old["length"], -old["start_rank"])
                if old is not None
                else None
            )
            if old_score is None or score > old_score:
                extreme_runs[field] = run.copy()

    rank = 6
    current_offset = state_offset()
    while rank < horizon:
        source_rank = rank
        old_offset = current_offset
        g1, g2 = divisor_load[rank + 1], divisor_load[rank + 2]
        c1 = target_bit(rank + 1) - g1
        c2 = target_bit(rank + 2) - g2
        correction = 2 * c1 + c2
        next_carry = raw_carry(rank + 2)
        next_top = 4 * suffix_top + correction
        next_width = suffix_length + 2
        bottom = next_top - next_carry
        if not (0 <= bottom <= next_top < 1 << next_width):
            raise AssertionError((rank, suffix_length, suffix_top, correction))

        difference = next_top ^ bottom
        common = next_width - (difference.bit_length() if difference else 0)
        raw_offset = 4 * old_offset + correction
        trace.update(
            f"{rank + 2}:{old_offset}:{correction}:{raw_offset}:{common};".encode()
        )

        if common == 0:
            if not (0 <= raw_offset < next_carry):
                raise AssertionError(("bad no-strip offset", rank, raw_offset, next_carry))
            if active is None:
                active = {
                    "start_rank": source_rank,
                    "starting_width": suffix_length,
                    "offsets": [old_offset],
                    "corrections": [],
                    "odd_loads": [],
                    "even_loads": [],
                }
            active["offsets"].append(raw_offset)
            active["corrections"].append(correction)
            active["odd_loads"].append(g1)
            active["even_loads"].append(g2)

            burden = max(1, 2 * old_offset) - raw_offset
            if maximum_burden is None or burden > maximum_burden[0]:
                maximum_burden = (burden, source_rank, old_offset, correction)
        elif active is not None:
            finish_run(active, source_rank)
            active = None

        for offset in range(common):
            bit = (next_top >> (next_width - 1 - offset)) & 1
            prefix_length += 1
            fix_rank(prefix_length, bit)
        next_width -= common
        suffix_length = next_width
        suffix_top = next_top & ((1 << suffix_length) - 1 if suffix_length else 0)
        rank += 2
        current_offset = state_offset()

        if common > 0:
            strip_reset_count += 1
            if maximum_strip_reset is None or current_offset > maximum_strip_reset[2]:
                maximum_strip_reset = (rank, common, current_offset)
            if maximum_post_strip_width is None or suffix_length > maximum_post_strip_width[1]:
                maximum_post_strip_width = (
                    rank,
                    suffix_length,
                    common,
                    current_offset,
                )

        if prefix_length < rank // 2 + 1:
            raise AssertionError(("first midpoint seam", rank, prefix_length, suffix_length))
        if rank <= crosscheck:
            expected_carry, expected = snapshots[rank]
            if expected_carry != next_carry or set(expected) != set(range(next_carry + 1)):
                raise AssertionError(("crosscheck", rank))

    if active is not None:
        finish_run(active, rank)

    if (
        not run_count
        or maximum_burden is None
        or maximum_strip_reset is None
        or maximum_post_strip_width is None
    ):
        raise AssertionError("insufficient ride data")

    longest = extreme_runs["length"]
    worst_strict = extreme_runs["strict_growth_tail_start"]
    worst_double = extreme_runs["doubling_tail_start"]
    worst_escape = extreme_runs["escape_tail_start"]
    worst_triple = extreme_runs["tripling_tail_start"]
    longest_double_tail = extreme_runs["doubling_tail_length"]
    longest_escape_tail = extreme_runs["escape_tail_length"]

    def witness(run: dict[str, Any]) -> dict[str, Any]:
        return {
            "start_rank": run["start_rank"],
            "end_rank": run["end_rank"],
            "length": run["length"],
            "starting_width": run["starting_width"],
            "offsets": run["offsets"],
            "corrections": run["corrections"],
            "odd_loads": run["odd_loads"],
            "even_loads": run["even_loads"],
            "strict_growth_tail_start": run["strict_growth_tail_start"],
            "doubling_tail_start": run["doubling_tail_start"],
            "escape_tail_start": run["escape_tail_start"],
            "tripling_tail_start": run["tripling_tail_start"],
        }

    observed_stall_bound = worst_escape["escape_tail_start"]
    result: dict[str, Any] = {
        "schema": "erdos257_four_ninths_seam_ride_service_v0",
        "parameters": {"horizon": horizon, "crosscheck": crosscheck},
        "source": {
            "existing_cylinder_audit": str(AUDIT_PATH.relative_to(SCRIPT_PATH.parents[2])),
            "existing_cylinder_audit_sha256": hashlib.sha256(AUDIT_PATH.read_bytes()).hexdigest(),
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
            "boundary_below_top": current_offset,
        },
        "census": {
            "maximal_no_strip_ride_count": run_count,
            "nonzero_strip_count": strip_reset_count,
            "run_census_sha256": run_trace.hexdigest(),
        },
        "extremes": {
            "maximum_ride_length": longest["length"],
            "maximum_strict_growth_stall_prefix": worst_strict["strict_growth_tail_start"],
            "maximum_doubling_stall_prefix": worst_double["doubling_tail_start"],
            "maximum_escape_stall_prefix": observed_stall_bound,
            "maximum_tripling_stall_prefix": worst_triple["tripling_tail_start"],
            "maximum_doubling_tail_length": longest_double_tail["doubling_tail_length"],
            "maximum_escape_tail_length": longest_escape_tail["escape_tail_length"],
            "maximum_escape_service_deficit": {
                "value": maximum_burden[0],
                "rank": maximum_burden[1],
                "offset": maximum_burden[2],
                "correction": maximum_burden[3],
            },
            "maximum_post_strip_reset_offset": {
                "rank": maximum_strip_reset[0],
                "common_bits_stripped": maximum_strip_reset[1],
                "offset": maximum_strip_reset[2],
            },
            "maximum_post_strip_width": {
                "rank": maximum_post_strip_width[0],
                "width": maximum_post_strip_width[1],
                "common_bits_stripped": maximum_post_strip_width[2],
                "offset": maximum_post_strip_width[3],
            },
        },
        "witnesses": {
            "worst_escape_stall": witness(worst_escape),
            "longest_escape_tail": witness(longest_escape_tail),
        },
        "mechanism_decision": {
            "candidate": (
                "prove a uniform bound on the number of initial no-strip steps "
                "before x' >= max(1,2*x) holds forever on that ride"
            ),
            "observed_stall_bound": observed_stall_bound,
            "one_way_effect": (
                "a uniform stall bound plus the linear carry corridor bounds every "
                "no-strip ride by O(log n), reducing the 4/9 seam theorem to the "
                "already elementary post-strip reset geometry"
            ),
            "status": "finite_service_target_opened",
            "stop_condition": (
                "prove or exactly falsify the bounded-stall service statement; "
                "do not extend the horizon without a structural service lemma"
            ),
        },
        "claim_ceiling": (
            "exact finite service census for the existing 4/9 cylinder; no uniform "
            "stall bound, all-depth seam exclusion, or Erdos 257 conclusion"
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
