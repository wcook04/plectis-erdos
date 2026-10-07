#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Replay the Erdős #257 integer seam orbit to a fixed row and tally resets.

Row s >= 5 uses the weights floor(4^s/(2^d-1)), 2 <= d < s, and the target
2^(2s-1) - 2^s.  Each step classifies the transition from row s to row s+1
as U (upper reset), M (middle reset) or R (right step).  The remainder of
every row is an exact Python integer; the direct row-local greedy is checked
against the recursion through row 100, and a literal set recurrence is
checked through row 2000.

Provenance.  The functions from ``canonical_bytes`` to ``verify_direct`` are
copied unchanged from the maintainer's private probe
``run_erdos257_unbounded_skips_probe.py`` (its recorded 200,000-row receipt
is summarised in ``receipts/seam-orbit-200000.json``).  The loop in
``replay`` follows that probe's loop and hashes the same row and producer
streams.  The reset tally (the square-root target, run lengths, and counts
from row 6) was added on 23 September 2026 for this public copy, because
the program behind the earlier 200,000-row target count was not found.

This is a finite computation.  It proves no statement about every reset
row and does not decide Erdős #257.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from typing import Any, Callable


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        allow_nan=False,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def file_sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def compact_int(n: int) -> dict[str, Any]:
    if n.bit_length() <= 256:
        return {"hex": hex(n), "bit_length": n.bit_length()}
    raw = n.to_bytes((n.bit_length() + 7) // 8, "big")
    return {
        "bit_length": n.bit_length(),
        "sha256": hashlib.sha256(raw).hexdigest(),
        "low64_hex": hex(n & ((1 << 64) - 1)),
    }


def weight(s: int, d: int) -> int:
    return (1 << (2 * s)) // ((1 << d) - 1)


def direct_row(s: int) -> tuple[bytearray, int]:
    support = bytearray(s + 1)
    remainder = (1 << (2 * s - 1)) - (1 << s)
    for d in range(2, s):
        w = weight(s, d)
        if w <= remainder:
            support[d] = 1
            remainder -= w
    return support, remainder


def divisors_between_two_and(n: int, upper_exclusive: int) -> list[int]:
    out: list[int] = []
    for d in range(1, math.isqrt(n) + 1):
        if n % d:
            continue
        q = n // d
        if 2 <= d < upper_exclusive:
            out.append(d)
        if q != d and 2 <= q < upper_exclusive:
            out.append(q)
    return out


def pulse_from_accessor(s: int, selected: Callable[[int], bool]) -> int:
    p1 = sum(
        selected(d) for d in divisors_between_two_and(2 * s + 2, s)
    )
    p2 = sum(
        selected(d) for d in divisors_between_two_and(2 * s + 1, s)
    )
    return p1 + 2 * p2


def exact_adjacent_gap(s: int, d: int) -> int:
    """Return weight(s,d) minus the full suffix d+1,...,s-1."""

    if 3 * d > 2 * s:
        return (1 << (s + 1)) + (2 * (1 << (2 * (s - d))) + 4) // 3
    return weight(s, d) - sum(weight(s, e) for e in range(d + 1, s))


def rightmost_zero(support: bytearray, s: int) -> int:
    d = s - 1
    while d >= 2 and support[d]:
        d -= 1
    if d < 2:
        raise AssertionError((s, "no skipped rank"))
    return d


def successor(
    s: int,
    support: bytearray,
    remainder: int,
    d: int,
) -> tuple[bytearray, int, str, int, dict[str, int]]:
    delta = exact_adjacent_gap(s, d)
    overshoot = delta - remainder
    if overshoot <= 0:
        raise AssertionError(
            (s, "nonpositive adjacent overshoot", delta, remainder)
        )

    below_pulse = pulse_from_accessor(s, lambda e: bool(support[e]))
    above_pulse = pulse_from_accessor(
        s,
        lambda e: bool(support[e]) if e < d else e == d,
    )
    gap = 1 << (s + 1)
    upper_quantity = 4 * overshoot + above_pulse
    middle_quantity = 4 * remainder + gap - below_pulse

    support.append(0)
    if upper_quantity <= gap:
        branch = "U"
        support[d] = 1
        support[d + 1 : s + 1] = b"\x00" * (s - d)
        next_remainder = gap - upper_quantity
        next_d = s
    elif middle_quantity < 2 * gap + 4:
        branch = "M"
        next_remainder = middle_quantity
        next_d = s
    else:
        branch = "R"
        support[s] = 1
        next_remainder = middle_quantity - (2 * gap + 4)
        next_d = d

    return support, next_remainder, branch, next_d, {
        "delta": delta,
        "overshoot": overshoot,
        "below_pulse": below_pulse,
        "above_pulse": above_pulse,
        "upper_quantity": upper_quantity,
        "middle_quantity": middle_quantity,
    }


def verify_direct(
    s: int,
    support: bytearray,
    remainder: int,
) -> None:
    direct_support, direct_remainder = direct_row(s)
    if (
        direct_remainder != remainder
        or direct_support[2:s] != support[2:s]
    ):
        raise AssertionError(
            (s, "direct mismatch", direct_remainder, remainder)
        )


# ---------------------------------------------------------------------------
# Literal reference recurrence (copied unchanged from the same private probe)
# ---------------------------------------------------------------------------

def ref_weight(s: int, d: int) -> int:
    return (1 << (2 * s)) // ((1 << d) - 1)


def ref_direct(s: int) -> tuple[set[int], int]:
    support: set[int] = set()
    remainder = (1 << (2 * s - 1)) - (1 << s)
    for d in range(2, s):
        item_weight = ref_weight(s, d)
        if item_weight <= remainder:
            support.add(d)
            remainder -= item_weight
    return support, remainder


def ref_divisors(n: int, upper: int) -> set[int]:
    out: set[int] = set()
    for d in range(1, math.isqrt(n) + 1):
        if n % d:
            continue
        q = n // d
        if 2 <= d < upper:
            out.add(d)
        if 2 <= q < upper:
            out.add(q)
    return out


def ref_pulse(s: int, support: set[int]) -> int:
    return sum(
        d in support for d in ref_divisors(2 * s + 2, s)
    ) + 2 * sum(
        d in support for d in ref_divisors(2 * s + 1, s)
    )


def ref_successor(
    s: int,
    support: set[int],
    remainder: int,
) -> tuple[set[int], int, str, int]:
    d = s - 1
    while d in support:
        d -= 1
    if d < 2:
        raise AssertionError((s, "reference has no skip"))
    delta = ref_weight(s, d) - sum(
        ref_weight(s, e) for e in range(d + 1, s)
    )
    overshoot = delta - remainder
    above = {e for e in support if e < d} | {d}
    below_pulse = ref_pulse(s, support)
    above_pulse = ref_pulse(s, above)
    gap = 1 << (s + 1)
    upper_quantity = 4 * overshoot + above_pulse
    middle_quantity = 4 * remainder + gap - below_pulse
    if upper_quantity <= gap:
        return above, gap - upper_quantity, "U", s
    if middle_quantity < 2 * gap + 4:
        return set(support), middle_quantity, "M", s
    return (
        set(support) | {s},
        middle_quantity - (2 * gap + 4),
        "R",
        d,
    )


def literal_reference_check(through: int) -> dict[str, Any]:
    """Compare the fast recursion with the literal set recurrence."""

    ref_support, ref_remainder = ref_direct(5)
    fast_support, fast_remainder = direct_row(5)
    fast_d = rightmost_zero(fast_support, 5)
    for s in range(5, through):
        ref_support, ref_remainder, ref_branch, ref_d = ref_successor(
            s, ref_support, ref_remainder
        )
        fast_support, fast_remainder, fast_branch, fast_d, _ = successor(
            s, fast_support, fast_remainder, fast_d
        )
        fast_selected = {d for d in range(2, s + 1) if fast_support[d]}
        if (
            fast_branch != ref_branch
            or fast_d != ref_d
            or fast_remainder != ref_remainder
            or fast_selected != ref_support
        ):
            raise AssertionError((s + 1, "literal reference mismatch"))
    return {"rows": [5, through], "agrees": True}


# ---------------------------------------------------------------------------
# Replay with the reset tally
# ---------------------------------------------------------------------------

def replay(limit: int, direct_through: int, window_end: int) -> dict[str, Any]:
    if limit < 8:
        raise ValueError("limit must be at least 8")
    support, remainder = direct_row(5)
    d = rightmost_zero(support, 5)
    counts_from_row_5 = {"U": 0, "M": 0, "R": 0}
    counts_from_row_6 = {"U": 0, "M": 0, "R": 0}
    counts_window = {"U": 0, "M": 0, "R": 0}
    row_hash = hashlib.sha256()
    producer_hash = hashlib.sha256()
    target_failures: list[dict[str, Any]] = []
    min_margin: float | None = None
    min_margin_row: int | None = None
    last_reset_row: int | None = None
    current_run = 0
    longest_run = 0
    longest_run_reset_row: int | None = None
    last_producer: int | None = None
    max_producer_gap = 0
    max_producer_gap_pair: list[int] | None = None

    for s in range(5, limit + 1):
        if s <= direct_through:
            verify_direct(s, support, remainder)
        actual_d = rightmost_zero(support, s)
        if actual_d != d:
            raise AssertionError((s, "cached rightmost zero", actual_d, d))
        row_hash.update(
            canonical_bytes(
                {
                    "row": s,
                    "rightmost_zero": d,
                    "remainder": compact_int(remainder),
                }
            )
        )
        if s == limit:
            break

        support, next_remainder, branch, next_d, details = successor(
            s, support, remainder, d
        )
        counts_from_row_5[branch] += 1
        if s >= 6:
            counts_from_row_6[branch] += 1
        if 6 <= s < window_end:
            counts_window[branch] += 1

        if branch == "R":
            current_run += 1
            if current_run > longest_run:
                longest_run = current_run
                longest_run_reset_row = last_reset_row
        else:
            current_run = 0
            packet = {
                "producer_row": s,
                "branch": branch,
                "next_row": s + 1,
                "next_largest_skipped_rank": next_d,
                "next_rank_equals_producer_row": next_d == s,
                "remainder": compact_int(remainder),
                "adjacent_gap": compact_int(details["delta"]),
                "below_pulse": details["below_pulse"],
                "above_pulse": details["above_pulse"],
            }
            producer_hash.update(canonical_bytes(packet))
            if last_producer is not None and s - last_producer > max_producer_gap:
                max_producer_gap = s - last_producer
                max_producer_gap_pair = [last_producer, s]
            last_producer = s
            last_reset_row = s
            # Reset at row r = s: deviation Delta_{r+1} = rem(r+1) - 2^(r+1).
            deviation = next_remainder - (1 << (s + 1))
            if deviation * deviation <= 1 << (s + 5):
                target_failures.append(
                    {"reset_row": s, "branch": branch, "deviation": deviation}
                )
            if s >= 14 and deviation != 0:
                bits = abs(deviation).bit_length()
                top = abs(deviation) >> max(0, bits - 60)
                log2_abs = math.log2(top) + max(0, bits - 60)
                margin = log2_abs - (s + 5) / 2
                if min_margin is None or margin < min_margin:
                    min_margin = margin
                    min_margin_row = s

        remainder = next_remainder
        d = next_d

    return {
        "rows": [5, limit],
        "direct_definition_checked_through": min(limit, direct_through),
        "branch_counts_rows_5_to_limit": counts_from_row_5,
        "branch_counts_rows_6_to_limit": counts_from_row_6,
        "branch_counts_rows_6_to_window_end": {
            "window_end": window_end,
            **counts_window,
        },
        "target_inequality": "Delta_(r+1)^2 > 2^(r+5) at every U or M reset row r",
        "target_failures": target_failures,
        "minimum_log2_margin_rows_14_up": min_margin,
        "minimum_log2_margin_row": min_margin_row,
        "longest_right_run": longest_run,
        "reset_row_before_first_longest_run": longest_run_reset_row,
        "max_gap_between_resets": max_producer_gap,
        "max_gap_pair": max_producer_gap_pair,
        "final_state": {
            "row": limit,
            "largest_skipped_rank": d,
            "remainder": compact_int(remainder),
        },
        "row_stream_sha256": row_hash.hexdigest(),
        "producer_stream_sha256": producer_hash.hexdigest(),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--limit", type=int, default=200_000,
                        help="last row replayed (default 200000)")
    parser.add_argument("--direct-through", type=int, default=100,
                        help="check the recursion against the direct row greedy through this row")
    parser.add_argument("--literal-through", type=int, default=2000,
                        help="check against the literal set recurrence through this row")
    parser.add_argument("--window-end", type=int, default=2500,
                        help="also count transitions from rows 6 up to this row")
    args = parser.parse_args()
    if args.direct_through < 5 or args.literal_through < 6 or args.window_end < 7:
        parser.error("check ranges start at row 5 or later")
    result = {
        "probe": "erdos257_seam_orbit_replay",
        "literal_reference": literal_reference_check(min(args.literal_through, args.limit)),
        **replay(args.limit, args.direct_through, args.window_end),
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
