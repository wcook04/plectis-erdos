#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Certify a finite greedy-1/2 orbit and its reduced-prefix gap invariant.

For the greedy remainder

    r_n = 1/2 - sum_{m <= n, selected} 1/(2^m - 1),

put ``s_n = 2^n r_n``.  Before rank ``m = n + 1`` the exact update is

    s_m = 2 s_n                                      (skip),
    s_m = 2 s_n - 1 - 1/(2^m - 1)                  (take).

For ``n >= 1``, the reduced-prefix coordinates in
``DyadicPrefixCompression.lean`` satisfy

    E_n <= 0  <->  s_n <= 1/2,
    E_n >= p_n <->  s_n >= 1/2 + 1/(2(2^n - 1)).

This runner uses integer lower and upper bounds at a fixed binary scale.  It
independently replays the greedy decisions, certifies the tail comparison,
audits the Boolean carry, and checks that every replayed state lies on the
appropriate side of the forbidden reduced-prefix gap.  The default run also
byte-compares the selected-index digest with the imported 100,000-rank Type B
receipt.  It is a finite computation receipt, not a proof of the universal
Erdos #257 statement.

Public copy (23 September 2026): the numerical algorithm is unchanged.  Only
the two default file locations below were moved from the private working tree
to this directory.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from collections import deque
from fractions import Fraction
from pathlib import Path
from typing import Any


HERE = Path(__file__).resolve().parent
IMPORTED_RECEIPT = HERE / "receipts" / "greedy-half-stream-100000.json"
OUT_PATH = HERE / "greedy-interval-report.json"
SCHEMA = "erdos257_greedy_interval_gap_receipt_v1"


def scaled_reciprocal_bounds(bits: int, rank: int) -> tuple[int, int]:
    """Return inclusive bounds for ``2^bits / (2^rank - 1)``.

    For ``rank > 1`` the lower endpoint is the exact floor and the upper
    endpoint is floor plus one.  The repunit formula avoids constructing a
    general rational number.
    """

    if bits < 1 or not 1 <= rank <= bits:
        raise ValueError("require bits >= 1 and 1 <= rank <= bits")
    scale = 1 << bits
    if rank == 1:
        return scale, scale

    blocks, remainder = divmod(bits, rank)
    if blocks <= 8:
        floor = sum(1 << (bits - k * rank) for k in range(1, blocks + 1))
    else:
        repunit = ((1 << (blocks * rank)) - 1) // ((1 << rank) - 1)
        floor = repunit << remainder
    return floor, floor + 1


def _exact_remainder_before_rank(rank: int) -> Fraction:
    """Replay exactly through ``rank - 1``; used only for early equalities."""

    remainder = Fraction(1, 2)
    for prior_rank in range(1, rank):
        weight = Fraction(1, (1 << prior_rank) - 1)
        if weight <= remainder:
            remainder -= weight
    return remainder


def _exact_branch(rank: int) -> bool:
    remainder = _exact_remainder_before_rank(rank)
    return Fraction(1, (1 << rank) - 1) <= remainder


def _ceil_four_sqrt_plus_eight(n: int) -> int:
    floor = math.isqrt(16 * n)
    return floor + int(floor * floor < 16 * n) + 8


def _payload_sha256(payload: dict[str, Any]) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(canonical).hexdigest()


def _comparison_receipt(
    report: dict[str, Any], imported: dict[str, Any] | None
) -> dict[str, Any]:
    if imported is None:
        return {"status": "not_requested", "checks": {}}

    parameters = report["parameters"]
    applicable = (
        imported.get("certified_through") == parameters["horizon"]
        and imported.get("bits") == parameters["precision_bits"]
        and imported.get("cutoff") == parameters["tail_cutoff"]
    )
    if not applicable:
        return {
            "status": "inapplicable_parameter_mismatch",
            "expected": {
                "certified_through": imported.get("certified_through"),
                "bits": imported.get("bits"),
                "cutoff": imported.get("cutoff"),
            },
            "checks": {},
        }

    summary = report["summary"]
    carry = report["boolean_carry"]
    checks = {
        "status_survives": imported.get("status") == "survives",
        "selected_count": imported.get("selected_count") == summary["takes"],
        "selected_sequence_sha256": imported.get("selected_sequence_sha256")
        == summary["selected_sequence_sha256"],
        "selected_prefix": imported.get("selected_prefix")
        == summary["selected_prefix"],
        "selected_suffix": imported.get("selected_suffix")
        == summary["selected_suffix"],
        "boolean_carry_min_U": imported.get("boolean_carry_min_U")
        == carry["min_U"],
        "boolean_carry_max_U": imported.get("boolean_carry_max_U")
        == carry["max_U"],
        "boolean_carry_max_U_level": imported.get("boolean_carry_max_U_level")
        == carry["max_U_level"],
    }
    return {
        "status": "matched" if all(checks.values()) else "mismatch",
        "source_schema": imported.get("schema"),
        "source_payload_sha256": _payload_sha256(imported),
        "checks": checks,
    }


def build_report(
    horizon: int,
    bits: int,
    cutoff: int,
    *,
    exact_resolution_limit: int = 4096,
    imported_receipt: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Build one exact finite replay receipt."""

    if not 1 <= horizon <= cutoff <= bits:
        raise ValueError("require 1 <= horizon <= cutoff <= bits")
    if exact_resolution_limit < 1:
        raise ValueError("exact_resolution_limit must be positive")

    scale = 1 << bits
    half = 1 << (bits - 1)

    # Enclose the complete reciprocal tail after each decision.  The omitted
    # tail past cutoff is less than 2^(1-cutoff).
    tail_lower = 0
    tail_upper = 0
    for rank in range(1, cutoff + 1):
        weight_lower, weight_upper = scaled_reciprocal_bounds(bits, rank)
        tail_lower += weight_lower
        tail_upper += weight_upper
    omitted_tail_exponent = bits + 1 - cutoff
    tail_upper += (
        1 << omitted_tail_exponent if omitted_tail_exponent >= 0 else 1
    )

    # r_* is the unscaled greedy remainder interval.  s_* is the independently
    # propagated interval for s_n = 2^n r_n, needed at the exponentially narrow
    # reduced-prefix thresholds.
    remainder_lower = remainder_upper = half
    state_lower = state_upper = half
    previous_weight_bounds: tuple[int, int] | None = None

    decision_digest = hashlib.sha256()
    selected_digest = hashlib.sha256()
    selected: list[int] = []
    selected_prefix: list[int] = []
    selected_suffix: deque[int] = deque(maxlen=32)

    unresolved_branches: list[int] = []
    exact_resolved_branches: list[int] = []
    unsafe_skips: list[int] = []
    unresolved_skip_signs: list[int] = []
    exact_skip_equalities: list[int] = []
    exact_skip_strict: list[int] = []
    weak_takes: list[int] = []
    unresolved_take_strength: list[int] = []
    exact_take_equalities: list[int] = []
    exact_take_strict: list[int] = []

    tightest_decision: tuple[int, int, str] | None = None
    tightest_tail: tuple[int, int] | None = None
    status = "survives"
    certified_through = 0

    for rank in range(1, horizon + 1):
        weight_lower, weight_upper = scaled_reciprocal_bounds(bits, rank)
        tail_lower -= weight_upper
        tail_upper -= weight_lower

        if remainder_lower >= weight_upper:
            take = True
            decision_separation = remainder_lower - weight_upper
        elif remainder_upper < weight_lower:
            take = False
            decision_separation = weight_lower - remainder_upper
        elif rank <= exact_resolution_limit:
            take = _exact_branch(rank)
            exact_resolved_branches.append(rank)
            decision_separation = 0
        else:
            unresolved_branches.append(rank)
            status = "ambiguous_selection"
            break

        if (
            tightest_decision is None
            or decision_separation < tightest_decision[0]
        ):
            tightest_decision = (decision_separation, rank, "take" if take else "skip")

        decision_digest.update(b"1" if take else b"0")
        if take:
            if selected:
                selected_digest.update(b",")
            selected_digest.update(str(rank).encode("ascii"))
            selected.append(rank)
            if len(selected_prefix) < 64:
                selected_prefix.append(rank)
            selected_suffix.append(rank)

            # At state n=rank-1, E_n >= p_n is the displayed inequality.
            if rank == 1:
                weak_takes.append(rank)
            else:
                assert previous_weight_bounds is not None
                prior_lower, prior_upper = previous_weight_bounds
                if 2 * state_lower >= scale + prior_upper:
                    pass
                elif 2 * state_upper < scale + prior_lower:
                    weak_takes.append(rank)
                elif rank <= exact_resolution_limit:
                    exact_remainder = _exact_remainder_before_rank(rank)
                    threshold = Fraction(1, 2 * ((1 << (rank - 1)) - 1))
                    if exact_remainder == threshold:
                        exact_take_equalities.append(rank)
                    elif exact_remainder > threshold:
                        exact_take_strict.append(rank)
                    else:
                        weak_takes.append(rank)
                else:
                    unresolved_take_strength.append(rank)

            remainder_lower, remainder_upper = (
                remainder_lower - weight_upper,
                remainder_upper - weight_lower,
            )
            state_lower, state_upper = (
                2 * state_lower - scale - weight_upper,
                2 * state_upper - scale - weight_lower,
            )
        else:
            # At state n=rank-1, E_n <= 0 iff s_n <= 1/2.
            if state_upper <= half:
                pass
            elif state_lower > half:
                unsafe_skips.append(rank)
            elif rank <= exact_resolution_limit:
                exact_remainder = _exact_remainder_before_rank(rank)
                exact_state = (1 << (rank - 1)) * exact_remainder
                if exact_state == Fraction(1, 2):
                    exact_skip_equalities.append(rank)
                elif exact_state < Fraction(1, 2):
                    exact_skip_strict.append(rank)
                else:
                    unsafe_skips.append(rank)
            else:
                unresolved_skip_signs.append(rank)

            state_lower, state_upper = 2 * state_lower, 2 * state_upper

        certified_through = rank
        if remainder_lower > tail_upper:
            status = "death"
            break
        if remainder_upper > tail_lower:
            status = "ambiguous_tail_comparison"
            break

        tail_gap = tail_lower - remainder_upper
        if tightest_tail is None or tail_gap < tightest_tail[0]:
            tightest_tail = (tail_gap, rank)

        previous_weight_bounds = (weight_lower, weight_upper)

    divisor_counts = [0] * (certified_through + 1)
    for chosen_rank in selected:
        for multiple in range(chosen_rank, certified_through + 1, chosen_rank):
            divisor_counts[multiple] += 1

    carry = 1
    carry_min: int | None = None
    carry_max: int | None = None
    carry_max_level = 0
    carry_positive_even = True
    carry_bound = True
    for rank in range(1, certified_through + 1):
        carry = 2 * carry - 2 * divisor_counts[rank]
        carry_positive_even = carry_positive_even and carry > 0 and carry % 2 == 0
        carry_bound = carry_bound and carry <= _ceil_four_sqrt_plus_eight(rank)
        carry_min = carry if carry_min is None else min(carry_min, carry)
        if carry_max is None or carry > carry_max:
            carry_max = carry
            carry_max_level = rank

    summary = {
        "certified_through": certified_through,
        "takes": len(selected),
        "skips": certified_through - len(selected),
        "selected_density": len(selected) / certified_through
        if certified_through
        else 0.0,
        "selected_prefix": selected_prefix,
        "selected_suffix": list(selected_suffix),
        "selected_sequence_sha256": selected_digest.hexdigest(),
        "decision_bit_sha256": decision_digest.hexdigest(),
    }
    gap_invariant = {
        "state_range": (
            f"n = 0 satisfies the low branch; 1 <= n < {certified_through} "
            "satisfies the displayed dichotomy"
        ),
        "statement": (
            "for n >= 1: s_n <= 1/2 or "
            "s_n >= 1/2 + 1/(2*(2^n-1)); "
            "equivalently E_n <= 0 or E_n >= p_n"
        ),
        "unsafe_skip_ranks": unsafe_skips,
        "weak_take_ranks": weak_takes,
        "unresolved_skip_sign_ranks": unresolved_skip_signs,
        "unresolved_take_strength_ranks": unresolved_take_strength,
        "exact_skip_equalities": exact_skip_equalities,
        "exact_skip_strict_resolutions": exact_skip_strict,
        "exact_take_equalities": exact_take_equalities,
        "exact_take_strict_resolutions": exact_take_strict,
    }
    checks = {
        "full_horizon_replayed": certified_through == horizon,
        "survives_tail_comparison": status == "survives",
        "all_greedy_branches_resolved": not unresolved_branches,
        "no_unsafe_skips": not unsafe_skips and not unresolved_skip_signs,
        "no_weak_takes": not weak_takes and not unresolved_take_strength,
        "decision_partition": len(selected) + (certified_through - len(selected))
        == certified_through,
        "boolean_carry_positive_even": carry_positive_even,
        "boolean_carry_sqrt_bound": carry_bound,
    }
    report: dict[str, Any] = {
        "schema": SCHEMA,
        "claim_ceiling": (
            "finite exact interval/carry receipt only; it does not prove the "
            "universal actual-history gap invariant or Erdos #257"
        ),
        "parameters": {
            "horizon": horizon,
            "precision_bits": bits,
            "tail_cutoff": cutoff,
            "guard_bits": bits - horizon,
            "exact_resolution_limit": exact_resolution_limit,
        },
        "status": status,
        "summary": summary,
        "gap_invariant": gap_invariant,
        "interval_receipt": {
            "unresolved_branch_ranks": unresolved_branches,
            "exact_resolved_branch_ranks": exact_resolved_branches,
            "final_state_interval_width_bits": (state_upper - state_lower).bit_length(),
            "tightest_decision_level": tightest_decision[1]
            if tightest_decision
            else None,
            "tightest_decision": tightest_decision[2]
            if tightest_decision
            else None,
            "tightest_decision_gap_scaled_bit_length": tightest_decision[
                0
            ].bit_length()
            if tightest_decision
            else None,
            "tightest_tail_level": tightest_tail[1] if tightest_tail else None,
            "tightest_tail_gap_scaled_bit_length": tightest_tail[0].bit_length()
            if tightest_tail
            else None,
            "tail_beyond_cutoff_upper_bound": f"2^(1-{cutoff})",
        },
        "boolean_carry": {
            "min_U": carry_min,
            "max_U": carry_max,
            "max_U_level": carry_max_level,
        },
        "checks": checks,
    }
    comparison = _comparison_receipt(report, imported_receipt)
    report["imported_receipt_comparison"] = comparison
    if comparison["status"] != "not_requested" and comparison["checks"]:
        checks["imported_receipt_matches"] = all(comparison["checks"].values())
    report["pass"] = all(checks.values())
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--horizon", type=int, default=100_000)
    parser.add_argument(
        "--bits",
        type=int,
        help="fixed precision; defaults to horizon + guard",
    )
    parser.add_argument("--guard", type=int, default=512)
    parser.add_argument(
        "--cutoff",
        type=int,
        help="tail cutoff; defaults to the fixed precision",
    )
    parser.add_argument("--exact-resolution-limit", type=int, default=4096)
    parser.add_argument("--output", type=Path, default=OUT_PATH)
    parser.add_argument("--compare-receipt", type=Path, default=IMPORTED_RECEIPT)
    parser.add_argument("--no-compare", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--stdout", action="store_true")
    args = parser.parse_args()

    if args.guard < 0:
        parser.error("--guard must be nonnegative")
    bits = args.bits if args.bits is not None else args.horizon + args.guard
    cutoff = args.cutoff if args.cutoff is not None else bits
    imported = None
    if not args.no_compare:
        imported = json.loads(args.compare_receipt.read_text(encoding="utf-8"))

    report = build_report(
        args.horizon,
        bits,
        cutoff,
        exact_resolution_limit=args.exact_resolution_limit,
        imported_receipt=imported,
    )
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if not args.check:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    if args.stdout:
        print(rendered, end="")
    else:
        print(
            json.dumps(
                {
                    "output": str(args.output),
                    "certified_through": report["summary"]["certified_through"],
                    "takes": report["summary"]["takes"],
                    "decision_bit_sha256": report["summary"][
                        "decision_bit_sha256"
                    ],
                    "comparison": report["imported_receipt_comparison"]["status"],
                    "pass": report["pass"],
                },
                sort_keys=True,
            )
        )
    return 0 if report["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
