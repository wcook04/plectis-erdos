#!/usr/bin/env python3
"""Exact margin audit for the 4/9 diagonal recurrence.

The Lean reduction in ``FourNinthsDiagonalNoPositiveFatal.lean`` shows that a
negative skipped successor can occur only after the current remainder loses a
linear selected-count reserve.  This audit tests the sharper inductive reserve

    2 * selected_count <= 3 * rho

on the exact executable diagonal.  It also separates take and skip rows.  The
separation matters mathematically: the existing paired-load bound makes the
reserve automatic across a skipped row, so only post-take rows can create a
new proof obligation.

All arithmetic is exact.  Divisor loads are maintained by a forward sieve:
when rank ``a`` is selected, it schedules weight two on future ``d`` with
``a | 2*d-1`` and weight one on future ``d`` with ``a | 2*d``.  A successful
finite run is a conjecture discriminator, not an all-depth proof.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from array import array
from math import gcd
from pathlib import Path


SCHEMA = "erdos257_four_ninths_diagonal_margin_audit_v1"
EXPECTED_PREFIX = "010110110001"
EXPECTED_RHO_12 = 2460


def pair_pulse(d: int) -> int:
    """The paired source pulse ``0,1,3`` in phases ``0,1,2 mod 3``."""

    return 0 if d % 3 == 0 else (1 if d % 3 == 1 else 3)


def schedule_selected_rank(loads: array, a: int, horizon: int) -> None:
    """Add the exact future paired-load contribution of selected rank ``a``."""

    # Weight one at a | 2*d.  The period is a/gcd(a,2); start strictly after a
    # because the diagonal load uses only proper earlier ranks.
    period = a // gcd(a, 2)
    start = (a // period + 1) * period
    for d in range(start, horizon + 1, period):
        loads[d] += 1

    # Weight two at a | 2*d-1.  This congruence exists only for odd a.  Its
    # first solution strictly after a is d=(3a+1)/2.
    if a % 2 == 1:
        start = (3 * a + 1) // 2
        for d in range(start, horizon + 1, a):
            loads[d] += 2


def run(horizon: int) -> dict[str, object]:
    if horizon < 12:
        raise ValueError("horizon must be at least 12 for the Lean base fixture")

    loads = array("I", [0]) * (horizon + 1)
    rho = 0
    selected = 0
    bits = bytearray(horizon + 1)

    minimum_all: tuple[int, int, int, int, int, int, bool] | None = None
    minimum_take: tuple[int, int, int, int, int, int] | None = None
    minimum_skip: tuple[int, int, int, int, int, int] | None = None
    minimum_load_slack: tuple[int, int, int, int] | None = None
    minimum_take_rank_slack: tuple[int, int, int, int] | None = None
    minimum_take_double_count_slack: tuple[int, int, int, int] | None = None
    first_negative: dict[str, int] | None = None
    first_margin_violation: dict[str, int | bool] | None = None
    first_take_rank_bound_violation: dict[str, int] | None = None
    take_record_lows: list[dict[str, int]] = []
    take_margin_record: int | None = None

    for d in range(1, horizon + 1):
        selected_before = selected
        pulse = pair_pulse(d)
        load = int(loads[d])
        transition = 4 * rho + pulse - load
        coin = (1 << d) + 1
        take = transition >= coin
        rho = transition - coin if take else transition

        if take:
            bits[d] = 1
            selected += 1

        margin = 3 * rho - 2 * selected
        row = (margin, d, rho, selected, load, pulse, take)
        if minimum_all is None or row < minimum_all:
            minimum_all = row

        if take:
            take_row = (margin, d, rho, selected, load, pulse)
            if minimum_take is None or take_row < minimum_take:
                minimum_take = take_row
            if take_margin_record is None or margin < take_margin_record:
                take_margin_record = margin
                take_record_lows.append(
                    {
                        "rank": d,
                        "rho": rho,
                        "selected_count": selected,
                        "margin": margin,
                        "load": load,
                        "pulse": pulse,
                    }
                )
            rank_row = (rho - d, d, rho, selected)
            if minimum_take_rank_slack is None or rank_row < minimum_take_rank_slack:
                minimum_take_rank_slack = rank_row
            double_count_row = (rho - 2 * selected, d, rho, selected)
            if (
                minimum_take_double_count_slack is None
                or double_count_row < minimum_take_double_count_slack
            ):
                minimum_take_double_count_slack = double_count_row
            if rho < d and first_take_rank_bound_violation is None:
                first_take_rank_bound_violation = {
                    "rank": d,
                    "rho": rho,
                    "selected_count": selected,
                    "rank_slack": rho - d,
                }
        else:
            skip_row = (margin, d, rho, selected, load, pulse)
            if minimum_skip is None or skip_row < minimum_skip:
                minimum_skip = skip_row

        load_slack = 2 * selected_before - load
        load_row = (load_slack, d, selected_before, load)
        if minimum_load_slack is None or load_row < minimum_load_slack:
            minimum_load_slack = load_row

        if rho < 0 and first_negative is None:
            first_negative = {
                "rank": d,
                "rho": rho,
                "selected_count": selected,
                "load": load,
                "pulse": pulse,
                "take": int(take),
            }
            break

        if margin < 0 and first_margin_violation is None:
            first_margin_violation = {
                "rank": d,
                "rho": rho,
                "selected_count": selected,
                "margin": margin,
                "load": load,
                "pulse": pulse,
                "take": take,
            }
            break

        if take:
            schedule_selected_rank(loads, d, horizon)

    prefix = "".join("1" if bits[d] else "0" for d in range(1, 13))
    base_fixture_ok = prefix == EXPECTED_PREFIX

    # Recompute rho_12 cheaply and independently of the final orbit state so
    # the receipt binds the exact Lean fixture rather than only its bit word.
    fixture_loads = array("I", [0]) * 13
    fixture_rho = 0
    for d in range(1, 13):
        transition = 4 * fixture_rho + pair_pulse(d) - int(fixture_loads[d])
        take = transition >= (1 << d) + 1
        fixture_rho = transition - ((1 << d) + 1) if take else transition
        if take:
            schedule_selected_rank(fixture_loads, d, 12)
    base_fixture_ok = base_fixture_ok and fixture_rho == EXPECTED_RHO_12

    source_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()

    def render_row(row: tuple[int, ...] | None) -> dict[str, int] | None:
        if row is None:
            return None
        keys = ("margin", "rank", "rho", "selected_count", "load", "pulse")
        return dict(zip(keys, row[:6], strict=True))

    return {
        "schema": SCHEMA,
        "status": "pass" if first_negative is None and first_margin_violation is None else "fail",
        "horizon": horizon,
        "selected_count": selected,
        "base_fixture": {
            "bits_1_through_12": prefix,
            "rho_12": fixture_rho,
            "matches_lean": base_fixture_ok,
        },
        "candidate_invariant": "2 * selected_count <= 3 * rho",
        "first_negative": first_negative,
        "first_margin_violation": first_margin_violation,
        "stronger_selected_candidate": "rank <= rho (hence selected_count <= rho)",
        "first_take_rank_bound_violation": first_take_rank_bound_violation,
        "minimum_all_state_margin": render_row(minimum_all),
        "minimum_take_margin": render_row(minimum_take),
        "minimum_take_rank_slack": {
            "slack": minimum_take_rank_slack[0],
            "rank": minimum_take_rank_slack[1],
            "rho": minimum_take_rank_slack[2],
            "selected_count": minimum_take_rank_slack[3],
        }
        if minimum_take_rank_slack is not None
        else None,
        "minimum_take_double_selected_slack": {
            "slack": minimum_take_double_count_slack[0],
            "rank": minimum_take_double_count_slack[1],
            "rho": minimum_take_double_count_slack[2],
            "selected_count": minimum_take_double_count_slack[3],
        }
        if minimum_take_double_count_slack is not None
        else None,
        "minimum_skip_margin": render_row(minimum_skip),
        "minimum_paired_load_slack": {
            "slack": minimum_load_slack[0],
            "rank": minimum_load_slack[1],
            "selected_count_before": minimum_load_slack[2],
            "load": minimum_load_slack[3],
        }
        if minimum_load_slack is not None
        else None,
        "take_margin_record_lows": take_record_lows,
        "proof_relevance": {
            "skip_rows": (
                "already controlled by the paired-load bound once the reserve "
                "holds at the preceding state"
            ),
            "remaining_producer": (
                "exclude a selected post-step landing with "
                "3*rho < 2*selected_count"
            ),
            "claim_boundary": "finite exact evidence only",
        },
        "script_sha256": source_hash,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--horizon", type=int, default=100_000)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    result = run(args.horizon)
    text = json.dumps(result, indent=2, sort_keys=True)
    print(text)
    if args.json_out is not None:
        args.json_out.write_text(text + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
