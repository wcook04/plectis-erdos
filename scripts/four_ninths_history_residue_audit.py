#!/usr/bin/env python3
"""Exact base-four history-residue audit for the 4/9 diagonal.

The Lean history identity implies that ``rho_d mod 4^k`` depends only on the
last ``k`` signed transition increments.  Since a selected landing is always
nonnegative, the attractive local certificate

    rho_d mod 4^k >= d

would prove ``rho_d >= d``.  This audit tests how many base-four digits beyond
the least ``k`` with ``4^k > d`` are actually required on the exact orbit.
It is a falsifier for bounded recent-history arguments, not an all-depth
proof or a replacement for the Lean identity.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from array import array
from math import gcd
from pathlib import Path


SCHEMA = "erdos257_four_ninths_history_residue_audit_v1"


def pair_pulse(rank: int) -> int:
    return 0 if rank % 3 == 0 else (1 if rank % 3 == 1 else 3)


def schedule_selected_rank(loads: array, rank: int, horizon: int) -> None:
    period = rank // gcd(rank, 2)
    start = (rank // period + 1) * period
    for future in range(start, horizon + 1, period):
        loads[future] += 1
    if rank % 2 == 1:
        start = (3 * rank + 1) // 2
        for future in range(start, horizon + 1, rank):
            loads[future] += 2


def run(horizon: int) -> dict[str, object]:
    if horizon < 12:
        raise ValueError("horizon must be at least 12")

    loads = array("I", [0]) * (horizon + 1)
    bits = bytearray(horizon + 1)
    rho = 0
    rho_12: int | None = None
    selected_count = 0
    extra_digit_histogram: dict[int, int] = {}
    first_base_certificate_failure: dict[str, int] | None = None
    first_rank_bound_violation: dict[str, int] | None = None
    maximum_extra_digits: dict[str, int] | None = None

    for rank in range(1, horizon + 1):
        transition = 4 * rho + pair_pulse(rank) - int(loads[rank])
        coin = (1 << rank) + 1
        take = transition >= coin
        rho = transition - coin if take else transition
        if rank == 12:
            rho_12 = rho
        if not take:
            continue

        bits[rank] = 1
        selected_count += 1
        if rho < rank:
            first_rank_bound_violation = {
                "rank": rank,
                "rho": rho,
                "selected_count": selected_count,
            }
            break

        base_digits = 0
        modulus = 1
        while modulus <= rank:
            base_digits += 1
            modulus *= 4

        base_residue = rho % modulus
        if base_residue < rank and first_base_certificate_failure is None:
            first_base_certificate_failure = {
                "rank": rank,
                "rho_mod_base_modulus": base_residue,
                "base_digits": base_digits,
                "modulus": modulus,
            }

        extra_digits = 0
        residue = base_residue
        while residue < rank:
            extra_digits += 1
            modulus *= 4
            residue = rho % modulus

        extra_digit_histogram[extra_digits] = (
            extra_digit_histogram.get(extra_digits, 0) + 1
        )
        witness = {
            "extra_digits": extra_digits,
            "rank": rank,
            "residue": residue,
            "base_digits": base_digits,
            "total_digits": base_digits + extra_digits,
            "rho_bit_length": rho.bit_length(),
        }
        if (
            maximum_extra_digits is None
            or extra_digits > maximum_extra_digits["extra_digits"]
        ):
            maximum_extra_digits = witness

        schedule_selected_rank(loads, rank, horizon)

    prefix = "".join("1" if bits[rank] else "0" for rank in range(1, 13))
    return {
        "schema": SCHEMA,
        "status": "pass" if first_rank_bound_violation is None else "fail",
        "horizon": horizon,
        "selected_count": selected_count,
        "base_fixture": {
            "bits_1_through_12": prefix,
            "rho_12": rho_12,
            "matches_lean": prefix == "010110110001" and rho_12 == 2460,
        },
        "first_rank_bound_violation": first_rank_bound_violation,
        "first_base_certificate_failure": first_base_certificate_failure,
        "extra_digit_histogram": {
            str(key): extra_digit_histogram[key]
            for key in sorted(extra_digit_histogram)
        },
        "maximum_extra_digits": maximum_extra_digits,
        "interpretation": {
            "falsified_local_certificate": (
                "the least k with 4^k > rank does not always make "
                "rho mod 4^k at least rank"
            ),
            "claim_boundary": (
                "finite exact evidence only; growth of the required recent "
                "history length is not proved"
            ),
        },
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--horizon", type=int, default=200_000)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    result = run(args.horizon)
    rendered = json.dumps(result, indent=2, sort_keys=True)
    print(rendered)
    if args.json_out is not None:
        args.json_out.write_text(rendered + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
