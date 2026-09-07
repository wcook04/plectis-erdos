#!/usr/bin/env python3
"""Identify the fixed-prefix resolvent with the existing hole coordinate.

The original version correctly certified the numerical resolvent intervals
but presented the resolvent as a new proof object.  Pairing the two binary
rows shows exactly that ``sigma = Psi - theta`` and hence ``x - sigma = u``
when the hole-geometry carry ``Q`` is ``x``.  This producer now binds and
checks that cross-program identity so the coordinate is not counted twice.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from array import array
from fractions import Fraction
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
TARGET_RIDES = {293_578: 13, 2_287_936: 13, 4_662_078: 11}


def canonical_digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def selected_load(value: int, fixed: bytearray) -> int:
    total = 0
    for divisor in range(1, math.isqrt(value) + 1):
        if value % divisor:
            continue
        quotient = value // divisor
        if divisor < value and fixed[divisor]:
            total += 1
        if quotient != divisor and quotient < value and fixed[quotient]:
            total += 1
    return total


def correction(rank: int, fixed: bytearray) -> int:
    return (
        2 * (target_bit(rank + 1) - selected_load(rank + 1, fixed))
        + target_bit(rank + 2)
        - selected_load(rank + 2, fixed)
    )


def scientific(value: Fraction) -> str:
    return f"{float(value):.17e}"


def snapshot(
    rank: int,
    suffix_width: int,
    suffix_top: int,
    prefix_length: int,
    selected_count: int,
    fixed: bytearray,
    resolvent_terms: int,
) -> dict[str, Any]:
    boundary = 1 << (suffix_width - 1)
    x = suffix_top - boundary
    if not (0 <= x < raw_carry(rank)):
        raise AssertionError(("bad boundary offset", rank, x, raw_carry(rank)))

    corrections = []
    paired_loads = []
    paired_targets = []
    for j in range(resolvent_terms):
        source_rank = rank + 2 * j
        paired_load = (
            2 * selected_load(source_rank + 1, fixed)
            + selected_load(source_rank + 2, fixed)
        )
        paired_target = (
            2 * target_bit(source_rank + 1) + target_bit(source_rank + 2)
        )
        paired_loads.append(paired_load)
        paired_targets.append(paired_target)
        corrections.append(paired_target - paired_load)
    denominator = 4**resolvent_terms
    sigma_numerator = sum(
        -value * 4 ** (resolvent_terms - index - 1)
        for index, value in enumerate(corrections)
    )
    load_numerator = sum(
        value * 4 ** (resolvent_terms - index - 1)
        for index, value in enumerate(paired_loads)
    )
    target_numerator = sum(
        value * 4 ** (resolvent_terms - index - 1)
        for index, value in enumerate(paired_targets)
    )
    if sigma_numerator != load_numerator - target_numerator:
        raise AssertionError(("paired Psi-theta identity", rank))
    tail_coefficient_bound = 3 * selected_count + 3
    tail_radius = Fraction(tail_coefficient_bound, 3 * denominator)
    center_sigma = Fraction(sigma_numerator, denominator)
    center_residual = Fraction(x * denominator - sigma_numerator, denominator)
    nearest = (sigma_numerator + denominator // 2) // denominator
    nearest_distance = abs(Fraction(nearest) - center_sigma)
    sign_certified = abs(center_residual) > tail_radius

    # Replay the actual no-strip ride without allowing any new prefix bits.
    ride_top = suffix_top
    ride_width = suffix_width
    ride_rank = rank
    offsets = [x]
    ride_corrections = []
    while True:
        value = correction(ride_rank, fixed)
        next_carry = raw_carry(ride_rank + 2)
        next_top = 4 * ride_top + value
        next_width = ride_width + 2
        bottom = next_top - next_carry
        difference = next_top ^ bottom
        common = next_width - (difference.bit_length() if difference else 0)
        if common:
            break
        ride_corrections.append(value)
        ride_top = next_top
        ride_width = next_width
        ride_rank += 2
        offsets.append(ride_top - (1 << (ride_width - 1)))

    expected = TARGET_RIDES[rank]
    if len(ride_corrections) != expected:
        raise AssertionError(("record ride mismatch", rank, len(ride_corrections), expected))
    if ride_corrections != corrections[:expected]:
        raise AssertionError(("correction prefix mismatch", rank))

    return {
        "start_rank": rank,
        "prefix_length": prefix_length,
        "starting_suffix_width": suffix_width,
        "selected_fixed_bit_count": selected_count,
        "starting_boundary_offset": x,
        "ride_length": len(ride_corrections),
        "ride_offsets": offsets,
        "ride_corrections": ride_corrections,
        "resolvent": {
            "term_count": resolvent_terms,
            "center_nearest_integer": nearest,
            "nearest_integer_equals_boundary_offset": nearest == x,
            "center_distance_to_nearest_integer": scientific(nearest_distance),
            "tail_radius_bound": scientific(tail_radius),
            "boundary_offset_minus_center": scientific(center_residual),
            "residual_sign_certified_under_tail_bound": sign_certified,
            "center_residual_amplified_by_ride": scientific(
                center_residual * 4 ** len(ride_corrections)
            ),
            "correction_stream_sha256": canonical_digest(corrections),
            "paired_load_stream_sha256": canonical_digest(paired_loads),
            "paired_target_stream_sha256": canonical_digest(paired_targets),
            "truncated_sigma_equals_truncated_Psi_minus_theta": True,
            "theta_n": str(Fraction((4 * pow(2, rank, 9)) % 9, 9)),
        },
    }


def analyze(horizon: int, crosscheck: int, resolvent_terms: int) -> dict[str, Any]:
    if horizon < max(TARGET_RIDES) or horizon % 2:
        raise ValueError("--horizon must be even and reach every target ride")
    if resolvent_terms < 32:
        raise ValueError("--resolvent-terms must be at least 32")
    snapshots = full_prefix_dp(crosscheck)
    prefix_word, prefix_length, suffix_width, suffix_top = initialize_cylinder(
        snapshots
    )
    fixed = bytearray(horizon + 2 * resolvent_terms + 5)
    loads = array("H", [0]) * len(fixed)
    selected_count = 0

    def fix_rank(position: int, bit: int) -> None:
        nonlocal selected_count
        fixed[position] = bit
        if bit:
            selected_count += 1
            for multiple in range(2 * position, len(loads), position):
                loads[multiple] += 1

    for position in range(1, prefix_length + 1):
        fix_rank(position, (prefix_word >> (position - 1)) & 1)

    rows = []
    rank = 6
    previous_common = None
    trace = hashlib.sha256()
    while rank <= horizon:
        if rank in TARGET_RIDES:
            if previous_common is not None and previous_common == 0:
                raise AssertionError(("target is not a maximal ride start", rank))
            rows.append(
                snapshot(
                    rank,
                    suffix_width,
                    suffix_top,
                    prefix_length,
                    selected_count,
                    fixed,
                    resolvent_terms,
                )
            )
        if rank == horizon:
            break

        g1, g2 = loads[rank + 1], loads[rank + 2]
        value = 2 * (target_bit(rank + 1) - g1) + target_bit(rank + 2) - g2
        next_top = 4 * suffix_top + value
        next_width = suffix_width + 2
        next_carry = raw_carry(rank + 2)
        bottom = next_top - next_carry
        difference = next_top ^ bottom
        common = next_width - (difference.bit_length() if difference else 0)
        trace.update(f"{rank + 2}:{suffix_width}:{value}:{common};".encode())
        for offset in range(common):
            bit = (next_top >> (next_width - 1 - offset)) & 1
            prefix_length += 1
            fix_rank(prefix_length, bit)
        next_width -= common
        suffix_width = next_width
        suffix_top = next_top & ((1 << suffix_width) - 1 if suffix_width else 0)
        rank += 2
        previous_common = common
        if prefix_length < rank // 2 + 1:
            raise AssertionError(("first midpoint seam", rank, prefix_length, suffix_width))

    if [row["start_rank"] for row in rows] != sorted(TARGET_RIDES):
        raise AssertionError("not every target ride was captured")
    result: dict[str, Any] = {
        "schema": "erdos257_four_ninths_fixed_prefix_resolvent_v0",
        "parameters": {
            "horizon": horizon,
            "crosscheck": crosscheck,
            "resolvent_terms": resolvent_terms,
        },
        "source": {
            "existing_cylinder_audit": str(AUDIT_PATH.relative_to(SCRIPT_PATH.parents[2])),
            "existing_cylinder_audit_sha256": hashlib.sha256(AUDIT_PATH.read_bytes()).hexdigest(),
        },
        "validation": {
            "exact_integer_cylinder": True,
            "fixed_prefix_future_loads_recounted_from_divisors": True,
            "trace_sha256": trace.hexdigest(),
            "record_ride_lengths_reproduced": True,
            "paired_resolvent_factorization_verified": True,
        },
        "cross_program_identity": {
            "fixed_prefix_resolvent": "sigma_n^P = Psi_n^P - theta_n",
            "boundary_residual": "x_n - sigma_n^P = u_n when Q_n = x_n",
            "weighted_divisor_term": (
                "Psi_n^P = sum_{d in P} 2^(-rho_d(n))/(1-2^(-d))"
            ),
            "target_rotation": "theta_n = fractional_part(2^n * 4/9)",
            "status": "exact_existing_coordinate_identified",
        },
        "record_rides": rows,
        "mechanism_decision": {
            "candidate": "treat the fixed-prefix resolvent as a new seam mechanism",
            "status": "equivalent_coordinate_eliminated",
            "reason": (
                "pairing odd/even rows gives sigma=Psi-theta and x-sigma=u, "
                "already the hole-geometry coordinate"
            ),
            "stop_condition": (
                "do not count resolvent anti-concentration separately from the "
                "existing u/Psi/theta lane; rotate to a distinct mechanism"
            ),
        },
        "claim_ceiling": (
            "exact cross-program coordinate identity plus certified finite intervals; "
            "no seam exclusion, support construction, or Erdos 257 conclusion"
        ),
    }
    result["canonical_digest"] = canonical_digest(result)
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--horizon", type=int, default=4_662_078)
    parser.add_argument("--crosscheck", type=int, default=300)
    parser.add_argument("--resolvent-terms", type=int, default=96)
    parser.add_argument("--check-receipt")
    args = parser.parse_args()
    result = analyze(args.horizon, args.crosscheck, args.resolvent_terms)
    if args.check_receipt:
        with open(args.check_receipt, encoding="utf-8") as handle:
            if result != json.load(handle):
                raise SystemExit("receipt mismatch")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
