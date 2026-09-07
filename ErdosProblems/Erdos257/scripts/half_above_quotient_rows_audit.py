#!/usr/bin/env python3
"""Exact target-zero quotient-row audit for Erdős problem 257.

For each endpoint ``N`` the target-zero row runs integer greedy against

    q_N(d) = floor(2^N / (2^d - 1))

with target ``2^(N-1)``.  Ranks above ``floor(N/2)`` are the complete binary
bank, so only the lower core is evaluated explicitly.

The independent real half-greedy word is certified with scaled-integer
enclosures.  No floating-point number decides a bit.  The comparison tests
the live structural conjecture suggested by the fractional-financing lemma:
the target-zero quotient lower core agrees with the real-feasible half core.

Finite success is evidence only.  The Lean theorem
``not_universal_of_cofinalExactAboveLocalRows`` consumes a cofinal supply of
exact rows; this script does not prove that quantified producer.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from typing import Any


def certified_half_bits(max_rank: int, slack_bits: int) -> bytearray:
    """Return real half-greedy bits through ``max_rank`` exactly.

    At dyadic precision ``P`` the residual is enclosed by integer endpoints
    ``lower / 2^P`` and ``upper / 2^P``.  Since every Mersenne denominator at
    rank at least two is odd and greater than one, its scaled weight lies
    strictly between ``q`` and ``q+1``.
    """

    precision = 2 * max_rank + slack_bits
    scale = 1 << precision
    lower = scale // 2
    upper = lower
    bits = bytearray(max_rank + 1)

    for d in range(2, max_rank + 1):
        quotient = scale // ((1 << d) - 1)
        if lower >= quotient + 1:
            bits[d] = 1
            lower -= quotient + 1
            upper -= quotient
        elif upper <= quotient:
            bits[d] = 0
        else:
            raise AssertionError(
                f"real half decision ambiguous at rank {d}; "
                "increase --slack-bits"
            )
        if lower < 0 or lower > upper:
            raise AssertionError(f"invalid residual enclosure at rank {d}")

    return bits


def packed_sha256(bits: bytearray, max_rank: int) -> str:
    packed = bytearray((max_rank + 7) // 8)
    for rank in range(1, max_rank + 1):
        if bits[rank]:
            packed[(rank - 1) // 8] |= 1 << ((rank - 1) % 8)
    return hashlib.sha256(bytes(packed)).hexdigest()


def audit(max_n: int, slack_bits: int) -> dict[str, Any]:
    if max_n < 4:
        raise ValueError("--max-n must be at least 4")
    if slack_bits < 32:
        raise ValueError("--slack-bits must be at least 32")

    max_core = max_n // 2
    half_bits = certified_half_bits(max_core, slack_bits)

    closure_failures: list[dict[str, int]] = []
    core_mismatches: list[dict[str, int]] = []
    negative_financing: list[dict[str, int]] = []
    midpoint_holes: list[int] = []
    midpoint_takes = 0
    small_midpoint_slack: list[dict[str, int]] = []
    late_midpoint_margin: tuple[int, int, int] | None = None
    minimum_financing: tuple[int, int] | None = None
    tightest_bank: tuple[int, int, int] | None = None
    exact_rows = 0
    real_feasible_cores = 0

    for n in range(4, max_n + 1):
        cutoff = n // 2
        residual = 1 << (n - 1)
        core: list[int] = []

        for d in range(2, cutoff + 1):
            coin = (1 << n) // ((1 << d) - 1)
            take = coin <= residual
            if take:
                residual -= coin
                core.append(d)
            if take != bool(half_bits[d]):
                core_mismatches.append(
                    {
                        "N": n,
                        "rank": d,
                        "quotient_bit": int(take),
                        "real_half_bit": int(half_bits[d]),
                    }
                )
                break

        bank_capacity = 1 << (n - cutoff)
        bank_margin = bank_capacity - residual
        if bank_margin <= 0:
            closure_failures.append(
                {"N": n, "residual": residual, "capacity": bank_capacity}
            )
        else:
            exact_rows += 1

        if not core_mismatches or core_mismatches[-1]["N"] != n:
            real_feasible_cores += 1

        candidate_tightness = (bank_margin, n, residual)
        if tightest_bank is None or candidate_tightness < tightest_bank:
            tightest_bank = candidate_tightness

        endpoint_divisors = sum((n + 1) % d == 0 for d in core)
        financing = 2 * residual - endpoint_divisors
        if minimum_financing is None or financing < minimum_financing[0]:
            minimum_financing = (financing, n)
        if financing < 0:
            negative_financing.append(
                {
                    "N": n,
                    "upper_bank_value": residual,
                    "endpoint_divisors": endpoint_divisors,
                    "financing": financing,
                }
            )
        if n % 2 == 1 and financing == 1 << (cutoff + 1):
            midpoint_holes.append(n)

        # At an even endpoint N=2d, the only new lower-core decision is the
        # midpoint rank d.  The Lean mismatch certificate proves that a
        # quotient-take/real-skip crossing would force residual < d.
        if n % 2 == 0 and cutoff in core:
            midpoint_takes += 1
            if residual < cutoff:
                small_midpoint_slack.append(
                    {"N": n, "rank": cutoff, "residual": residual}
                )
            if cutoff >= 8:
                candidate_margin = (residual - cutoff, cutoff, residual)
                if late_midpoint_margin is None or candidate_margin < late_midpoint_margin:
                    late_midpoint_margin = candidate_margin

    assert tightest_bank is not None
    assert minimum_financing is not None
    return {
        "schema": "erdos257_half_above_quotient_rows_audit_v0",
        "target": "2^(N-1)",
        "horizons": [4, max_n],
        "horizons_checked": max_n - 3,
        "exact_row_count": exact_rows,
        "closure_failure_count": len(closure_failures),
        "first_closure_failures": closure_failures[:8],
        "real_feasible_core_count": real_feasible_cores,
        "core_mismatch_count": len(core_mismatches),
        "first_core_mismatches": core_mismatches[:8],
        "negative_financing_count": len(negative_financing),
        "first_negative_financing": negative_financing[:8],
        "minimum_financing": {
            "value": minimum_financing[0],
            "N": minimum_financing[1],
        },
        "midpoint_hole_count": len(midpoint_holes),
        "first_midpoint_holes": midpoint_holes[:8],
        "midpoint_take_count": midpoint_takes,
        "midpoint_slack_lt_rank_count": len(small_midpoint_slack),
        "midpoint_slack_lt_rank_events": small_midpoint_slack[:8],
        "minimum_midpoint_slack_minus_rank_from_rank_8": (
            None if late_midpoint_margin is None else {
                "value": late_midpoint_margin[0],
                "rank": late_midpoint_margin[1],
                "residual": late_midpoint_margin[2],
            }
        ),
        "tightest_bank_margin": {
            "value": tightest_bank[0],
            "N": tightest_bank[1],
            "lower_core_residual": tightest_bank[2],
        },
        "real_half_bits_through": max_core,
        "real_half_bits_sha256": packed_sha256(half_bits, max_core),
        "decision_arithmetic": "exact scaled-integer enclosure",
        "claim_ceiling": (
            "finite evidence only; cofinal target-zero row existence remains "
            "the open producer consumed by Lean"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=2000)
    parser.add_argument("--slack-bits", type=int, default=256)
    args = parser.parse_args()
    result = audit(args.max_n, args.slack_bits)
    print(json.dumps(result, indent=2, sort_keys=True))
    if result["closure_failure_count"]:
        raise SystemExit("target-zero quotient-row closure failed")
    if result["core_mismatch_count"]:
        raise SystemExit("quotient lower core diverged from real half greedy")
    if result["negative_financing_count"]:
        raise SystemExit("adjacent endpoint financing became negative")


if __name__ == "__main__":
    main()
