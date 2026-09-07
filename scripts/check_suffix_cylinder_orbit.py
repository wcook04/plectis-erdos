#!/usr/bin/env python3
"""Replay the exact post-depth-52 suffix-cylinder scalar orbit.

This checker deliberately proves only a finite statement.  It verifies the
same low/high feedback decisions consumed by ``SuffixCylinderOrbit.lean`` and
reports the first in-strip crossing if one occurs.  A green finite run is a
reproducible search receipt, not an infinite no-crossing theorem.
"""

from __future__ import annotations

problem_id = "erdos_257"

import argparse
import hashlib
import json
from math import isqrt
from typing import Any


START_CUTOFF = 26
START_ENDPOINT = 35_546_624
START_SUPPORT = frozenset({2, 3, 6, 7, 14, 20, 21, 26})
LEAN_CUTOFF = 60
LEAN_ENDPOINT = 199_390_140_118_282_369
LEAN_FEEDBACK_BITS = "1000011110011001011111111010111111"
DEFAULT_FINAL_CUTOFF = 200_026


def word_coeff(support: set[int], n: int) -> int:
    """Count selected divisors of ``n`` without scanning the whole support."""

    total = 0
    for divisor in range(1, isqrt(n) + 1):
        if n % divisor:
            continue
        total += divisor in support
        conjugate = n // divisor
        if conjugate != divisor:
            total += conjugate in support
    return total


def endpoint_digest(endpoint: int) -> dict[str, Any]:
    width = max(1, (endpoint.bit_length() + 7) // 8)
    encoded = endpoint.to_bytes(width, "big")
    return {
        "bit_length": endpoint.bit_length(),
        "big_endian_sha256": hashlib.sha256(encoded).hexdigest(),
        "low_256_bits_hex": f"{endpoint & ((1 << 256) - 1):064x}",
    }


def replay(final_cutoff: int) -> tuple[dict[str, Any], bool]:
    if final_cutoff < LEAN_CUTOFF:
        raise ValueError(f"final cutoff must be at least {LEAN_CUTOFF}")

    cutoff = START_CUTOFF
    endpoint = START_ENDPOINT
    support = set(START_SUPPORT)
    feedback_bits: list[str] = []
    low_count = 0
    high_count = 0
    minimum: dict[str, Any] | None = None
    crossing: dict[str, Any] | None = None
    lean_endpoint_observed: int | None = None

    while cutoff < final_cutoff:
        odd_row = 2 * cutoff + 1
        odd_coeff = word_coeff(support, odd_row)
        odd_endpoint = 2 * endpoint - odd_coeff
        strip_bound = 2 * isqrt(odd_row) + 4
        signed_threshold_delta = odd_endpoint - (1 << cutoff)

        if signed_threshold_delta >= strip_bound:
            bit = True
            clearance = signed_threshold_delta - strip_bound
            promoted_endpoint = signed_threshold_delta
            high_count += 1
        elif signed_threshold_delta <= 0:
            bit = False
            clearance = -signed_threshold_delta
            promoted_endpoint = odd_endpoint
            low_count += 1
        else:
            crossing = {
                "cutoff": cutoff,
                "odd_row": odd_row,
                "odd_coeff": odd_coeff,
                "signed_threshold_delta": signed_threshold_delta,
                "strip_bound": strip_bound,
            }
            break

        feedback_bits.append("1" if bit else "0")
        row = {
            "clearance": clearance,
            "cutoff": cutoff,
            "decision": "high" if bit else "low",
            "odd_coeff": odd_coeff,
            "signed_threshold_delta": signed_threshold_delta,
            "strip_bound": strip_bound,
        }
        if minimum is None or clearance < minimum["clearance"]:
            minimum = row

        cutoff += 1
        if bit:
            support.add(cutoff)
        even_coeff = word_coeff(support, 2 * cutoff)
        endpoint = 2 * promoted_endpoint - even_coeff

        if cutoff == LEAN_CUTOFF:
            lean_endpoint_observed = endpoint

    prefix = "".join(feedback_bits[: len(LEAN_FEEDBACK_BITS)])
    fixture_ok = (
        lean_endpoint_observed == LEAN_ENDPOINT
        and prefix == LEAN_FEEDBACK_BITS
    )
    no_crossing = crossing is None and cutoff == final_cutoff
    payload: dict[str, Any] = {
        "schema": "erdos257_suffix_cylinder_orbit_replay_v1",
        "claim_ceiling": (
            "exact finite scalar no-crossing replay; not an infinite invariant "
            "and not a proof of Erdos problem 257"
        ),
        "input": {
            "start_cutoff": START_CUTOFF,
            "start_endpoint": START_ENDPOINT,
            "start_support": sorted(START_SUPPORT),
            "requested_final_cutoff": final_cutoff,
        },
        "lean_fixture": {
            "cutoff": LEAN_CUTOFF,
            "expected_endpoint": LEAN_ENDPOINT,
            "observed_endpoint": lean_endpoint_observed,
            "expected_feedback_bits": LEAN_FEEDBACK_BITS,
            "observed_feedback_bits": prefix,
            "ok": fixture_ok,
        },
        "result": {
            "no_crossing": no_crossing,
            "crossing": crossing,
            "completed_decision_count": len(feedback_bits),
            "final_cutoff": cutoff,
            "final_endpoint": endpoint_digest(endpoint),
            "support_count": len(support),
            "low_decision_count": low_count,
            "high_decision_count": high_count,
            "first_256_feedback_bits": "".join(feedback_bits[:256]),
            "minimum_clearance": minimum,
        },
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_payload_sha256"] = hashlib.sha256(
        canonical.encode("utf-8")
    ).hexdigest()
    return payload, no_crossing and fixture_ok


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--final-cutoff",
        type=int,
        default=DEFAULT_FINAL_CUTOFF,
        help=(
            "exclusive final cutoff state (default: %(default)s, so decisions "
            "are checked at cutoffs 26 through 200025)"
        ),
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        payload, ok = replay(args.final_cutoff)
    except ValueError as exc:
        raise SystemExit(str(exc)) from exc
    print(json.dumps({"ok": ok, "payload": payload}, sort_keys=True, indent=2))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
