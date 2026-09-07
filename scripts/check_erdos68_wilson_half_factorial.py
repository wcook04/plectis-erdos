#!/usr/bin/env python3
"""Exact finite Wilson/half-factorial record scan for Erdős 68.

For a prime ``p``, write

    W_p = ((p - 1)! + 1) / p.

The Lean theorem
``factorialWilsonQuotient_modEq_one_iff_square_dvd_gap`` proves

    W_p == 1 (mod p)  iff  p^2 divides (p - 2)! - 1.

The companion theorem
``factorialGap_halfFactorial_Wilson_record_entry`` says that a
half-factorial ``+1`` hit, the Wilson congruence, and first occurrence of
the square together force ``p^2`` into the actual next reduced
denominator, with a nonzero numerator projection.

This checker scans those hypotheses using only exact integer modular
arithmetic.  It is finite evidence, not an infinitude, density, or
irrationality proof.
"""

from __future__ import annotations

problem_id = "erdos_68"

import argparse
import hashlib
import json
from math import factorial, isqrt
from pathlib import Path
import platform
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
DEFAULT_RECEIPT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "erdos68_wilson_half_factorial_receipt.json"
)
DEFAULT_MAX_PRIME = 50_000

# OEIS A079853, read 2026-07-30, lists precisely these generalized
# order-2 Wilson primes and reports no other term below 4 * 10^11.
# The local checker only asserts the prefix within its own finite bound.
OEIS_A079853_KNOWN_TERMS = (2, 3, 11, 107, 4931)


def canonical_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def canonical_payload_sha256(payload: dict[str, Any]) -> str:
    encoded = json.dumps(
        payload, separators=(",", ":"), sort_keys=True
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def primes_through(bound: int) -> list[int]:
    if bound < 2:
        return []
    sieve = bytearray(b"\x01") * (bound + 1)
    sieve[:2] = b"\x00\x00"
    for q in range(2, isqrt(bound) + 1):
        if sieve[q]:
            start = q * q
            sieve[start : bound + 1 : q] = b"\x00" * (
                ((bound - start) // q) + 1
            )
    return [n for n in range(2, bound + 1) if sieve[n]]


def scan_prime(p: int) -> dict[str, int | bool | None]:
    """Scan one prime with multiplication modulo ``p^2``.

    The sieve is the primality authority inside the requested finite
    interval.  This function deliberately performs no probabilistic test.
    """

    modulus = p * p
    half_index = (p - 1) // 2
    residue = 1
    half_residue = 1 if half_index < 2 else None
    first_square_index: int | None = None

    for n in range(2, p - 1):
        residue = (residue * n) % modulus
        if n == half_index:
            half_residue = residue % p
        if first_square_index is None and residue == 1:
            first_square_index = n

    near_wilson = residue == 1
    half_plus = (
        5 <= p
        and p % 4 == 3
        and half_residue == 1
    )
    joint_record = (
        half_plus
        and near_wilson
        and first_square_index == p - 2
    )
    return {
        "p": p,
        "factorial_p_minus_2_mod_p_squared": residue,
        "half_factorial_index": half_index,
        "half_factorial_mod_p": half_residue,
        "first_square_hit_index_at_least_2": first_square_index,
        "near_wilson_order_2": near_wilson,
        "half_factorial_plus_one_hit": half_plus,
        "joint_first_square_record": joint_record,
    }


def exact_factorial_crosscheck(p: int) -> dict[str, int | bool]:
    """Independent big-integer check for a reported near-Wilson event."""

    p_minus_2_residue = factorial(p - 2) % (p * p)
    half_residue = factorial((p - 1) // 2) % p
    return {
        "p": p,
        "exact_factorial_p_minus_2_mod_p_squared": p_minus_2_residue,
        "exact_half_factorial_mod_p": half_residue,
        "near_wilson_order_2": p_minus_2_residue == 1,
        "half_factorial_plus_one_hit": (
            5 <= p and p % 4 == 3 and half_residue == 1
        ),
    }


def build_receipt(max_prime: int) -> dict[str, Any]:
    if max_prime < 4931:
        raise ValueError(
            "max_prime must be at least 4931 so both known joint records "
            "are inside the certified interval"
        )

    primes = primes_through(max_prime)
    rows = [scan_prime(p) for p in primes]
    near_wilson = [
        int(row["p"]) for row in rows if row["near_wilson_order_2"]
    ]
    half_plus = [
        int(row["p"])
        for row in rows
        if row["half_factorial_plus_one_hit"]
    ]
    joint_records = [
        int(row["p"]) for row in rows if row["joint_first_square_record"]
    ]

    expected_near_wilson = [
        p for p in OEIS_A079853_KNOWN_TERMS if p <= max_prime
    ]
    if max_prime <= DEFAULT_MAX_PRIME and near_wilson != expected_near_wilson:
        raise AssertionError(
            "A079853 prefix regression: "
            f"computed {near_wilson}, expected {expected_near_wilson}"
        )
    if max_prime <= DEFAULT_MAX_PRIME and joint_records != [107, 4931]:
        raise AssertionError(
            "joint-record regression through "
            f"{max_prime}: computed {joint_records}"
        )
    if max_prime > DEFAULT_MAX_PRIME and [
        p for p in joint_records if p <= DEFAULT_MAX_PRIME
    ] != [107, 4931]:
        raise AssertionError(
            "the certified joint-record prefix through 50000 changed"
        )

    independent = [
        exact_factorial_crosscheck(p) for p in near_wilson
    ]
    for row in independent:
        if not row["near_wilson_order_2"]:
            raise AssertionError(
                f"independent factorial crosscheck failed at p={row['p']}"
            )

    trace_rows = [
        {
            "p": row["p"],
            "p_minus_2_residue": row[
                "factorial_p_minus_2_mod_p_squared"
            ],
            "half_residue": row["half_factorial_mod_p"],
            "first_square_index": row[
                "first_square_hit_index_at_least_2"
            ],
        }
        for row in rows
    ]
    source_sha256 = hashlib.sha256(
        Path(__file__).read_bytes()
    ).hexdigest()
    payload: dict[str, Any] = {
        "schema": "erdos68_wilson_half_factorial_exact_scan_v1",
        "parameters": {
            "max_prime": max_prime,
            "prime_count": len(primes),
            "arithmetic": "exact_python_integer_modular_multiplication",
            "floating_point_used": False,
            "probabilistic_primality_used": False,
        },
        "authority": {
            "source_sha256": source_sha256,
            "python_version": platform.python_version(),
            "prime_enumeration": "deterministic_eratosthenes_sieve",
            "lean_consumers": [
                "factorialWilsonQuotient_modEq_one_iff_square_dvd_gap",
                "factorialGap_halfFactorial_Wilson_record_entry",
            ],
            "oeis_crosscheck": {
                "sequence": "A079853",
                "url": "https://oeis.org/A079853",
                "accessed": "2026-07-30",
                "locally_asserted_prefix": expected_near_wilson,
                "external_only_claim_not_locally_reproduced": (
                    "No other A079853 terms below 4*10^11."
                ),
            },
        },
        "certificate": {
            "near_wilson_order_2_primes": near_wilson,
            "near_wilson_order_2_count": len(near_wilson),
            "half_factorial_plus_one_count": len(half_plus),
            "half_factorial_plus_one_trace_sha256": (
                canonical_payload_sha256({"primes": half_plus})
            ),
            "joint_first_square_record_primes": joint_records,
            "joint_first_square_record_count": len(joint_records),
            "scan_trace_sha256": canonical_payload_sha256(
                {"rows": trace_rows}
            ),
            "independent_exact_factorial_crosschecks": independent,
        },
        "mathematical_consequence": {
            "claim": (
                f"Within primes p<={max_prime}, the joint half-factorial +1, "
                "near-Wilson order-2, and first-square-record hypotheses "
                f"hold at precisely {joint_records}."
            ),
            "lean_reach": (
                "Each certified joint event satisfies the arithmetic "
                "hypotheses of the checked denominator-growth theorem; "
                "the universal first-square premise is represented here "
                "by an exact finite scan, not imported into the Lean "
                "kernel for p=4931."
            ),
            "logical_reach": "finite_two_event_denominator_record_evidence",
            "not_claimed": [
                "a Lean-kernel certificate for every p=4931 scan cell",
                "another event above 50000",
                "infinitely many joint records",
                "cofinally large amplification mass",
                "the required Archimedean numerator-residue lower bound",
                "irrationality of the Erdős 68 series",
            ],
        },
    }
    payload["receipt_payload_sha256"] = canonical_payload_sha256(payload)
    return payload


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--max-prime", type=int, default=DEFAULT_MAX_PRIME
    )
    parser.add_argument(
        "--output", type=Path, default=DEFAULT_RECEIPT
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--write", action="store_true", help="write the canonical receipt"
    )
    mode.add_argument(
        "--check",
        action="store_true",
        help="require the canonical receipt to be current",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    payload = build_receipt(args.max_prime)
    rendered = canonical_json(payload)
    if args.write:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
        print(args.output)
        return 0
    if args.check:
        if not args.output.exists():
            raise SystemExit(f"missing receipt: {args.output}")
        current = args.output.read_text()
        if current != rendered:
            raise SystemExit(f"stale receipt: {args.output}")
        print(
            "erdos68 Wilson/half-factorial receipt current: "
            f"{args.output}"
        )
        return 0
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
