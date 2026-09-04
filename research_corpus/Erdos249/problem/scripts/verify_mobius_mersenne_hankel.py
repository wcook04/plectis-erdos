#!/usr/bin/env python3
"""Exact rational checks for the Möbius--Mersenne Hankel packet.

This verifier has two jobs:

1. certify the four small shifted 2x2 Hankel gaps using five exact atoms and
   a rigorous geometric tail interval;
2. certify the base inequality at r = 5 for the eventual two-atom
   perturbation argument and expose the exact contraction identity used by
   the infinite induction.

It uses only Python's integer arithmetic and ``fractions.Fraction``.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction


def moebius(n: int) -> int:
    if n < 1:
        raise ValueError("the Möbius function is evaluated only at n >= 1")
    remaining = n
    factor_count = 0
    prime = 2
    while prime * prime <= remaining:
        if remaining % prime == 0:
            remaining //= prime
            factor_count += 1
            if remaining % prime == 0:
                return 0
            while remaining % prime == 0:
                remaining //= prime
        prime += 1
    if remaining > 1:
        factor_count += 1
    return -1 if factor_count % 2 else 1


def theta_prefix(rung: int, cutoff: int) -> Fraction:
    return sum(
        (
            Fraction(moebius(d), (2**d - 1) ** rung)
            for d in range(1, cutoff + 1)
        ),
        Fraction(),
    )


def tail_bound(rung: int, cutoff: int) -> Fraction:
    """Bound the atoms d > cutoff by sum_(j>=cutoff) 2^(-rung*j)."""
    q = Fraction(1, 2**rung)
    return q**cutoff / (1 - q)


def theta_interval(rung: int, cutoff: int) -> tuple[Fraction, Fraction]:
    prefix = theta_prefix(rung, cutoff)
    error = tail_bound(rung, cutoff)
    return prefix - error, prefix + error


def two_atom_tail_bound(rung: int) -> Fraction:
    return tail_bound(rung, 2)


def two_atom_gap(rung: int) -> Fraction:
    return Fraction(4, 3 ** (rung + 2))


def perturbation_error(rung: int) -> Fraction:
    b0 = two_atom_tail_bound(rung)
    b1 = two_atom_tail_bound(rung + 1)
    b2 = two_atom_tail_bound(rung + 2)
    return b0 + 2 * b1 + b2 + b0 * b2


def fraction_record(value: Fraction) -> dict[str, int | str]:
    return {
        "numerator": value.numerator,
        "denominator": value.denominator,
        "decimal": format(float(value), ".17g"),
    }


def verify(cutoff: int = 5) -> dict[str, object]:
    if cutoff < 2:
        raise ValueError("cutoff must contain at least the two dominant atoms")

    intervals = {
        rung: theta_interval(rung, cutoff) for rung in range(1, 7)
    }
    small_gap_certificates: list[dict[str, object]] = []
    for rung in range(1, 5):
        theta_lo = intervals[rung + 1][0]
        assert theta_lo > 0
        certified_lower_gap = (
            theta_lo**2
            - intervals[rung][1] * intervals[rung + 2][1]
        )
        assert certified_lower_gap > 0
        small_gap_certificates.append(
            {
                "rung": rung,
                "certified_lower_gap": fraction_record(certified_lower_gap),
            }
        )

    base_rung = 5
    base_margin = two_atom_gap(base_rung) - perturbation_error(base_rung)
    assert base_margin > 0

    # Exact algebraic identity behind B_(r+1) < B_r/4.  With a = 2^r,
    # B_r - 4 B_(r+1) = 1 / (a (a - 1) (2a - 1)) > 0.
    contraction_checks: list[dict[str, object]] = []
    for rung in range(1, 33):
        a = 2**rung
        lhs = two_atom_tail_bound(rung) - 4 * two_atom_tail_bound(rung + 1)
        rhs = Fraction(1, a * (a - 1) * (2 * a - 1))
        assert lhs == rhs and rhs > 0
        assert perturbation_error(rung + 1) < perturbation_error(rung) / 4
        contraction_checks.append(
            {"rung": rung, "tail_contraction_identity": fraction_record(lhs)}
        )

    return {
        "schema": "erdos249_mobius_mersenne_hankel_exact_verifier_v0",
        "status": "verified",
        "arithmetic": "exact_rational",
        "finite_cutoff": cutoff,
        "small_shifted_hankel_gaps": small_gap_certificates,
        "eventual_induction": {
            "base_rung": base_rung,
            "base_margin": fraction_record(base_margin),
            "two_atom_gap_contraction": "M_(r+1) = M_r / 3",
            "perturbation_contraction": "E_(r+1) < E_r / 4",
            "tail_contraction_identity": (
                "B_r - 4*B_(r+1) = "
                "1/(2^r*(2^r-1)*(2^(r+1)-1)) > 0"
            ),
        },
        "sampled_exact_contraction_checks": contraction_checks,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cutoff", type=int, default=5)
    parser.add_argument("--compact", action="store_true")
    args = parser.parse_args()
    payload = verify(args.cutoff)
    print(json.dumps(payload, sort_keys=True, separators=(",", ":") if args.compact else None))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
