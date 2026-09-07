#!/usr/bin/env python3
"""Probe primitive-prime projective trapping of exact rational greedy residuals.

For a rational target ``y`` and its exact greedy Mersenne prefix, write the
reduced residual after rank ``N`` as ``a_N / D_N``.  If a selected rank ``k``
has a primitive prime divisor ``p | 2^k-1``, then ``ord_p(2)=k``.  This script
tests whether the source-reachable numerator residues ``a_N mod p`` remain in
one (or a bounded handful of) cosets of the dyadic subgroup ``<2>``.

That is the algebraically relevant strengthening of merely observing serial
correlation in ``a_N``.  The computation is exact; it is a finite mechanism
falsifier, not an all-depth irrationality or membership proof.
"""

from __future__ import annotations

import argparse
from functools import lru_cache
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from typing import Any

from sympy import cyclotomic_poly, factorint, n_order

from cantor_staircase_run_length_lab import Engine


ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/"
    "RationalResidualNumeratorResidueProbe.md"
)

TARGETS = (
    ("1/2", 1, 2),
    ("1/21", 1, 21),
    ("4/9", 4, 9),
    ("1/465", 1, 465),
    ("3/7", 3, 7),
)


def canonical_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


@lru_cache(maxsize=None)
def primitive_prime(period: int) -> int | None:
    """Return the least primitive prime divisor of ``2^period-1`` if present."""

    if period <= 1:
        return None
    value = int(cyclotomic_poly(period, 2))
    candidates = []
    for prime in factorint(value):
        prime = int(prime)
        if n_order(2, prime) == period:
            candidates.append(prime)
    return min(candidates) if candidates else None


def exact_orbit(p: int, q: int, depth: int) -> tuple[list[int], list[Fraction]]:
    """Return the exact greedy bits and reduced prefix residuals."""

    result = Engine(depth).run(p, q)
    if result["status"] != "alive":
        raise AssertionError(
            f"target {p}/{q} is not certified alive through {depth}: {result}"
        )
    bits = [0] + [int(bit) for bit in result["word"]]
    residual = Fraction(p, q)
    residuals = [residual]
    for rank in range(1, depth + 1):
        if bits[rank]:
            residual -= Fraction(1, (1 << rank) - 1)
        if residual <= 0:
            raise AssertionError(f"nonpositive residual at {p}/{q}, rank {rank}")
        residuals.append(residual)
    return bits, residuals


def channel_receipt(
    target: str,
    period: int,
    prime: int,
    residuals: list[Fraction],
) -> dict[str, Any]:
    """Measure the numerator orbit in ``F_p^*/<2>`` exactly."""

    if n_order(2, prime) != period:
        raise AssertionError("primitive-prime order mismatch")
    quotient_capacity = (prime - 1) // period
    rows = []
    for horizon in range(period, len(residuals)):
        residual = residuals[horizon]
        if residual.denominator % prime:
            continue
        residue = residual.numerator % prime
        if residue == 0:
            raise AssertionError("reduced numerator vanished at an active prime")
        signature = pow(residue, period, prime)
        centered = min(residue, prime - residue)
        rows.append((horizon, residue, signature, centered))

    signatures = {row[2] for row in rows}
    first_change = None
    if rows:
        initial = rows[0][2]
        first_change = next(
            (
                {
                    "horizon": horizon,
                    "residue": residue,
                    "coset_signature": signature,
                }
                for horizon, residue, signature, _ in rows[1:]
                if signature != initial
            ),
            None,
        )
    tight = min(rows, key=lambda row: row[3]) if rows else None
    signatures_rendered = json.dumps(
        [row[2] for row in rows], separators=(",", ":")
    ).encode()
    return {
        "target": target,
        "selected_period": period,
        "primitive_prime": prime,
        "dyadic_subgroup_order": period,
        "quotient_coset_capacity": quotient_capacity,
        "active_horizon_count": len(rows),
        "distinct_dyadic_coset_count": len(signatures),
        "signature_change_count": sum(
            rows[index][2] != rows[index - 1][2]
            for index in range(1, len(rows))
        ),
        "single_dyadic_coset": len(signatures) <= 1,
        "initial_active_state": (
            None
            if not rows
            else {
                "horizon": rows[0][0],
                "residue": rows[0][1],
                "coset_signature": rows[0][2],
            }
        ),
        "first_coset_escape": first_change,
        "smallest_centered_residue": (
            None
            if tight is None
            else {
                "horizon": tight[0],
                "centered_residue": tight[3],
                "prime": prime,
            }
        ),
        "ordered_coset_signature_sha256": hashlib.sha256(
            signatures_rendered
        ).hexdigest(),
    }


def target_receipt(name: str, p: int, q: int, depth: int, max_period: int) -> dict[str, Any]:
    bits, residuals = exact_orbit(p, q, depth)
    channels = []
    exceptional_selected_periods = []
    for period in range(2, min(depth, max_period) + 1):
        if not bits[period]:
            continue
        prime = primitive_prime(period)
        if prime is None:
            exceptional_selected_periods.append(period)
            continue
        channels.append(channel_receipt(name, period, prime, residuals))

    nontrivial = [row for row in channels if row["quotient_coset_capacity"] > 1]
    escaped = [row for row in nontrivial if not row["single_dyadic_coset"]]
    widest = max(
        nontrivial,
        key=lambda row: (
            row["distinct_dyadic_coset_count"],
            row["active_horizon_count"],
        ),
        default=None,
    )
    return {
        "target": name,
        "depth": depth,
        "selected_count": sum(bits),
        "primitive_channel_count": len(channels),
        "nontrivial_quotient_channel_count": len(nontrivial),
        "channels_escaping_first_dyadic_coset": len(escaped),
        "all_nontrivial_channels_single_coset": not escaped,
        "first_exact_coset_escape": (
            None
            if not escaped
            else min(
                escaped,
                key=lambda row: row["first_coset_escape"]["horizon"],
            )["first_coset_escape"]
            | {
                "selected_period": min(
                    escaped,
                    key=lambda row: row["first_coset_escape"]["horizon"],
                )["selected_period"],
                "primitive_prime": min(
                    escaped,
                    key=lambda row: row["first_coset_escape"]["horizon"],
                )["primitive_prime"],
            }
        ),
        "widest_channel": widest,
        "exceptional_selected_periods_without_primitive_prime": exceptional_selected_periods,
        "channels": channels,
    }


def build_receipt(depth: int, max_period: int) -> dict[str, Any]:
    targets = [
        target_receipt(name, p, q, depth, max_period)
        for name, p, q in TARGETS
    ]
    channels = [row for target in targets for row in target["channels"]]
    nontrivial = [row for row in channels if row["quotient_coset_capacity"] > 1]
    escaped = [row for row in nontrivial if not row["single_dyadic_coset"]]
    widest = max(
        nontrivial,
        key=lambda row: (
            row["distinct_dyadic_coset_count"],
            row["active_horizon_count"],
        ),
    )
    return {
        "schema": "erdos257_rational_residual_numerator_residue_probe_v0",
        "analysis_ref": ANALYSIS_REF,
        "claim_status": "exact finite source-reachable mechanism falsifier",
        "parameters": {"depth": depth, "max_selected_period": max_period},
        "exact_setup": {
            "residual": "r_N=y-sum_(k<=N,b_k=1) 1/(2^k-1)=a_N/D_N in lowest terms",
            "primitive_channel": "p divides 2^k-1 and ord_p(2)=k for a selected k",
            "projective_coordinate": "(a_N mod p)^k; equal values iff residues occupy the same coset of <2> in F_p^*",
        },
        "summary": {
            "target_count": len(targets),
            "primitive_channel_count": len(channels),
            "nontrivial_quotient_channel_count": len(nontrivial),
            "channels_escaping_first_dyadic_coset": len(escaped),
            "universal_single_dyadic_coset_trap_falsified": bool(escaped),
            "maximum_distinct_dyadic_cosets_in_one_channel": widest[
                "distinct_dyadic_coset_count"
            ],
            "median_distinct_dyadic_cosets": sorted(
                row["distinct_dyadic_coset_count"] for row in nontrivial
            )[len(nontrivial) // 2],
            "widest_channel": widest,
        },
        "targets": targets,
        "analytic_boundary": {
            "eliminated": (
                "The actual rational greedy numerator orbit is not confined to "
                "one dyadic projective class at every selected primitive prime."
            ),
            "not_eliminated": (
                "An all-depth source-specific relation involving many primitive "
                "channels simultaneously, rather than bounded one-channel trapping."
            ),
            "not_claimed": [
                "unbounded coset proliferation",
                "membership of any tested rational target",
                "a proof or disproof of Erdős problem 257",
            ],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=180)
    parser.add_argument("--max-period", type=int, default=60)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check-receipt", type=Path)
    args = parser.parse_args()
    receipt = build_receipt(args.depth, args.max_period)
    rendered = canonical_json(receipt)
    if args.check_receipt:
        expected = args.check_receipt.read_text()
        if rendered != expected:
            raise SystemExit("receipt drift")
        print("receipt check: ok")
    elif args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
