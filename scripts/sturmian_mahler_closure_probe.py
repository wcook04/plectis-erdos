#!/usr/bin/env python3
"""Exact finite obstruction to polynomial 2-Mahler closure of Sturmian series.

For H(x) = sum a_n x^n, search for a relation

    sum_{j=0}^J P_j(x) H(x^(2^j)) = Q(x),

where deg(P_j) <= D.  Above degree D the polynomial Q disappears.  The
coefficient equations form a 0/1 matrix.  Full column rank over F_2 proves
full column rank over Q, so it rules out every rational relation in the box.

The three characteristic Sturmian words are generated with exact integer
square roots; no floating-point slope decisions enter the certificate.
"""

from __future__ import annotations

import argparse
import json
from math import isqrt


SLOPES = ("golden_conjugate", "sqrt2_minus_1", "sqrt3_minus_1")


def quadratic_floor(kind: str, n: int) -> int:
    if kind == "golden_conjugate":
        return (isqrt(5 * n * n) - n) // 2
    if kind == "sqrt2_minus_1":
        return isqrt(2 * n * n) - n
    if kind == "sqrt3_minus_1":
        return isqrt(3 * n * n) - n
    raise ValueError(f"unknown slope: {kind}")


def characteristic_bits(kind: str, stop: int) -> list[int]:
    floors = [quadratic_floor(kind, n) for n in range(stop + 2)]
    return [floors[n + 1] - floors[n] for n in range(stop + 1)]


def gf2_rank_certificate(kind: str, levels: int, degree: int) -> dict[str, int | str | bool]:
    column_count = levels * (degree + 1)
    row_start = degree + 1
    row_stop = row_start + column_count + 64
    bits = characteristic_bits(kind, row_stop)
    basis: dict[int, int] = {}

    for n in range(row_start, row_stop):
        row = 0
        for j in range(levels):
            scale = 1 << j
            column_base = j * (degree + 1)
            smallest_index = max(0, n - degree)
            for m in range(
                (smallest_index + scale - 1) // scale,
                n // scale + 1,
            ):
                if bits[m]:
                    row |= 1 << (column_base + n - scale * m)

        reduced = row
        while reduced:
            pivot = reduced.bit_length() - 1
            incumbent = basis.get(pivot)
            if incumbent is None:
                basis[pivot] = reduced
                break
            reduced ^= incumbent

        if len(basis) == column_count:
            rows_used = n - row_start + 1
            return {
                "slope": kind,
                "rank": column_count,
                "column_count": column_count,
                "rows_used": rows_used,
                "full_column_rank": True,
            }

    return {
        "slope": kind,
        "rank": len(basis),
        "column_count": column_count,
        "rows_used": row_stop - row_start,
        "full_column_rank": len(basis) == column_count,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--levels", type=int, default=13)
    parser.add_argument("--degree", type=int, default=1024)
    args = parser.parse_args()
    if args.levels < 1 or args.degree < 0:
        parser.error("levels must be positive and degree nonnegative")

    cohorts = [
        gf2_rank_certificate(kind, args.levels, args.degree)
        for kind in SLOPES
    ]
    passed = all(row["full_column_rank"] for row in cohorts)
    receipt = {
        "schema": "erdos257_sturmian_mahler_closure_probe_v1",
        "status": "pass" if passed else "rank_defect_found",
        "relation_family": (
            "sum_{j=0}^{levels-1} P_j(x) H(x^(2^j)) = Q(x), "
            "deg(P_j)<=degree; Q arbitrary of degree<=degree"
        ),
        "field": "F_2 (full rank here implies full rank over Q)",
        "levels": args.levels,
        "maximum_tower_exponent": 1 << (args.levels - 1),
        "degree": args.degree,
        "cohorts": cohorts,
        "claim_ceiling": (
            "Exact finite elimination of the displayed polynomial Mahler box. "
            "It does not exclude unbounded-degree, non-polynomial, nonlinear, "
            "or genuinely infinite-tower identities and does not prove the "
            "Sturmian Lambert value irrational."
        ),
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
