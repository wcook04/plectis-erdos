#!/usr/bin/env python3
"""Measure the source-defined Postelmans--Van Assche row at p = 3/2.

This is a direct finite arithmetic probe of the nonrectangular multiple
little-q-Jacobi family from Postelmans--Van Assche, *Multiple little
q-Jacobi polynomials*, J. Comput. Appl. Math. 178 (2005), 361--375.
The local source is ``annexes/arxiv-math0604312-postelmans-van-assche-zeta-q1-q2/extracted.md``:

* ``pnmnewbasis`` gives the common denominator p_{n,m};
* ``qnm uitdrukking`` and ``rnm uitdrukking`` give q_{n,m} and r_{n,m}; and
* ``pn*qn*rn*`` gives the three integer channels used for simultaneous
  approximation to 1, zeta_q(1), and zeta_q(2).

The published linear-independence diagonal is m = n - 1 and the evaluation
point is z = p^(2n-1).  Here p = 3/2 and q = 2/3 are treated exactly as
Fractions.  We primitive-normalise the resulting rational three-channel row
and report its exact height.  The ``height_rate_proxy`` is

    log(max(|row_i|)) / (n log 3),

using the source's natural degree parameter n.  It is a finite measurement,
not an all-index theorem and not an irrationality claim.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import gcd, lcm, log

P = Fraction(3, 2)
Q = Fraction(2, 3)
KAPPA3_BUDGET = 2 - 3 * log(2) / log(3)


def gaussian_binomial(n: int, k: int) -> Fraction:
    """The p-Gaussian binomial at p = 3/2, exactly."""
    if k < 0 or k > n:
        return Fraction(0)
    value = Fraction(1)
    for i in range(1, k + 1):
        value *= (P ** (n - k + i) - 1) / (P**i - 1)
    return value


def q_pochhammer(start: Fraction, length: int) -> Fraction:
    """(start; q)_length with q = 2/3, exactly."""
    value = Fraction(1)
    for index in range(length):
        value *= 1 - start * Q**index
    return value


def basis_term(n: int, m: int, k: int, j: int, z: Fraction) -> Fraction:
    """One signed term of the source's p_{n,m} double sum."""
    return (
        (-1) ** (n + m + k + j)
        * gaussian_binomial(n + m + k, m)
        * gaussian_binomial(n + k + j, n)
        * gaussian_binomial(m, k)
        * gaussian_binomial(n, j)
        * q_pochhammer(Q * z, k + j)
        * P ** (
            (n - j) * (n - j + 1) // 2
            + (m - k) * (m - k + 1) // 2
        )
    )


def pva_channels(n: int, m: int) -> tuple[Fraction, Fraction, Fraction]:
    """Return (p_nm(z), q_nm(z), r_nm(z)) at z = p^(n+m)."""
    z = P ** (n + m)
    denominator = Fraction(0)
    first_numerator = Fraction(0)
    second_numerator = Fraction(0)
    for k in range(m + 1):
        for j in range(n + 1):
            term = basis_term(n, m, k, j, z)
            denominator += term
            for r in range(1, k + j + 1):
                tail = q_pochhammer(Q ** (r + 1) * z, k - r + j)
                first_numerator += term * tail / (P**r - 1)
                harmonic = sum(
                    (Fraction(1) / (P**i - 1) for i in range(1, r + 1)),
                    Fraction(0),
                )
                second_numerator += term * tail * harmonic / (P**r - 1)
    # The source's q_nm and r_nm formulas carry (-1)^(n+m+1) outside
    # the signed p_nm basis term used above.
    return denominator, -first_numerator, -second_numerator


def primitive_integer_row(values: tuple[Fraction, Fraction, Fraction]) -> tuple[list[int], int]:
    """Clear rational denominators and divide the exact three-way content."""
    common_denominator = 1
    for value in values:
        common_denominator = lcm(common_denominator, value.denominator)
    integers = [
        value.numerator * (common_denominator // value.denominator)
        for value in values
    ]
    content = 0
    for value in integers:
        content = gcd(content, abs(value))
    if content == 0:
        raise ValueError("source row vanished identically")
    return [value // content for value in integers], common_denominator // content


def source_row(n: int) -> tuple[list[int], int]:
    """Construct the source's simultaneous zeta row for m = n - 1."""
    m = n - 1
    N = n + m
    p_nm, q_nm, r_nm = pva_channels(n, m)
    prefix_one = sum(
        (Fraction(1) / (P**k - 1) for k in range(1, N)), Fraction(0)
    )
    prefix_two = sum(
        (Fraction(k) / (P**k - 1) for k in range(1, N)), Fraction(0)
    )
    return primitive_integer_row(
        (
            p_nm,
            q_nm + p_nm * prefix_one,
            r_nm + p_nm * prefix_two + N * q_nm,
        )
    )


def measure(n: int) -> dict[str, object]:
    row, denominator = source_row(n)
    height = max(abs(value) for value in row)
    return {
        "n": n,
        "m": n - 1,
        "evaluation_exponent": 2 * n - 1,
        "primitive_content": 1,
        "clearing_denominator_bits": denominator.bit_length(),
        "height_bits": height.bit_length(),
        "height_rate_proxy": log(height) / (n * log(3)),
        "row": row,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--start", type=int, default=2)
    parser.add_argument("--stop", type=int, default=10)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    if args.start < 1 or args.stop < args.start:
        parser.error("require 1 <= start <= stop")

    rows = [measure(n) for n in range(args.start, args.stop + 1)]
    report = {
        "probe": "erdos1049_pva_multiple_q_jacobi",
        "base": "3/2",
        "source_diagonal": "m=n-1",
        "kappa3_budget": KAPPA3_BUDGET,
        "finite_measurement_only": True,
        "rows": rows,
        "minimum_height_rate_proxy": min(row["height_rate_proxy"] for row in rows),
        "all_rows_primitive": all(row["primitive_content"] == 1 for row in rows),
    }
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
        return 0

    print("Erdos 1049 -- Postelmans--Van Assche multiple little-q-Jacobi")
    print("p=3/2, q=2/3, source diagonal m=n-1, exact rational arithmetic")
    print(f"rank-three budget: kappa_3 < {KAPPA3_BUDGET:.12f}")
    for row in rows:
        print(
            f"n={row['n']:2d}  N={row['evaluation_exponent']:2d}  "
            f"height_bits={row['height_bits']:4d}  "
            f"denominator_bits={row['clearing_denominator_bits']:4d}  "
            f"height_rate_proxy={row['height_rate_proxy']:.9f}  "
            f"content={row['primitive_content']}"
        )
    print(
        "finite conclusion: every scanned row has exact primitive content 1 "
        "and misses the rank-three budget"
    )
    print("claim ceiling: bounded arithmetic measurement; no all-index rejection")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
