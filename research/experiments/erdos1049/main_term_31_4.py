#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check the sign of the main term K_n log 4 - (K_n - W_n) log 31 for n <= 400.

In the long Erdos 1049 paper (subsection 'Finite calculations') the degrees of
the cancelled polynomials are

    K_n = (1091 n^2 + 81 n + 2)/2,   M_n = 266 n^2 + 34 n + 1,
    W_n = K_n - M_n + sum_{l <= 15n} phi(l) - sum_{2 <= l <= 15n} omega(n/l) phi(l),

with omega the weight of the direction (14,12,14;27).  This program computes
W_n exactly from a totient sieve, encloses log 4 and log 31 by artanh series
with a geometric tail bound, and checks that the main term
T_n = K_n log 4 - (K_n - W_n) log 31 is negative for every 1 <= n <= 400.  It
also checks the printed values of T_n / n^2 to three decimal places at
n = 1, 10, 100, 400 (-58.478, -10.280, -4.297, -3.863), the printed W_n for
n <= 4, and the printed limit C1 log 4 - C0 log 31 = -3.718...

It proves nothing about indices above 400; the irrationality theorem uses the
limit, not this finite sign check.  No floating point and no Lean kernel.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path

SCHEMA = "erdos1049-public-computation/1"
PROGRAM = "main_term_31_4.py"
LIMIT_N = 400
PRINTED_RATIOS = {1: "-58.478", 10: "-10.280", 100: "-4.297", 400: "-3.863"}
PRINTED_W = {1: 333, 2: 1315, 3: 2944, 4: 5220}
PRINTED_LIMIT = "-3.718"
INTERVALS = [
    (Fraction(1, 14), Fraction(1, 12)), (Fraction(1, 7), Fraction(1, 6)),
    (Fraction(3, 14), Fraction(1, 4)), (Fraction(2, 7), Fraction(1, 3)),
    (Fraction(5, 14), Fraction(2, 5)), (Fraction(3, 7), Fraction(7, 15)),
    (Fraction(1, 2), Fraction(8, 15)), (Fraction(4, 7), Fraction(3, 5)),
    (Fraction(9, 14), Fraction(2, 3)), (Fraction(5, 7), Fraction(11, 15)),
    (Fraction(11, 14), Fraction(4, 5)), (Fraction(6, 7), Fraction(13, 15)),
    (Fraction(13, 14), Fraction(14, 15)),
]


def artanh_bounds(t: Fraction, terms: int = 60) -> tuple[Fraction, Fraction]:
    low = sum((t ** (2 * k + 1) / (2 * k + 1) for k in range(terms)), Fraction(0))
    return low, low + t ** (2 * terms + 1) / ((2 * terms + 1) * (1 - t * t))


def log_bounds_integer(x: int) -> tuple[Fraction, Fraction]:
    """log x = k log 2 + 2 artanh((y-1)/(y+1)), y = x/2^k in [1, 2)."""

    log2 = tuple(2 * v for v in artanh_bounds(Fraction(1, 3)))
    k = x.bit_length() - 1
    y = Fraction(x, 2**k)
    a = artanh_bounds((y - 1) / (y + 1))
    return k * log2[0] + 2 * a[0], k * log2[1] + 2 * a[1]


def omega(num: int, den: int) -> int:
    def fl(c: int) -> int:
        return (c * num) // den

    return max(0, fl(14) + fl(13) - fl(12) - fl(15), 2 * fl(14) - fl(13) - fl(15))


def totients(limit: int) -> list[int]:
    phi = list(range(limit + 1))
    for p in range(2, limit + 1):
        if phi[p] == p:
            for multiple in range(p, limit + 1, p):
                phi[multiple] -= phi[multiple] // p
    return phi


def pi_bounds() -> tuple[Fraction, Fraction]:
    def arctan(x: Fraction, terms: int) -> tuple[Fraction, Fraction]:
        s = sum(((-1) ** k * x ** (2 * k + 1) / (2 * k + 1) for k in range(terms)), Fraction(0))
        t = s + (-1) ** terms * x ** (2 * terms + 1) / (2 * terms + 1)
        return min(s, t), max(s, t)

    a, b = arctan(Fraction(1, 5), 40), arctan(Fraction(1, 239), 12)
    return 16 * a[0] - 4 * b[1], 16 * a[1] - 4 * b[0]


def c0_bounds() -> tuple[Fraction, Fraction]:
    scale, m = 10**30, 1024
    j_low = j_high = Fraction(0)
    for u, v in INTERVALS:
        p1, q1, p2, q2 = u.numerator, u.denominator, v.numerator, v.denominator
        rounded = 0
        for k in range(m):
            a, b = k * q1 + p1, k * q2 + p2
            rounded += (scale * (q1 * q1 * b * b - q2 * q2 * a * a)) // (a * a * b * b)
        integral = 1 / (m + u) - 1 / (m + v)
        j_low += Fraction(rounded, scale) + integral
        j_high += Fraction(rounded + m, scale) + integral + 1 / (m + u) ** 2 - 1 / (m + v) ** 2
    pi = pi_bounds()
    return 266 - 3 * (225 - j_low) / pi[0] ** 2, 266 - 3 * (225 - j_high) / pi[1] ** 2


def rounds_to(low: Fraction, high: Fraction, printed: str) -> bool:
    places = len(printed.split(".")[1])
    target = Fraction(printed)
    half = Fraction(1, 2 * 10**places)
    return target - half <= low and high < target + half


def truncates_to_negative(low: Fraction, high: Fraction, printed: str) -> bool:
    """For a negative printed value -d.ddd..., the true value lies in (-(d.ddd + 10^-k), -d.ddd]."""

    places = len(printed.split(".")[1])
    target = Fraction(printed)
    return target - Fraction(1, 10**places) < low and high <= target


def compute() -> dict:
    log2 = tuple(2 * v for v in artanh_bounds(Fraction(1, 3)))  # log 2 = 2 artanh(1/3)
    log4 = (2 * log2[0], 2 * log2[1])
    log31 = log_bounds_integer(31)
    phi = totients(15 * LIMIT_N)
    prefix = [0] * (15 * LIMIT_N + 1)
    for l in range(1, 15 * LIMIT_N + 1):
        prefix[l] = prefix[l - 1] + phi[l]
    worst_upper = None
    ratios = {}
    degrees = {}
    all_negative = True
    for n in range(1, LIMIT_N + 1):
        N = 15 * n
        K = (1091 * n * n + 81 * n + 2) // 2
        M = 266 * n * n + 34 * n + 1
        sigma = sum(phi[l] for l in range(2, N + 1) if omega(n, l))
        W = K - M + prefix[N] - sigma
        degrees[n] = W
        low = K * log4[0] - (K - W) * log31[1]
        high = K * log4[1] - (K - W) * log31[0]
        if not high < 0:
            all_negative = False
        ratio_high = high / (n * n)
        if worst_upper is None or ratio_high > worst_upper[1]:
            worst_upper = (n, ratio_high)
        if n in PRINTED_RATIOS:
            ratios[n] = (low / (n * n), high / (n * n))
    c0 = c0_bounds()
    c1 = Fraction(1091, 2)
    limit = (c1 * log4[0] - c0[1] * log31[1], c1 * log4[1] - c0[0] * log31[0])

    def show(x: Fraction, upward: bool = False) -> str:
        """Nine decimal places, rounded down (or up when upward is set)."""

        k = (x.numerator * 10**9) // x.denominator
        if upward and k * x.denominator != x.numerator * 10**9:
            k += 1
        sign = "-" if k < 0 else ""
        k = abs(k)
        return f"{sign}{k // 10**9}.{k % 10**9:09d}"

    checks = {
        "main term negative for 1 <= n <= 400": all_negative,
        "W_n for n <= 4 matches the degree table": all(degrees[n] == w for n, w in PRINTED_W.items()),
    }
    for n, printed in PRINTED_RATIOS.items():
        checks[f"T_n/n^2 at n={n} rounds to {printed}"] = rounds_to(*ratios[n], printed)
    checks[f"limit C1 log 4 - C0 log 31 = {PRINTED_LIMIT}..."] = truncates_to_negative(*limit, PRINTED_LIMIT)
    return {
        "range": "1 <= n <= 400",
        "W_n_first_four": [degrees[n] for n in range(1, 5)],
        "T_n_over_n2_enclosures": {str(n): [show(a), show(b, True)] for n, (a, b) in ratios.items()},
        "largest_upper_bound_of_T_n_over_n2": {"n": worst_upper[0], "value": show(worst_upper[1], True)},
        "limit_enclosure": [show(limit[0]), show(limit[1], True)],
        "checks": checks,
        "all_printed_claims_verified": all(checks.values()),
    }


def canonical(obj: object) -> str:
    return json.dumps(obj, indent=2, sort_keys=True) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--receipt", type=Path, help="write a receipt JSON to this path")
    args = parser.parse_args()
    result = compute()
    if args.receipt:
        receipt = {
            "schema": SCHEMA,
            "program": PROGRAM,
            "program_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "arguments": [],
            "verification_scope": "finite_computation_only",
            "claim_boundary": (
                "Sign of the main term at 31/4 for 1 <= n <= 400 and four rounded values; no "
                "statement for larger n. No floating point and no Lean kernel."
            ),
            "paper_passage": "Subsection 'Finite calculations', paragraph beginning 'The main term'",
            "result": result,
        }
        args.receipt.write_text(canonical(receipt), encoding="utf-8")
    sys.stdout.write(canonical(result))
    return 0 if result["all_printed_claims_verified"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
