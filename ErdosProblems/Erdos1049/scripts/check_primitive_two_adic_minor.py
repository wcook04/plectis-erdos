#!/usr/bin/env python3
"""Exact finite check of primitive 2-adic minors in the three-row 2004 family.

Stdlib only.  Default n=1 is a cheap smoke test; n=6 is the full table from the
ordinary-proof note and is slow.  The 3-adic column is recorded, not proved.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as F
from functools import lru_cache
from math import gcd, lcm
import sys

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(100000)

P = F(3, 2)


@lru_cache(None)
def power(j: int) -> F:
    return P**j


@lru_cache(None)
def qfactorial(m: int) -> F:
    out = F(1)
    for j in range(1, m + 1):
        out *= power(j) - 1
    return out


@lru_cache(None)
def gaussian(m: int, r: int) -> F:
    if not 0 <= r <= m:
        raise ValueError("Gaussian-binomial index outside 0 <= r <= m")
    return qfactorial(m) / (qfactorial(r) * qfactorial(m - r))


@lru_cache(None)
def harmonic(k: int) -> F:
    return sum((1 / (power(j) - 1) for j in range(1, k + 1)), F(0))


@lru_cache(None)
def second_sum(a0: int, d: int) -> F:
    return sum((power(-j * d) / (power(j) - 1) for j in range(1, a0)), F(0))


def primitive_row(n: int, s: int) -> tuple[int, int]:
    if n < 1 or s not in (0, 1, 2):
        raise ValueError("Use n >= 1 and s in {0,1,2}")
    a0, a1, a2, beta = 14 * n + 2, 12 * n + 1, 14 * n + 1 - s, 27 * n + 2
    assert a1 <= a2 and a1 + a2 <= beta <= a0 + a2
    A, B = F(0), F(0)
    for k in range(a2, beta):
        e = (
            a1 * (a1 - 1) // 2
            - (beta - a2) * (beta - a2 - 1) // 2
            + (beta - k) * (beta - k - 1) // 2
        )
        c = (
            ((-1) ** (a1 + a2 + k + 1))
            * power(e + a0 * k)
            * gaussian(k - 1, a1 - 1)
            * gaussian(beta - a2 - 1, beta - k - 1)
        )
        A += c
        B += c * (harmonic(k - a1) + second_sum(a0, k - a1))
    den = lcm(A.denominator, B.denominator)
    a, b = int(den * A), int(den * B)
    common = gcd(a, b)
    if common == 0:
        raise ArithmeticError("Unexpected zero rational row")
    a, b = a // common, b // common
    if a < 0:
        a, b = -a, -b
    assert gcd(a, b) == 1
    return a, b


def valuation(a: int, prime: int) -> int:
    if a == 0:
        raise ValueError("The valuation of zero is not a finite integer")
    a, exponent = abs(a), 0
    while a % prime == 0:
        a //= prime
        exponent += 1
    return exponent


EXPECTED = {
    1: (586, 0),
    2: (2264, 2),
    3: (5033, 8),
    4: (8893, 18),
    5: (13844, 32),
    6: (19886, 50),
}


def check_n(n: int) -> tuple[int, int]:
    rows = [primitive_row(n, s) for s in range(3)]
    minors = [
        rows[i][0] * rows[j][1] - rows[j][0] * rows[i][1]
        for i, j in ((0, 1), (0, 2), (1, 2))
    ]
    if not all(minors):
        raise SystemExit(f"zero minor at n={n}")
    g = gcd(gcd(minors[0], minors[1]), minors[2])
    result = (valuation(g, 2), valuation(g, 3))
    expected_two = (1091 * n * n + 83 * n - 2) // 2
    if result[0] != expected_two:
        raise SystemExit(f"v2 mismatch at n={n}: {result[0]} != {expected_two}")
    if n in EXPECTED and result != EXPECTED[n]:
        raise SystemExit(f"table mismatch at n={n}: {result} != {EXPECTED[n]}")
    print(n, result, "all minors nonzero")
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=1)
    args = parser.parse_args()
    for n in range(1, args.max_n + 1):
        check_n(n)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
