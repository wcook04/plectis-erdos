#!/usr/bin/env python3
"""Exact finite signed-pulse moment controls from Round 8 P4.

Finite packets do not prove the simultaneous infinite construction or the
rationality of the actual totient series.
"""
from __future__ import annotations
from fractions import Fraction
import json
from math import comb, factorial

SOURCE_COMMIT = '0268dd8bfb2a556a0c93078337d42c6d07138fa2'


def pulse(n: int, k: int, digit: int = 1) -> dict[int, int]:
    if type(n) is not int or not 1 <= n <= 10_000 or type(k) is not int or not 1 <= k <= 6:
        raise ValueError('bounded pulse parameters required')
    if type(digit) is not int or abs(digit) > 4:
        raise ValueError('bounded integer digit required')
    t = 2*factorial(k); M = factorial(k)
    return {n+j*t: digit*M*(-1)**j*comb(k, j) for j in range(k+1)}


def moment(coefficients: dict[int, int], degree: int, modulus: int = 1,
           residue: int = 0) -> int:
    if not 0 <= degree <= 6 or not 1 <= modulus <= 6 or not 0 <= residue < modulus:
        raise ValueError('bounded moment/progression inputs required')
    return sum(c*x**degree for x, c in coefficients.items() if x % modulus == residue)


def totient(n: int) -> int:
    if type(n) is not int or not 1 <= n <= 10_100:
        raise ValueError('bounded totient input required')
    out = n; remaining = n; p = 2
    while p*p <= remaining:
        if remaining % p == 0:
            out -= out//p
            while remaining % p == 0:
                remaining //= p
        p += 1
    if remaining > 1:
        out -= out//remaining
    return out


def report() -> dict:
    checked = 0
    for k in range(2, 6):
        coefficients = pulse(1000, k, -2)
        if sum(coefficients.values()) != 0 or min(coefficients.values()) >= 0:
            raise ArithmeticError('signed zero-mass packet changed')
        for q in range(1, k+1):
            for c in range(q):
                for degree in range(k):
                    if moment(coefficients, degree, q, c) != 0:
                        raise ArithmeticError('low progression moment did not vanish')
                    checked += 1
        t = 2*factorial(k); M = factorial(k)
        predicted = -2*M*(-1)**k*factorial(k)*t**k
        if moment(coefficients, k) != predicted:
            raise ArithmeticError('first unpreserved moment changed')
    actual = pulse(1000, 2)
    rows = [{'n': n, 'totient': totient(n), 'correction': c,
             'modified': totient(n)+c} for n, c in sorted(actual.items())]
    if not all(0 <= row['modified'] <= row['n'] for row in rows):
        raise ArithmeticError('genuine finite totient room failed')
    evaluation = sum((Fraction(c, 2**n) for n, c in actual.items()), Fraction())
    closed = Fraction(2, 2**1000)*(1-Fraction(1, 2**4))**2
    if evaluation != closed:
        raise ArithmeticError('finite packet value changed')
    return {'schema': 'round8-signed-pulse/1', 'source_commit': SOURCE_COMMIT,
            'low_progression_moment_checks': checked, 'genuine_totient_rows': rows,
            'packet_value': str(evaluation),
            'evidence_class': 'exact_finite_stencil_only'}


if __name__ == '__main__':
    print(json.dumps(report(), indent=2))
