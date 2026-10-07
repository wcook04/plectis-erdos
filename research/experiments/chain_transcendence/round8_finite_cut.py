#!/usr/bin/env python3
"""Exact finite separated-cut and rational-displacement examples from Round 8 P1.

These computations do not prove the infinite Subspace-Theorem claim.
"""
from __future__ import annotations
from fractions import Fraction
import json

SOURCE_COMMIT = '0268dd8bfb2a556a0c93078337d42c6d07138fa2'


def lambert(weights: dict[int, int], q: Fraction) -> Fraction:
    return sum((w * q**n / (1 - q**n) for n, w in weights.items()), Fraction())


def displacement(weights: dict[int, int], u: int, v: int, N: int) -> tuple[Fraction, Fraction, Fraction]:
    if not (u > v >= 1 and 1 <= N <= 32 and 0 < len(weights) <= 16):
        raise ValueError('bounded rational displacement inputs required')
    q = Fraction(v, u); t = 1 / q
    X = lambert(weights, q)
    J = sum((w * t**(N - j*n) for n, w in weights.items()
             for j in range(1, N//n + 1)), Fraction())
    delta = sum((w * (t**(N % n) - 1) / (t**n - 1)
                 for n, w in weights.items()), Fraction())
    return X, J, delta


def report() -> dict:
    q = Fraction(2, 3)
    X, J, delta = displacement({1: 1, 3: 1}, 3, 2, 2)
    if (X, J, delta) != (Fraction(46, 19), Fraction(5, 2), Fraction(10, 19)):
        raise ArithmeticError('rational displacement control changed')
    if delta != (q**-2 - 1)*X - J or J.denominator == 1 or (2**2*J).denominator != 1:
        raise ArithmeticError('lattice-loss identity failed')
    weights = {1: 1, 2: 1, 6: 1, 12: 1}
    L, M, R = 2, 6, 3
    if not all((L % n == 0 if n <= L else n % M == 0) for n in weights):
        raise ArithmeticError('separated finite cut failed')
    prefix = {n: w for n, w in weights.items() if n <= L}
    tail = lambert({n: w for n, w in weights.items() if n > L}, q)
    polynomial = [sum(w for n, w in prefix.items() if e % n == 0)
                  for e in range(L + 1)]
    polynomial[0] = 0
    if sum((c*q**i for i, c in enumerate(polynomial)), Fraction()) != (1-q**L)*lambert(prefix, q):
        raise ArithmeticError('cleared prefix polynomial failed')
    coefficients = [sum(w for n, w in weights.items() if n > L and (k*M) % n == 0)
                    for k in range(1, R)]
    remainder = tail - sum((c*q**(k*M) for k, c in enumerate(coefficients, 1)), Fraction())
    W = max(weights.values())
    bound = W*(Fraction(R, 1-q)+q/(1-q)**2)*q**(R*M)
    if not 0 < remainder < bound:
        raise ArithmeticError('finite tail bound failed')
    return {'schema': 'round8-finite-cut/1', 'source_commit': SOURCE_COMMIT,
            'rational_displacement': {'X': str(X), 'J': str(J), 'delta': str(delta),
                                      'cleared_J_integral': True},
            'separated_cut': {'L': L, 'M': M, 'truncation': R,
                              'tail_coefficients': coefficients,
                              'remainder': str(remainder), 'upper_bound': str(bound)},
            'evidence_class': 'exact_finite_identity_only'}


if __name__ == '__main__':
    print(json.dumps(report(), indent=2))
