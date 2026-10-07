#!/usr/bin/env python3
"""Exact finite denominator trap for the Round 8 P3 calibrated model.

The all-rank Hankel asymptotic and actual #1049 value are outside this check.
"""
from __future__ import annotations
from fractions import Fraction
import json

SOURCE_COMMIT = '0268dd8bfb2a556a0c93078337d42c6d07138fa2'
Q = Fraction(2, 3)
L = 32


def coefficient(k: int) -> int:
    if type(k) is not int or not 0 <= k <= 64:
        raise ValueError('bounded coefficient index required')
    return (k + 1)**2 * (k + 2) // 2


def d(k: int) -> int:
    return (k + 1)*(k + 2)//2


def rational_seed(w: Fraction) -> Fraction:
    if not 0 <= w < 1:
        raise ValueError('seed argument outside [0,1)')
    return (1 + 2*w)/(1-w)**4


def tail_seed(w: Fraction) -> Fraction:
    return rational_seed(w) - 12*Q/(1-w)**3 - sum(
        ((coefficient(k)-12*Q*d(k))*w**k for k in range(L)), Fraction())


def a_zero() -> Fraction:
    return 1-(1-Q)**L*sum((coefficient(k)*Q**k for k in range(1, L)), Fraction())-tail_seed(Q)


def seed(w: Fraction) -> Fraction:
    return a_zero()+(1-Q)**L*sum((coefficient(k)*w**k for k in range(1, L)), Fraction())+tail_seed(w)


def moment(n: int) -> Fraction:
    if type(n) is not int or not 0 <= n <= 8:
        raise ValueError('finite moment index must be 0..8')
    return seed(Q**(n+1))


def report() -> dict:
    if not Fraction(1, 2) < a_zero() < 1 or seed(Q) != 1:
        raise ArithmeticError('positive rational mass calibration changed')
    rows = []
    for n in range(1, 6):
        mu = moment(n)
        delta = 3**(n+1) - 2**(n+1)
        predicted = 3**(31*n+62)*delta**4
        tail_predicted = 3**(32*n+62)*delta**4
        if mu.denominator != predicted or (Q**n*mu).denominator != tail_predicted:
            raise ArithmeticError(f'exact denominator formula failed at n={n}')
        rows.append({'n': n, 'moment_denominator': str(predicted),
                     'normalised_tail_denominator': str(tail_predicted)})
    mu1, mu2 = moment(1), moment(2)
    H2 = mu2 - mu1**2
    naive = mu1.denominator*mu2.denominator
    residual = naive*H2
    if residual.denominator != 625:
        raise ArithmeticError('rank-two nonnested row clearer trap changed')
    return {'schema': 'round8-calibrated-denominators/1', 'source_commit': SOURCE_COMMIT,
            'q': '2/3', 'xi': '1', 'finite_rows': rows,
            'rank_two_bad_clearer': {'remaining_denominator': 625,
                                     'cleared_value': str(residual)},
            'evidence_class': 'exact_finite_countermodel_arithmetic_only'}


if __name__ == '__main__':
    print(json.dumps(report(), indent=2))
