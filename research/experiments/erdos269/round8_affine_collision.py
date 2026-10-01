#!/usr/bin/env python3
"""Exact finite affine-swap and collision controls from Round 8 P2.

A finite swap identity neither produces late orbit swaps nor proves irrationality.
"""
from __future__ import annotations
from fractions import Fraction
import json
from math import prod

SOURCE_COMMIT = '0268dd8bfb2a556a0c93078337d42c6d07138fa2'


def word_map(radices: tuple[int, ...], digits: tuple[int, ...] | None = None) -> tuple[int, int]:
    if digits is None:
        digits = (1,) * len(radices)
    if len(radices) != len(digits) or len(radices) > 16:
        raise ValueError('bounded equal-length word required')
    B, D = 1, 0
    for b, c in zip(radices, digits):
        if type(b) is not int or b < 2 or type(c) is not int:
            raise ValueError('integer radix and digit required')
        D = D*b + c
        B *= b
    return B, D


def apply(word: tuple[int, int], tail: Fraction) -> Fraction:
    B, D = word
    return (D + tail) / B


def report() -> dict:
    prefix, suffix = (5, 7, 2), (3, 7, 5)
    left = word_map(prefix + (2, 3) + suffix)
    right = word_map(prefix + (3, 2) + suffix)
    defect = Fraction(1, 2*3*prod(prefix))
    for tail in (Fraction(-7, 3), Fraction(0), Fraction(11, 5)):
        if apply(left, tail) - apply(right, tail) != defect:
            raise ArithmeticError('contextual swap defect changed')
    collision_a, collision_b = word_map((5, 7, 3, 2)), word_map((7, 2, 3, 5))
    if collision_a != collision_b or collision_a != (210, 51):
        raise ArithmeticError('distinct-word affine collision changed')
    fixed = Fraction(collision_a[1], collision_a[0]-1)
    if fixed != Fraction(51, 209):
        raise ArithmeticError('fixed-point control changed')
    periodic = word_map((2, 3))
    if Fraction(periodic[1], periodic[0]-1) != Fraction(4, 5):
        raise ArithmeticError('unequal-radix periodic rational control changed')
    return {'schema': 'round8-affine-controls/1', 'source_commit': SOURCE_COMMIT,
            'contextual_swap_defect': str(defect),
            'collision': {'first_word': [5, 7, 3, 2], 'second_word': [7, 2, 3, 5],
                          'shared_affine_map': {'B': 210, 'D': 51}, 'fixed_point': str(fixed)},
            'periodic_unequal_radix_fixed_point': '4/5',
            'evidence_class': 'exact_finite_algebra_and_counterexample_only'}


if __name__ == '__main__':
    print(json.dumps(report(), indent=2))
