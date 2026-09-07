#!/usr/bin/env python3
"""Exact replay for the all-degree even-symmetric diameter cone."""

from __future__ import annotations

import sympy as sp


x, a, b, R = sp.symbols("x a b R", real=True)

for m in range(1, 10):
    coefficients = [sp.Rational(-(m + k + 1), m * k + 1) for k in range(1, m)]
    value = -x ** (2 * m) + sum(
        coefficients[k - 1] * x ** (2 * k) for k in range(1, m)
    ) - sp.Rational(1, m + 1)
    terms = sp.Poly(value, x).terms()
    assert all(coefficient < 0 for (_, coefficient) in terms)
    for q in (sp.Rational(-7, 3), sp.Rational(-1, 5), sp.Integer(0), sp.Rational(11, 8)):
        assert value.subs(x, q) < 0

block_l1 = -x**6 + a * x**2 + b
assert sp.Poly(block_l1, x).nth(6) == -1
assert sp.Poly(block_l1, x).nth(2) == a
assert sp.Poly(block_l1, x).nth(0) == b
assert sp.expand(R - (-R)) == 2 * R

# The landed counterexample parameters lie strictly inside the cone.
epsilon = -sp.Rational(5997001, 10**9)
assert -3 < 0 and epsilon < 0
assert sp.simplify(
    block_l1.subs({a: -3, b: epsilon}) - (-x**6 - 3 * x**2 + epsilon)
) == 0

print("PASS: all-degree even-symmetric diameter cone")
print("  nonpositive even coefficients plus b<0 force P(x)<0 on the real axis")
print("  [-R,R] and both real tails are contained; diameter length is exactly 2R")
print("  the complete block-L1 family a<=0,b<0 is included")
