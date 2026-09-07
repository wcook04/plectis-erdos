#!/usr/bin/env python3
"""Exact replay for the strict companion of the sextic null branch."""

from __future__ import annotations

import sympy as sp

t, beta = sp.symbols("t beta", real=True)
s = sp.sqrt(3)
t0 = s - 1
q0 = (7 + 4 * s) / 27
beta_star = (106 + 25 * s) / 1221

p = t**2 + 2 * t - 2
left = t**2 - 4 * t + 1
right = 2 * t**2 - 2 * t - 1
base = sp.expand(p * (1 - q0 * left * right))
slope = sp.expand(
    -sp.Rational(3, 2) * q0 * t0 * p * left * right
    + 3 * s * (2 - s) * t - 3 * s * t * (1 - t)
)
mirror_endpoint = sp.expand(base - beta_star * slope)

quartic = sp.expand(
    t**4 + (-5 + 2 * s) * t**3 + (sp.Rational(21, 2) - 12 * s) * t**2
    + (-41 + 27 * s) * t - sp.Rational(8794, 853) * s
    + sp.Rational(40775, 1706)
)
factor = sp.expand(
    -(4943 + 2813 * s) / 10989 * (t - t0) ** 2 * quartic
)
assert sp.simplify(mirror_endpoint - factor) == 0


def bernstein(poly: sp.Expr, degree: int) -> list[sp.Expr]:
    expanded = sp.Poly(sp.expand(poly), t)
    return [
        sp.simplify(sum(
            expanded.nth(j) * sp.binomial(k, j) / sp.binomial(degree, j)
            for j in range(k + 1)
        ))
        for k in range(degree + 1)
    ]


coefficients = bernstein(quartic, 4)
expected = [
    (40775 - 17588 * s) / 1706,
    (46577 - 12145 * s) / 3412,
    (17575 + 4062 * s) / 3412,
    (-9721 + 15151 * s) / 3412,
    (-9041 + 5707 * s) / 853,
]
assert all(sp.simplify(a - b) == 0 for a, b in zip(coefficients, expected))
assert all(value.is_positive for value in coefficients)

q_mirror_terminal = sp.simplify(q0 * (1 - sp.Rational(3, 2) * beta_star * t0))
assert sp.simplify(q_mirror_terminal - sp.Rational(1, 6)).is_positive

# The actual-to-mirror difference has the exact favourable sign
# -3*s*beta*t*((L-1)*(2-s)+(1-M)*(1-t)).
L, M = sp.symbols("L M", real=True)
actual_minus_mirror = sp.factor(
    -3 * s * beta * L * (2 - s) * t + 3 * s * beta * M * t * (1 - t)
    - (-3 * s * beta * (2 - s) * t + 3 * s * beta * t * (1 - t))
)
expected_difference = sp.expand(
    -3 * s * beta * t * ((L - 1) * (2 - s) + (1 - M) * (1 - t))
)
assert sp.simplify(actual_minus_mirror - expected_difference) == 0

print(f"mirror terminal q = {q_mirror_terminal} = {sp.N(q_mirror_terminal, 16)}")
print("mirror quartic Bernstein coefficients:")
for value in coefficients:
    print(f"  {value} = {sp.N(value, 16)}")
print("PASS: mirror endpoint and favourable companion correction are exact")
