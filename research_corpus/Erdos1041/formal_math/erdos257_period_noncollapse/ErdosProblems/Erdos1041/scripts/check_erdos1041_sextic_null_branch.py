#!/usr/bin/env python3
"""Exact replay for the sextic square-contact null branch.

Floating point is used only for the printed orientation values.  Every
identity and sign gate is decided symbolically over Q(sqrt(3)).
"""

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
    + 3 * s * (2 - s) * t
    - 3 * s * t * (1 - t)
)
branch = sp.expand(base + beta * slope)

endpoint_cubic = sp.expand(
    -t**3 + (4 - 2 * s) * t**2 + (-sp.Rational(13, 2) + 10 * s) * t
    + sp.Rational(69, 2) - 17 * s
)
endpoint_factor = sp.expand(
    (239 + 137 * s) / 407 * (t - 1) * (t - t0) ** 2 * endpoint_cubic
)


def bernstein_coefficients(poly: sp.Expr, degree: int) -> list[sp.Expr]:
    expanded = sp.Poly(sp.expand(poly), t)
    return [
        sp.simplify(
            sum(
                expanded.nth(j) * sp.binomial(k, j) / sp.binomial(degree, j)
                for j in range(k + 1)
            )
        )
        for k in range(degree + 1)
    ]


assert sp.simplify(branch.subs(beta, beta_star) - endpoint_factor) == 0
assert sp.simplify(branch.subs({beta: 0, t: t0})) == 0
assert sp.simplify(sp.diff(branch, t).subs({beta: 0, t: t0})) == 0
assert sp.simplify(branch.subs({beta: beta_star, t: t0})) == 0
assert sp.simplify(sp.diff(branch, t).subs({beta: beta_star, t: t0})) == 0
assert sp.simplify(branch.subs({beta: beta_star, t: 1})) == 0

coefficients = bernstein_coefficients(endpoint_cubic, 3)
expected = [
    sp.Rational(69, 2) - 17 * s,
    sp.Rational(97, 3) - sp.Rational(41, 3) * s,
    sp.Rational(63, 2) - 11 * s,
    31 - 9 * s,
]
assert all(sp.simplify(a - b) == 0 for a, b in zip(coefficients, expected))
assert all(value.is_positive for value in coefficients)

q_branch = sp.expand(q0 * (1 + sp.Rational(3, 2) * beta * t0))
ray_start = sp.expand(3 * s * beta * (2 - s) + 1 - 2 * q_branch)
ray_factor = sp.expand((-sp.Rational(86, 9) + sp.Rational(17, 3) * s) *
                       (beta - beta_star))
assert sp.simplify(ray_start - ray_factor) == 0
assert sp.simplify(ray_start.subs(beta, beta_star)) == 0
assert (-sp.Rational(86, 9) + sp.Rational(17, 3) * s).is_positive

q_terminal = sp.simplify(q_branch.subs(beta, beta_star))
r_terminal = q_terminal ** sp.Rational(1, 4)
c_terminal = beta_star / r_terminal
u_terminal = 3 * beta_star * r_terminal * (2 - s)

print(f"beta* = {sp.N(beta_star, 16)}")
print(f"q(beta*) = {q_terminal} = {sp.N(q_terminal, 16)}")
print(f"r(beta*) = {sp.N(r_terminal, 16)}")
print(f"c(beta*) = {sp.N(c_terminal, 16)}")
print(f"u(beta*) = {sp.N(u_terminal, 16)}")
print("terminal cubic Bernstein coefficients:")
for value in coefficients:
    print(f"  {value} = {sp.N(value, 16)}")
print("PASS: exact square-contact null branch closes for 0 <= beta <= beta*")
