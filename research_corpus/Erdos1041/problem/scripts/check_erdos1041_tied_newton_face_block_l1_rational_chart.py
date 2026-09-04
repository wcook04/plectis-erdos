#!/usr/bin/env python3
"""Exact replay for the two-parameter chart around the block-L1 rescue."""

from __future__ import annotations

from math import comb

import sympy as sp


t, r, da, db = sp.symbols("t r da db", real=True)
I = sp.I
s3 = sp.sqrt(3)
epsilon = -sp.Rational(5997001, 10**9)
rho = sp.Rational(1, 192)
a0 = -sp.Integer(3)
R = sp.Rational(5, 4)
h = sp.Rational(7, 10) + I * sp.Rational(57, 80)
u = sp.Integer(1)
v = sp.Rational(1, 2) + I * s3 / 2


def P(w: sp.Expr, a: sp.Expr = a0 + da, b: sp.Expr = epsilon + db) -> sp.Expr:
    return -w**6 + a * w**2 + b


def bernstein_coefficients(poly: sp.Expr, degree: int = 6) -> list[sp.Expr]:
    # Keep `da` and `db` as symbolic coefficients.  SymPy's generic
    # expression domain is sufficient because the conversion below uses
    # only rational linear combinations of power-basis coefficients.
    p = sp.Poly(sp.expand(poly), t)
    power = [p.nth(k) for k in range(degree + 1)]
    return [
        sp.factor(
            sum(
                power[k] * sp.Rational(comb(j, k), comb(degree, k))
                for k in range(j + 1)
            )
        )
        for j in range(degree + 1)
    ]


def central(w: sp.Expr) -> sp.Expr:
    return P(w, a0, epsilon)


base_u = bernstein_coefficients(sp.re(central(h + t * (R * u - h))))
base_v = bernstein_coefficients(sp.re(central(h + t * (R * v - h))))
sens_u = bernstein_coefficients(sp.re((h + t * (R * u - h)) ** 2))
sens_v = bernstein_coefficients(sp.re((h + t * (R * v - h)) ** 2))
chart_u = bernstein_coefficients(sp.re(P(h + t * (R * u - h))))
chart_v = bernstein_coefficients(sp.re(P(h + t * (R * v - h))))

expected_sens_u = [
    -sp.Rational(113, 6400),
    sp.Rational(2687, 9600),
    sp.Rational(27061, 48000),
    sp.Rational(26687, 32000),
    sp.Rational(104687, 96000),
    sp.Rational(4, 3),
    sp.Rational(25, 16),
]
expected_sens_v = [
    -sp.Rational(113, 6400),
    -(-429 + 475 * s3) / 3200,
    -(-2787 + 3800 * s3) / 16000,
    -19 * (-173 + 450 * s3) / 32000,
    -(2571 + 7600 * s3) / 32000,
    -(19 * s3 + 48) / 128,
    -sp.Rational(25, 32),
]

assert all(sp.simplify(x - y) == 0 for x, y in zip(sens_u, expected_sens_u))
assert all(sp.simplify(x - y) == 0 for x, y in zip(sens_v, expected_sens_v))
assert all(sp.simplify(c - (b + da * s + db)) == 0 for c, b, s in zip(chart_u, base_u, sens_u))
assert all(sp.simplify(c - (b + da * s + db)) == 0 for c, b, s in zip(chart_v, base_v, sens_v))
assert all(abs(s) < 2 for s in sens_u + sens_v)
control_radii = [
    sp.factor(-b / (abs(s) + 1))
    for b, s in zip(base_u + base_v, sens_u + sens_v)
]
controlling_radius = sp.Rational(20577415197, 3931840000000)
assert control_radii[1] == controlling_radius
assert all(q >= controlling_radius for q in control_radii)
assert rho < controlling_radius < sp.Rational(1, 191)
assert all(
    -b > rho * (abs(s) + 1)
    for b, s in zip(base_u + base_v, sens_u + sens_v)
)

a_lo = a0 - rho
a_hi = a0 + rho
b_hi = epsilon + rho
assert a_lo == -sp.Rational(577, 192)
assert a_hi == -sp.Rational(575, 192) < 0
assert b_hi == -sp.Rational(2366003, 3000000000) < 0

# The four noncentral critical values are b+(2a/3)z^2 with z^4=a/3.
# For a<0, z^2 is purely imaginary, so their real parts and the central
# critical value's real part are all b.
z2_im = sp.symbols("z2_im", real=True)
critical_value_model = (epsilon + db) + sp.Rational(2, 3) * (a0 + da) * I * z2_im
assert sp.re(critical_value_model) == epsilon + db

worst_tail_v = -r**6 - a_lo * r**2 / 2 + b_hi
derivative_bracket_at_R = sp.factor(-6 * R**4 - a_lo)
cutoff = sp.factor(worst_tail_v.subs(r, R))
assert derivative_bracket_at_R == -sp.Rational(4471, 384) < 0
assert cutoff == -sp.Rational(11741335383, 8000000000) < 0
assert sp.factor(sp.diff(worst_tail_v, r) - r * (-6 * r**4 - a_lo)) == 0

dist_u_sq = sp.Rational(1037, 1280)
dist_v_sq = sp.Rational(2157, 1280) - 57 * s3 / 64
assert dist_u_sq < 1
assert dist_v_sq < 1
assert sp.sqrt(dist_u_sq) + sp.sqrt(dist_v_sq) < 2 < 2 * R

print("PASS: exact two-parameter rational chart around the block-L1 rescue")
print(f"  |a+3| <= {rho}, |b-epsilon| <= {rho}")
print(f"  exact controlling arm radius={controlling_radius}")
print("  reciprocal-integer sharpness: 1/192 < controlling radius < 1/191")
print(
    "  weakest closed-box arm slack="
    f"{min(-b-rho*(abs(s)+1) for b, s in zip(base_u+base_v, sens_u+sens_v))}"
)
print(f"  max |arm sensitivity|={max(abs(s) for s in sens_u + sens_v)} < 2")
print(f"  worst tail-V cutoff={cutoff}")
print("  all five critical values retain negative real part b; component count remains one")
