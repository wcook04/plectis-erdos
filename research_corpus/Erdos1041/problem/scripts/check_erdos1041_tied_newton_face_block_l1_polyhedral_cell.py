#!/usr/bin/env python3
"""Exact elimination for the complete block-L1 fixed-template chart cell."""

from __future__ import annotations

from math import comb

import sympy as sp


t, r, a, b = sp.symbols("t r a b", real=True)
I = sp.I
s3 = sp.sqrt(3)
R = sp.Rational(5, 4)
h = sp.Rational(7, 10) + I * sp.Rational(57, 80)
u = sp.Integer(1)
v = sp.Rational(1, 2) + I * s3 / 2
a_min = -sp.Rational(1875, 128)
epsilon = -sp.Rational(5997001, 10**9)
rho = sp.Rational(1, 192)


def P(w: sp.Expr) -> sp.Expr:
    return -w**6 + a * w**2 + b


def bernstein(poly: sp.Expr, degree: int = 6) -> list[sp.Expr]:
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


controls_u = bernstein(sp.re(P(h + t * (R * u - h))))
controls_v = bernstein(sp.re(P(h + t * (R * v - h))))
sens_u = bernstein(sp.re((h + t * (R * u - h)) ** 2))
sens_v = bernstein(sp.re((h + t * (R * v - h)) ** 2))
const_u = bernstein(sp.re(-(h + t * (R * u - h)) ** 6))
const_v = bernstein(sp.re(-(h + t * (R * v - h)) ** 6))

expected_sens_u = [
    -sp.Rational(113, 6400), sp.Rational(2687, 9600),
    sp.Rational(27061, 48000), sp.Rational(26687, 32000),
    sp.Rational(104687, 96000), sp.Rational(4, 3), sp.Rational(25, 16),
]
expected_const_u = [
    -sp.Rational(13814656687, 262144000000),
    sp.Rational(274918973, 327680000),
    sp.Rational(40742687, 26214400), sp.Rational(46277, 32768),
    sp.Rational(2825, 65536), -sp.Rational(4375, 2048),
    -sp.Rational(15625, 4096),
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
expected_const_v = [
    -sp.Rational(13814656687, 262144000000),
    -(-2199351784 + 2403129063 * s3) / 5242880000,
    -(1442784 * s3 + 40742687) / 52428800,
    -sp.Rational(46277, 32768),
    -25 * (113 + 6384 * s3) / 131072,
    -625 * (56 + 57 * s3) / 32768,
    -sp.Rational(15625, 4096),
]

for got, want in (
    (sens_u, expected_sens_u), (const_u, expected_const_u),
    (sens_v, expected_sens_v), (const_v, expected_const_v),
):
    assert all(sp.simplify(x - y) == 0 for x, y in zip(got, want))
assert all(
    sp.simplify(c - (T + a * S + b)) == 0
    for c, T, S in zip(controls_u + controls_v, const_u + const_v, sens_u + sens_v)
)

S = sens_u + sens_v
T = const_u + const_v
lines = [sp.factor(-Ti - a * Si) for Ti, Si in zip(T, S)]
# U0..U6,V0..V6.  The common hub lines U0,V0 coincide.
active = [13, 11, 10, 9, 8, 0, 1, 2]
breaks = [
    sp.factor((T[q] - T[p]) / (S[p] - S[q]))
    for p, q in zip(active, active[1:])
]
assert a_min < breaks[0]
assert all(x < y for x, y in zip(breaks, breaks[1:]))
assert breaks[-1] < 0
assert breaks[-2] == -sp.Rational(701249505261, 234004480000)
assert breaks[-1] == -sp.Rational(468729229, 186040320)

# Exact lower-envelope proof: on each interval an affine competitor minus the
# claimed active line is nonnegative at both endpoints, hence everywhere.
endpoints = [a_min, *breaks, sp.Integer(0)]
for k, idx in enumerate(active):
    left, right = endpoints[k], endpoints[k + 1]
    for competitor in lines:
        d_left = sp.simplify(competitor.subs(a, left) - lines[idx].subs(a, left))
        d_right = sp.simplify(competitor.subs(a, right) - lines[idx].subs(a, right))
        assert d_left >= 0
        assert d_right >= 0

# The previously proved reciprocal-integer-optimal square is contained.
for aa in (-3 - rho, -3 + rho):
    for bb in (epsilon - rho, epsilon + rho):
        assert a_min < aa < 0 and bb < 0
        assert all(sp.simplify(c.subs({a: aa, b: bb})) < 0 for c in controls_u + controls_v)

tail_u = sp.expand(sp.re(P(r * u)))
tail_v = sp.expand(sp.re(P(r * v)))
assert tail_u == -r**6 + a * r**2 + b
assert tail_v == -r**6 - a * r**2 / 2 + b
assert sp.factor(sp.diff(tail_v, r) - r * (-6 * r**4 - a)) == 0
assert sp.factor(tail_v.subs(r, R) - controls_v[-1]) == 0
assert a_min == -6 * R**4

y = sp.symbols("y", real=True)
critical_value_model = b + sp.Rational(2, 3) * a * I * y
assert sp.re(critical_value_model) == b

names = ["V6", "V4", "V3", "V2", "V1", "H", "U1", "U2"]
print("PASS: complete exact fixed-template polyhedral cell")
print(f"  a-domain: {a_min} < a < 0; b below fourteen affine controls")
print(f"  active lower-envelope facets: {', '.join(names)}")
print("  transition abscissae:")
for x in breaks:
    print(f"    {x}  ~= {sp.N(x, 14)}")
print("  reciprocal-integer-optimal square is strictly contained")
print("  V6 is exactly the tail cutoff; a>-6R^4 makes the tail decreasing")
