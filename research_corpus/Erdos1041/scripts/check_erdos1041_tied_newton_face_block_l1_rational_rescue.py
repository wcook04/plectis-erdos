#!/usr/bin/env python3
"""Exact replay for the rational rescue of the block-L1 sextic."""

from __future__ import annotations

from math import comb

import sympy as sp


t, r, z = sp.symbols("t r z", real=True)
I = sp.I
s3 = sp.sqrt(3)
x = sp.Rational(999, 1000)
epsilon = x**3 + 3 * x - 4
R = sp.Rational(5, 4)
h = sp.Rational(7, 10) + I * sp.Rational(57, 80)
u = sp.Integer(1)
v = sp.Rational(1, 2) + I * s3 / 2


def Q(w: sp.Expr) -> sp.Expr:
    return -w**6 - 3 * w**2 + epsilon


def bernstein_coefficients(poly: sp.Expr, degree: int = 6) -> list[sp.Expr]:
    p = sp.Poly(sp.expand(poly), t, extension=s3)
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


arm_u = bernstein_coefficients(sp.re(Q(h + t * (R * u - h))))
arm_v = bernstein_coefficients(sp.re(Q(h + t * (R * v - h))))

expected_u = [
    -sp.Rational(187661814643, 32768000000000),
    -sp.Rational(6859138399, 1024000000000),
    -sp.Rational(293067436173, 2048000000000),
    -sp.Rational(70121042439, 64000000000),
    -sp.Rational(413998038003, 128000000000),
    -sp.Rational(24568909879, 4000000000),
    -sp.Rational(68065554133, 8000000000),
]
expected_v = [
    -sp.Rational(187661814643, 32768000000000),
    -(-185279460616 + 213778321875 * s3) / 16384000000000,
    (-5348002137971 + 2805682500000 * s3) / 4096000000000,
    (-110490573689 + 51300000000 * s3) / 64000000000,
    -19 * (-2876378401 + 6806250000 * s3) / 256000000000,
    -(-3256816936 + 41080078125 * s3) / 64000000000,
    -sp.Rational(11815554133, 8000000000),
]
assert all(sp.simplify(a - b) == 0 for a, b in zip(arm_u, expected_u))
assert all(sp.simplify(a - b) == 0 for a, b in zip(arm_v, expected_v))
assert all(c < 0 for c in arm_u)
assert all(c < 0 for c in arm_v)

tail_u = sp.expand(sp.re(Q(r * u)))
tail_v = sp.expand(sp.re(Q(r * v)))
assert tail_u == -r**6 - 3 * r**2 + epsilon
assert tail_v == -r**6 + sp.Rational(3, 2) * r**2 + epsilon
assert sp.factor(tail_v.subs(r, R)) == -sp.Rational(11815554133, 8000000000)
assert sp.factor(sp.diff(tail_v, r) - 3 * r * (1 - 2 * r**4)) == 0
assert R**4 > sp.Rational(3, 2)

dist_u_sq = sp.expand(sp.re((R * u - h) * sp.conjugate(R * u - h)))
dist_v_sq = sp.expand(sp.re((R * v - h) * sp.conjugate(R * v - h)))
assert dist_u_sq == sp.Rational(1037, 1280)
assert sp.simplify(dist_v_sq - (sp.Rational(2157, 1280) - 57 * s3 / 64)) == 0
assert dist_u_sq < 1
assert dist_v_sq < 1
assert sp.sqrt(dist_u_sq) + sp.sqrt(dist_v_sq) < 2 < 2 * R

print("PASS: exact rational rescue of the block-L1 sextic")
print(f"  epsilon={epsilon}, hub={h}, radius={R}")
print(f"  arm-U Bernstein max={max(arm_u)}")
print(f"  arm-V Bernstein max={max(arm_v)}")
print(f"  tail-V cutoff value={tail_v.subs(r, R)}")
print(f"  metric length={sp.N(sp.sqrt(dist_u_sq) + sp.sqrt(dist_v_sq), 20)} < 2 < 2R")
