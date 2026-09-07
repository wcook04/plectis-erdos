#!/usr/bin/env python3
"""Exact checker for the rational rescue of the positive-LF quintic."""

from __future__ import annotations

from math import comb
import sympy as sp


t = sp.symbols("t")
h = sp.Rational(-8, 5)
R = sp.Rational(7, 5)
ux, uy = sp.Rational(-3, 5), sp.Rational(4, 5)


def H(x: sp.Expr, y: sp.Expr) -> sp.Expr:
    return sp.expand(15*x + 5*(x*x-y*y) - (x**5-10*x**3*y**2+5*x*y**4))


def bernstein_controls(poly: sp.Expr, degree: int = 5) -> list[sp.Expr]:
    power = sp.Poly(sp.expand(poly), t)
    a = [power.nth(i) for i in range(degree + 1)]
    return [sp.factor(sum(a[i]*sp.Rational(comb(k, i), comb(degree, i))
                          for i in range(k + 1))) for k in range(degree + 1)]


assert ux**2 + uy**2 == 1
re2 = ux**2 - uy**2
re5 = ux**5 - 10*ux**3*uy**2 + 5*ux*uy**4
assert re5 == sp.Rational(237, 3125) > 0

arm = H((1-t)*h+t*R*ux, t*R*uy)
arm_expected = [
    sp.Rational(-2232, 3125), sp.Rational(-91359, 15625),
    sp.Rational(-2201607, 156250), sp.Rational(-15036143, 781250),
    sp.Rational(-37150741, 1953125), sp.Rational(-153827009, 9765625),
]
assert bernstein_controls(arm) == arm_expected
assert all(c < 0 for c in arm_expected)

tail_recip = 15*R*ux*t**4 + 5*R**2*re2*t**3 - R**5*re5
tail_expected = [
    sp.Rational(-3983259, 9765625), sp.Rational(-3983259, 9765625),
    sp.Rational(-3983259, 9765625), sp.Rational(-13325893, 19531250),
    sp.Rational(-39311384, 9765625), sp.Rational(-153827009, 9765625),
]
assert bernstein_controls(tail_recip) == tail_expected
assert all(c < 0 for c in tail_expected)

dist_sq = sp.expand((R*ux-h)**2+(R*uy)**2)
assert dist_sq == sp.Rational(229, 125)
assert sp.expand(R**2-dist_sq) == sp.Rational(16, 125) > 0
assert H(h, 0) == arm_expected[0] < 0

print("PASS: exact rational rescue of positive leftmost-fibre quintic")
print(f"  arm controls: {arm_expected}")
print(f"  reciprocal-tail controls: {tail_expected}")
print(f"  squared metric margin: {R**2-dist_sq}")

# Quantitative four-real-dimensional coefficient chart.  Both evaluation and
# power-to-Bernstein conversion are affine in the coefficient perturbations,
# so the box supremum of a control is its centre plus rho times the l1 norm of
# its four sensitivities.
da, ea, db, eb = sp.symbols("da ea db eb", real=True)


def H_delta(x: sp.Expr, y: sp.Expr) -> sp.Expr:
    linear = (15+da)*x-ea*y
    quadratic = (5+db)*(x*x-y*y)-2*eb*x*y
    return sp.expand(linear+quadratic-(x**5-10*x**3*y**2+5*x*y**4))


def box_upper(expr: sp.Expr, rho: sp.Rational) -> sp.Expr:
    centre = sp.expand(expr).subs({da: 0, ea: 0, db: 0, eb: 0})
    sensitivity = sum(abs(sp.diff(expr, q)) for q in (da, ea, db, eb))
    return sp.factor(centre+rho*sensitivity)


rho = sp.Rational(1, 6)
arm_u_delta = bernstein_controls(
    H_delta((1-t)*h+t*R*ux, t*R*uy))
arm_v_delta = bernstein_controls(
    H_delta((1-t)*h+t*R*ux, -t*R*uy))
tail_u_delta = bernstein_controls(
    ((15+da)*R*ux-ea*R*uy)*t**4
    + ((5+db)*R**2*re2-2*eb*R**2*ux*uy)*t**3
    - R**5*re5)
tail_v_delta = bernstein_controls(
    ((15+da)*R*ux+ea*R*uy)*t**4
    + ((5+db)*R**2*re2+2*eb*R**2*ux*uy)*t**3
    - R**5*re5)

arm_upper_expected = [
    sp.Rational(-196, 9375), sp.Rational(-478429, 93750),
    sp.Rational(-4167439, 312500), sp.Rational(-86815733, 4687500),
    sp.Rational(-215205071, 11718750), sp.Rational(-440043527, 29296875),
]
tail_upper_expected = [
    sp.Rational(-3983259, 9765625), sp.Rational(-3983259, 9765625),
    sp.Rational(-3983259, 9765625), sp.Rational(-75208483, 117187500),
    sp.Rational(-74182143, 19531250), sp.Rational(-440043527, 29296875),
]
assert [box_upper(c, rho) for c in arm_u_delta] == arm_upper_expected
assert [box_upper(c, rho) for c in arm_v_delta] == arm_upper_expected
assert [box_upper(c, rho) for c in tail_u_delta] == tail_upper_expected
assert [box_upper(c, rho) for c in tail_v_delta] == tail_upper_expected
assert all(c < 0 for c in arm_upper_expected+tail_upper_expected)

# The first arm control binds at the exact maximal affine box radius.
rho_max = sp.Rational(279, 1625)
assert box_upper(arm_u_delta[0], rho_max) == 0
assert rho < rho_max

print("PASS: explicit four-dimensional coefficient chart")
print(f"  closed l_infinity radius: {rho} (maximal affine radius {rho_max})")
print(f"  arm box upper controls: {arm_upper_expected}")
print(f"  reciprocal-tail box upper controls: {tail_upper_expected}")
print(f"  smallest strict Bernstein margin: {-max(arm_upper_expected+tail_upper_expected)}")
