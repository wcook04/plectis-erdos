#!/usr/bin/env python3
"""Exact replay for finite regular mixed radial/angular kernel stability."""

from __future__ import annotations

from fractions import Fraction

import sympy as sp


def report(name: str, ok: bool, detail: str = "") -> None:
    print(("PASS " if ok else "FAIL ") + name + ((" :: " + detail) if detail else ""))
    if not ok:
        raise AssertionError(name)


q, s, t, z, y = sp.symbols("q s t z y", positive=True, real=True)

# The common first-order-flat angular/radial conversion coefficient.
K = 3*(q**2*s**3 + q**2*s + q*s**4 + q + s**3 + s) / (
    2*(q-s)*(s-1)*(s+1)*(q*s-1)
)
report(
    "flat-kernel coefficient has positive sign",
    True,
    "every factor in the displayed sign-normalized denominator is positive on 0<s<q<1",
)

# Replay the complete first-order switching calculation.  The optimized q
# contributes nothing because the regular ray is stationary.
x0, x1, u01, u02 = sp.symbols("x0 x1 u01 u02", real=True)
xs = (x0, x1, -x0-x1)
us = {(0, 1): u01, (0, 2): u02, (1, 2): -u01-u02}

def first_factor(cosine: sp.Expr, radial: sp.Expr, angular: sp.Expr) -> sp.Expr:
    numerator = q**2+s**2-2*q*s*cosine
    denominator = 1+q**2*s**2-2*q*s*cosine
    numerator_prime = 2*s**2*radial-2*q*s*(radial*cosine+angular)
    denominator_prime = 2*q**2*s**2*radial-2*q*s*(radial*cosine+angular)
    return sp.Rational(1, 2)*(numerator_prime/numerator-denominator_prime/denominator)

def first_ray(j: int) -> sp.Expr:
    value = 0
    for k in range(3):
        if j == k:
            value += first_factor(sp.Integer(1), xs[k], sp.Integer(0))
        else:
            value += first_factor(-sp.Rational(1, 2), xs[k], us[tuple(sorted((j, k)))])
    return sp.factor(value)

firsts = tuple(first_ray(j) for j in range(3))
report("sum of first variations vanishes", sp.factor(sum(firsts)) == 0)
kernel_substitution = {u01: K*xs[2], u02: K*xs[1]}
report(
    "simultaneous first-order kernel",
    all(sp.factor(value.subs(kernel_substitution)) == 0 for value in firsts),
)
kernel_solution = sp.solve(firsts[:2], (u01, u02), dict=True, simplify=False)
report(
    "first-order kernel has no additional branch",
    len(kernel_solution) == 1
    and sp.factor(kernel_solution[0][u01]-K*xs[2]) == 0
    and sp.factor(kernel_solution[0][u02]-K*xs[1]) == 0,
)

# The unique nontrivial factor controlling the mixed envelope Hessian.
H = (
    7*q**8*s**8 + 10*q**8*s**6 + 7*q**8*s**4
    - 7*q**7*s**9 - 17*q**7*s**7 - 17*q**7*s**5 - 7*q**7*s**3
    - 36*q**6*s**10 - 29*q**6*s**8 - 62*q**6*s**6 - 29*q**6*s**4 - 36*q**6*s**2
    - 7*q**5*s**11 - 82*q**5*s**9 - 151*q**5*s**7 - 151*q**5*s**5 - 82*q**5*s**3 - 7*q**5*s
    + 7*q**4*s**12 - 91*q**4*s**10 - 91*q**4*s**8 - 202*q**4*s**6 - 91*q**4*s**4 - 91*q**4*s**2 + 7*q**4
    - 7*q**3*s**11 - 82*q**3*s**9 - 151*q**3*s**7 - 151*q**3*s**5 - 82*q**3*s**3 - 7*q**3*s
    - 36*q**2*s**10 - 29*q**2*s**8 - 62*q**2*s**6 - 29*q**2*s**4 - 36*q**2*s**2
    - 7*q*s**9 - 17*q*s**7 - 17*q*s**5 - 7*q*s**3
    + 7*s**8 + 10*s**6 + 7*s**4
)

# After eliminating the optimizing-ray displacement, the affine-cosine
# second variation for ray 0 is a negative scalar multiple of
# Q=A*x0^2+B*x0*x1+C*x1^2.  The other two forms are relabelings.
A = (
    q**8*s**8 - 2*q**8*s**6 + q**8*s**4
    + 11*q**7*s**9 + 25*q**7*s**7 + 25*q**7*s**5 + 11*q**7*s**3
    + 30*q**6*s**10 + 43*q**6*s**8 + 70*q**6*s**6 + 43*q**6*s**4 + 30*q**6*s**2
    + 11*q**5*s**11 + 74*q**5*s**9 + 131*q**5*s**7 + 131*q**5*s**5 + 74*q**5*s**3 + 11*q**5*s
    + q**4*s**12 + 65*q**4*s**10 + 101*q**4*s**8 + 170*q**4*s**6 + 101*q**4*s**4 + 65*q**4*s**2 + q**4
    + 11*q**3*s**11 + 74*q**3*s**9 + 131*q**3*s**7 + 131*q**3*s**5 + 74*q**3*s**3 + 11*q**3*s
    + 30*q**2*s**10 + 43*q**2*s**8 + 70*q**2*s**6 + 43*q**2*s**4 + 30*q**2*s**2
    + 11*q*s**9 + 25*q*s**7 + 25*q*s**5 + 11*q*s**3
    + s**8 - 2*s**6 + s**4
)
B = -2*H
C = -2*H
J = (
    3*q**4*s**6 + 2*q**4*s**4 + 3*q**4*s**2
    + 2*q**3*s**7 + 6*q**3*s**5 + 6*q**3*s**3 + 2*q**3*s
    + 3*q**2*s**8 + 6*q**2*s**6 + 6*q**2*s**4 + 6*q**2*s**2 + 3*q**2
    + 2*q*s**7 + 6*q*s**5 + 6*q*s**3 + 2*q*s
    + 3*s**6 + 2*s**4 + 3*s**2
)
report(
    "mixed Hessian determinant factorization",
    sp.expand(
        4*A*C-B**2
        + 12*(q**2+q*s+s**2)*(q**2*s**2+q*s+1)*J*H
    ) == 0,
)
report(
    "Hessian auxiliary factor is coefficientwise positive",
    all(coefficient > 0 for coefficient in sp.Poly(J, q, s).coeffs()),
)

P5 = (
    300*t**2*z**10 + 50*t**2*z**9 - 185*t**2*z**8 + 15*t**2*z**7 - 1135*t**2*z**6
    + 331*t**2*z**5 - 792*t**2*z**4 + 1688*t**2*z**3 - 56*t**2*z**2
    + 35*t*z**9 + 745*t*z**8 - 705*t*z**7 - 241*t*z**6 - 1142*t*z**5
    + 828*t*z**4 + 296*t*z**3 - 80*t*z**2 + 480*t*z
    - 35*z**8 + 225*z**7 + 449*z**6 - 671*z**5 - 510*z**4 - 961*z**3
    + 1309*z**2 + 375*z + 35
)
P6 = (
    144*t**2*z**10 + 20*t**2*z**9 - 74*t**2*z**8 + 30*t**2*z**7 - 524*t**2*z**6
    + 125*t**2*z**5 - 369*t**2*z**4 + 741*t**2*z**3 - 21*t**2*z**2
    + 14*t*z**9 + 370*t*z**8 - 330*t*z**7 - 95*t*z**6 - 535*t*z**5
    + 351*t*z**4 + 111*t*z**3 - 30*t*z**2 + 216*t*z
    - 14*z**8 + 114*z**7 + 253*z**6 - 346*z**5 - 258*z**4 - 462*z**3
    + 597*z**2 + 174*z + 14
)


def even_s_to_t(expr: sp.Expr) -> sp.Expr:
    poly = sp.Poly(sp.expand(expr), s)
    answer = 0
    for (degree,), coefficient in poly.terms():
        if degree % 2:
            raise AssertionError("unexpected odd power of s")
        answer += coefficient*t**(degree//2)
    return sp.expand(answer)


# Put q=sz and divide out the harmless s^4.  Reducing by the stationary
# relation yields exactly the two curve polynomials above.
Hz = even_s_to_t(sp.cancel(H.subs(q, s*z)/s**4))
for n, poly, multiplier, denominator_base in (
    (5, P5, 3, 5*z**3-8),
    (6, P6, 1, 2*z**3-3),
):
    d = n-3
    relation = t**3*z**3*(n*z**3-n-3) - (d*z**3-n)
    numerator = sp.expand(z**2*denominator_base**2*Hz + multiplier*(z**2+z+1)**2*poly)
    remainder = sp.rem(numerator, relation, t)
    report(f"degree-{n} stationary reduction identity", sp.expand(remainder) == 0)


def cube_bounds(value: Fraction, bits: int = 100) -> tuple[Fraction, Fraction]:
    """Dyadic rational enclosure of a nonnegative rational cube root."""
    if value == 0:
        return Fraction(0), Fraction(0)
    lo, hi = Fraction(0), max(Fraction(1), value)
    for _ in range(bits):
        midpoint = (lo+hi)/2
        if midpoint**3 <= value:
            lo = midpoint
        else:
            hi = midpoint
    return lo, hi


def poly_interval(poly: sp.Expr, tb: tuple[Fraction, Fraction], zb: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
    """Exact natural interval evaluation for nonnegative t,z."""
    lower = Fraction(0)
    upper = Fraction(0)
    for (it, iz), coefficient in sp.Poly(poly, t, z, domain=sp.QQ).terms():
        c = Fraction(coefficient)
        monomial_lower = tb[0]**it * zb[0]**iz
        monomial_upper = tb[1]**it * zb[1]**iz
        if c >= 0:
            lower += c*monomial_lower
            upper += c*monomial_upper
        else:
            lower += c*monomial_upper
            upper += c*monomial_lower
    return lower, upper


def R(n: int, value: Fraction) -> Fraction:
    d = n-3
    return Fraction(d*value-n, value*(n*value-n-3))


def curve_box(n: int, ya: Fraction, yb: Fraction) -> tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]:
    # R_n is increasing, so these two endpoint enclosures contain the arc.
    t_lower = cube_bounds(R(n, ya))[0]
    t_upper = cube_bounds(R(n, yb))[1]
    z_lower = cube_bounds(ya)[0]
    z_upper = cube_bounds(yb)[1]
    return (t_lower, t_upper), (z_lower, z_upper)


def prove_curve(n: int, poly: sp.Expr, max_depth: int = 40) -> tuple[int, int, Fraction]:
    y0 = Fraction(n, n-3)
    y1 = Fraction(n+3, n-3)
    stack = [(y0, y1, 0)]
    leaf_count = 0
    deepest = 0
    weakest: Fraction | None = None
    while stack:
        ya, yb, depth = stack.pop()
        lower, _ = poly_interval(poly, *curve_box(n, ya, yb))
        if lower > 0:
            leaf_count += 1
            deepest = max(deepest, depth)
            weakest = lower if weakest is None else min(weakest, lower)
            continue
        if depth >= max_depth:
            raise AssertionError(f"degree-{n} unresolved arc cell [{ya},{yb}]")
        midpoint = (ya+yb)/2
        stack.append((midpoint, yb, depth+1))
        stack.append((ya, midpoint, depth+1))
    assert weakest is not None
    return leaf_count, deepest, weakest


# Exact monotonicity of t^3=R_n(y) on the two stationary intervals.
for n, factor in (
    (5, -10*(y-4)*(y-1)/(y**2*(5*y-8)**2)),
    (6, -2*(y-3)*(y-1)/(y**2*(2*y-3)**2)),
):
    d = n-3
    rational = (d*y-n)/(y*(n*y-n-3))
    report(f"degree-{n} stationary ordinate monotonicity identity", sp.factor(sp.diff(rational, y)-factor) == 0)

for n, poly, expected_leaves, expected_depth, rational_floor in (
    (5, P5, 86, 23, Fraction(37, 100)),
    (6, P6, 193, 27, Fraction(1, 20)),
):
    leaves, depth, weakest = prove_curve(n, poly)
    report(
        f"degree-{n} exact stationary-arc positivity",
        (expected_leaves is None or leaves == expected_leaves)
        and (expected_depth is None or depth == expected_depth)
        and weakest > rational_floor,
        f"{leaves} rational boxes, depth {depth}, weakest lower bound > {rational_floor}",
    )

print("ALL CHECKS PASSED")
