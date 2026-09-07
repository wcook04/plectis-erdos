#!/usr/bin/env python3
"""Symbolic replay of the three-exterior terminal saturation cubic atlas."""

from __future__ import annotations

import sympy as sp


q, p, n = sp.symbols("q p n", positive=True, real=True)
Lreg = -n * sp.log(q) + sp.log(q**3 - p) - sp.log(1 - p * q**3)
p0 = (n - 3) / (n + 3)

assert sp.factor(sp.diff(Lreg, q).subs({q: 1, p: p0})) == 0
assert sp.factor(sp.diff(Lreg, q, 2).subs({q: 1, p: p0})) == 0
assert sp.factor(sp.diff(Lreg, q, 3).subs({q: 1, p: p0})) == n * (n - 3) * (n + 3) / 2
assert sp.factor(sp.diff(Lreg, q, 4).subs({q: 1, p: p0})) == -3 * n * (n - 3) * (n + 3)
assert sp.factor(sp.diff(Lreg, p, q).subs({q: 1, p: p0})) == (n + 3) ** 2 / 6

for degree, expected_x2, expected_k2 in (
    (5, sp.Rational(8, 15), sp.Rational(32768, 1215)),
    (6, sp.Rational(1, 3), sp.Integer(27)),
):
    A = sp.Rational((degree + 3) ** 2, 6)
    C = sp.Rational(degree * (degree - 3) * (degree + 3), 2)
    X2 = sp.factor(2 * A / C)
    K2 = sp.factor((sp.Rational(2, 3) * A) ** 2 * X2)
    assert X2 == expected_x2
    assert K2 == expected_k2


# Endpoint perturbation variables.
s, T = sp.symbols("s T", positive=True, real=True)
x0, x1 = sp.symbols("x0 x1", real=True)
xs = (x0, x1, -x0 - x1)
phi0, phi1 = sp.symbols("phi0 phi1", real=True)
phis = (phi0, phi1, -phi0 - phi1)


def poisson(radius: sp.Expr, cosine: sp.Expr) -> sp.Expr:
    return (1 - radius**2) / (1 - 2 * radius * cosine + radius**2)


def speeds(radii: tuple[sp.Expr, ...], angles: tuple[sp.Expr, ...]) -> tuple[sp.Expr, ...]:
    return tuple(
        sum(poisson(radii[k], sp.cos(angles[k] - angles[j])) for k in range(3))
        for j in range(3)
    )


radii1 = tuple(s * sp.exp(T * xs[k]) for k in range(3))
angles1 = tuple(2 * sp.pi * k / 3 + T * phis[k] for k in range(3))
g1 = speeds(radii1, angles1)
ells = tuple(sp.factor(sp.diff(value, T).subs(T, 0)) for value in g1)
assert sp.factor(sum(ells)) == 0

kernel = sp.solve(ells[:2], (phi0, phi1), dict=True, simplify=False)
assert len(kernel) == 1
kernel = {key: sp.factor(value) for key, value in kernel[0].items()}
common = s**4 + 2 * s**3 + 2 * s + 1
expected_kernel = {
    phi0: sp.sqrt(3) * (x0 + 2 * x1) * common / (3 * (s - 1) ** 3 * (s + 1)),
    phi1: -sp.sqrt(3) * (2 * x0 + x1) * common / (3 * (s - 1) ** 3 * (s + 1)),
}
assert all(sp.factor(kernel[key] - expected_kernel[key]) == 0 for key in expected_kernel)
assert sp.factor(ells[2].subs(kernel)) == 0


# The potentially dangerous first variation of L_qq vanishes on the speed
# kernel for each attached ray.
def attached_log(ray: int) -> sp.Expr:
    value = -n * sp.log(q)
    for k in range(3):
        radius = radii1[k]
        cosine = sp.cos(angles1[k] - angles1[ray])
        value += sp.Rational(1, 2) * sp.log(q**2 - 2 * q * radius * cosine + radius**2)
        value -= sp.Rational(1, 2) * sp.log(1 - 2 * q * radius * cosine + q**2 * radius**2)
    return value


for ray in range(3):
    mixed = sp.diff(sp.diff(attached_log(ray), q, 2).subs(q, 1), T).subs(T, 0)
    assert sp.factor(mixed.subs(kernel)) == 0


# Fixed product p=p0-T^2 gives sum second log-radius accelerations -1/s^3.
# A common acceleration is sufficient because the summed linear acceleration
# coefficient is symmetric; zero-sum accelerations cancel.
v = -1 / (3 * s**3)
radii2 = tuple(s * sp.exp(T * xs[k] + T**2 * v) for k in range(3))
angles2 = tuple(2 * sp.pi * k / 3 + T * phis[k] for k in range(3))
sum_speed = sum(speeds(radii2, angles2))
sum_second = sp.factor(sp.diff(sum_speed, T, 2).subs(T, 0) / 2)
sum_second = sp.factor(sum_second.subs(kernel))
regular_second = sp.factor(sum_second.subs({x0: 0, x1: 0}))
assert regular_second == -18 / ((s - 1) ** 2 * (s**2 + s + 1) ** 2)

D = (
    18
    * s**2
    * (s**2 - s + 1)
    * (s**2 + 4 * s + 1)
    * (4 * s**4 + 5 * s**3 + 5 * s + 4)
    / ((1 - s) ** 5 * (1 + s) * (s**2 + s + 1) ** 3)
)
Q = D * (x0**2 + x0 * x1 + x1**2)
assert sp.factor(sum_second - regular_second - Q) == 0

# At s^3=p0, -regular_second is 3A_n.
assert sp.factor(
    (-regular_second).subs(s**3, p0) - 3 * (n + 3) ** 2 / 6
) == 0

# Endpoint sign factor from the already-certified finite mixed-kernel
# Hessian.  Reduction modulo s^3=p0 proves that its single (1-q) factor is
# the only vanishing order at saturation.
hend = (
    7 * s**10
    - 21 * s**9
    - 149 * s**8
    - 8 * s**7
    + 22 * s**6
    - 350 * s**5
    + 22 * s**4
    - 8 * s**3
    - 149 * s**2
    - 21 * s
    + 7
)
for degree, expected in (
    (5, -sp.Rational(9, 64) * (1748 * s**2 + 113 * s - 43)),
    (6, -sp.Rational(2, 27) * (3810 * s**2 + 193 * s - 81)),
):
    endpoint_product = sp.Rational(degree - 3, degree + 3)
    reduced = sp.rem(hend, s**3 - endpoint_product, s)
    assert sp.factor(reduced - expected) == 0
    # Since s>1/2, the parenthesis is bounded below by this positive value.
    assert sp.factor((-expected).subs(s, sp.Rational(1, 2))) > 0

print("PASS regular cubic endpoint jets")
print("PASS exact n=5,6 scaled optimizer constants")
print("PASS speed first-variation zero-sum and unique kernel")
print("PASS mixed L_qq cancellation on the speed kernel")
print("PASS positive-definite second-order speed loss")
print("PASS nondegenerate endpoint limit of the finite mixed-kernel Hessian")
print("ALL CHECKS PASSED")
