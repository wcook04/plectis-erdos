#!/usr/bin/env python3
"""Exact replay for the degree-six component-block L1 no-go."""

from __future__ import annotations

from fractions import Fraction

import sympy as sp


z, y = sp.symbols("z y")
x = sp.Rational(999, 1000)
epsilon = x**3 + 3 * x - 4
Q = -z**6 - 3 * z**2 + epsilon

assert epsilon == -sp.Rational(5997001, 10**9)
assert epsilon < 0
assert sp.factor(sp.diff(Q, z) + 6 * z * (z**4 + 1)) == 0
assert sp.gcd(sp.Poly(sp.diff(Q, z), z), sp.Poly(sp.diff(Q, z, 2), z)).degree() == 0
assert sp.Poly(sp.diff(Q, z), z).degree() == 5

# Every critical value has real part epsilon: at zero it is epsilon; at
# z^4=-1 it is epsilon +/- 2i.
assert sp.expand(Q.subs(z, 0) - epsilon) == 0
critical_reduction = sp.rem(
    sp.Poly(Q - (epsilon - 2 * z**2), z),
    sp.Poly(z**4 + 1, z),
)
assert critical_reduction.as_expr() == 0

# The negative fibre Q=-4 factors after y=z^2.
fibre_y = y**3 + 3 * y - (4 + epsilon)
assert sp.factor(fibre_y - (y - x) * (y**2 + x * y + x**2 + 3)) == 0
assert sp.discriminant(y**2 + x * y + x**2 + 3, y) == -3 * x**2 - 12

# For either nonreal y-root u, |u|^2=x^2+3 and
# |u^2+1|^2=(x^2+1)(x^2+4).
u, v = sp.symbols("u v")
norm_identity = sp.expand(
    ((u**2 + 1) * (v**2 + 1) - (x**2 + 1) * (x**2 + 4)).subs(v, -x - u)
)
assert sp.rem(norm_identity, u**2 + x * u + x**2 + 3, u) == 0

# Exact passport arithmetic: six total sheets and five simple critical points
# inside the negative preimage force one component.
total_degree = 6
total_ramification = sp.Poly(sp.diff(Q, z), z).degree()
component_count = total_degree - total_ramification
assert total_ramification == 5
assert component_count == 1

A0 = Fraction(31748, 10000)
D1 = Fraction(20031, 10000)
D2 = Fraction(44759, 10000)
xf = Fraction(999, 1000)

assert A0**3 < 32
gap1 = D1**2 - xf * (xf**2 + 1) ** 2
gap2 = D2**4 - (xf**2 + 3) * ((xf**2 + 1) * (xf**2 + 4)) ** 2
assert gap1 == Fraction(24393621995001, 10**15)
assert gap2 == Fraction(2666045458759613463223942009999, 10**30)
assert gap1 > 0 and gap2 > 0

lower = 2 * A0 / D1 + 4 * A0 / D2
assert lower == Fraction(44510696, 7409649)
assert lower - 6 == Fraction(52802, 7409649)
assert lower > 6

print("PASS: exact degree-six component-block L1 no-go")
print(f"  x={x}, epsilon={epsilon}")
print("  all five simple critical values have real part epsilon < 0")
print("  component passport: 6 sheets - 5 ramification = 1 negative component")
print(f"  rational block-speed lower bound={lower} = 6 + {lower - 6}")

