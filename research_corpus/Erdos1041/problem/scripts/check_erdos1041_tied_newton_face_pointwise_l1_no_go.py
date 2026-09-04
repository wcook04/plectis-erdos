#!/usr/bin/env python3
"""Exact replay for the degree-six pointwise full-fibre L1 no-go."""

from __future__ import annotations

from fractions import Fraction

import sympy as sp


z, y = sp.symbols("z y")
x = sp.Rational(1001, 1000)
epsilon = x**3 + 3 * x - 4
P = z**6 + 3 * z**2 - epsilon

assert epsilon == sp.Rational(6003001, 10**9)
assert epsilon > 0
assert sp.factor(sp.diff(P, z) - 6 * z * (z**4 + 1)) == 0

# Every critical value has real part -epsilon: at zero it is -epsilon; at
# z^4=-1 it is +/- 2i-epsilon.
assert sp.expand(P.subs(z, 0) + epsilon) == 0
critical_reduction = sp.rem(sp.Poly(P - (2 * z**2 - epsilon), z), sp.Poly(z**4 + 1, z))
assert critical_reduction.as_expr() == 0

# The positive fibre P=4 factors after y=z^2.
fibre_y = y**3 + 3 * y - (4 + epsilon)
assert sp.factor(fibre_y - (y - x) * (y**2 + x * y + x**2 + 3)) == 0
assert sp.discriminant(y**2 + x * y + x**2 + 3, y) == -3 * x**2 - 12

# For either nonreal y-root u, |u|^2=x^2+3 and
# |u^2+1|^2=(x^2+1)(x^2+4).  Reduce the symmetric identities modulo the
# quadratic and its conjugate relations.
u, v = sp.symbols("u v")
norm_identity = sp.expand(
    ((u**2 + 1) * (v**2 + 1) - (x**2 + 1) * (x**2 + 4)).subs(v, -x - u)
)
assert sp.rem(norm_identity, u**2 + x * u + x**2 + 3, u) == 0

# Rational radical bounds from the proof.
A0 = Fraction(31748, 10000)
D1 = Fraction(20031, 10000)
D2 = Fraction(44759, 10000)
xf = Fraction(1001, 1000)

assert A0**3 < 32
gap1 = D1**2 - xf * (xf**2 + 1) ** 2
gap2 = D2**4 - (xf**2 + 3) * ((xf**2 + 1) * (xf**2 + 4)) ** 2
assert gap1 == Fraction(393597994999, 10**15)
assert gap2 == Fraction(26040130756897462775941989999, 10**30)
assert gap1 > 0 and gap2 > 0

lower = 2 * A0 / D1 + 4 * A0 / D2
assert lower == Fraction(44510696, 7409649)
assert lower - 6 == Fraction(52802, 7409649)
assert lower > 6

print("PASS: exact degree-six pointwise full-fibre L1 no-go")
print(f"  x={x}, epsilon={epsilon}")
print(f"  rational speed lower bound={lower} = 6 + {lower - 6}")
print("  all critical values have real part -epsilon < 0")
