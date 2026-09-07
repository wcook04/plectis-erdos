#!/usr/bin/env python3
"""Exact obstruction to the finite radius-weighted three-ray product.

All decisions are rational Sturm counts.  No floating-point optimization is
used in the proof certificate.
"""

from __future__ import annotations

import sympy as sp


x, q = sp.symbols("x q", real=True)
r = sp.Rational(59, 100)
s = sp.Rational(11, 25)
c = -sp.Rational(57, 100)
speed_cap = sp.Rational(19, 4)

# With x=cos(phi), pairing the two symmetric outer Poisson kernels removes
# sin(phi) exactly.  D is their positive denominator product.
A = 1 + r**2 - 2 * r * c * x
D = sp.expand(A**2 - 4 * r**2 * (1 - c**2) * (1 - x**2))
central_den = 1 + s**2 - 2 * s * x
speed = (1 - s**2) / central_den + 2 * (1 - r**2) * A / D
speed_num, speed_den = map(sp.Poly, sp.together(speed_cap - speed).as_numer_denom())

assert central_den.subs(x, -1) > 0 and central_den.subs(x, 1) > 0
assert sp.Poly(D, x).LC() > 0 and sp.discriminant(D, x) < 0
assert sp.count_roots(speed_num, -1, 1) == 0
assert speed_num.eval(0) > 0
assert speed_den.eval(0) > 0

# Regular comparison: R_5(p) is bounded by K on all 0<q<1.  The lower
# endpoint p^(1/3) is unnecessary because the stronger interval is certified.
p = r**2 * s
K = sp.Rational(1213, 1000)
regular_gap = sp.Poly(sp.expand(K * q**5 * (1 - p * q**3) - (q**3 - p)), q)
assert sp.count_roots(regular_gap, 0, 1) == 0
assert regular_gap.eval(0) > 0

# Centre-ray value at q=7/12.  The symmetric outer pair squares to a rational
# factor, so no algebraic sine remains.
q0 = sp.Rational(7, 12)
centre_value = sp.factor(
    ((q0 - s) / (1 - s * q0))
    * ((q0**2 + r**2 - 2 * q0 * r * c) / (1 + q0**2 * r**2 - 2 * q0 * r * c))
    / q0**5
)
assert centre_value == sp.Rational(16651505000448, 8153887797433)

# Clearing the hundredths in the weights leaves powers 59,44,59.  Endpoint
# limits give V_outer >= 1, hence this strict comparison refutes the product.
power_gap = sp.factor(centre_value**44 - K**162)
assert power_gap > 0

print("finite speed cap:", speed_cap)
print("regular comparator cap:", K)
print("centre-ray rational witness:", centre_value)
print("PASS exact finite weighted-product obstruction")
