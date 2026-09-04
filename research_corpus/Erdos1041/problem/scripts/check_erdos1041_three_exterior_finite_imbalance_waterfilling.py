#!/usr/bin/env python3
"""Exact replay for the finite three-exterior imbalance water-filling cone."""

from __future__ import annotations

import sympy as sp


def report(name: str, ok: bool, detail: str = "") -> None:
    print(("PASS " if ok else "FAIL ") + name + ((" :: " + detail) if detail else ""))
    if not ok:
        raise AssertionError(name)


q, r, u = sp.symbols("q r u", positive=True, real=True)
p = u * r**2
A = (q**2-r**2)*(q+u)/((1-r**2*q**2)*(1+u*q))
T = (q**3-p)/(1-p*q**3)
B = -r**2*(1-u**2)*(q**2+1) + q*u*(1-r**4)
factor = q*(q-1)*(q+1)*B / ((q*r-1)*(q*r+1)*(q*u+1)*(p*q**3-1))
report("exact regular-minus-water factorization", sp.factor(T-A-factor) == 0)

h = sp.symbols("h", positive=True, real=True)
D = (1-r**2*q**2)*(1+h*r*q)
report(
    "water denominator displacement identity",
    sp.expand(D-1-q*(h*r-r**2*q-h*r**3*q**2)) == 0,
)
report(
    "pointwise bracket majorization",
    sp.factor(
        B.subs(u,h*r)
        - q*(h*r*(1-r**4)-2*r**2*(1-h**2*r**2))
        + r**2*(1-h**2*r**2)*(q-1)**2
    ) == 0,
)

# Exact h_n=T_n^{-3} enclosures.  For n=5, h_5^2=C_5^3/M_5^3 and
# C_5^3=108/3125.  For n=6, h_6=C_6/M_6 with C_6=1/4.
M5 = (sp.Integer(822) + 82*sp.sqrt(41))/3125
h5_sq = sp.Rational(108,3125)/M5**3
h5 = sp.sqrt(h5_sq)
M6 = (sp.Integer(12881) + 2117*sp.sqrt(73))/93312
h6 = sp.Rational(1,4)/M6
report(
    "degree-five exact h enclosure",
    sp.simplify(h5_sq-sp.Rational(13,20)**2) > 0
    and sp.simplify(sp.Rational(2,3)**2-h5_sq) > 0,
    "13/20<h5<2/3",
)
report(
    "degree-six exact h enclosure",
    sp.simplify(h6-sp.Rational(3,4)) > 0
    and sp.simplify(sp.Rational(19,25)-h6) > 0,
    "3/4<h6<19/25",
)

r5 = sp.Rational(3,8)
r6 = sp.Rational(5,12)
low5 = sp.factor((1-r5**2)**5-(r5/sp.Rational(13,20))**2)
low6 = sp.factor((1-r6**2)**2-r6/sp.Rational(3,4))
report(
    "degree-five low-radius splice",
    low5 == sp.Rational(24657081775,181462368256) and low5 > 0,
    str(low5),
)
report(
    "degree-six low-radius splice",
    low6 == sp.Rational(2641,20736) and low6 > 0,
    str(low6),
)

def F(rr, hh):
    return sp.factor(2*rr*(1-hh**2*rr**2)-hh*(1-rr**4))

high5 = F(r5,sp.Rational(2,3))
high6 = F(r6,sp.Rational(19,25))
report(
    "degree-five high-radius starting margin",
    high5 == sp.Rational(305,6144) and high5 > 0,
    str(high5),
)
report(
    "degree-six high-radius starting margin",
    high6 == sp.Rational(6571,518400) and high6 > 0,
    str(high6),
)

# F'(r)=2-6h^2r^2+4hr^3.  The displayed rational lower estimates suffice
# throughout the exact speed ranges r<2/3 and r<5/7.
der5_floor = sp.factor(2-6*sp.Rational(2,3)**2*sp.Rational(2,3)**2)
der6_floor = sp.factor(2-6*sp.Rational(19,25)**2*sp.Rational(5,7)**2)
report("degree-five F increasing", der5_floor > 0, str(der5_floor))
report("degree-six F increasing", der6_floor > 0, str(der6_floor))

# The speed radii force p<d/n, so the homogeneous regular maximizer lies
# inside q<1 and supplies the lower comparator C_n p^{-d/3}.
report("degree-five regular maximizer in domain", sp.Rational(2,3)**3 < sp.Rational(2,5))
report("degree-six regular maximizer in domain", sp.Rational(5,7)**3 < sp.Rational(1,2))

print("ALL CHECKS PASSED")
