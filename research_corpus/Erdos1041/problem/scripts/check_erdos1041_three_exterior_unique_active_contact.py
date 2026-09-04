#!/usr/bin/env python3
"""Exact replay for exclusion of smooth unique-active three-ray contacts."""

from __future__ import annotations

import sympy as sp


def report(name: str, ok: bool) -> None:
    print(("PASS " if ok else "FAIL ") + name)
    if not ok:
        raise AssertionError(name)


q, r, a = sp.symbols("q r a", positive=True, real=True)
c = sp.cos(a)
N = q**2+r**2-2*q*r*c
D = 1+q**2*r**2-2*q*r*c
logrho = sp.log(N)/2-sp.log(D)/2
angular = sp.factor(sp.diff(logrho, a))
angular_expected = q*r*(1-q**2)*(1-r**2)*sp.sin(a)/(N*D)
report("strict angular sine factor", sp.simplify(angular-angular_expected) == 0)

P_plus_contract = (1+q*r)/(1-q*r)
P_plus_expand = (q+r)/(q-r)
S_plus = sp.factor((P_plus_contract-P_plus_expand)/2)
report(
    "same-ray scale derivative",
    sp.factor(S_plus+r*(1-q**2)/((1-q*r)*(q-r))) == 0,
)

P_minus_contract = (1-q*r)/(1+q*r)
P_minus_expand = (q-r)/(q+r)
S_minus = sp.factor((P_minus_contract-P_minus_expand)/2)
report(
    "opposite-ray scale derivative",
    sp.factor(S_minus-r*(1-q**2)/((1+q*r)*(q+r))) == 0,
)

cluster_gap = sp.factor(
    (q**2+q*r+r**2)*(1-q*r)**2
    -(q-r)**2*(1+q*r+q**2*r**2)
)
report(
    "triple-cluster strict polarization factor",
    cluster_gap == 3*q*r*(q-1)*(q+1)*(r-1)*(r+1),
)

print("ALL CHECKS PASSED")
