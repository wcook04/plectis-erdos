#!/usr/bin/env python3
"""Exact symbolic replay for the three-exterior soft-min scale derivative."""

from __future__ import annotations

import sympy as sp


def report(name: str, ok: bool) -> None:
    print(("PASS " if ok else "FAIL ") + name)
    if not ok:
        raise AssertionError(name)


q, r, c = sp.symbols("q r c", positive=True, real=True)
N = q**2 + r**2 - 2*q*r*c
D = 1 + q**2*r**2 - 2*q*r*c
log_q = q*((q-r*c)/N - (q*r**2-r*c)/D)
log_r = r*((r-q*c)/N - (q**2*r-q*c)/D)
P_expanded = (q**2-r**2)/N
P_contracted = (1-q**2*r**2)/D

report(
    "radial-parameter Poisson average identity",
    sp.factor(log_q-(P_expanded+P_contracted)/2) == 0,
)
report(
    "common-scale Poisson difference identity",
    sp.factor(log_r-(P_contracted-P_expanded)/2) == 0,
)

# Stationarity eliminates the expanded Poisson row.
n, contracted = sp.symbols("n contracted", real=True)
expanded = 2*n-contracted
report(
    "stationary scale-envelope elimination",
    sp.expand((contracted-expanded)/2-(contracted-n)) == 0,
)

# Three regular directions: one diagonal and two cosines -1/2.
rho = sp.symbols("rho", positive=True, real=True)
P_diag = (1-rho**2)/(1+rho**2-2*rho)
P_off = (1-rho**2)/(1+rho**2+rho)
report(
    "regular three-ray contracted speed",
    sp.factor(P_diag+2*P_off-3*(1+rho**3)/(1-rho**3)) == 0,
)

# A negative-order power mean has logarithmic coordinate weights x_j^-p/S.
x1, x2, x3, p = sp.symbols("x1 x2 x3 p", positive=True, real=True)
xs = (x1, x2, x3)
S = sum(x**(-p) for x in xs)
logM = (sp.log(3)-sp.log(S))/p
for index, x in enumerate(xs):
    weight = x**(-p)/S
    report(
        f"soft-min logarithmic weight {index}",
        sp.simplify(x*sp.diff(logM, x)-weight) == 0,
    )

# The equality Hessian can be replayed with a formal second-order jet.
eps, e = sp.symbols("eps e", positive=True, real=True)
v1, v2, w1, w2, w3 = sp.symbols("v1 v2 w1 w2 w3", real=True)
v3 = -v1-v2
jets = (
    e+eps*v1+eps**2*w1/2,
    e+eps*v2+eps**2*w2/2,
    e+eps*v3+eps**2*w3/2,
)
mean = (3/sum(x**(-p) for x in jets))**(1/p)
second = sp.simplify(sp.diff(mean, eps, 2).subs(eps, 0))
expected = (w1+w2+w3)/3-(p+1)*(v1**2+v2**2+v3**2)/(3*e)
report("soft-min equality Hessian", sp.simplify(second-expected) == 0)

# Parameter derivative identity.  Its sign is the standard negative-order
# power-mean monotonicity; the checker replays the exact formula.
M = sp.exp(logM)
weights = [x**(-p)/S for x in xs]
parameter_formula = sum(w*sp.log(x/M) for w, x in zip(weights, xs))/p
report(
    "soft-min exponent derivative identity",
    sp.simplify(sp.diff(logM, p)-parameter_formula) == 0,
)

print("ALL CHECKS PASSED")
