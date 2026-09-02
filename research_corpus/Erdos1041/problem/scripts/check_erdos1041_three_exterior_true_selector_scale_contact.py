#!/usr/bin/env python3
"""Exact replay for the true-selector scale-contact reduction."""

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
expanded = (q**2-r**2)/N
contracted = (1-q**2*r**2)/D

report(
    "radial Poisson average",
    sp.factor(log_q-(expanded+contracted)/2) == 0,
)
report(
    "scale Poisson difference",
    sp.factor(log_r-(contracted-expanded)/2) == 0,
)

n, C, Cstar = sp.symbols("n C Cstar", real=True)
expanded_sum = 2*n-C
scale_v = sp.expand((C-expanded_sum)/2)
report("stationary attached scale derivative", sp.expand(scale_v-(C-n)) == 0)
report(
    "relative envelope cancellation",
    sp.expand((C-n)-(Cstar-n)-(C-Cstar)) == 0,
)

rho = sp.symbols("rho", positive=True, real=True)
P_diag = (1-rho**2)/(1+rho**2-2*rho)
P_off = (1-rho**2)/(1+rho**2+rho)
report(
    "regular contracted speed",
    sp.factor(P_diag+2*P_off-3*(1+rho**3)/(1-rho**3)) == 0,
)

# Direct regular-profile differentiation agrees with the Poisson envelope
# formula before imposing optimizer stationarity.
s = sp.symbols("s", positive=True, real=True)
T = (q**3-s**3)/(1-s**3*q**3)
C_regular = 3*(1+(q*s)**3)/(1-(q*s)**3)
report(
    "regular scale/radial envelope identity",
    sp.factor(
        s*sp.diff(sp.log(T), s)
        -(C_regular-q*sp.diff(sp.log(T), q))
    ) == 0,
)

print("ALL CHECKS PASSED")
