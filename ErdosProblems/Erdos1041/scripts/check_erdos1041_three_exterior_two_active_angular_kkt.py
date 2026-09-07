#!/usr/bin/env python3
"""Symbolic replay for the smooth two-active angular KKT reduction."""

from __future__ import annotations

import sympy as sp


def main() -> None:
    q, r, x = sp.symbols("q r x", positive=True, real=True)
    N = q**2 + r**2 - 2*q*r*sp.cos(x)
    D = 1 + q**2*r**2 - 2*q*r*sp.cos(x)
    log_rho = (sp.log(N) - sp.log(D))/2
    kernel = q*r*(1-q**2)*(1-r**2)/(N*D)

    assert sp.simplify(sp.diff(log_rho, x) - kernel*sp.sin(x)) == 0
    assert sp.factor(D-N) == (q-1)*(q+1)*(r-1)*(r+1)

    def poisson(radius: sp.Expr) -> sp.Expr:
        return (1-radius**2)/(1+radius**2-2*radius*sp.cos(x))

    radial = sp.simplify(r*sp.diff(log_rho, r))
    radial_poisson = sp.simplify((poisson(q*r)-poisson(r/q))/2)
    assert sp.simplify(radial-radial_poisson) == 0

    a, b, c, d, t = sp.symbols("a b c d t", nonzero=True, real=True)
    relations = {d: -t*b, c: -t*(a+b)}
    determinant = d*(a+b)-b*c
    assert sp.simplify(determinant.subs(relations, simultaneous=True)) == 0

    # The two KKT coordinates invert exactly to the displayed relations.
    eq_a = t*a+c-d
    eq_b = t*b+d
    assert sp.simplify(eq_a.subs(relations, simultaneous=True)) == 0
    assert sp.simplify(eq_b.subs(relations, simultaneous=True)) == 0

    # Positive tension form in the canonical coordinates B=pi+C.
    k01, k10, k02, k12 = sp.symbols("k01 k10 k02 k12", positive=True)
    sA, sC, sAC = sp.symbols("sA sC sAC", positive=True)
    tension_t = k12*sAC/(k02*sC)
    tension_equation = sp.expand((tension_t*k01+k10)*sA-k12*sAC)
    positive_form = k10*sA-k12*sAC*(1-k01*sA/(k02*sC))
    assert sp.simplify(tension_equation-positive_form) == 0

    lam = sp.symbols("lam", positive=True)
    w02 = lam*k02
    w12 = (1-lam)*k12
    assert sp.simplify(
        (w12*sAC-w02*sC).subs(lam, tension_t/(1+tension_t))
    ) == 0

    # A representative point of the canonical chamber has the forced signs.
    A0 = sp.pi/3
    B0 = 7*sp.pi/6
    assert sp.sin(A0) > 0
    assert sp.sin(B0) < 0
    assert sp.sin(B0-A0) > 0
    assert 0 < A0 < sp.pi < B0 < A0+sp.pi < 2*sp.pi

    print("PASS exact two-active angular KKT reduction")
    print("angular derivative", sp.simplify(sp.diff(log_rho, x)))
    print("radial derivative", radial_poisson)
    print("canonical chamber 0<A<pi<B<A+pi<2pi")
    print("positive tension equation", positive_form)


if __name__ == "__main__":
    main()
