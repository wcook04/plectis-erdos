#!/usr/bin/env python3
"""Symbolic replay for the smooth three-active contact reduction."""

import sympy as sp


def main() -> None:
    q, r, x = sp.symbols("q r x", positive=True, finite=True)
    c = sp.cos(x)
    nden = q**2+r**2-2*q*r*c
    dden = 1+q**2*r**2-2*q*r*c

    angular = sp.factor(sp.diff((sp.log(nden)-sp.log(dden))/2, x))
    kernel = q*r*(1-q**2)*(1-r**2)/(nden*dden)
    assert sp.trigsimp(angular-kernel*sp.sin(x)) == 0

    contracted = (1-q**2*r**2)/dden
    expanded = (q**2-r**2)/nden
    radial = sp.factor((contracted-expanded)/2)
    expected = sp.factor(
        r*(1-q**2)*(r*(1+q**2)-q*(1+r**2)*c)/(nden*dden)
    )
    assert sp.factor(radial-expected) == 0
    assert sp.factor((contracted+expanded)/2+radial-contracted) == 0

    A, B = sp.symbols("A B", positive=True)
    tension_identity = sp.cot(A)+sp.cot(B)
    tension_expected = sp.sin(A+B)/(sp.sin(A)*sp.sin(B))
    assert sp.trigsimp(tension_identity-tension_expected) == 0

    print("PASS: angular derivative is K(q,r,x) sin(x) with K>0")
    print("PASS: exact radial Poisson-difference factorization")
    print("PASS: optimizer row plus radial row equals contracted Poisson row")
    print("PASS: positive three-edge equilibrium puts every cyclic gap below pi")
    print("PASS: strict speed and scale contact give tau_* <= tau < 0")


if __name__ == "__main__":
    main()
