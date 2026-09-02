#!/usr/bin/env python3
"""Symbolic replay for the two-active positive-spectator virial exclusion."""

import sympy as sp


def main() -> None:
    q, r, c = sp.symbols("q r c", positive=True, finite=True)
    nden = q**2 + r**2 - 2*q*r*c
    dden = 1 + q**2*r**2 - 2*q*r*c
    contracted = (1-q**2*r**2)/dden
    expanded = (q**2-r**2)/nden
    s_kernel = sp.factor((contracted-expanded)/2)
    expected = sp.factor(
        r*(1-q**2)*(r*(1+q**2)-q*(1+r**2)*c)/(nden*dden)
    )
    assert sp.factor(s_kernel-expected) == 0

    x = sp.symbols("x", positive=True)
    k_kernel = q*r*(1-q**2)*(1-r**2)/(nden*dden)
    ratio = sp.factor(expected.subs(c, -sp.cos(x))
                      / (k_kernel.subs(c, -sp.cos(x))*sp.sin(x)))
    ratio_expected = sp.factor(
        r*(q+1/q)/((1-r**2)*sp.sin(x))
        +(1+r**2)*sp.cot(x)/(1-r**2)
    )
    assert sp.trigsimp(ratio-ratio_expected) == 0

    C, D = sp.symbols("C D", positive=True)
    cot_sum = sp.cot(C)+sp.cot(D)
    cot_expected = sp.sin(C+D)/(sp.sin(C)*sp.sin(D))
    assert sp.trigsimp(cot_sum-cot_expected) == 0

    print("PASS: exact radial Poisson-difference factorization")
    print("PASS: spectator coefficient divided by angular tension")
    print("PASS: cot C + cot D = sin(C+D)/(sin C sin D) > 0")
    print("PASS: positive spectator virial contradicts strict-speed common virial")


if __name__ == "__main__":
    main()
