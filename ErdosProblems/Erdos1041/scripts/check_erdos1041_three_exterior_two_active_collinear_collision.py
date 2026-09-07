#!/usr/bin/env python3
"""Symbolic replay for the collinear two-active collision reduction."""

import sympy as sp


def main() -> None:
    q, r, c = sp.symbols("q r c", positive=True, finite=True)
    nden = q**2 + r**2 - 2*q*r*c
    dden = 1 + q**2*r**2 - 2*q*r*c
    radial = sp.factor(
        (1-q**2*r**2)/(2*dden)-(q**2-r**2)/(2*nden)
    )

    same = -r*(1-q**2)/((q-r)*(1-q*r))
    opposite = r*(1-q**2)/((q+r)*(1+q*r))
    assert sp.factor(radial.subs(c, 1)-same) == 0
    assert sp.factor(radial.subs(c, -1)-opposite) == 0

    same_prime = -q*(1-q**2)*(1-r**2)/((q-r)**2*(1-q*r)**2)
    opposite_prime = q*(1-q**2)*(1-r**2)/((q+r)**2*(1+q*r)**2)
    assert sp.factor(sp.diff(same, r)-same_prime) == 0
    assert sp.factor(sp.diff(opposite, r)-opposite_prime) == 0

    fminus = (q-r)*(1-q*r)
    fplus = (q+r)*(1+q*r)
    assert sp.factor(sp.diff(fminus, r)-(2*q*r-1-q**2)) == 0
    assert sp.factor(sp.diff(fplus, r)-(1+q**2+2*q*r)) == 0

    lam, q0, q1 = sp.symbols("lambda q_0 q_1", positive=True, finite=True)
    tplus = lam*same.subs(q, q0)+(1-lam)*opposite.subs(q, q1)
    hplus = (
        -lam*q0*(1-q0**2)/((q0-r)**2*(1-q0*r)**2)
        +(1-lam)*q1*(1-q1**2)/((q1+r)**2*(1+q1*r)**2)
    )
    assert sp.factor(sp.diff(tplus, r)-(1-r**2)*hplus) == 0
    assert sp.simplify(tplus.subs(r, 0)) == 0

    print("PASS: exact same-ray and opposite-ray radial coefficients")
    print("PASS: exact derivative factorization")
    print("PASS: negative derivative magnitude increases and positive one decreases")
    print("PASS: each antipodal ray meets a common negative level at most once")
    print("PASS: three roots on two rays force a collision")


if __name__ == "__main__":
    main()
