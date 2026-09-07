#!/usr/bin/env python3
"""Exact symbolic replay for regular three-exterior saturation scaling."""

import sympy as sp


def main() -> None:
    n, p, q, e, X = sp.symbols("n p q e X", positive=True)
    p0 = (n - 3) / (n + 3)
    L = -n * sp.log(q) + sp.log(q**3 - p) - sp.log(1 - p * q**3)
    A = (n + 3) ** 2 / 6
    C = n * (n - 3) * (n + 3) / 2

    assert sp.factor(sp.diff(L, q).subs({p: p0, q: 1})) == 0
    assert sp.factor(sp.diff(L, q, 2).subs({p: p0, q: 1})) == 0
    assert sp.factor(sp.diff(L, q, 3).subs({p: p0, q: 1}) - C) == 0
    assert sp.factor(sp.diff(sp.diff(L, q), p).subs({p: p0, q: 1}) - A) == 0
    assert sp.factor(
        sp.diff(L, q, 4).subs({p: p0, q: 1})
        + 3 * n * (n - 3) * (n + 3)
    ) == 0

    scaled = L.subs({p: p0 - e**2, q: 1 - e * X})
    cubic_coefficient = sp.factor(sp.expand(sp.series(scaled, e, 0, 4).removeO()).coeff(e, 3))
    G = sp.factor(A * X - C * X**3 / 6)
    assert sp.factor(cubic_coefficient - G) == 0

    scaled_stationarity = sp.diff(L, q).subs({p: p0 - e**2, q: 1 - e * X})
    stationarity_e2 = sp.factor(
        sp.expand(sp.series(scaled_stationarity, e, 0, 3).removeO()).coeff(e, 2)
    )
    assert sp.factor(stationarity_e2 - (-A + C * X**2 / 2)) == 0

    X2 = sp.factor(2 * A / C)
    assert X2 == sp.factor(2 * (n + 3) / (3 * n * (n - 3)))
    # At X^2=2A/C, G=(2/3)AX.  Verify without adjoining a radical.
    assert sp.factor(((G - sp.Rational(2, 3) * A * X) / X).subs(X**2, X2)) == 0

    assert sp.factor(X2.subs(n, 5) - sp.Rational(8, 15)) == 0
    assert sp.factor(X2.subs(n, 6) - sp.Rational(1, 3)) == 0
    # Squared checks for K_5=256/(9 sqrt 30), K_6=3 sqrt 3.
    K2 = sp.factor((sp.Rational(2, 3) * A) ** 2 * X2)
    assert sp.factor(K2.subs(n, 5) - sp.Rational(32768, 1215)) == 0
    assert sp.factor(K2.subs(n, 6) - 27) == 0

    print("three-exterior regular saturation cubic: exact replay PASS")
    print("checked: corner jets, scaled cubic, optimizer equation, n=5/6 constants")


if __name__ == "__main__":
    main()
