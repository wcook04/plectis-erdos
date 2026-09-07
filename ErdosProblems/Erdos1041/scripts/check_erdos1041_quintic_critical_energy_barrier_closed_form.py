#!/usr/bin/env python3
"""Exact replay for the quintic critical energy barrier."""

from __future__ import annotations

import sympy as sp


def main() -> None:
    t, s = sp.symbols("t s", nonnegative=True)
    h = 1 + t / 2 + s * t**2 / 4
    energy = sp.expand((1 - t) * h**2)
    derivative = sp.factor(sp.diff(energy, t))
    assert derivative == sp.factor(h * t * (4 * s - 6 - 5 * s * t) / 4)

    t_star = (4 * s - 6) / (5 * s)
    assert sp.factor(1 - t_star - (s + 6) / (5 * s)) == 0
    assert sp.factor(1 + s * t_star - (4 * s - 1) / 5) == 0
    assert sp.factor(h.subs(t, t_star) - (1 - t_star) * (1 + s * t_star)) == 0

    maximum = sp.factor(energy.subs(t, t_star))
    closed = (s + 6) ** 3 * (4 * s - 1) ** 2 / (5**5 * s**3)
    assert sp.factor(maximum - closed) == 0

    # The occupied-cone endpoint agrees with the all-degree factorization.
    endpoint = sp.Rational(3, 2)
    assert sp.factor(closed.subs(s, endpoint) - 1) == 0
    endpoint_gap = sp.factor(1 - energy.subs(s, endpoint))
    assert endpoint_gap == t**3 * (9 * t**2 + 15 * t + 40) / 64

    # Reciprocal-vector balance gives p_2>=1/20, hence S_2<=19.
    assert sp.factor(closed.subs(s, 19) - sp.Rational(28125, 6859)) == 0
    assert sp.Rational(1, 1) / closed.subs(s, 19) == sp.Rational(6859, 28125)

    # Exact rational samples verify the derivative sign split around t_*.
    for value in [sp.Rational(3, 2), sp.Rational(8, 5), sp.Rational(2), sp.Rational(4), sp.Rational(19)]:
        if value == endpoint:
            continue
        ts = sp.factor(t_star.subs(s, value))
        assert 0 < ts < 1
        left = sp.factor(derivative.subs({s: value, t: ts / 2}))
        right = sp.factor(derivative.subs({s: value, t: (1 + ts) / 2}))
        assert left > 0 and right < 0

    print("Quintic critical energy barrier closed form: PASS")
    print("Phi_5(S)=1 for S<=3/2; otherwise (S+6)^3(4S-1)^2/(3125S^3)")
    print("sharp target test: mu(S+6)^3(4S-1)^2 <= 3125S^3")


if __name__ == "__main__":
    main()
