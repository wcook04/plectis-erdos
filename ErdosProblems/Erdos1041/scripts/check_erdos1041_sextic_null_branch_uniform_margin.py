#!/usr/bin/env python3
"""Exact identities and a deterministic stress check for the uniform margin."""

from __future__ import annotations

import math

import sympy as sp


def main() -> None:
    s = sp.sqrt(3)
    beta_star = (106 + 25 * s) / 1221
    q0 = (7 + 4 * s) / 27
    a0 = -sp.Rational(86, 9) + sp.Rational(17, 3) * s
    kappa = sp.Rational(3, 10) * s * (s - 1) * (2 - s)

    assert sp.simplify(a0 * beta_star - (-sp.Rational(13, 27) + 8 * s / 27)) == 0
    assert sp.N(a0 * beta_star - sp.Rational(1, 100), 50) > 0
    assert sp.simplify(kappa - (sp.Rational(27, 10) - 3 * s / 2)) == 0
    assert sp.N(kappa - sp.Rational(1, 10), 50) > 0
    assert sp.N(sp.Rational(1, 4) - beta_star, 50) > 0

    beta, t, ell, emm = sp.symbols("beta t L M", real=True)
    p = t**2 + 2 * t - 2
    left = t**2 - 4 * t + 1
    right = 2 * t**2 - 2 * t - 1
    qminus = q0 * (1 - sp.Rational(3, 2) * beta * (s - 1))
    qplus = q0 * (1 + sp.Rational(3, 2) * beta * (s - 1))
    mirror = p * (1 - qminus * left * right) - 3 * s * beta * (2 - s) * t + 3 * s * beta * t * (1 - t)
    companion = p * (1 - qminus * left * right) - 3 * s * beta * ell * (2 - s) * t + 3 * s * beta * emm * t * (1 - t)
    defect = -3 * s * beta * t * ((ell - 1) * (2 - s) + (1 - emm) * (1 - t))
    assert sp.expand(companion - mirror - defect) == 0
    assert sp.simplify(qplus - qminus - 3 * q0 * beta * (s - 1)) == 0

    sf = math.sqrt(3.0)
    bsf = float(beta_star)
    q0f = float(q0)

    def chord(b: float, x: float) -> float:
        qm = q0f * (1.0 - 1.5 * b * (sf - 1.0))
        qp = q0f * (1.0 + 1.5 * b * (sf - 1.0))
        L = (qp / qm) ** 0.25
        M = 1.0 / L
        pp = x * x + 2.0 * x - 2.0
        lf = x * x - 4.0 * x + 1.0
        rf = 2.0 * x * x - 2.0 * x - 1.0
        return pp * (1.0 - qm * lf * rf) - 3.0 * sf * b * L * (2.0 - sf) * x + 3.0 * sf * b * M * x * (1.0 - x)

    worst_slack = math.inf
    worst_point = None
    # Each epsilon is checked against all beta in its remaining compact branch.
    for eps_fraction in (1 / 64, 1 / 32, 1 / 16, 1 / 8, 1 / 4, 1 / 2, 1.0):
        eps = bsf * eps_fraction
        for ib in range(81):
            b = eps + (bsf - eps) * ib / 80.0
            for it in range(401):
                x = it / 400.0
                slack = -eps * eps / 10.0 - chord(b, x)
                if slack < worst_slack:
                    worst_slack = slack
                    worst_point = (eps, b, x)
                assert slack >= -2e-12, (slack, eps, b, x)

    print("exact identities: PASS")
    print(f"betaStar={bsf:.15f}")
    print(f"ray margin={float(a0 * beta_star):.15f}")
    print(f"large-chord coefficient={float(kappa):.15f}")
    print(f"dense margin stress: PASS; least slack={worst_slack:.12g} at {worst_point}")


if __name__ == "__main__":
    main()
