#!/usr/bin/env python3
"""Exact symbolic replay for the GP3 endpoint curvature gain."""

from fractions import Fraction as Q
import json

import sympy as sp


def main() -> int:
    q, r, x = sp.symbols("q r x", positive=True)
    d1 = q**2 + r**2 - 2 * q * r * x
    d2 = 1 + q**2 * r**2 - 2 * q * r * x
    H = (q - r * x) / d1 - (q * r**2 - r * x) / d2
    h2 = 4 * q * r**2 * ((q**2 - r**2) / d1**3 + (1 - q**2 * r**2) / d2**3)
    h3 = 24 * q**2 * r**3 * ((q**2 - r**2) / d1**4 + (1 - q**2 * r**2) / d2**4)
    derivative_two = sp.cancel(sp.diff(H, x, 2) - h2) == 0
    derivative_three = sp.cancel(sp.diff(H, x, 3) - h3) == 0

    a, b, c, kappa, mu = sp.symbols("a b c kappa mu", positive=True)
    F = b * c - a * (b + c)
    slope_identity = sp.factor(a - b * c / (b + c) + F / (b + c)) == 0
    m_stat = -sp.Rational(1, 2) * (a * b / c + a * c / b + b * c / a)
    m_end = a - b - c
    switch_square = sp.factor(m_end - m_stat - F**2 / (2 * a * b * c)) == 0

    xstar = kappa / mu - sp.Rational(1, 2)
    gain = kappa * (1 - x) + mu * (x + sp.Rational(1, 2))**2 / 2
    interior_gain = sp.factor(gain.subs(x, xstar))
    endpoint_gain = sp.factor(gain.subs(x, 1))
    interior_formula = sp.factor(
        interior_gain - (3 * kappa / 2 - kappa**2 / (2 * mu))
    ) == 0
    endpoint_formula = endpoint_gain == 9 * mu / 8
    splice_agrees = sp.factor(
        (3 * kappa / 2 - kappa**2 / (2 * mu) - 9 * mu / 8).subs(
            kappa, 3 * mu / 2
        )
    ) == 0

    # Exact in-domain specimen: q=3/4 and radii 1/4,1/2.
    h2_fn = sp.lambdify((q, r, x), h2, "sympy")
    mu_spec = Q(1, 4) * Q(h2_fn(Q(3, 4), Q(1, 2), Q(-1)))
    mu_spec += Q(1, 2) * Q(h2_fn(Q(3, 4), Q(1, 4), Q(-1)))
    specimen_positive = mu_spec > 0

    checks = {
        "second_derivative_identity": derivative_two,
        "third_derivative_identity": derivative_three,
        "endpoint_slope_identity": slope_identity,
        "switch_square_identity": switch_square,
        "interior_gain_formula": interior_formula,
        "endpoint_gain_formula": endpoint_formula,
        "splice_agrees": splice_agrees,
        "exact_mu_specimen_positive": specimen_positive,
    }
    passed = all(checks.values())
    result = {
        "schema": "erdos1041_three_exterior_endpoint_curvature_gain_receipt_v1",
        "checks": checks,
        "exact_mu_specimen": str(mu_spec),
        "gain_formula": {
            "interior": "3*kappa/2-kappa^2/(2*mu)",
            "boundary": "9*mu/8",
            "switch": "kappa=3*mu/2",
        },
        "endpoint_curvature_gain_exact": passed,
        "claim_boundary": ("Proves the exact positive curvature payment on the "
                           "GP3 endpoint branch. It does not establish the "
                           "remaining switch-surface stationary inequality, "
                           "GP3, or Erdos 1041."),
        "pass": passed,
    }
    print(json.dumps(result, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
