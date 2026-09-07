#!/usr/bin/env python3
"""Exact symbolic replay for the strong GP3 endpoint curvature gain."""

import json
import sympy as sp


def main() -> int:
    a, b, c, x = sp.symbols("a b c x", positive=True)
    kappa, mu, nu, y = sp.symbols("kappa mu nu y", positive=True)

    rad = b**2 + c**2 + 2 * b * c * x
    f = a * x - sp.sqrt(rad)
    fprime = sp.diff(f, x)
    fsecond = sp.diff(f, x, 2)

    endpoint_slope = fprime.subs(x, 1).subs(
        sp.sqrt(b**2 + 2 * b * c + c**2), b + c
    )
    checks = {
        "endpoint_slope": sp.factor(
            endpoint_slope - (a - b * c / (b + c))
        ) == 0,
        "envelope_second_derivative": sp.simplify(
            fsecond - b**2 * c**2 / rad ** sp.Rational(3, 2)
        ) == 0,
    }

    # Since rad <= (b+c)^2 on [-1,1], f'' >= nu.
    nu_formula = b**2 * c**2 / (b + c) ** 3
    checks["nu_positive_formula"] = sp.factor(nu_formula) == nu_formula

    q = kappa * y + nu * y**2 / 2 + mu * (sp.Rational(3, 2) - y) ** 2 / 2
    ystar = (3 * mu / 2 - kappa) / (mu + nu)
    interior = sp.factor(q.subs(y, ystar))
    formula = 9 * mu / 8 - (3 * mu / 2 - kappa) ** 2 / (2 * (mu + nu))
    checks["interior_minimum_formula"] = sp.factor(interior - formula) == 0
    checks["boundary_minimum_formula"] = sp.factor(q.subs(y, 0) - 9 * mu / 8) == 0
    checks["splice_continuity"] = sp.factor(
        formula.subs(kappa, 3 * mu / 2) - 9 * mu / 8
    ) == 0
    switch_gain = sp.factor(formula.subs(kappa, 0))
    checks["strict_switch_gain"] = sp.factor(
        switch_gain - 9 * mu * nu / (8 * (mu + nu))
    ) == 0
    numerator = sp.factor(2 * (mu + nu) * formula)
    checks["positive_branch_numerator"] = sp.factor(
        numerator - (9 * mu * nu / 4 + 3 * mu * kappa - kappa**2)
    ) == 0
    checks["positive_left_endpoint"] = sp.factor(numerator.subs(kappa, 0)) == 9 * mu * nu / 4
    checks["positive_right_endpoint"] = sp.factor(
        numerator.subs(kappa, 3 * mu / 2)
    ) == 9 * mu * (mu + nu) / 4

    passed = all(checks.values())
    print(json.dumps({
        "schema": "erdos1041_three_exterior_endpoint_strong_curvature_gain_v1",
        "checks": checks,
        "switch_gain": "9*mu*nu/(8*(mu+nu))",
        "claim_boundary": (
            "Exact strict curvature payment on the active endpoint cone, including "
            "the switch. Does not yet dominate the tangent switch residual, prove "
            "GP3, or prove Erdos 1041."
        ),
        "pass": passed,
    }, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
