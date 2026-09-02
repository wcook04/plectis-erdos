#!/usr/bin/env python3
"""Exact algebra receipt for the two-exterior symmetric merge envelope."""

from __future__ import annotations

import json

import sympy as sp


def main() -> int:
    x, rho, c = sp.symbols("x rho c", positive=True, real=True)
    q = (1 - 2 * rho * x * c + rho**2 * x**2) / (
        x**2 - 2 * rho * x * c + rho**2
    )
    angular = sp.factor(sp.diff(q, c))
    angular_expected = sp.factor(
        2 * rho * x * (1 - x**2) * (1 - rho**2)
        / (x**2 - 2 * rho * x * c + rho**2) ** 2
    )

    r, p = sp.symbols("r p", positive=True, real=True)
    s = sp.sqrt(p)
    h_r = (1 - r * x) * (1 + (p / r) * x) / (
        (x - r) * (x + p / r)
    )
    h_s = (1 - s * x) * (1 + s * x) / ((x - s) * (x + s))
    radial = sp.factor(h_s - h_r)
    radial_expected = sp.factor(
        x * (x**2 - 1) * (1 + p) * (r**2 - p)
        / ((x**2 - p) * (p + r * x) * (x - r))
    )

    n, y = sp.symbols("n y", positive=True, real=True)
    profile = y ** (n / 2) * (1 - p * y) / (y - p)
    critical_numerator = sp.factor(sp.diff(sp.log(profile), y) * 2 * y * (1 - p * y) * (y - p))
    reciprocal = sp.factor(
        n * p * y**2 - ((n + 2) * p**2 + (n - 2)) * y + n * p
    )
    critical_match = sp.simplify(critical_numerator + reciprocal) == 0

    result = {
        "schema": "erdos1041_two_exterior_symmetric_envelope_receipt_v1",
        "angular_polarization_identity": sp.simplify(angular - angular_expected) == 0,
        "radial_polarization_identity": sp.simplify(radial - radial_expected) == 0,
        "symmetric_critical_equation": critical_match,
        "sign_domain": {
            "angular": "x>=1 and 0<rho<1 imply Q'(c)<=0",
            "radial": "1<=x<=1/r, r>=sqrt(p), and 0<p<1 make the displayed difference nonnegative",
        },
        "claim_boundary": "Exact symbolic algebra for the m=2 theorem; no claim for m>=3 or unrestricted Erdős 1041.",
    }
    result["pass"] = all(
        result[key]
        for key in (
            "angular_polarization_identity",
            "radial_polarization_identity",
            "symmetric_critical_equation",
        )
    )
    print(json.dumps(result, indent=2))
    return 0 if result["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
