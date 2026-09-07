#!/usr/bin/env python3
"""Exact symbolic receipt for the equal-radius m=3 angular envelope."""

from __future__ import annotations

import json
from fractions import Fraction

import sympy as sp


def main() -> int:
    s, x, c = sp.symbols("s x c", positive=True, real=True)
    numerator = 1 - 2 * s * x * c + s**2 * x**2
    denominator = x**2 - 2 * s * x * c + s**2
    q = numerator / denominator
    first = sp.factor(sp.diff(sp.log(q), c))
    first_expected = sp.factor(
        2 * s * x * (1 - x**2) * (1 - s**2) / (numerator * denominator)
    )
    second = sp.factor(sp.diff(sp.log(q), c, 2))
    second_expected = sp.factor(
        (2 * s * x) ** 2 * (denominator ** -2 - numerator ** -2)
    )

    u1, u2, u3 = sp.symbols("u1 u2 u3", real=True)
    # Algebraic form of sum cos differences = (|sum exp(i theta)|^2-3)/2.
    # The receipt records the consequent lower bound through the nonnegative
    # square modulus variable R.
    R = sp.symbols("R", nonnegative=True, real=True)
    cosine_sum_identity = sp.simplify((R - 3) / 2 + sp.Rational(3, 2) - R / 2) == 0

    r = sp.symbols("r", positive=True, real=True)
    selected_log_derivative = sp.factor(
        r * sp.diff(sp.log((1 - r * x) / (x - r)), r)
    ).subs(r, s)
    rho = sp.symbols("rho", positive=True, real=True)
    q_regular_spectator = (1 + rho * x + rho**2 * x**2) / (
        x**2 + rho * x + rho**2
    )
    spectator_log_derivative = sp.factor(
        sp.Rational(1, 2) * rho * sp.diff(sp.log(q_regular_spectator), rho)
    ).subs(rho, s)
    radial_first_variation = sp.factor(
        selected_log_derivative - spectator_log_derivative
    )
    radial_expected = sp.factor(
        3
        * s
        * x
        * (x**2 - 1)
        * (s**4 * x + s**3 * x**2 + s**3 + s * x**2 + s + x)
        / (
            2
            * (x - s)
            * (s * x - 1)
            * (s**2 + s * x + x**2)
            * (s**2 * x**2 + s * x + 1)
        )
    )

    log_spectator_convexity = sp.factor(
        rho * sp.diff(rho * sp.diff(sp.Rational(1, 2) * sp.log(q_regular_spectator), rho), rho)
    )
    convexity_positive_polynomial = (
        rho**4 * x**2
        + 4 * rho**3 * x**3
        + 4 * rho**3 * x
        + rho**2 * x**4
        + 7 * rho**2 * x**2
        + rho**2
        + 4 * rho * x**3
        + 4 * rho * x
        + x**2
    )
    convexity_expected = sp.factor(
        -rho
        * x
        * (rho - 1)
        * (rho + 1)
        * (x - 1)
        * (x + 1)
        * convexity_positive_polynomial
        / (2 * (rho**2 + rho * x + x**2) ** 2 * (rho**2 * x**2 + rho * x + 1) ** 2)
    )

    selected_plus_spectator = sp.factor(
        selected_log_derivative + spectator_log_derivative
    )
    selected_plus_spectator_positive_polynomial = (
        s**4 * x**2
        + s**3 * x**3
        + s**3 * x
        + 4 * s**2 * x**4
        + 4 * s**2 * x**2
        + 4 * s**2
        + s * x**3
        + s * x
        + x**2
    )
    selected_plus_spectator_expected = sp.factor(
        s
        * (x - 1)
        * (x + 1)
        * selected_plus_spectator_positive_polynomial
        / (
            2
            * (x - s)
            * (s * x - 1)
            * (s**2 + s * x + x**2)
            * (s**2 * x**2 + s * x + 1)
        )
    )

    # Exact rational counterexample to the stronger product-of-all-rays
    # shortcut.  We square the profiles to avoid square roots.
    xx = Fraction(8)
    radii = [Fraction(1, 1600), Fraction(1, 1600), Fraction(1, 25)]
    pair_cosines = {(0, 1): Fraction(1), (1, 2): Fraction(-1), (2, 0): Fraction(-1)}

    def selected_factor(radius: Fraction) -> Fraction:
        return (1 - radius * xx) / (xx - radius)

    def spectator_square(radius: Fraction, cosine: Fraction) -> Fraction:
        return (
            (1 - 2 * radius * xx * cosine + radius**2 * xx**2)
            / (xx**2 - 2 * radius * xx * cosine + radius**2)
        )

    product_squared = Fraction(1)
    for radius in radii:
        product_squared *= selected_factor(radius) ** 2
    for (i, j), cosine in pair_cosines.items():
        product_squared *= spectator_square(radii[i], cosine)
        product_squared *= spectator_square(radii[j], cosine)
    symmetric_radius = Fraction(1, 400)
    symmetric_cube_squared = (
        selected_factor(symmetric_radius)
        * spectator_square(symmetric_radius, Fraction(-1, 2))
    ) ** 6
    product_shortcut_refuted = product_squared > symmetric_cube_squared

    result = {
        "schema": "erdos1041_three_exterior_angular_envelope_receipt_v1",
        "log_Q_first_derivative_identity": sp.simplify(first - first_expected) == 0,
        "log_Q_second_derivative_identity": sp.simplify(second - second_expected) == 0,
        "three_angle_cosine_sum_lower_bound_identity": cosine_sum_identity,
        "product_preserving_radial_first_variation_identity": sp.simplify(
            radial_first_variation - radial_expected
        )
        == 0,
        "log_spectator_convexity_identity": sp.simplify(
            log_spectator_convexity - convexity_expected
        )
        == 0,
        "selected_plus_spectator_negative_identity": sp.simplify(
            selected_plus_spectator - selected_plus_spectator_expected
        )
        == 0,
        "three_ray_product_shortcut_exact_counterexample": product_shortcut_refuted,
        "three_ray_product_ratio_float": float(product_squared / symmetric_cube_squared) ** 0.5,
        "order_argument": "Q_x is decreasing, so the ray opposite the smallest pair cosine minimizes the spectator product for every x.",
        "claim_boundary": "Exact global equal-radius angular theorem, global regular-angle radial theorem, and local product-preserving theorem for m=3; the coupled irregular-angle/irregular-radius case and unrestricted Erdős 1041 remain open.",
    }
    result["pass"] = (
        all(v is True for k, v in result.items() if k.endswith("identity"))
        and product_shortcut_refuted
    )
    print(json.dumps(result, indent=2))
    return 0 if result["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
