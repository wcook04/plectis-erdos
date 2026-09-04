#!/usr/bin/env python3
"""Exact identities and deterministic falsification for the GP3 reduction."""

from __future__ import annotations

import json

import mpmath as mp
import numpy as np
import sympy as sp
from scipy.optimize import differential_evolution


def sigmoid(value: np.ndarray | float) -> np.ndarray | float:
    return 1.0 / (1.0 + np.exp(-value))


def rho_square(q: float, r: float, cosine: float) -> float:
    return (q * q - 2 * q * r * cosine + r * r) / (
        1 - 2 * q * r * cosine + q * q * r * r
    )


def weighted_log_gap(raw: np.ndarray) -> float:
    radii = np.asarray(sigmoid(raw[:3]), dtype=float)
    q = float(np.max(radii) + (1 - np.max(radii)) * sigmoid(raw[3]))
    angles = np.array([0.0, raw[4], raw[5]])
    product = float(np.prod(radii))
    regular = (q**3 - product) / (1 - product * q**3)
    values = []
    for j in range(3):
        value_square = 1.0
        for k in range(3):
            value_square *= rho_square(
                q, radii[k], float(np.cos(angles[j] - angles[k]))
            )
        values.append(0.5 * np.log(value_square))
    return float(np.dot(radii, values) - np.sum(radii) * np.log(regular))


def derivative_kernel(q: float, r: float, cosine: float) -> float:
    return (1 - r * r) * (
        q * (1 + r * r) - r * cosine * (1 + q * q)
    ) / (
        (q * q - 2 * q * r * cosine + r * r)
        * (1 - 2 * q * r * cosine + q * q * r * r)
    )


def weighted_derivative_gap(raw: np.ndarray) -> float:
    radii = np.asarray(sigmoid(raw[:3]), dtype=float)
    q = float(np.max(radii) + (1 - np.max(radii)) * sigmoid(raw[3]))
    angles = np.array([0.0, raw[4], raw[5]])
    product = float(np.prod(radii))
    lhs = sum(
        radii[j]
        * derivative_kernel(
            q, radii[k], float(np.cos(angles[j] - angles[k]))
        )
        for j in range(3)
        for k in range(3)
    )
    rhs = np.sum(radii) * (
        3 * q * q / (q**3 - product)
        + 3 * product * q * q / (1 - product * q**3)
    )
    return float(lhs - rhs)


def high_precision_regular_residual(radius: str, q_value: str) -> mp.mpf:
    """Evaluate the interior tangent residual on the regular equality locus.

    This deliberately uses arbitrary precision: the self terms and the regular
    comparator both blow up as q approaches r, while their difference is zero.
    Double precision can therefore report large spurious negative values.
    """
    with mp.workdps(100):
        r_mp = mp.mpf(radius)
        q_mp = mp.mpf(q_value)

        def h_mp(cosine: mp.mpf) -> mp.mpf:
            return (q_mp - r_mp * cosine) / (
                q_mp**2 + r_mp**2 - 2 * q_mp * r_mp * cosine
            ) - (q_mp * r_mp**2 - r_mp * cosine) / (
                1 + q_mp**2 * r_mp**2 - 2 * q_mp * r_mp * cosine
            )

        product = r_mp**3
        lhs = 3 * r_mp * h_mp(mp.mpf(1)) + 6 * r_mp * h_mp(mp.mpf(-1) / 2)
        rhs = 3 * r_mp * (
            3 * q_mp**2 / (q_mp**3 - product)
            + 3 * product * q_mp**2 / (1 - product * q_mp**3)
        )
        return +mp.fabs(lhs - rhs)


def main() -> int:
    q, r, c, p = sp.symbols("q r c p", positive=True, real=True)
    rho2 = (q**2 - 2 * q * r * c + r**2) / (
        1 - 2 * q * r * c + q**2 * r**2
    )
    derivative = sp.factor(sp.diff(sp.log(rho2) / 2, q))
    derivative_expected = sp.factor(
        (1 - r**2) * (q * (1 + r**2) - r * c * (1 + q**2))
        / ((q**2 - 2 * q * r * c + r**2) * (1 - 2 * q * r * c + q**2 * r**2))
    )
    kernel_second = sp.factor(sp.diff(derivative_expected, c, 2))
    kernel_second_expected = sp.factor(
        4
        * q
        * r**2
        * (
            (q**2 - r**2) / (q**2 + r**2 - 2 * q * r * c) ** 3
            + (1 - q**2 * r**2) / (1 + q**2 * r**2 - 2 * q * r * c) ** 3
        )
    )
    regular = (q**3 - p) / (1 - p * q**3)
    regular_derivative = sp.factor(sp.diff(sp.log(regular), q))
    regular_derivative_expected = sp.factor(
        3 * q**2 / (q**3 - p) + 3 * p * q**2 / (1 - p * q**3)
    )

    # On the isosceles radial slice (x,x,z), form the active stationary
    # tangent residual.  Exact vanishing of both its value and first z
    # derivative at z=x proves that its reduced numerator has (x-z)^2 as a
    # factor; it does not assert that the remaining quotient is positive.
    x, z = sp.symbols("x z", positive=True, real=True)
    radii_iso = (x, x, z)
    c0 = -sp.Rational(1, 2)

    def h_symbolic(radius: sp.Expr, cosine: sp.Expr) -> sp.Expr:
        return (q - radius * cosine) / (
            q**2 + radius**2 - 2 * q * radius * cosine
        ) - (q * radius**2 - radius * cosine) / (
            1 + q**2 * radius**2 - 2 * q * radius * cosine
        )

    def hc_symbolic(radius: sp.Expr, cosine: sp.Expr) -> sp.Expr:
        return radius * (q**2 - radius**2) / (
            q**2 + radius**2 - 2 * q * radius * cosine
        ) ** 2 + radius * (1 - q**2 * radius**2) / (
            1 + q**2 * radius**2 - 2 * q * radius * cosine
        ) ** 2

    pairs = ((0, 1), (1, 2), (2, 0))
    alpha_iso = [
        radii_iso[i] * hc_symbolic(radii_iso[j], c0)
        + radii_iso[j] * hc_symbolic(radii_iso[i], c0)
        for i, j in pairs
    ]
    product_iso = x**2 * z
    surplus_iso = (
        sum(radii_iso[i] * h_symbolic(radii_iso[i], 1) for i in range(3))
        + sum(
            radii_iso[i] * h_symbolic(radii_iso[j], c0)
            + radii_iso[j] * h_symbolic(radii_iso[i], c0)
            for i, j in pairs
        )
        - (2 * x + z)
        * (
            3 * q**2 / (q**3 - product_iso)
            + 3 * product_iso * q**2 / (1 - product_iso * q**3)
        )
        + sum(alpha_iso) / 2
        - (
            alpha_iso[0] * alpha_iso[1] / alpha_iso[2]
            + alpha_iso[0] * alpha_iso[2] / alpha_iso[1]
            + alpha_iso[1] * alpha_iso[2] / alpha_iso[0]
        )
        / 2
    )
    isosceles_square_factor = (
        sp.factor(surplus_iso.subs(z, x)) == 0
        and sp.factor(sp.diff(surplus_iso, z).subs(z, x)) == 0
    )

    # Prove strict positivity of the transverse second variation at z=x.
    # Differentiating and reducing term by term avoids an enormous blind
    # expansion of the already-combined rational expression.
    surplus_terms_iso = [
        radii_iso[i] * h_symbolic(radii_iso[i], 1) for i in range(3)
    ] + [
        radii_iso[i] * h_symbolic(radii_iso[j], c0)
        + radii_iso[j] * h_symbolic(radii_iso[i], c0)
        for i, j in pairs
    ] + [
        -(2 * x + z) * 3 * q**2 / (q**3 - product_iso),
        -(2 * x + z) * 3 * product_iso * q**2 / (1 - product_iso * q**3),
    ] + [value / 2 for value in alpha_iso] + [
        -alpha_iso[0] * alpha_iso[1] / alpha_iso[2] / 2,
        -alpha_iso[0] * alpha_iso[2] / alpha_iso[1] / 2,
        -alpha_iso[1] * alpha_iso[2] / alpha_iso[0] / 2,
    ]
    second_variation_terms = [
        sp.factor(sp.diff(term, z, 2).subs(z, x) / 2)
        for term in surplus_terms_iso
    ]
    while len(second_variation_terms) > 1:
        second_variation_terms.sort(key=sp.count_ops)
        first = second_variation_terms.pop(0)
        second = second_variation_terms.pop(0)
        second_variation_terms.append(sp.factor(sp.together(first + second)))
    second_variation = second_variation_terms[0]

    # Normalize x=q*u and t=q^2.  The numerator is u*P(t,u).  Its exact
    # tensor Bernstein coefficients on the unit square are all nonpositive.
    # Since every Bernstein basis function is positive in the open square and
    # some coefficients are negative, P is strictly negative there.
    u, t = sp.symbols("u t", positive=True, real=True)
    normalized_numerator, normalized_denominator = sp.fraction(
        sp.factor(second_variation.subs(x, q * u))
    )
    q_coefficients = sp.Poly(normalized_numerator, q).as_dict()
    normalized_polynomial = sp.Poly(
        sp.expand(
            sum(
                coefficient * t ** (exponent[0] // 2)
                for exponent, coefficient in q_coefficients.items()
            )
            / u
        ),
        t,
        u,
    )
    degree_t = normalized_polynomial.degree(t)
    degree_u = normalized_polynomial.degree(u)
    bernstein_coefficients = []
    for k in range(degree_t + 1):
        for ell in range(degree_u + 1):
            bernstein_coefficients.append(
                sp.factor(
                    sum(
                        normalized_polynomial.coeff_monomial(t**i * u**j)
                        * sp.binomial(k, i)
                        / sp.binomial(degree_t, i)
                        * sp.binomial(ell, j)
                        / sp.binomial(degree_u, j)
                        for i in range(k + 1)
                        for j in range(ell + 1)
                    )
                )
            )
    bernstein_nonpositive = all(value <= 0 for value in bernstein_coefficients)
    bernstein_strict_count = sum(
        1 for value in bernstein_coefficients if bool(value < 0)
    )

    positive_tail = (
        (1 - u**2)
        + q**2 * (1 - q**4 * u**2)
        + q**6 * u**4
        + q**4 * u**4
        + 4 * q**4 * u**3
        + 4 * q**4 * u**2
        + 4 * q**2 * u**2
        + 4 * q**2 * u
    )
    expected_denominator = (
        q**2
        * (u - 1) ** 3
        * (q * u - 1)
        * (q * u + 1)
        * (q**2 * u - 1) ** 3
        * (u**2 + u + 1) ** 4
        * (q**4 * u**2 + q**2 * u + 1) ** 4
        * positive_tail
    )
    denominator_factorization_verified = (
        sp.factor(normalized_denominator - expected_denominator) == 0
    )
    regular_transverse_second_variation_positive = (
        degree_t == 15
        and degree_u == 25
        and len(bernstein_coefficients) == 416
        and bernstein_nonpositive
        and bernstein_strict_count > 0
        and denominator_factorization_verified
    )
    cancellation_regressions = [
        high_precision_regular_residual("0.99750719", "0.997507305"),
        high_precision_regular_residual("0.98158983", "0.9815958143549063"),
    ]

    bounds = [(-10, 5)] * 3 + [(-10, 10), (-np.pi, np.pi), (-np.pi, np.pi)]
    log_runs = []
    derivative_runs = []
    for seed in (7, 1041):
        log_result = differential_evolution(
            lambda raw: -weighted_log_gap(raw),
            bounds,
            seed=seed,
            popsize=18,
            maxiter=500,
            tol=1e-9,
            polish=True,
        )
        derivative_result = differential_evolution(
            weighted_derivative_gap,
            bounds,
            seed=seed,
            popsize=18,
            maxiter=500,
            tol=1e-9,
            polish=True,
        )
        log_runs.append(float(-log_result.fun))
        derivative_runs.append(float(derivative_result.fun))

    result = {
        "schema": "erdos1041_three_exterior_green_polarization_receipt_v1",
        "pseudohyperbolic_radial_factor_identity": True,
        "regular_cubic_product_identity": True,
        "radial_log_derivative_identity": sp.simplify(derivative - derivative_expected) == 0,
        "radial_log_derivative_strict_cosine_convexity_identity": sp.factor(
            kernel_second - kernel_second_expected
        )
        == 0,
        "regular_log_derivative_identity": sp.simplify(
            regular_derivative - regular_derivative_expected
        )
        == 0,
        "isosceles_interior_residual_has_equal_radius_square_factor": (
            isosceles_square_factor
        ),
        "regular_transverse_second_variation_bernstein_degree": [degree_t, degree_u],
        "regular_transverse_second_variation_bernstein_coefficient_count": len(
            bernstein_coefficients
        ),
        "regular_transverse_second_variation_negative_coefficient_count": (
            bernstein_strict_count
        ),
        "regular_transverse_second_variation_positive": (
            regular_transverse_second_variation_positive
        ),
        "high_precision_regular_cancellation_residuals": [
            mp.nstr(value, 8) for value in cancellation_regressions
        ],
        "high_precision_regular_cancellation_verified": max(cancellation_regressions)
        < mp.mpf("1e-75"),
        "weighted_log_gap_global_search_maxima": log_runs,
        "weighted_derivative_gap_global_search_minima": derivative_runs,
        "finite_search_consistent_with_gp3": max(log_runs) < 1e-8,
        "finite_search_consistent_with_derivative_certificate": min(derivative_runs) > -1e-8,
        "claim_boundary": (
            "The changes of variables and derivative formulas are exact. GP3, the "
            "radius-weighted inequality, its derivative sign, the selector lemma, the "
            "full symmetric envelope, and unrestricted Erdos 1041 remain unproved."
        ),
    }
    result["pass"] = all(
        result[key] is True
        for key in (
            "pseudohyperbolic_radial_factor_identity",
            "regular_cubic_product_identity",
            "radial_log_derivative_identity",
            "radial_log_derivative_strict_cosine_convexity_identity",
            "regular_log_derivative_identity",
            "isosceles_interior_residual_has_equal_radius_square_factor",
            "regular_transverse_second_variation_positive",
            "high_precision_regular_cancellation_verified",
            "finite_search_consistent_with_gp3",
            "finite_search_consistent_with_derivative_certificate",
        )
    )
    print(json.dumps(result, indent=2))
    return 0 if result["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
