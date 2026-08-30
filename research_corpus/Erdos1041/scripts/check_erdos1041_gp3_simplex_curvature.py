"""Exact simplex tangent curvature certificate for the GP3 stationary surplus.

Along the exactly product-preserving isosceles path

    r1 = r2 = s*w,   r3 = s/w**2,    p = s**3 for every w,

the stationary-branch radial surplus S_stat(q; r1, r2, r3) of
ThreeExteriorGreenPolarization.md satisfies

    (w d/dw) S_stat |_{w=1} = 0
    (w d/dw)^2 S_stat |_{w=1} = 18 u^3 Nhat(t,u) / D(q,u),   u = s/q, t = q^2,

where D is strictly negative on the open unit square and Nhat has bidegree
(15,25).  Converting Nhat to the tensor Bernstein basis on [0,1]^2 and finding
every coefficient nonpositive proves the tangent curvature is strictly
positive: the regular triangle is a strict local minimizer of the stationary
surplus on every product-preserving simplex, in the tangent direction that the
existing transverse second-variation certificate does not cover.

Replay:
    ./repo-python source-provenance://private-authoring-project/ErdosProblems/\
Erdos1041/scripts/check_erdos1041_gp3_simplex_curvature.py
"""

import json
import sys

import mpmath as mp
import sympy as sp

mp.mp.dps = 60


def main() -> int:
    q, s, w = sp.symbols("q s w", positive=True, real=True)
    half = sp.Rational(1, 2)

    def h(radius, cosine):
        return (q - radius * cosine) / (
            q**2 + radius**2 - 2 * q * radius * cosine
        ) - (q * radius**2 - radius * cosine) / (
            1 + q**2 * radius**2 - 2 * q * radius * cosine
        )

    def hc(radius, cosine):
        return radius * (q**2 - radius**2) / (
            q**2 + radius**2 - 2 * q * radius * cosine
        ) ** 2 + radius * (1 - q**2 * radius**2) / (
            1 + q**2 * radius**2 - 2 * q * radius * cosine
        ) ** 2

    radii = (s * w, s * w, s / w**2)
    pairs = ((0, 1), (0, 2), (1, 2))

    terms = [radii[i] * h(radii[i], 1) for i in range(3)]
    terms += [
        radii[i] * h(radii[j], -half) + radii[j] * h(radii[i], -half)
        for i, j in pairs
    ]
    alpha = [
        radii[i] * hc(radii[j], -half) + radii[j] * hc(radii[i], -half)
        for i, j in pairs
    ]
    p = radii[0] * radii[1] * radii[2]
    total = radii[0] + radii[1] + radii[2]
    terms += [
        -total * 3 * q**2 / (q**3 - p),
        -total * 3 * p * q**2 / (1 - p * q**3),
    ]
    terms += [value / 2 for value in alpha]
    terms += [
        -alpha[0] * alpha[1] / alpha[2] / 2,
        -alpha[0] * alpha[2] / alpha[1] / 2,
        -alpha[1] * alpha[2] / alpha[0] / 2,
    ]

    def reduce_sum(exprs):
        acc = [sp.factor(expr) for expr in exprs]
        acc.sort(key=sp.count_ops)
        while len(acc) > 1:
            a = acc.pop(0)
            b = acc.pop(0)
            acc.append(sp.factor(sp.together(a + b)))
            acc.sort(key=sp.count_ops)
        return acc[0]

    first_terms = [sp.diff(term, w).subs(w, 1) for term in terms]
    first_derivative = sp.simplify(reduce_sum(first_terms))
    first_derivative_zero = first_derivative == 0

    second_terms = []
    for term in terms:
        d1 = sp.diff(term, w)
        second_terms.append((sp.diff(d1, w) + d1).subs(w, 1))
    curvature = reduce_sum(second_terms)

    # Numeric cross-validation of the symbolic curvature against finite
    # differences of the direct surplus along the path.
    import math
    import random

    random.seed(1041)

    def h_mp(qq, rr, cc):
        a = qq * qq + rr * rr - 2 * qq * rr * cc
        b = 1 + qq * qq * rr * rr - 2 * qq * rr * cc
        return (qq - rr * cc) / a - (qq * rr * rr - rr * cc) / b

    def hc_mp(qq, rr, cc):
        a = qq * qq + rr * rr - 2 * qq * rr * cc
        b = 1 + qq * qq * rr * rr - 2 * qq * rr * cc
        return rr * (qq * qq - rr * rr) / (a * a) + rr * (
            1 - qq * qq * rr * rr
        ) / (b * b)

    def surplus_mp(qq, rr1, rr2, rr3):
        p3 = rr1 * rr2 * rr3
        tot = rr1 + rr2 + rr3
        rhs = tot * (3 * qq * qq / (qq**3 - p3) + 3 * p3 * qq * qq / (1 - p3 * qq**3))
        acc = rr1 * h_mp(qq, rr1, 1) + rr2 * h_mp(qq, rr2, 1) + rr3 * h_mp(qq, rr3, 1)
        alphas = []
        for ri, rj in ((rr1, rr2), (rr1, rr3), (rr2, rr3)):
            acc += ri * h_mp(qq, rj, -mp.mpf(1) / 2) + rj * h_mp(qq, ri, -mp.mpf(1) / 2)
            alphas.append(
                ri * hc_mp(qq, rj, -mp.mpf(1) / 2)
                + rj * hc_mp(qq, ri, -mp.mpf(1) / 2)
            )
        a12, a13, a23 = alphas
        acc += (a12 + a13 + a23) / 2
        acc -= (a12 * a13 / a23 + a12 * a23 / a13 + a13 * a23 / a12) / 2
        return acc - rhs

    curvature_function = sp.lambdify((q, s), curvature, "mpmath")
    numeric_checks = []
    for _ in range(6):
        qq = mp.mpf(random.uniform(0.1, 0.95))
        uu = mp.mpf(random.uniform(0.02, 0.9))
        ss = qq * uu
        step = mp.mpf("1e-7")

        def path(aa):
            rr1 = rr2 = ss * mp.e**aa
            rr3 = ss * mp.e ** (-2 * aa)
            return surplus_mp(qq, rr1, rr2, rr3)

        fd = (path(step) - 2 * path(mp.mpf(0)) + path(-step)) / step**2
        exact = mp.mpf(curvature_function(mp.mpf(qq), mp.mpf(ss)))
        numeric_checks.append(float(abs(fd - exact) / abs(exact)))
    numeric_validated = max(numeric_checks) < mp.mpf("1e-4")

    u = sp.symbols("u", positive=True, real=True)
    t = sp.symbols("t", positive=True, real=True)
    num, den = sp.fraction(sp.factor(curvature.subs(s, q * u)))

    expected_tail = (
        q**6 * u**4
        - q**6 * u**2
        + q**4 * u**4
        + 4 * q**4 * u**3
        + 4 * q**4 * u**2
        + 4 * q**2 * u**2
        + 4 * q**2 * u
        + q**2
        - u**2
        + 1
    )
    expected_denominator = (
        (u - 1) ** 3
        * (q * u - 1)
        * (q * u + 1)
        * (q**2 * u - 1) ** 3
        * (u**2 + u + 1) ** 4
        * (q**4 * u**2 + q**2 * u + 1) ** 4
        * expected_tail
    )
    denominator_factorization_verified = sp.factor(den - expected_denominator) == 0

    # Strip the exact u^3 prefactor; the remaining numerator has only even
    # powers of q, hence is a polynomial in (t, u) = (q^2, s/q).
    quotient = sp.cancel(sp.together(num / (18 * u**3)))
    num3, extra3 = sp.fraction(quotient)
    prefactor_clean = extra3 == 1
    # Univariate in q so each coefficient carries its full u-dependence;
    # this mirrors the transverse certificate's normalization.
    q_poly = sp.Poly(sp.expand(num3), q)

    def q_power(exponent):
        return exponent[0] if isinstance(exponent, tuple) else exponent

    even_q_powers = all(q_power(exponent) % 2 == 0 for exponent in q_poly.as_dict())
    normalized_polynomial = sp.Poly(
        sp.expand(
            sum(
                coefficient * t ** (q_power(exponent) // 2)
                for exponent, coefficient in q_poly.as_dict().items()
            )
        ),
        t,
        u,
    )
    degree_t = normalized_polynomial.degree(t)
    degree_u = normalized_polynomial.degree(u)

    # Monomial -> tensor Bernstein conversion as two exact triangular
    # one-variable passes.
    monomial = {}
    for (i, j), coefficient in normalized_polynomial.terms():
        monomial[(i, j)] = sp.Rational(coefficient)
    bernstein = {}
    # Pass 1: convert the t direction for each fixed u-degree j.
    for j in range(degree_u + 1):
        column = [
            monomial.get((i, j), sp.Rational(0)) for i in range(degree_t + 1)
        ]
        converted = []
        for k in range(degree_t + 1):
            acc = sp.Rational(0)
            for i in range(k + 1):
                acc += column[i] * sp.binomial(k, i) / sp.binomial(degree_t, i)
            converted.append(acc)
        for k, value in enumerate(converted):
            bernstein[(k, j)] = value
    # Pass 2: convert the u direction for each fixed t-degree k.
    final = {}
    for k in range(degree_t + 1):
        column = [bernstein[(k, j)] for j in range(degree_u + 1)]
        for ell in range(degree_u + 1):
            acc = sp.Rational(0)
            for j in range(ell + 1):
                acc += column[j] * sp.binomial(ell, j) / sp.binomial(degree_u, j)
            final[(k, ell)] = acc

    coefficient_values = list(final.values())
    bernstein_nonpositive = all(value <= 0 for value in coefficient_values)
    bernstein_strict_count = sum(1 for value in coefficient_values if value < 0)

    # Independent Bernstein verification at a random interior point: the
    # polynomial value must equal the Bernstein expansion there.
    t0 = sp.Rational(3, 7)
    u0 = sp.Rational(5, 11)
    basis_value = sum(
        final[(k, ell)]
        * sp.binomial(degree_t, k) ** 1
        * t0**k
        * (1 - t0) ** (degree_t - k)
        * sp.binomial(degree_u, ell)
        * u0**ell
        * (1 - u0) ** (degree_u - ell)
        for k in range(degree_t + 1)
        for ell in range(degree_u + 1)
    )
    bernstein_expansion_verified = (
        basis_value
        == normalized_polynomial.eval({t: t0, u: u0})
    )

    tangent_curvature_positive = (
        degree_t == 15
        and degree_u == 25
        and len(coefficient_values) == 416
        and bernstein_nonpositive
        and bernstein_strict_count > 0
        and denominator_factorization_verified
        and prefactor_clean
        and even_q_powers
        and bernstein_expansion_verified
    )

    result = {
        "schema": "erdos1041_gp3_simplex_curvature_receipt_v1",
        "path": "r1=r2=s*w, r3=s/w**2 (exactly product-preserving)",
        "first_simplex_derivative_zero": first_derivative_zero,
        "denominator_factorization_verified": denominator_factorization_verified,
        "u_cubed_prefactor_clean": prefactor_clean,
        "numerator_even_q_powers": even_q_powers,
        "bernstein_degree": [degree_t, degree_u],
        "bernstein_coefficient_count": len(coefficient_values),
        "bernstein_nonpositive": bernstein_nonpositive,
        "bernstein_strict_negative_count": bernstein_strict_count,
        "bernstein_expansion_verified": bernstein_expansion_verified,
        "numeric_relative_mismatches": numeric_checks,
        "numeric_validated": numeric_validated,
        "tangent_curvature_positive": tangent_curvature_positive,
        "claim_boundary": (
            "This proves (w d/dw)^2 S_stat > 0 at w=1 on 0<u=t^{1/2}<1 for the "
            "stationary branch: the regular triangle is a strict local "
            "minimizer of the stationary surplus along the product-preserving "
            "simplex, complementing the transverse certificate. GP3 itself, "
            "the endpoint branch, the global surplus inequality, the selector "
            "lemma, and unrestricted Erdos 1041 remain unproved."
        ),
    }
    result["pass"] = all(
        result[key]
        for key in (
            "first_simplex_derivative_zero",
            "denominator_factorization_verified",
            "u_cubed_prefactor_clean",
            "numerator_even_q_powers",
            "tangent_curvature_positive",
            "numeric_validated",
        )
    )
    print(json.dumps(result, indent=2))
    return 0 if result["pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
