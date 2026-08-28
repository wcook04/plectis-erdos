#!/usr/bin/env python3
"""Exact Bernstein certificate for the GP3 simplex tangent curvature.

Along the exactly product-preserving isosceles path r1=r2=s*w, r3=s/w**2 the
stationary-branch residual E of the coupled three-exterior inequality has
(w d/dw)E|_(w=1)=0 and (w d/dw)^2 E|_(w=1)=18 u^3 Nhat(t,u)/D(q,u) with
u=s/q, t=q^2.  This replay proves that first identity, the denominator
factorization, and that all 416 tensor Bernstein coefficients of Nhat on
[0,1]^2 are nonpositive with 405 strictly negative, so the tangent curvature
is strictly positive on the regular radial locus.

This optional research replay requires SymPy.  It proves a local theorem only;
the global radial inequality, GP3, and unrestricted Erdos 1041 remain open.
"""
import json
import sympy as s


def main():
    q, sv, w, u, t = s.symbols("q sv w u t", positive=True)
    radii = (sv * w, sv * w, sv / w**2)
    c = -s.Rational(1, 2)
    pairs = ((0, 1), (0, 2), (1, 2))

    def H(r, c):
        return (q - r * c) / (q * q + r * r - 2 * q * r * c) - (
            q * r * r - r * c
        ) / (1 + q * q * r * r - 2 * q * r * c)

    def Hc(r, c):
        return r * (q * q - r * r) / (q * q + r * r - 2 * q * r * c) ** 2 + r * (
            1 - q * q * r * r
        ) / (1 + q * q * r * r - 2 * q * r * c) ** 2

    alpha = [radii[i] * Hc(radii[j], c) + radii[j] * Hc(radii[i], c) for i, j in pairs]
    product = radii[0] * radii[1] * radii[2]
    total = radii[0] + radii[1] + radii[2]
    terms = [radii[i] * H(radii[i], 1) for i in range(3)]
    terms += [radii[i] * H(radii[j], c) + radii[j] * H(radii[i], c) for i, j in pairs]
    terms += [-total * 3 * q * q / (q**3 - product),
              -total * 3 * product * q * q / (1 - product * q**3)]
    terms += [a / 2 for a in alpha]
    terms += [-alpha[0] * alpha[1] / alpha[2] / 2,
              -alpha[0] * alpha[2] / alpha[1] / 2,
              -alpha[1] * alpha[2] / alpha[0] / 2]

    first = s.factor(sum(s.diff(term, w).subs(w, 1) for term in terms))
    first_derivative_zero = first == 0

    values = []
    for term in terms:
        d1 = s.diff(term, w)
        values.append(s.factor((s.diff(d1, w) + d1).subs(w, 1)))
    while len(values) > 1:
        values.sort(key=s.count_ops)
        a = values.pop(0)
        b = values.pop(0)
        values.append(s.factor(s.together(a + b)))
    numerator, denominator = s.fraction(s.factor(values[0].subs(sv, q * u)))

    positive_tail = (
        (1 - u**2)
        + q**2 * (1 - q**4 * u**2)
        + q**4 * u**4 * (1 + q**2)
        + 4 * q**4 * u**3
        + 4 * q**2 * u**2 * (1 + q**2)
        + 4 * q**2 * u
    )
    expected_denominator = (
        (u - 1) ** 3
        * (q * u - 1)
        * (q * u + 1)
        * (q**2 * u - 1) ** 3
        * (u**2 + u + 1) ** 4
        * (q**4 * u**2 + q**2 * u + 1) ** 4
        * positive_tail
    )
    denominator_ok = s.factor(denominator - expected_denominator) == 0

    quotient = s.cancel(s.together(numerator / (18 * u**3)))
    num3, extra = s.fraction(quotient)
    prefactor_clean = extra == 1
    q_coefficients = s.Poly(s.expand(num3), q).as_dict()
    even_q_powers = all(exponent[0] % 2 == 0 for exponent in q_coefficients)
    polynomial = s.Poly(
        s.expand(
            sum(
                coefficient * t ** (exponent[0] // 2)
                for exponent, coefficient in q_coefficients.items()
            )
        ),
        t,
        u,
    )
    degree_t, degree_u = polynomial.degree(t), polynomial.degree(u)
    bernstein = []
    for k in range(degree_t + 1):
        for ell in range(degree_u + 1):
            bernstein.append(
                s.factor(
                    sum(
                        polynomial.coeff_monomial(t**i * u**j)
                        * s.binomial(k, i)
                        / s.binomial(degree_t, i)
                        * s.binomial(ell, j)
                        / s.binomial(degree_u, j)
                        for i in range(k + 1)
                        for j in range(ell + 1)
                    )
                )
            )
    nonpositive = all(value <= 0 for value in bernstein)
    negative = sum(1 for value in bernstein if bool(value < 0))
    passed = (
        first_derivative_zero
        and denominator_ok
        and prefactor_clean
        and even_q_powers
        and (degree_t, degree_u) == (15, 25)
        and len(bernstein) == 416
        and negative == 405
        and nonpositive
    )
    print(
        json.dumps(
            {
                "schema": "erdos1041-gp3-simplex-curvature/1",
                "first_simplex_derivative_zero": first_derivative_zero,
                "denominator_factorization_verified": denominator_ok,
                "u_cubed_prefactor_clean": prefactor_clean,
                "bernstein_degree": [degree_t, degree_u],
                "coefficient_count": len(bernstein),
                "strictly_negative_coefficient_count": negative,
                "all_coefficients_nonpositive": nonpositive,
                "tangent_curvature_strictly_positive": passed,
                "claim_boundary": "Local stationary-branch theorem only; the global radial inequality, GP3, the selector lemma, and unrestricted Erdos 1041 remain unproved.",
            },
            indent=2,
        )
    )
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
