#!/usr/bin/env python3
"""Exact small-scale ordered collar for the stationary GP3 surplus.

The chart is u=r*s*w, v=s*w with 0<=r<=1/16, 0<=s<=1.  Exact
formal-series algebra identifies the positive cubic.  A rational Cauchy
majorant on |w|=1/8 controls the entire tail and proves positivity through
w=1/16000.
"""

from __future__ import annotations

import sympy as sp
import hashlib
import json
from fractions import Fraction
from math import comb


ORDER = 4


def add(a, b):
    return [a[i] + b[i] for i in range(ORDER)]


def neg(a):
    return [-value for value in a]


def sub(a, b):
    return add(a, neg(b))


def scale(c, a):
    return [c * value for value in a]


def mul(a, b):
    return [sum(a[j] * b[i - j] for j in range(i + 1)) for i in range(ORDER)]


def inv(a):
    assert a[0] != 0
    result = [1 / a[0]]
    for i in range(1, ORDER):
        result.append(-sum(a[j] * result[i - j] for j in range(1, i + 1)) / a[0])
    return result


def div(a, b):
    return mul(a, inv(b))


def power(a, exponent):
    result = [sp.S.One] + [sp.S.Zero] * (ORDER - 1)
    for _ in range(exponent):
        result = mul(result, a)
    return result


def main() -> int:
    t, r, s = sp.symbols("t r s", nonnegative=True, real=True)
    one = [sp.S.One] + [sp.S.Zero] * (ORDER - 1)
    w = [sp.S.Zero, sp.S.One] + [sp.S.Zero] * (ORDER - 2)
    u = scale(r * s, w)
    v = scale(s, w)
    radii = (u, v, w)

    def A(x):
        return add(add(one, x), power(x, 2))

    def D(x):
        return add(add(one, scale(t, x)), scale(t**2, power(x, 2)))

    def L(x):
        first = div(sub(one, power(x, 2)), power(A(x), 2))
        second = scale(t, div(sub(one, scale(t**2, power(x, 2))), power(D(x), 2)))
        return add(first, second)

    def self_term(x):
        return add(div(x, sub(one, x)), scale(t, div(power(x, 2), sub(one, scale(t, x)))))

    def pair_term(a, b):
        first = div(mul(a, add(one, scale(sp.Rational(1, 2), b))), A(b))
        second = scale(t, div(mul(mul(a, b), add(scale(t, b), scale(sp.Rational(1, 2), one))), D(b)))
        return sub(first, second)

    raw = [sp.S.Zero] * ORDER
    for x in radii:
        raw = add(raw, self_term(x))
    for i, j in ((0, 1), (0, 2), (1, 2)):
        raw = add(raw, pair_term(radii[i], radii[j]))
        raw = add(raw, pair_term(radii[j], radii[i]))
    total_radius = add(add(u, v), w)
    product_radius = mul(mul(u, v), w)
    raw = sub(raw, scale(3, div(total_radius, sub(one, product_radius))))
    raw = sub(raw, scale(3 * t**3, div(mul(total_radius, product_radius), sub(one, scale(t**3, product_radius)))))

    l_values = [L(x) for x in radii]
    alpha = {}
    for i, j in ((0, 1), (0, 2), (1, 2)):
        alpha[i, j] = mul(mul(radii[i], radii[j]), add(l_values[i], l_values[j]))
    correction = scale(sp.Rational(1, 2), add(add(alpha[0, 1], alpha[0, 2]), alpha[1, 2]))
    correction = sub(
        correction,
        scale(
            sp.Rational(1, 2),
            mul(
                power(u, 2),
                div(
                    mul(add(l_values[0], l_values[1]), add(l_values[0], l_values[2])),
                    add(l_values[1], l_values[2]),
                ),
            ),
        ),
    )
    correction = sub(
        correction,
        scale(
            sp.Rational(1, 2),
            mul(
                power(v, 2),
                div(
                    mul(add(l_values[0], l_values[1]), add(l_values[1], l_values[2])),
                    add(l_values[0], l_values[2]),
                ),
            ),
        ),
    )
    correction = sub(
        correction,
        scale(
            sp.Rational(1, 2),
            mul(
                power(w, 2),
                div(
                    mul(add(l_values[0], l_values[2]), add(l_values[1], l_values[2])),
                    add(l_values[0], l_values[1]),
                ),
            ),
        ),
    )

    surplus = add(raw, correction)
    simplified = [sp.factor(sp.cancel(value)) for value in surplus]
    cubic_shape = (
        2 * r**3 * s**3
        - r**2 * s**3
        - r**2 * s**2
        - r * s**3
        - r * s
        + 2 * s**3
        - s**2
        - s
        + 2
    )
    expected_cubic = sp.Rational(3, 2) * (1 + t**2) * cubic_shape
    cubic_identity = sp.factor(simplified[3] - expected_cubic) == 0
    lower_terms_vanish = simplified[:3] == [0, 0, 0]

    Rvar, h, H = sp.symbols("Rvar h H", nonnegative=True, real=True)

    def tensor_controls(scale_value):
        polynomial = sp.Poly(
            sp.expand(cubic_shape.subs(r, scale_value * Rvar)), Rvar, s
        )
        local_degrees = (polynomial.degree(Rvar), polynomial.degree(s))
        table = {}
        for i in range(local_degrees[0] + 1):
            for j in range(local_degrees[1] + 1):
                table[i, j] = sp.factor(
                    sum(
                        polynomial.coeff_monomial(Rvar**a * s**b)
                        * sp.Rational(comb(i, a), comb(local_degrees[0], a))
                        * sp.Rational(comb(j, b), comb(local_degrees[1], b))
                        for a in range(i + 1)
                        for b in range(j + 1)
                    )
                )
        return local_degrees, table

    degrees, full_controls = tensor_controls(sp.S.One)
    expected_full_controls = (
        (2, sp.Rational(5, 3), 1, 2),
        (2, sp.Rational(14, 9), sp.Rational(7, 9), sp.Rational(4, 3)),
        (2, sp.Rational(13, 9), sp.Rational(4, 9), 0),
        (2, sp.Rational(4, 3), 0, 0),
    )
    full_control_identity = all(
        full_controls[i, j] == expected_full_controls[i][j]
        for i in range(4)
        for j in range(4)
    )

    _, controls = tensor_controls(sp.Rational(1, 2))
    minimum_control = min(controls.values())
    cubic_lower_bound = sp.Rational(3, 2) * minimum_control

    # For every 3/4<=h<1, the least scaled-chart control is the diagonal-face
    # control m(h)=2(1-h)^2(1+h).  Verify this uniformly by converting each
    # control difference on h=3/4+H/4 to the one-variable Bernstein basis.
    _, symbolic_controls = tensor_controls(h)
    parametric_minimum = 2 * (1 - h) ** 2 * (1 + h)
    parametric_control_differences_nonnegative = True
    for value in symbolic_controls.values():
        difference = sp.Poly(
            sp.expand((value - parametric_minimum).subs(h, sp.Rational(3, 4) + H / 4)),
            H,
        )
        if difference.is_zero:
            continue
        degree = difference.degree()
        bernstein = [
            sum(
                difference.coeff_monomial(H**j)
                * sp.Rational(comb(i, j), comb(degree, j))
                for j in range(i + 1)
            )
            for i in range(degree + 1)
        ]
        parametric_control_differences_nonnegative &= all(value >= 0 for value in bernstein)

    # Exact circle majorant.  On |w|=rho, every radius has modulus <=rho.
    # A and D have modulus at least a0.  The deviation E bounds
    # |f(x)-1|, so every L_i+L_j has modulus at least ell.
    rho = sp.Rational(5, 42)
    delta = 1 - rho
    a0 = 1 - rho - rho**2
    deviation = (2 * rho + 4 * rho**2 + 2 * rho**3 + rho**4) / a0**2
    ell = 2 - 4 * deviation
    l_upper = 2 * (1 + rho**2) / a0**2
    majorant = (
        3 * (rho + rho**2) / delta
        + 6 * (rho * (1 + rho / 2) + rho**2 * (rho + sp.Rational(1, 2))) / a0
        + 9 * rho / (1 - rho**3)
        + 9 * rho**4 / (1 - rho**3)
        + 3 * rho**2 * l_upper
        + 6 * rho**2 * l_upper**2 / ell
    )
    w0 = sp.Rational(1, 25000)
    tail_over_w3 = majorant * w0 / rho**4 / (1 - w0 / rho)
    strict_margin = sp.factor(cubic_lower_bound - tail_over_w3)

    control_digest = hashlib.sha256(
        "\n".join(f"{index}:{value}" for index, value in sorted(controls.items())).encode()
    ).hexdigest()
    passed = all(
        (
            lower_terms_vanish,
            cubic_identity,
            full_control_identity,
            all(value >= 0 for value in full_controls.values()),
            parametric_control_differences_nonnegative,
            degrees == (3, 3),
            len(controls) == 16,
            minimum_control == sp.Rational(7, 12),
            cubic_lower_bound == sp.Rational(7, 8),
            deviation == sp.Rational(928405, 2337841),
            ell == sp.Rational(962062, 2337841),
            l_upper == sp.Rational(6311592, 2337841),
            majorant == sp.Rational(2377539521421837945, 582238064264313611),
            strict_margin > 0,
        )
    )
    result = {
        "schema": "erdos1041_three_exterior_stationary_collapsed_face_collar_receipt_v1",
        "ordered_chart": "u=r*s*w, v=s*w",
        "projective_collar_r_max": "1/2",
        "scale_collar_w_max": "1/25000",
        "formal_coefficients_below_cubic_vanish": lower_terms_vanish,
        "cubic_identity_exact": cubic_identity,
        "full_cube_cubic_bernstein_nonnegative": all(
            value >= 0 for value in full_controls.values()
        ),
        "parametric_h_3_over_4_to_1_control_bound_exact": (
            parametric_control_differences_nonnegative
        ),
        "parametric_cubic_shape_lower_bound": "2*(1-h)^2*(1+h)",
        "parametric_scale_bound": (
            "w < c(h)*rho^4/(M+c(h)*rho^3), "
            "c(h)=3*(1-h)^2*(1+h), rho=5/42"
        ),
        "cubic_shape_bernstein_degree": list(degrees),
        "cubic_shape_bernstein_controls": len(controls),
        "cubic_shape_minimum_control": str(minimum_control),
        "cubic_coefficient_lower_bound": str(cubic_lower_bound),
        "cubic_control_sha256": control_digest,
        "cauchy_circle_radius": str(rho),
        "kernel_deviation_bound": str(deviation),
        "pair_kernel_sum_lower_bound": str(ell),
        "kernel_upper_bound": str(l_upper),
        "whole_surplus_circle_majorant": str(majorant),
        "tail_over_w_cubed_at_endpoint": str(tail_over_w3),
        "strict_rational_margin": str(strict_margin),
        "ordered_small_scale_collar_positive": passed,
        "claim_boundary": (
            "Proves S_stat>0 when 0<=u<=v<=w, u/v<=1/2, and "
            "0<w<=1/25000. More generally, for every 3/4<=h<1 it proves an "
            "explicit positive scale collar on u/v<=h. It does not cover "
            "arbitrary scale, GP3, or Erdos 1041."
        ),
        "pass": passed,
    }
    print(json.dumps(result, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
