#!/usr/bin/env python3
"""Exact finite-scale collar experiment off the stationary u=0 face."""

from __future__ import annotations

from fractions import Fraction
from math import comb

import sympy as sp
import hashlib
import json


def bernstein_coefficients(poly: sp.Poly, variables):
    degrees = [poly.degree(variable) for variable in variables]
    arr = {tuple(ex): Fraction(coefficient) for ex, coefficient in poly.as_dict().items()}
    for axis, degree in enumerate(degrees):
        groups = {}
        for exponent, coefficient in arr.items():
            other = exponent[:axis] + exponent[axis + 1 :]
            groups.setdefault(other, {})[exponent[axis]] = coefficient
        converted = {}
        for other, column in groups.items():
            for k in range(degree + 1):
                value = sum(
                    column.get(i, Fraction(0))
                    * Fraction(comb(k, i), comb(degree, i))
                    for i in range(k + 1)
                )
                converted[other[:axis] + (k,) + other[axis:]] = value
        arr = converted
    return degrees, arr


def split_controls(values, parameter):
    levels = [list(values)]
    while len(levels[-1]) > 1:
        previous = levels[-1]
        levels.append(
            [
                (1 - parameter) * previous[i] + parameter * previous[i + 1]
                for i in range(len(previous) - 1)
            ]
        )
    left = [level[0] for level in levels]
    right = [level[-1] for level in reversed(levels)]
    return left, right


def build_face_controls():
    t, v, w = sp.symbols("t v w", nonnegative=True, real=True)

    def A(x):
        return 1 + x + x**2

    def D(x):
        return 1 + t * x + t**2 * x**2

    def l_fraction(x):
        qx = sp.expand(A(x) ** 2 * D(x) ** 2)
        nx = sp.expand(
            (1 - x**2) * D(x) ** 2
            + t * (1 - t**2 * x**2) * A(x) ** 2
        )
        return nx, qx

    nv, qv = l_fraction(v)
    nw, qw = l_fraction(w)
    kv = sp.expand((1 + t) * qv + nv)
    kw = sp.expand((1 + t) * qw + nw)
    mvw = sp.expand(nv * qw + nw * qv)

    def P(expr):
        return sp.Poly(expr, t, v, w, domain=sp.QQ)

    def mul(*factors):
        answer = P(1)
        for factor in factors:
            answer *= factor if isinstance(factor, sp.Poly) else P(factor)
        return answer

    qvp, qwp, kvp, kwp, mvwp = map(P, (qv, qw, kv, kw, mvw))
    avp, awp, dvp, dwp = map(P, (A(v), A(w), D(v), D(w)))
    sf = [P(1 - v), P(1 - t * v), P(1 - w), P(1 - t * w)]
    common_tail = mul(qvp**2, qwp**2, kvp, kwp)
    terms = [
        mul(v, sf[1], sf[2], sf[3], common_tail),
        mul(t * v**2, sf[0], sf[2], sf[3], common_tail),
        mul(w, sf[3], sf[0], sf[1], common_tail),
        mul(t * w**2, sf[2], sf[0], sf[1], common_tail),
        mul(v * (1 + w / 2), *sf, qvp**2, awp**3, dwp**4, kvp, kwp),
        mul(-t * v * w * (t * w + sp.Rational(1, 2)), *sf, qvp**2, awp**4, dwp**3, kvp, kwp),
        mul(w * (1 + v / 2), *sf, qwp**2, avp**3, dvp**4, kvp, kwp),
        mul(-t * w * v * (t * v + sp.Rational(1, 2)), *sf, qwp**2, avp**4, dvp**3, kvp, kwp),
        mul(-2 * (v + w), *sf, common_tail),
        mul(v * w / 2, mvwp, *sf, qvp, qwp, kvp, kwp),
        mul(-v**2 / 2, kvp, mvwp, *sf, qwp**2, kvp),
        mul(-w**2 / 2, kwp, mvwp, *sf, qvp**2, kwp),
    ]
    numerator = P(0)
    for term in terms:
        numerator += term
    ordered_dict = {}
    for (it, iv, iw), coefficient in numerator.as_dict().items():
        assert iv + iw >= 3
        exponent = (it, iv, iv + iw - 3)
        ordered_dict[exponent] = ordered_dict.get(exponent, 0) + coefficient
    s = sp.symbols("s", nonnegative=True, real=True)
    ordered = sp.Poly.from_dict(ordered_dict, (t, s, w), domain=sp.QQ)
    degrees, controls = bernstein_coefficients(ordered, (t, s, w))
    return degrees, controls


def restrict_w(controls, degrees, lower, upper):
    dt, ds, dw = degrees
    result = {}
    relative = lower / upper
    for i in range(dt + 1):
        for j in range(ds + 1):
            column = [controls[i, j, k] for k in range(dw + 1)]
            left, _ = split_controls(column, upper)
            _, restricted = split_controls(left, relative)
            for k, value in enumerate(restricted):
                result[i, j, k] = value
    return result


def main() -> int:
    degrees, controls = build_face_controls()
    lower = Fraction(1, 25000)
    upper = Fraction(1, 2)
    restricted = restrict_w(controls, degrees, lower, upper)
    values = list(restricted.values())
    minimum = min(values)
    nonnegative = all(value >= 0 for value in values)
    positive = all(value > 0 for value in values)

    # Quantitative face lower bound S_0=w^3 P_ord/C.  On w<=1/2,
    # A,D<=7/4, hence Q<=Qmax and K<=(1+t)Q+N<=Kmax.
    qmax = Fraction(2401, 256)
    kmax = Fraction(3185, 128)
    denominator_max = qmax**4 * kmax**2
    face_lower = lower**3 * minimum / denominator_max

    # Complex-r Cauchy majorant in u=r*s*w on |r|=1/8.  Then |u|<=1/16,
    # while the two real radii are <=1/2.  The L-sum denominators stay away
    # from zero by the explicit bounds below.
    circle = Fraction(1, 8)
    u_radius = Fraction(1, 16)
    x_radius = Fraction(1, 2)
    a_u = 1 - u_radius - u_radius**2
    deviation_u = (
        2 * u_radius
        + 4 * u_radius**2
        + 2 * u_radius**3
        + u_radius**4
    ) / a_u**2
    l_u_upper = 2 * (1 + u_radius**2) / a_u**2
    l_real_lower = Fraction(12, 49)
    l_sum_lower = min(
        2 * l_real_lower,
        1 + l_real_lower - 2 * deviation_u,
    )
    l_sum_upper = max(l_u_upper + 2, Fraction(4))
    pair_bound = (
        x_radius * (1 + x_radius / 2)
        + x_radius**2 * (x_radius + Fraction(1, 2))
    ) / a_u
    product_bound = u_radius * x_radius**2
    radius_sum_bound = u_radius + 2 * x_radius
    circle_majorant = (
        (u_radius + u_radius**2) / (1 - u_radius)
        + 3
        + 6 * pair_bound
        + 3 * radius_sum_bound / (1 - product_bound)
        + 3 * radius_sum_bound * product_bound / (1 - product_bound)
        + Fraction(3, 8) * l_sum_upper
        + Fraction(3, 8) * l_sum_upper**2 / l_sum_lower
    )
    collar = Fraction(1, 10**22)
    variation = circle_majorant * (collar / circle) / (1 - collar / circle)
    margin = face_lower - variation

    digest = hashlib.sha256(
        "\n".join(
            f"{index}:{value.numerator}/{value.denominator}"
            for index, value in sorted(restricted.items())
        ).encode()
    ).hexdigest()
    passed = all(
        (
            degrees == [28, 28, 50],
            len(values) == 42891,
            nonnegative,
            positive,
            minimum
            == Fraction(
                12279771987308302586472053335247680637483798058378066075156428194742975182708104138949979874250363701733625111973,
                1412807648648595204576849937438964843750000000000000000000000000000000000000000000000000000000000000000000000000,
            ),
            deviation_u == Fraction(9249, 57121),
            l_u_upper == Fraction(131584, 57121),
            l_sum_lower == Fraction(24, 49),
            l_sum_upper == Fraction(245826, 57121),
            margin > 0,
        )
    )
    result = {
        "schema": "erdos1041_three_exterior_stationary_finite_scale_face_collar_receipt_v1",
        "scale_interval": [str(lower), str(upper)],
        "projective_collar_r_max": str(collar),
        "face_bernstein_degree": degrees,
        "face_restricted_control_count": len(values),
        "face_restricted_all_positive": positive,
        "face_restricted_minimum_control": str(minimum),
        "face_restricted_control_sha256": digest,
        "face_denominator_upper_bound": str(denominator_max),
        "face_surplus_lower_bound": str(face_lower),
        "complex_r_circle_radius": str(circle),
        "complex_u_radius": str(u_radius),
        "kernel_deviation_bound": str(deviation_u),
        "kernel_sum_lower_bound": str(l_sum_lower),
        "kernel_sum_upper_bound": str(l_sum_upper),
        "whole_surplus_circle_majorant": str(circle_majorant),
        "cauchy_variation_at_collar": str(variation),
        "strict_rational_margin": str(margin),
        "finite_scale_stationary_face_collar_positive": passed,
        "claim_boundary": (
            "Proves S_stat>0 for 0<=r=u/v<=10^-22, "
            "1/25000<=w<=1/2, and all s,t in [0,1]. It does not cover "
            "w>1/2, a practical-width collar, GP3, or Erdos 1041."
        ),
        "pass": passed,
    }
    print(json.dumps(result, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
