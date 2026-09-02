#!/usr/bin/env python3
"""Exact high-radius collars off the stationary GP3 face r=0.

The ordered chart is u=r*s*w, v=s*w.  The checker reconstructs the cleared
u=0 numerator, restricts its Bernstein controls to w in [1/2,1], and verifies
the control data used by the parameterized compact-radius theorem.  It also
replays the stronger concrete slab w in [1/2,3/4], r<=10^-12.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb
import hashlib
import json

import sympy as sp


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
    return bernstein_coefficients(ordered, (t, s, w))


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


def compact_bounds(radius: Fraction, face_control: Fraction):
    """Return the exact face lower bound, circle majorant, and collar."""
    lower = Fraction(1, 2)
    amax = 1 + radius + radius**2
    qmax = amax**4
    kmax = 2 * qmax + 2 * amax**2
    face_lower = lower**3 * face_control / (qmax**4 * kmax**2)

    circle = Fraction(1, 8)
    u_radius = circle
    au = 1 - u_radius - u_radius**2
    deviation = (
        2 * u_radius
        + 4 * u_radius**2
        + 2 * u_radius**3
        + u_radius**4
    ) / au**2
    mixed_floor = 1 - 2 * deviation
    real_floor = (1 - radius**2) / amax**2
    # This harmonic-mean lower bound is no larger than either admissible
    # denominator lower bound mixed_floor and 2*real_floor.
    ell = mixed_floor * (2 * real_floor) / (mixed_floor + 2 * real_floor)
    l_upper = 2 * (1 + u_radius**2) / au**2 + 2
    pair_bound = (
        radius * (1 + radius / 2)
        + radius**2 * (radius + Fraction(1, 2))
    ) / au
    product_bound = u_radius * radius**2
    radius_sum_bound = u_radius + 2 * radius
    majorant = (
        (u_radius + u_radius**2) / (1 - u_radius)
        + 2 * (radius + radius**2) / (1 - radius)
        + 6 * pair_bound
        + 3 * radius_sum_bound / (1 - product_bound)
        + 3 * radius_sum_bound * product_bound / (1 - product_bound)
        + Fraction(3, 2) * radius**2 * l_upper
        + Fraction(3, 2) * radius**2 * l_upper**2 / ell
    )
    collar = circle * face_lower / (majorant + face_lower)
    return {
        "face_lower": face_lower,
        "deviation": deviation,
        "mixed_floor": mixed_floor,
        "real_floor": real_floor,
        "ell": ell,
        "l_upper": l_upper,
        "majorant": majorant,
        "collar": collar,
    }


def main() -> int:
    degrees, controls = build_face_controls()
    half_to_one = restrict_w(controls, degrees, Fraction(1, 2), Fraction(1))
    global_values = list(half_to_one.values())
    leading_values = [
        value for (it, js, kw), value in half_to_one.items() if kw == 0
    ]
    leading_minimum = min(leading_values)
    global_digest = hashlib.sha256(
        "\n".join(
            f"{index}:{value.numerator}/{value.denominator}"
            for index, value in sorted(half_to_one.items())
        ).encode()
    ).hexdigest()

    concrete_radius = Fraction(3, 4)
    concrete_controls = restrict_w(
        controls, degrees, Fraction(1, 2), concrete_radius
    )
    concrete_minimum = min(concrete_controls.values())
    concrete = compact_bounds(concrete_radius, concrete_minimum)
    concrete_collar = Fraction(1, 10**12)
    circle = Fraction(1, 8)
    variation = concrete["majorant"] * (concrete_collar / circle) / (
        1 - concrete_collar / circle
    )
    concrete_margin = concrete["face_lower"] - variation

    # The all-R theorem uses de Casteljau positivity.  If theta=2R-1, every
    # left-subdivision control of w-index k is at least
    # b_0*(1-theta)^k, hence at least m_0*[2(1-R)]^50.
    # A rational reference R=7/8 replays every component of its explicit
    # formula; positivity for arbitrary real 1/2<=R<1 is then formal from the
    # displayed positive factors.
    reference_radius = Fraction(7, 8)
    parametric_control_floor = leading_minimum * (
        2 * (1 - reference_radius)
    ) ** degrees[2]
    reference = compact_bounds(reference_radius, parametric_control_floor)

    passed = all(
        (
            degrees == [28, 28, 50],
            len(global_values) == 42891,
            all(value >= 0 for value in global_values),
            sum(value == 0 for value in global_values) == 62,
            len(leading_values) == 841,
            all(value > 0 for value in leading_values),
            leading_minimum == Fraction(944707, 8192),
            global_digest
            == "c3bef1c70d3e9317aa6c711811c87bf1076b3ba46f2201d8aa2e49cc69a789c5",
            concrete_minimum == leading_minimum,
            concrete["deviation"] == Fraction(1297, 3025),
            concrete["mixed_floor"] == Fraction(431, 3025),
            concrete["ell"] == Fraction(96544, 1267639),
            concrete["l_upper"] == Fraction(2874, 605),
            concrete["majorant"]
            == Fraction(1357159489278069, 4805902393600),
            concrete_margin > 0,
            reference["face_lower"] > 0,
            reference["ell"] > 0,
            reference["majorant"] > 0,
            reference["collar"] > 0,
        )
    )
    result = {
        "schema": "erdos1041_three_exterior_stationary_high_radius_face_collar_receipt_v1",
        "face_bernstein_degree": degrees,
        "half_to_one_control_count": len(global_values),
        "half_to_one_nonnegative": all(value >= 0 for value in global_values),
        "half_to_one_zero_controls": sum(value == 0 for value in global_values),
        "w_left_face_control_count": len(leading_values),
        "w_left_face_all_positive": all(value > 0 for value in leading_values),
        "w_left_face_minimum": str(leading_minimum),
        "half_to_one_control_sha256": global_digest,
        "parametric_control_floor": "(944707/8192)*(2*(1-R))^50",
        "parametric_scope": "for every real 1/2<=R<1",
        "concrete_scale_interval": ["1/2", "3/4"],
        "concrete_projective_collar_r_max": str(concrete_collar),
        "concrete_face_lower": str(concrete["face_lower"]),
        "concrete_circle_majorant": str(concrete["majorant"]),
        "concrete_strict_margin": str(concrete_margin),
        "reference_radius": str(reference_radius),
        "reference_parametric_face_lower": str(reference["face_lower"]),
        "reference_parametric_collar": str(reference["collar"]),
        "all_compact_high_radius_collars_positive": passed,
        "claim_boundary": (
            "Proves S_stat>0 on r<=10^-12, 1/2<=w<=3/4, and gives "
            "an explicit positive collar epsilon(R) for every compact slab "
            "1/2<=w<=R<1. Together with the existing lower-scale collars "
            "this covers every point of the r=0 face locally. It does not "
            "give a uniform collar at w=1, prove GP3, or prove Erdos 1041."
        ),
        "pass": passed,
    }
    print(json.dumps(result, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
