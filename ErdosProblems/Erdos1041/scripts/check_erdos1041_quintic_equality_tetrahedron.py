#!/usr/bin/env python3
"""Exact replay of the four-contact quintic equality tetrahedron."""

from __future__ import annotations

import json

import numpy as np
import sympy as sp


def remainder_wh(expr: sp.Expr, w: sp.Symbol, h: sp.Symbol) -> sp.Expr:
    """Numerator remainder modulo h^2-3 and w^4-20w^2+80."""
    numerator = sp.together(expr).as_numer_denom()[0]
    reduced_h = sp.rem(numerator, h**2 - 3, h)
    reduced_w = sp.rem(reduced_h, w**4 - 20 * w**2 + 80, w)
    return sp.expand(reduced_w)


def box_interval(expr: sp.Expr, variables: tuple[sp.Symbol, ...],
                 boxes: tuple[tuple[sp.Rational, sp.Rational], ...]) -> tuple[sp.Rational, sp.Rational]:
    """Exact centred-form enclosure on a narrow rational box."""
    numerator, denominator = sp.fraction(sp.cancel(expr))

    def polynomial_interval(poly: sp.Expr) -> tuple[sp.Rational, sp.Rational]:
        deltas = sp.symbols(f"d0:{len(variables)}")
        mids = [(lo + hi) / 2 for lo, hi in boxes]
        radii = [(hi - lo) / 2 for lo, hi in boxes]
        shifted = sp.Poly(sp.expand(poly.subs(dict(zip(variables, [m + d for m, d in zip(mids, deltas)])))), *deltas, domain=sp.QQ)
        lower = sp.Rational(0)
        upper = sp.Rational(0)
        for powers, coefficient in shifted.terms():
            magnitude = abs(coefficient)
            for radius, power in zip(radii, powers):
                magnitude *= radius**power
            if all(power == 0 for power in powers):
                lower += coefficient
                upper += coefficient
            else:
                lower -= magnitude
                upper += magnitude
        return lower, upper

    numerator_interval = polynomial_interval(numerator)
    denominator_interval = polynomial_interval(denominator)
    if denominator_interval[0] <= 0:
        raise ValueError(f"denominator interval crosses zero: {denominator_interval}")
    candidates = [
        numerator_interval[0] / denominator_interval[0],
        numerator_interval[0] / denominator_interval[1],
        numerator_interval[1] / denominator_interval[0],
        numerator_interval[1] / denominator_interval[1],
    ]
    return min(candidates), max(candidates)


def main() -> None:
    w, h, t = sp.symbols("w h t", real=True)
    w_box = (sp.Rational(190211, 50000), sp.Rational(380423, 100000))
    h_box = (sp.Rational(34641, 20000), sp.Rational(86603, 50000))
    boxes = (w_box, h_box)
    sqrt5 = (w**2 - 10) / 2
    small_sine = 2 * (w**2 - 10) / w
    roots = [
        (sp.Integer(1), sp.Integer(0)),
        ((sqrt5 - 1) / 4, w / 4),
        (-(sqrt5 + 1) / 4, small_sine / 4),
        (-(sqrt5 + 1) / 4, -small_sine / 4),
        ((sqrt5 - 1) / 4, -w / 4),
    ]

    q_plus = w**3 * (3 * h - 5) / 160
    q_minus = w * (3 * h + 5) * (3 * w**2 - 40) / 160
    charts = [
        {
            "name": "upper_axis_13",
            "pair": (1, 3),
            "t0": 1 - w**2 / 20,
            "Q": q_plus,
            "kind": "concave_discriminant",
            "ray_kinds": ("endpoint", "endpoint"),
        },
        {
            "name": "lower_axis_34",
            "pair": (3, 4),
            "t0": w**2 / 20,
            "Q": q_minus,
            "kind": "convex_endpoints",
            "ray_kinds": ("endpoint", "quartic_drop"),
        },
    ]

    rows: list[dict[str, object]] = []
    exact_ok = True
    for chart in charts:
        i, j = chart["pair"]
        Q = chart["Q"]
        x = (1 - t) * roots[i][0] + t * roots[j][0]
        y = (1 - t) * roots[i][1] + t * roots[j][1]
        B = -2 * x * y
        C = x**5 - 10 * x**3 * y**2 + 5 * x * y**4
        Lp = sp.diff(x, t).subs(t, chart["t0"])
        Bp = sp.diff(B, t).subs(t, chart["t0"])
        Cp = sp.diff(C, t).subs(t, chart["t0"])
        k = sp.cancel((Q * Cp - Bp) / Lp)
        raw = k * x + B - Q * C
        raw_poly = sp.Poly(sp.together(raw), t)
        coefficients = [sp.cancel(raw_poly.coeff_monomial(t**degree)) for degree in range(5)]
        q2 = coefficients[4]
        q1 = sp.cancel(coefficients[3] + 2 * chart["t0"] * q2)
        q0 = sp.cancel(coefficients[2] - chart["t0"] ** 2 * q2 + 2 * chart["t0"] * q1)
        factor = (t - chart["t0"]) ** 2 * (q2 * t**2 + q1 * t + q0)
        factor_exact = remainder_wh(raw - factor, w, h) == 0
        transition_exact = remainder_wh(k**3 * Q - sp.Rational(27, 320), w, h) == 0

        sign_targets: dict[str, sp.Expr]
        if chart["kind"] == "concave_discriminant":
            discriminant = sp.cancel(q1**2 - 4 * q2 * q0)
            sign_targets = {
                "minus_q2": -q2,
                "minus_discriminant": -discriminant,
                "minus_q_at_contact": -(q2 * chart["t0"] ** 2 + q1 * chart["t0"] + q0),
            }
        else:
            sign_targets = {
                "q2": q2,
                "minus_q0": -q0,
                "minus_qsum": -(q2 + q1 + q0),
                "minus_q_at_contact": -(q2 * chart["t0"] ** 2 + q1 * chart["t0"] + q0),
            }
        sign_intervals = {name: box_interval(sp.cancel(expr), (w, h), boxes) for name, expr in sign_targets.items()}
        chord_signs = all(bound[0] > 0 for bound in sign_intervals.values())

        ray_rows = []
        for endpoint, kind in zip((i, j), chart["ray_kinds"], strict=True):
            rx, ry = roots[endpoint]
            a = sp.cancel(k * rx)
            b = sp.cancel(-2 * rx * ry)
            c = sp.cancel(-Q * (rx**5 - 10 * rx**3 * ry**2 + 5 * rx * ry**4))
            targets = {"minus_c": -c, "minus_endpoint_sum": -(a + b + c)}
            if kind == "endpoint":
                targets["minus_b"] = -b
            else:
                targets["minus_b_plus_4c"] = -(b + 4 * c)
            intervals = {name: box_interval(sp.cancel(expr), (w, h), boxes) for name, expr in targets.items()}
            ray_pass = all(bound[0] >= 0 for bound in intervals.values())
            ray_rows.append({
                "endpoint": endpoint,
                "criterion": kind,
                "exact_positive_lower_bounds": {name: str(bound[0]) for name, bound in intervals.items()},
                "pass": ray_pass,
            })

        chart_pass = factor_exact and transition_exact and chord_signs and all(row["pass"] for row in ray_rows)
        exact_ok = exact_ok and chart_pass
        rows.append({
            "chart": chart["name"],
            "double_contact_factor_exact": factor_exact,
            "transition_cube_exact": transition_exact,
            "chord_sign_lower_bounds": {name: str(bound[0]) for name, bound in sign_intervals.items()},
            "ray_certificates": ray_rows,
            "pass": chart_pass,
        })

    # Exact contact identities tying all four independently derived radii to
    # one y-scaled sqrt(3)/sqrt(5) configuration.
    t_left = -(w - 4) * (w**2 + 10 * w + 20) / 40
    t_right = -(w**3 - 8 * w - 40) / 80
    r3_left = -(13 * w**3 - 40 * w**2 - 200 * w + 520) / 160
    r3_right = 15 - w**2
    x_left = (1 - t_left) * roots[0][0] + t_left * roots[1][0]
    y_left = (1 - t_left) * roots[0][1] + t_left * roots[1][1]
    x_right = (1 - t_right) * roots[2][0] + t_right * roots[3][0]
    y_right = (1 - t_right) * roots[2][1] + t_right * roots[3][1]
    axis_plus = ((1 - charts[0]["t0"]) * roots[1][1] + charts[0]["t0"] * roots[3][1])
    axis_minus_magnitude = -((1 - charts[1]["t0"]) * roots[3][1] + charts[1]["t0"] * roots[4][1])
    contact_identities = {
        "left_direction_sqrt5_plus_i": remainder_wh(x_left - sqrt5 * y_left, w, h) == 0,
        "right_direction_minus_sqrt5_plus_i": remainder_wh(x_right + sqrt5 * y_right, w, h) == 0,
        "left_right_common_y_cube": remainder_wh(r3_left * y_left**3 - r3_right * y_right**3, w, h) == 0,
        "upper_axis_ratio_sqrt3_minus_one": remainder_wh(q_plus * axis_plus**3 - (h - 1) ** 3 * r3_left * y_left**3, w, h) == 0,
        "lower_axis_ratio_sqrt3_plus_one": remainder_wh(q_minus * axis_minus_magnitude**3 - (h + 1) ** 3 * r3_left * y_left**3, w, h) == 0,
    }
    exact_ok = exact_ok and all(contact_identities.values())

    s3, s5, yy = sp.symbols("s3 s5 yy", positive=True, real=True)
    gradients = sp.Matrix([
        [s5 * yy, -yy, -4 * yy**2],
        [0, -(s3 - 1) * yy, (s3 - 1) ** 2 * yy**2],
        [-s5 * yy, -yy, -4 * yy**2],
        [0, (s3 + 1) * yy, (s3 + 1) ** 2 * yy**2],
    ])
    gradient_sum = [sp.rem(sp.expand(value), s3**2 - 3, s3) for value in list(sum((gradients.row(i) for i in range(4)), sp.zeros(1, 3)))]
    augmented_det = sp.factor(gradients.row_join(sp.ones(4, 1)).det())
    determinant_normalized = sp.simplify(augmented_det.subs({yy: 1, s3: sp.sqrt(3), s5: sp.sqrt(5)}))
    tetrahedron_exact = gradient_sum == [0, 0, 0] and determinant_normalized == 16 * sp.sqrt(15)
    exact_ok = exact_ok and tetrahedron_exact

    # Independent directional stress test of the strict selector.
    rng = np.random.default_rng(1041)
    directions = rng.normal(size=(500_000, 3))
    directions /= np.linalg.norm(directions, axis=1)[:, None]
    g_num = np.array(gradients.subs({s3: sp.sqrt(3), s5: sp.sqrt(5), yy: 1})).astype(float)
    selected = np.min(directions @ g_num.T, axis=1)
    directional_pass = bool(np.max(selected) < 0)

    result = {
        "schema": "erdos1041_quintic_equality_tetrahedron_check_v1",
        "algebraic_root_brackets": {
            "w": [str(value) for value in w_box],
            "sqrt3": [str(value) for value in h_box],
            "w_polynomial_bracketed": bool((w_box[0]**4 - 20*w_box[0]**2 + 80) < 0 < (w_box[1]**4 - 20*w_box[1]**2 + 80)),
            "sqrt3_polynomial_bracketed": bool(h_box[0]**2 < 3 < h_box[1]**2),
        },
        "axis_connector_charts": rows,
        "contact_identities": contact_identities,
        "tetrahedron": {
            "gradient_sum_exact_zero": gradient_sum == [0, 0, 0],
            "normalized_augmented_determinant": str(determinant_normalized),
            "affinely_independent": tetrahedron_exact,
            "random_unit_directions": 500_000,
            "largest_sampled_best_first_variation": float(np.max(selected)),
            "directional_stress_pass": directional_pass,
        },
    }
    bracket_pass = all(result["algebraic_root_brackets"][key] for key in ("w_polynomial_bracketed", "sqrt3_polynomial_bracketed"))
    result["status"] = "PASS" if exact_ok and bracket_pass and directional_pass else "FAIL"
    print(json.dumps(result, indent=2, sort_keys=True))
    if result["status"] != "PASS":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
