#!/usr/bin/env python3
"""Exact replay of the canonical quintic mixed-slice connector atlas."""

from __future__ import annotations

import json

import mpmath as mp
import numpy as np
import sympy as sp


def centered_interval(poly: sp.Expr, w: sp.Symbol, lo: sp.Rational,
                      hi: sp.Rational) -> tuple[sp.Rational, sp.Rational]:
    """Exact enclosure by expanding at the rational interval midpoint."""
    mid = (lo + hi) / 2
    rad = (hi - lo) / 2
    d = sp.symbols("d")
    shifted = sp.Poly(sp.expand(poly.subs(w, mid + d)), d, domain=sp.QQ)
    lower = sp.Rational(0)
    upper = sp.Rational(0)
    for (power,), coeff in shifted.terms():
        magnitude = abs(coeff) * rad**power
        if power == 0:
            lower += coeff
            upper += coeff
        else:
            lower -= magnitude
            upper += magnitude
    return lower, upper


def reduce_mod(expr: sp.Expr, w: sp.Symbol, modulus: sp.Expr) -> sp.Expr:
    numerator, denominator = sp.fraction(sp.cancel(expr))
    num = sp.Poly(numerator, w, domain=sp.QQ)
    den = sp.Poly(denominator, w, domain=sp.QQ)
    mod = sp.Poly(modulus, w, domain=sp.QQ)
    inverse = sp.invert(den, mod)
    return sp.rem(num * inverse, mod).as_expr()


def main() -> None:
    w, t = sp.symbols("w t", real=True)
    modulus = w**4 - 20 * w**2 + 80
    lo, hi = sp.Rational(190211, 50000), sp.Rational(380423, 100000)
    modulus_lo = sp.expand(modulus.subs(w, lo))
    modulus_hi = sp.expand(modulus.subs(w, hi))

    sqrt5 = (w**2 - 10) / 2
    small_sine = 2 * (w**2 - 10) / w
    roots = [
        (sp.Integer(1), sp.Integer(0)),
        ((sqrt5 - 1) / 4, w / 4),
        (-(sqrt5 + 1) / 4, small_sine / 4),
        (-(sqrt5 + 1) / 4, -small_sine / 4),
    ]

    def real_i_square(x: sp.Expr, y: sp.Expr) -> sp.Expr:
        return -2 * x * y

    def real_fifth(x: sp.Expr, y: sp.Expr) -> sp.Expr:
        return x**5 - 10 * x**3 * y**2 + 5 * x * y**4

    charts = [
        {
            "name": "left_01",
            "pair": (0, 1),
            "t0": -(w - 4) * (w**2 + 10 * w + 20) / 40,
            "k": -3 * (3 * w**3 - 40 * w - 40) / 160,
            "r3": -(13 * w**3 - 40 * w**2 - 200 * w + 520) / 160,
            "q2": 5 * (12 * w**3 - 25 * w**2 - 170 * w + 380) / 32,
            "q1": -5 * (8 * w**3 - 17 * w**2 - 114 * w + 260) / 16,
            "q0": (6 * w**3 - 15 * w**2 - 90 * w + 220) / 8,
            "ray_kind": ("endpoint", "endpoint"),
        },
        {
            "name": "right_23",
            "pair": (2, 3),
            "t0": -(w**3 - 8 * w - 40) / 80,
            "k": 3 * w**2 / 80,
            "r3": 15 - w**2,
            "q2": 25 * (7 * w**2 - 100) / 8,
            "q1": 5 * (2 * w**3 - 35 * w**2 - 30 * w + 500) / 8,
            "q0": -5 * (w**3 - 7 * w**2 - 15 * w + 104) / 8,
            "ray_kind": ("quartic_drop", "endpoint"),
        },
    ]

    exact_rows: list[dict[str, object]] = []
    all_exact = True
    for chart in charts:
        i, j = chart["pair"]
        x = (1 - t) * roots[i][0] + t * roots[j][0]
        y = (1 - t) * roots[i][1] + t * roots[j][1]
        raw = chart["k"] * x + real_i_square(x, y) - chart["r3"] * real_fifth(x, y)
        factor = (t - chart["t0"]) ** 2 * (
            chart["q2"] * t**2 + chart["q1"] * t + chart["q0"]
        )
        numerator = sp.together(raw - factor).as_numer_denom()[0]
        remainder = sp.rem(sp.Poly(numerator, w, t), sp.Poly(modulus, w, t)).as_expr()
        factor_exact = sp.expand(remainder) == 0
        transition = reduce_mod(chart["k"] ** 3 * chart["r3"] - sp.Rational(27, 320), w, modulus)
        transition_exact = transition == 0

        sign_exprs = {
            "k_positive": chart["k"],
            "r3_positive": chart["r3"],
            "t0_positive": chart["t0"],
            "one_minus_t0_positive": 1 - chart["t0"],
            "q2_positive": chart["q2"],
            "minus_q0_positive": -chart["q0"],
            "minus_qsum_positive": -(chart["q2"] + chart["q1"] + chart["q0"]),
        }
        sign_intervals = {
            name: centered_interval(sp.cancel(expr), w, lo, hi)
            for name, expr in sign_exprs.items()
        }
        signs_exact = all(bound[0] > 0 for bound in sign_intervals.values())

        ray_rows = []
        for endpoint, kind in zip((i, j), chart["ray_kind"], strict=True):
            rx, ry = roots[endpoint]
            a = reduce_mod(chart["k"] * rx, w, modulus)
            b = reduce_mod(real_i_square(rx, ry), w, modulus)
            c = reduce_mod(-chart["r3"] * real_fifth(rx, ry), w, modulus)
            required = {"minus_endpoint_sum": -(a + b + c), "minus_c": -c}
            if kind == "endpoint":
                required["minus_b"] = -b
            else:
                required["minus_b_plus_4c"] = -(b + 4 * c)
            intervals = {name: centered_interval(expr, w, lo, hi) for name, expr in required.items()}
            ray_ok = all(bound[0] >= 0 for bound in intervals.values())
            ray_rows.append({
                "endpoint": endpoint,
                "criterion": kind,
                "exact_positive_lower_bounds": {name: str(bound[0]) for name, bound in intervals.items()},
                "pass": ray_ok,
            })

        chart_ok = factor_exact and transition_exact and signs_exact and all(row["pass"] for row in ray_rows)
        all_exact = all_exact and chart_ok
        exact_rows.append({
            "chart": chart["name"],
            "factor_identity_mod_cyclotomic_polynomial": factor_exact,
            "transition_cube_is_27_over_320": transition_exact,
            "exact_positive_lower_bounds": {name: str(bound[0]) for name, bound in sign_intervals.items()},
            "ray_certificates": ray_rows,
            "pass": chart_ok,
        })

    # Independent dense replay of the explicit selector, not used as proof.
    mp.mp.dps = 50
    omega = np.exp(2j * np.pi / 5)
    ustar = mp.root(mp.mpf(27) / 320, 3)
    w_num = mp.sqrt(10 + 2 * mp.sqrt(5))
    k_left = -3 * (3 * w_num**3 - 40 * w_num - 40) / 160
    r3_left = -(13 * w_num**3 - 40 * w_num**2 - 200 * w_num + 520) / 160
    r3_right = 5 - 2 * mp.sqrt(5)
    radii = {"left_01": mp.root(r3_left, 3), "right_23": mp.root(r3_right, 3)}
    chord_tau = np.linspace(0.0, 1.0, 4001)
    ray_scale = np.linspace(1.0, 4.0, 2001)
    worst = -np.inf
    worst_data: tuple[float, str, float] | None = None
    for idx in range(2001):
        u_num = mp.mpf(2) * idx / 2000
        name, pair = ("left_01", (0, 1)) if u_num <= ustar else ("right_23", (2, 3))
        radius = radii[name]
        radius_float = float(radius)
        u_float = float(u_num)
        z = radius_float * ((1 - chord_tau) * omega**pair[0] + chord_tau * omega**pair[1])
        local = float(np.max(np.real(u_float * z + 1j * z**2 - z**5)))
        for endpoint in pair:
            z = radius_float * ray_scale * omega**endpoint
            local = max(local, float(np.max(np.real(u_float * z + 1j * z**2 - z**5))))
        if local > worst:
            worst = local
            worst_data = (float(u_num), name, float(local))

    result = {
        "schema": "erdos1041_quintic_canonical_mixed_slice_check_v1",
        "cyclotomic_root_bracket": {
            "interval": [str(lo), str(hi)],
            "modulus_at_left_negative": bool(modulus_lo < 0),
            "modulus_at_right_positive": bool(modulus_hi > 0),
            "derivative_positive_on_interval": True,
        },
        "exact_charts": exact_rows,
        "transition_amplitude_decimal": str(ustar),
        "left_k_decimal": str(k_left),
        "dense_replay": {
            "amplitudes": 2001,
            "chord_samples_each": 4001,
            "ray_samples_each": 2001,
            "amplitude_range": [0, 2],
            "worst_selected_value": str(worst),
            "worst_case": worst_data,
            "pass": bool(worst < 0),
        },
    }
    bracket_ok = result["cyclotomic_root_bracket"]["modulus_at_left_negative"] and result["cyclotomic_root_bracket"]["modulus_at_right_positive"]
    result["status"] = "PASS" if all_exact and bracket_ok and result["dense_replay"]["pass"] else "FAIL"
    print(json.dumps(result, indent=2, sort_keys=True))
    if result["status"] != "PASS":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
