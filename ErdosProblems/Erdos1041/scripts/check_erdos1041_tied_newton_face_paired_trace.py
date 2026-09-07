#!/usr/bin/env python3
"""Exact replay for the paired critical-value trace on low Newton faces."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction

import sympy as sp

from check_erdos1041_tied_newton_face_critical_trace import (
    ZERO,
    active_coefficients,
    derivative_monic_coefficients,
    gadd,
    gmul,
    gscale,
    newton_power_sums,
)


def gconj(x):
    return x[0], -x[1]


def exact_degree_row(n: int) -> dict[str, object]:
    active = active_coefficients(n)
    moments = newton_power_sums(
        derivative_monic_coefficients(n, active), n - 1
    )
    moment_rows = []
    for m, coefficient in active.items():
        expected = gscale(Fraction(m * (n - m), n), coefficient)
        actual = moments[n - m]
        paired_trace = gscale(Fraction(-1), gmul(gconj(coefficient), actual))
        expected_trace = (
            -Fraction(m * (n - m), n)
            * (coefficient[0] ** 2 + coefficient[1] ** 2),
            Fraction(0),
        )
        moment_rows.append({
            "mode": m,
            "moment_degree": n - m,
            "moment_identity": actual == expected,
            "paired_trace_identity": paired_trace == expected_trace,
            "paired_trace_real": str(paired_trace[0]),
            "paired_trace_strictly_negative": paired_trace[0] < 0,
        })
    maximal = max(active)
    return {
        "degree": n,
        "maximal_active_mode": maximal,
        "first_gap": n - 2 * maximal,
        "rows": moment_rows,
        "first_paired_trace_negative": moment_rows[-1]["paired_trace_strictly_negative"],
    }


def quintic_equality_row() -> dict[str, object]:
    s = sp.sqrt(5)
    u = sp.symbols("u", positive=True, real=True)
    u3 = sp.Rational(27, 320)
    x_over_u = sp.Rational(2, 3) * (1 - sp.I * s)
    x3 = sp.expand(x_over_u ** 3 * u3)
    target_x3 = (-7 + sp.I * s) / 20
    critical_residual_over_u = sp.simplify(
        x_over_u * (5 * target_x3 + 2) - 1
    )
    # P(x)=x^5+x^2-u*x = -x^2(4x^3+1) at a critical point.
    p_over_u2 = sp.simplify(-x_over_u ** 2 * (4 * target_x3 + 1))
    return {
        "u_cubed": "27/320",
        "critical_coordinate_over_u": str(x_over_u),
        "critical_cube": str(sp.simplify(x3)),
        "critical_cube_identity": sp.simplify(x3 - target_x3) == 0,
        "critical_equation_residual_over_u": str(critical_residual_over_u),
        "leading_critical_value_polynomial_over_u_squared": str(p_over_u2),
        "leading_real_part_zero": sp.im(p_over_u2) == 0,
        "paired_cubic_real_correction": str(sp.re(target_x3)),
        "paired_cubic_is_negative_seven_twentieths": (
            sp.simplify(sp.re(target_x3) + sp.Rational(7, 20)) == 0
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    rows = [exact_degree_row(n) for n in range(5, 41)]
    equality = quintic_equality_row()
    ok = (
        all(row["first_gap"] >= 1 for row in rows)
        and all(all(item["moment_identity"] for item in row["rows"]) for row in rows)
        and all(all(item["paired_trace_identity"] for item in row["rows"]) for row in rows)
        and all(row["first_paired_trace_negative"] for row in rows)
        and equality["critical_cube_identity"]
        and equality["critical_equation_residual_over_u"] == "0"
        and equality["leading_real_part_zero"]
        and equality["paired_cubic_is_negative_seven_twentieths"]
    )
    payload = {
        "schema": "erdos1041_tied_newton_face_paired_trace_check_v1",
        "status": "pass" if ok else "fail",
        "exact_degree_range": [5, 40],
        "degree_rows": rows,
        "quintic_equality_chart": equality,
        "claim_boundary": (
            "Exact Newton recurrences verify the paired-trace identity on deterministic "
            "Gaussian-rational coefficient rows. The analytic proof is coefficient-general. "
            "This selects a lexicographically negative saddle but does not prove a metric connector."
        ),
    }
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"paired critical trace: {payload['status']}")
        print("degrees 5..40; first complementary trace strictly negative in every row")
        print("quintic equality paired correction:", equality["paired_cubic_real_correction"])
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
