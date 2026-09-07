#!/usr/bin/env python3
"""Exact replay of the minimum-real critical-value selector no-go.

The script uses symbolic rational arithmetic for every promoted claim.  The
floating critical roots are diagnostics only.
"""

from __future__ import annotations

import argparse
import json

import sympy as sp


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    z, r, x, y = sp.symbols("z r x y", real=True)
    Q = -sp.Rational(379, 256) * z + 3 * z**2 - z**5
    derivative = sp.diff(Q, z)
    cubic = 320 * z**3 + 80 * z**2 + 20 * z - 379
    critical_value = sp.Rational(9, 5) * z**2 - sp.Rational(379, 320) * z

    factor_ok = sp.factor(derivative + (4 * z - 1) * cubic / 256) == 0
    quarter_value = sp.factor(Q.subs(z, sp.Rational(1, 4)))
    witness_value = sp.factor(Q.subs(z, sp.Rational(2, 3)))
    critical_reduction = sp.factor(
        Q - critical_value - z * derivative / 5
    )

    p = sp.Poly(cubic, z)
    derivative_positive_identity = sp.expand(
        sp.diff(cubic, z)
        - 20 * (48 * (z + sp.Rational(1, 12)) ** 2 + sp.Rational(2, 3))
    )
    p_left = p.eval(sp.Rational(24, 25))
    p_right = p.eval(1)

    pair_real_part = (
        sp.Rational(9, 5) * (x**2 - y**2) - sp.Rational(379, 320) * x
    )
    viete_x = -(r + sp.Rational(1, 4)) / 2
    viete_y2 = sp.Rational(379, 320) / r - viete_x**2
    raw_gap = sp.factor(
        pair_real_part.subs({x: viete_x, y**2: viete_y2})
        + sp.Rational(47, 256)
    )
    expected_raw_gap = (
        11520 * r**3 + 13340 * r**2 + 4965 * r - 27288
    ) / (12800 * r)
    reduced_numerator = sp.rem(
        11520 * r**3 + 13340 * r**2 + 4965 * r - 27288,
        320 * r**3 + 80 * r**2 + 20 * r - 379,
        domain=sp.QQ,
    )
    expected_reduced_numerator = 10460 * r**2 + 4245 * r - 13644
    reduced_at_left = sp.factor(
        expected_reduced_numerator.subs(r, sp.Rational(24, 25))
    )

    critical_roots = sp.nroots(sp.Poly(derivative, z), n=40, maxsteps=200)
    numerical_rows = []
    for root in critical_roots:
        value = sp.N(Q.subs(z, root), 30)
        numerical_rows.append(
            {
                "critical_point": str(root),
                "critical_value": str(value),
                "critical_value_real": float(sp.re(value)),
            }
        )
    numerical_rows.sort(key=lambda row: row["critical_value_real"])

    exact_gates = {
        "derivative_factorization": bool(factor_ok),
        "quarter_is_critical": derivative.subs(z, sp.Rational(1, 4)) == 0,
        "quarter_value": quarter_value == -sp.Rational(47, 256),
        "positive_waypoint_value": witness_value == sp.Rational(6677, 31104),
        "positive_waypoint": witness_value > 0,
        "critical_value_reduction": critical_reduction == 0,
        "cubic_derivative_positive_identity": derivative_positive_identity == 0,
        "cubic_left_negative": p_left == -sp.Rational(9239, 3125),
        "cubic_right_positive": p_right == 41,
        "viete_pair_gap_identity": sp.factor(raw_gap - expected_raw_gap) == 0,
        "cubic_gap_remainder": sp.expand(
            reduced_numerator - expected_reduced_numerator
        ) == 0,
        "gap_numerator_positive_at_left_bound": (
            reduced_at_left == sp.Rational(8892, 125)
        ),
        "cutoff_dichotomy_rational_order": sp.Rational(1, 4) < sp.Rational(2, 3),
        "unique_numerical_minimum_matches_quarter": (
            abs(float(sp.N(critical_roots[0] - sp.Rational(1, 4)))) < 1e-25
            or abs(float(sp.N(critical_roots[-1] - sp.Rational(1, 4)))) < 1e-25
            or any(
                abs(complex(root) - 0.25) < 1e-25 for root in critical_roots
            )
        ),
    }
    exact_gates = {key: bool(value) for key, value in exact_gates.items()}
    numerical_minimum_ok = (
        abs(complex(numerical_rows[0]["critical_point"]) - 0.25) < 1e-20
        and all(
            row["critical_value_real"] > -47 / 256 + 1e-12
            for row in numerical_rows[1:]
        )
    )
    passed = all(exact_gates.values()) and numerical_minimum_ok
    receipt = {
        "schema": "erdos1041_tied_newton_face_minimum_real_selector_no_go_v1",
        "passed": passed,
        "model": "Q(z)=-(379/256)z+3z^2-z^5",
        "exact_gates": exact_gates,
        "exact_values": {
            "Q(1/4)": str(quarter_value),
            "Q(2/3)": str(witness_value),
            "p(24/25)": str(p_left),
            "p(1)": str(p_right),
            "conjugate_gap_numerator_at_24/25": str(reduced_at_left),
        },
        "critical_points": numerical_rows,
        "conclusion": (
            "The critical point 1/4 uniquely minimizes Re Q over the critical "
            "multiset, but every cutoff on its positive-real bracketing ray "
            "puts the positive waypoint 2/3 on the finite arm or outward tail."
        ),
        "claim_boundary": (
            "This refutes only the greedy minimum-real-critical-value hub "
            "selector. It does not refute existence of another adjacent hub, "
            "the barycentric-envelope programme, or Erdos #1041."
        ),
    }
    print(json.dumps(receipt, indent=2, sort_keys=True) if args.json else receipt)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
