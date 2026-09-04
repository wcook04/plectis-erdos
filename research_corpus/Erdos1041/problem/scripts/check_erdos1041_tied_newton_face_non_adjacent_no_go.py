#!/usr/bin/env python3
"""Exact replay of the small tied-face nonadjacency witness and free-pair chart."""
from __future__ import annotations

import argparse
import json
import math

import sympy as sp


def bernstein_controls(poly: sp.Expr, variable: sp.Symbol, degree: int) -> list[sp.Expr]:
    expanded = sp.Poly(sp.expand(poly), variable)
    power = [expanded.coeff_monomial(variable**k) for k in range(degree + 1)]
    return [
        sp.factor(sum(power[k] * sp.Rational(math.comb(j, k), math.comb(degree, k))
                      for k in range(j + 1)))
        for j in range(degree + 1)
    ]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    z = sp.symbols("z")
    t, s = sp.symbols("t s", real=True)
    da, ea, db, eb = sp.symbols("da ea db eb", real=True)
    I = sp.I
    Q = lambda w: -sp.Rational(65, 27) * w + sp.Rational(100, 27) * w**2 - w**5
    derivative = sp.diff(Q(z), z)
    factorization = -5 * (z-1) * (z-sp.Rational(1, 3)) * (z+sp.Rational(2, 3)-I) * (z+sp.Rational(2, 3)+I)

    criticals = [sp.Integer(1), sp.Rational(1, 3), -sp.Rational(2, 3)+I, -sp.Rational(2, 3)-I]
    heights = [sp.factor(sp.re(sp.expand_complex(Q(c)))) for c in criticals]

    h = sp.Rational(1, 3)
    radius = sp.Rational(1, 2)
    u = sp.Rational(5, 13) + sp.Rational(12, 13) * I
    v = sp.conjugate(u)

    def real_q(w: sp.Expr) -> sp.Expr:
        return sp.factor(sp.re(sp.expand_complex(Q(w))))

    arm_u = real_q((1-t)*h + t*radius*u)
    arm_v = real_q((1-t)*h + t*radius*v)
    tail_u = sp.factor(s**5 * real_q(radius*u/s))
    tail_v = sp.factor(s**5 * real_q(radius*v/s))
    controls = {
        "arm_u": bernstein_controls(arm_u, t, 5),
        "arm_v": bernstein_controls(arm_v, t, 5),
        "tail_u": bernstein_controls(tail_u, s, 5),
        "tail_v": bernstein_controls(tail_v, s, 5),
    }

    # A quantitative open chart, not merely qualitative stability.  Perturb the
    # two active coefficients independently in all four real coordinates:
    #
    #   A = -65/27 + da + i ea,   B = 100/27 + db + i eb.
    #
    # Every Bernstein control is affine in these four parameters.  Bounding
    # each perturbation coordinate by 2/3 and charging the exact l1 sensitivity
    # leaves every one of the 24 controls strictly negative.
    box_radius = sp.Rational(2, 3)
    A = -sp.Rational(65, 27) + da + I*ea
    B = sp.Rational(100, 27) + db + I*eb

    def perturbed_real_q(w: sp.Expr) -> sp.Expr:
        return sp.factor(sp.re(sp.expand_complex(A*w + B*w**2 - w**5)))

    perturbed_controls: dict[str, list[sp.Expr]] = {}
    for name, direction in (("u", u), ("v", v)):
        arm = perturbed_real_q((1-t)*h + t*radius*direction)
        tail = sp.factor(s**5 * perturbed_real_q(radius*direction/s))
        perturbed_controls[f"arm_{name}"] = bernstein_controls(arm, t, 5)
        perturbed_controls[f"tail_{name}"] = bernstein_controls(tail, s, 5)

    perturbation_variables = (da, ea, db, eb)
    box_upper_controls = {
        name: [
            sp.factor(
                control.subs({da: 0, ea: 0, db: 0, eb: 0})
                + box_radius * sum(
                    abs(sp.diff(control, variable))
                    for variable in perturbation_variables
                )
            )
            for control in row
        ]
        for name, row in perturbed_controls.items()
    }

    dist_sq = sp.factor(sp.re((radius*u-h) * sp.conjugate(radius*u-h)))
    margin = sp.factor(radius**2-dist_sq)
    expected_arm = [
        -sp.Rational(32, 81), -sp.Rational(32, 81), -sp.Rational(25157, 54756),
        -sp.Rational(2553583, 4270968), -sp.Rational(3400915, 4112784),
        -sp.Rational(366892775, 320797152),
    ]
    expected_tail = [
        -sp.Rational(341525, 11881376), -sp.Rational(341525, 11881376),
        -sp.Rational(341525, 11881376), -sp.Rational(30136615, 320797152),
        -sp.Rational(40862125, 106932384), -sp.Rational(366892775, 320797152),
    ]

    gates = {
        "derivative_factorization": sp.expand(derivative-factorization) == 0,
        "critical_height_pattern": heights == [sp.Rational(8, 27), -sp.Rational(32, 81), sp.Rational(4, 81), sp.Rational(4, 81)],
        "zero_regular": derivative.subs(z, 0) != 0,
        "directions_unit": sp.simplify(u*sp.conjugate(u)) == 1 and sp.simplify(v*sp.conjugate(v)) == 1,
        "directions_negative_at_infinity": sp.re(u**5) > 0 and sp.re(v**5) > 0,
        "arms_match_certificate": controls["arm_u"] == expected_arm and controls["arm_v"] == expected_arm,
        "tails_match_certificate": controls["tail_u"] == expected_tail and controls["tail_v"] == expected_tail,
        "all_controls_strictly_negative": all(c < 0 for row in controls.values() for c in row),
        "perturbed_controls_affine": all(
            sp.Poly(control, *perturbation_variables).total_degree() <= 1
            for row in perturbed_controls.values()
            for control in row
        ),
        "open_box_all_controls_strictly_negative": all(
            upper < 0 for row in box_upper_controls.values() for upper in row
        ),
        "strict_metric_margin": dist_sq == sp.Rational(1417, 6084) and margin == sp.Rational(2, 117),
    }
    gates = {key: bool(value) for key, value in gates.items()}
    passed = all(gates.values())
    output = {
        "schema": "erdos1041_tied_newton_face_non_adjacent_no_go_v1",
        "passed": passed,
        "gates": gates,
        "model": "Q(z)=-(65/27)z+(100/27)z^2-z^5",
        "critical_heights": [str(value) for value in heights],
        "directions": [str(u), str(v)],
        "re_direction_fifth": str(sp.factor(sp.re(u**5))),
        "controls": {key: [str(c) for c in row] for key, row in controls.items()},
        "open_coefficient_chart": {
            "parameterization": (
                "A=-65/27+da+i*ea, B=100/27+db+i*eb, "
                "max(|da|,|ea|,|db|,|eb|)<=2/3"
            ),
            "coordinate_radius": str(box_radius),
            "strict_upper_controls": {
                key: [str(c) for c in row] for key, row in box_upper_controls.items()
            },
            "largest_upper_control": str(
                max(c for row in box_upper_controls.values() for c in row)
            ),
        },
        "distance_squared": str(dist_sq),
        "squared_metric_margin": str(margin),
        "claim_boundary": (
            "Exact no-go for universal adjacent pairing and a four-real-dimensional strict "
            "nonadjacent free-pair chart of coordinate radius 2/3 around the rational tied "
            "quintic; not the all-degree selector or Erdős #1041."
        ),
    }
    print(json.dumps(output, indent=2, sort_keys=True) if args.json else output)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
