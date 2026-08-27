#!/usr/bin/env python3
"""Exact replay of the sharp quintic mixed-mode transition chart."""

from __future__ import annotations

import json

import sympy as sp


def main() -> None:
    rho, u, t = sp.symbols("rho u t", positive=True, real=True)
    s = sp.sqrt(5)
    p = sp.sqrt(10 + 2 * s)
    q = sp.sqrt(10 - 2 * s)
    omega = (s - 1) / 4 + sp.I * p / 4
    coeff_b = -q / 4 - sp.I * (1 + s) / 4

    def leading(alpha: sp.Expr) -> sp.Expr:
        return sp.trigsimp(
            rho * u * sp.cos(2 * sp.pi / 5 + alpha)
            + rho**2 * sp.cos(13 * sp.pi / 10 + 2 * alpha)
            - rho**5 * sp.cos(5 * alpha)
        )

    def correction(alpha: sp.Expr) -> sp.Expr:
        return sp.trigsimp(rho**3 * sp.cos(17 * sp.pi / 10 + 3 * alpha))

    alpha_pos = sp.pi / 10
    alpha_neg = -9 * sp.pi / 10
    leading_pos = sp.simplify(leading(alpha_pos))
    leading_neg = sp.simplify(leading(alpha_neg))
    correction_pos = sp.simplify(correction(alpha_pos) - rho**3)
    correction_neg = sp.simplify(correction(alpha_neg) + rho**3)

    # Exact stationary reduction for the adjacent fallback chord [1, omega^-1].
    chord = (1 - t) + t * omega**4
    linear = sp.simplify(sp.expand_complex(omega * chord).as_real_imag()[0])
    quadratic = sp.simplify(
        sp.expand_complex(coeff_b * chord**2).as_real_imag()[0]
    )
    quintic = sp.simplify(sp.expand_complex(chord**5).as_real_imag()[0])
    stationary = sp.simplify(
        4 * linear * quintic * sp.diff(quadratic, t)
        - 3 * quadratic * quintic * sp.diff(linear, t)
        - quadratic * linear * sp.diff(quintic, t)
    )
    t_star = s * (3 + s - q) / 10
    stationary_at_t_star = sp.simplify(stationary.subs(t, t_star))

    l_star = sp.simplify(linear.subs(t, t_star))
    b_star = sp.simplify(quadratic.subs(t, t_star))
    c_star = sp.simplify(quintic.subs(t, t_star))
    derived_u_cube = -27 * b_star**4 / (256 * c_star * l_star**3)
    amplitude_residual = abs(
        sp.N(derived_u_cube - sp.Rational(27, 320), 100)
    )
    u_star = sp.real_root(sp.Rational(27, 320), 3)
    amplitude_definition = sp.simplify(u_star**3 - sp.Rational(27, 320))

    # The two simultaneous-zero directions really lie on the stated chords.
    tau_pos = (5 - s) / 10
    point_pos = sp.simplify((1 - tau_pos) + tau_pos * omega**2)
    direction_pos_residual = sp.simplify(
        sp.im(point_pos * sp.exp(-sp.I * alpha_pos))
    )
    tau_neg = (5 + s) / 10
    point_neg = sp.simplify((1 - tau_neg) * omega**2 + tau_neg * omega**3)
    direction_neg_residual = sp.simplify(
        sp.im(point_neg * sp.exp(-sp.I * alpha_neg))
    )

    result = {
        "schema": "erdos1041_quintic_mixed_transition_resolution_check_v1",
        "leading_positive_direction_exact_zero": leading_pos == 0,
        "leading_negative_direction_exact_zero": leading_neg == 0,
        "paired_correction_positive_exact": correction_pos == 0,
        "paired_correction_negative_exact": correction_neg == 0,
        "stationary_eliminant_exact_at_t_star": stationary_at_t_star == 0,
        "transition_amplitude_definition_exact": amplitude_definition == 0,
        "derived_amplitude_cube_residual_100_digit": str(amplitude_residual),
        "derived_amplitude_cube_matches_27_over_320": bool(
            amplitude_residual < sp.Float("1e-80")
        ),
        "positive_zero_chord_direction_exact": direction_pos_residual == 0,
        "negative_zero_chord_direction_exact": direction_neg_residual == 0,
        "transition_amplitude_decimal": str(sp.N(u_star, 30)),
        "t_star_decimal": str(sp.N(t_star, 30)),
        "paired_signs": {"alpha_pi_over_10": "+rho^3", "alpha_minus_9pi_over_10": "-rho^3"},
    }
    required = [
        result["leading_positive_direction_exact_zero"],
        result["leading_negative_direction_exact_zero"],
        result["paired_correction_positive_exact"],
        result["paired_correction_negative_exact"],
        result["stationary_eliminant_exact_at_t_star"],
        result["transition_amplitude_definition_exact"],
        result["derived_amplitude_cube_matches_27_over_320"],
        result["positive_zero_chord_direction_exact"],
        result["negative_zero_chord_direction_exact"],
    ]
    result["status"] = "PASS" if all(required) else "FAIL"
    print(json.dumps(result, indent=2, sort_keys=True))
    if result["status"] != "PASS":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
