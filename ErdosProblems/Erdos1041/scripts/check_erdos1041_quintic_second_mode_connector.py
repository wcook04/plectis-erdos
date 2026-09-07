#!/usr/bin/env python3
"""Exact and bounded numerical replay for the all-phase quintic connector."""

from __future__ import annotations

import json
import math
import numpy as np
import sympy as sp


def main() -> None:
    t = sp.symbols("t", real=True)
    s = sp.sqrt(5)
    c = (s - 1) / 4
    y = sp.sqrt(10 + 2 * s) / 4
    omega = c + sp.I * y
    z = (1 - t) * omega + t * omega**2
    actual = sp.expand_complex(z**2 - z**5).as_real_imag()[0]
    base = (1 - t) + t * omega
    right_boundary = sp.expand_complex(omega**2 * base**2 - base**5).as_real_imag()[0]
    left_boundary = sp.expand_complex(omega * base**2 - base**5).as_real_imag()[0]
    rotation_identity = sp.simplify(actual - right_boundary)
    reflection_identity = sp.simplify(left_boundary - actual.subs(t, 1 - t))
    q = (
        t**4
        - 2 * t**3
        + (sp.Rational(11, 10) - 9 * s / 50) * t**2
        + s * t / 5
        - 3 * s / 50
        - sp.Rational(1, 10)
    )
    power_identity = sp.simplify(actual - sp.Rational(25, 4) * (s - 1) * q)

    coeffs = [
        (-5 - s) / 4,
        (-9 * s - 20) / 26,
        (-53 * s - 70) / 156,
        (-157 * s - 140) / 572,
        (-53 * s - 35) / 286,
        (-169 * s - 95) / 1716,
        3 * (-6 * s - 5) / 572,
        (-15 + 4 * s) / 572,
        (-95 + 29 * s) / 1716,
        (-35 + 2 * s) / 286,
        (-140 - 3 * s) / 572,
        (-70 + s) / 156,
        (-10 + s) / 13,
        (-5 + s) / 4,
    ]
    bernstein = sum(
        coeffs[k] * sp.binomial(13, k) * t**k * (1 - t) ** (13 - k)
        for k in range(14)
    )
    bernstein_identity = sp.simplify(actual - bernstein)
    coeff_values = [float(sp.N(x, 40)) for x in coeffs]

    # Bounded calibration only: for every sampled coefficient phase, choose the
    # best of the five rotated adjacent unit chords and maximize along it.
    phase_count = 20001
    chord_grid_count = 4001
    chord_t = np.linspace(0.0, 1.0, chord_grid_count)
    omega_float = np.exp(2j * np.pi / 5)
    base_float = (1.0 - chord_t) + chord_t * omega_float
    z2 = base_float**2
    z5 = base_float**5
    worst_best = -math.inf
    worst_phase = 0.0
    for phi in np.linspace(0.0, 2.0 * np.pi, phase_count, endpoint=False):
        best = math.inf
        for j in range(5):
            theta = phi + 4.0 * np.pi * j / 5.0
            chord_max = float(np.max(np.real(np.exp(1j * theta) * z2 - z5)))
            best = min(best, chord_max)
        if best > worst_best:
            worst_best = best
            worst_phase = float(phi)

    result = {
        "schema": "erdos1041_quintic_second_mode_connector_check_v2",
        "power_basis_identity_exact": power_identity == 0,
        "bernstein_identity_exact": bernstein_identity == 0,
        "rotation_to_fundamental_chord_exact": rotation_identity == 0,
        "boundary_reflection_exact": reflection_identity == 0,
        "max_bernstein_coefficient": max(coeff_values),
        "all_coefficients_below_minus_one_over_1000": all(
            x <= -0.001 for x in coeff_values
        ),
        "sampled_true_max_for_calibration_only": max(
            float(actual.subs(t, sp.Rational(k, 10000)).evalf(30))
            for k in range(10001)
        ),
        "all_phase_calibration": {
            "phase_count": phase_count,
            "chord_grid_count": chord_grid_count,
            "worst_best_adjacent_chord_max": worst_best,
            "worst_phase": worst_phase,
            "all_sampled_phases_strict": worst_best < 0.0,
        },
    }
    result["status"] = (
        "PASS"
        if result["power_basis_identity_exact"]
        and result["bernstein_identity_exact"]
        and result["rotation_to_fundamental_chord_exact"]
        and result["boundary_reflection_exact"]
        and result["all_coefficients_below_minus_one_over_1000"]
        and result["all_phase_calibration"]["all_sampled_phases_strict"]
        else "FAIL"
    )
    print(json.dumps(result, indent=2, sort_keys=True))
    if result["status"] != "PASS":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
