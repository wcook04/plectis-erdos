#!/usr/bin/env python3
"""Symbolic and numerical replay for the pure sextic second-mode circle."""

from __future__ import annotations

import json
import math

import numpy as np
import sympy as sp


def main() -> int:
    t = sp.symbols("t", real=True)
    s = sp.sqrt(3)
    omega = sp.Rational(1, 2) + sp.I * s / 2
    q = (7 + 4 * s) / 27
    w = (1 - t) + t * omega
    re2 = sp.expand_complex(w**2).as_real_imag()[0]
    re6 = sp.expand_complex(w**6).as_real_imag()[0]
    carrier = sp.expand(re2 + q * re6)

    phase_pi = sp.expand(-re2 - q * re6)
    assert sp.simplify(phase_pi + carrier) == 0

    phase_third = sp.expand(
        sp.re((sp.Rational(1, 2) + sp.I * s / 2) * w**2) - q * re6
    )
    assert sp.simplify(phase_third + carrier.subs(t, 1 - t)) == 0

    # Fixed exact radius calibration over the complete phase circle.
    r = float(q ** sp.Rational(1, 4))
    roots = np.exp(1j * np.pi * np.arange(6) / 3)
    chord_t = np.linspace(0.0, 1.0, 4001)
    ray_x = np.linspace(r, 1.0, 4001)
    rows = []
    pairs = []
    for j in range(6):
        k = (j + 1) % 6
        chord = r * ((1 - chord_t) * roots[j] + chord_t * roots[k])
        points = np.concatenate((chord, ray_x * roots[j], ray_x * roots[k]))
        rows.append(points)
        pairs.append((j, k))
    points = np.asarray(rows)
    z2 = points**2
    fixed = -np.real(points**6)
    worst = (-math.inf, None, None)
    for phi in np.linspace(0.0, 2 * math.pi, 1441):
        values = math.cos(phi) * np.real(z2) - math.sin(phi) * np.imag(z2) + fixed
        scores = np.max(values, axis=1)
        index = int(np.argmin(scores))
        if float(scores[index]) > worst[0]:
            worst = (float(scores[index]), phi, pairs[index])
    assert worst[0] < 1e-7

    receipt = {
        "schema": "erdos1041_sextic_second_mode_phase_circle_check_v1",
        "verdict": "PASS",
        "symbolic_boundary_identities": 2,
        "phase_rows": 1441,
        "chord_points_per_connector": 4001,
        "ray_points_per_arm": 4001,
        "exact_radius_float": r,
        "worst_sampled_best_score": worst[0],
        "worst_phase_over_pi": worst[1] / math.pi,
        "worst_pair": worst[2],
        "claim_boundary": (
            "The float sweep calibrates only. Symbolic boundary identities, the "
            "canonical Bernstein certificate, and Lean phase envelope carry the proof."
        ),
    }
    print(json.dumps(receipt, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

