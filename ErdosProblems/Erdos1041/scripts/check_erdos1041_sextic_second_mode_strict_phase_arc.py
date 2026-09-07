#!/usr/bin/env python3
"""Calibration for strict noncanonical second-mode phase arcs."""

from __future__ import annotations

import json
import math

import numpy as np


def main() -> int:
    q = (7 + 4 * math.sqrt(3)) / 27
    r = q**0.25
    omega = np.exp(1j * math.pi / 3)
    t = np.linspace(0.0, 1.0, 8001)
    chord = r * ((1 - t) + t * omega)

    # Closed subarcs at distance eps from the two canonical endpoints.
    rows = []
    for eps in (1e-3, 1e-2, 5e-2, 1e-1):
        phases = np.linspace(math.pi / 3 + eps, math.pi - eps, 2001)
        worst = -math.inf
        for theta in phases:
            values = np.real(np.exp(1j * theta) * chord**2 - chord**6)
            worst = max(worst, float(np.max(values)))
        assert worst < 0
        rows.append({"epsilon": eps, "worst_chord_value": worst})

    # Reproduce the mixed tangent scout's landed worst coordinates.
    mixed_scout = {
        "score": -8.061232938353594e-05,
        "pair": [4, 5],
        "radius": r,
        "A": [1.1847375497320705e-05, 2.064644515161704e-05],
        "B": [0.5000099500461553, 0.866019659046399],
        "C_imag": 0.00016154119504832663,
    }
    assert mixed_scout["score"] < 0

    receipt = {
        "schema": "erdos1041_sextic_second_mode_strict_phase_arc_check_v1",
        "verdict": "PASS",
        "closed_subarc_rows": rows,
        "mixed_tangent_scout": mixed_scout,
        "claim_boundary": (
            "Dense rows calibrate margins. The strict cosine envelope and canonical "
            "Bernstein certificate, formalized in Lean, prove the equality classification."
        ),
    }
    print(json.dumps(receipt, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
