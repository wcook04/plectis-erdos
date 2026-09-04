#!/usr/bin/env python3
"""Numerical replay for the exact primitive-quintic boundary theorem.

The analytic proof and Lean kernel are authority.  This audit checks the
nontrivial rational-coefficient paraorthogonal example and the exact cubic
separator identities used by the proof.
"""

from __future__ import annotations

from fractions import Fraction
import json

import numpy as np


def separator(r: Fraction, x: Fraction) -> Fraction:
    return (-r / 2 - x) * (1 - x) ** 2


def exact_separator_algebra() -> dict[str, str]:
    # Coefficient comparison verifies that substituting the three Newton
    # moments into sum Q_r gives 5-2r identically.  The sample r is only an
    # exact replay of the identity, not evidence for a single configuration.
    r = Fraction(1, 2)
    m1 = -r
    m2 = (5 + r**2) / 2
    m3 = -(r**3 + 3 * r) / 4
    h = -r / 2
    total = 5 * h + (-2 * h - 1) * m1 + (h + 2) * m2 - m3
    maximum_single = 4 - 2 * r
    assert total == 5 - 2 * r
    assert total - maximum_single == 1
    return {
        "r": str(r),
        "separator_sum": str(total),
        "maximum_single_safe_contribution": str(maximum_single),
        "exact_gap": str(total - maximum_single),
    }


def boundary_example() -> dict[str, object]:
    # q(z)=z^4+1/2 is Schur stable and
    # p(z)=z q(z)+q#(z)=z^5+z^4/2+z/2+1 is paraorthogonal.
    coefficients = np.array([1, 0.5, 0, 0, 0.5, 1], dtype=np.complex128)
    roots = np.roots(coefficients)
    moduli = np.abs(roots)
    tails = np.abs(1 + 0.5 * roots)
    x = np.real(roots)
    r = 0.5

    assert np.max(np.abs(moduli - 1)) < 2e-12
    assert abs(np.sum(x) + r) < 2e-12
    assert abs(np.sum(x**2) - (5 + r**2) / 2) < 2e-12
    assert abs(np.sum(x**3) + (r**3 + 3 * r) / 4) < 2e-12
    assert int(np.sum(tails < 1 - 1e-10)) >= 2

    q_values = (-r / 2 - x) * (1 - x) ** 2
    assert abs(np.sum(q_values) - (5 - 2 * r)) < 3e-12

    return {
        "polynomial_coefficients_descending": [
            "1", "1/2", "0", "0", "1/2", "1"
        ],
        "maximum_root_modulus_error": float(np.max(np.abs(moduli - 1))),
        "sorted_tail_moduli": [float(value) for value in np.sort(tails)],
        "strict_safe_tail_count": int(np.sum(tails < 1 - 1e-10)),
        "separator_sum_error": float(abs(np.sum(q_values) - (5 - 2 * r))),
    }


def radial_continuation_probe() -> dict[str, object]:
    """Falsification probe for the exact next analytic bridge.

    A fully stable sparse quartic core is generated through its Schur
    parameters.  Along four radial boundary-parameter directions we count
    safe tails on a fixed grid.  Any increase would falsify the proposed
    outward-crossing monotonicity.  Absence of one is evidence only.
    """

    rng = np.random.default_rng(4041)
    track_count = 0
    outward_crossings = 0
    inward_crossing_tracks = 0

    for _ in range(80):
        while True:
            delta_radius = np.sqrt(rng.random()) * 0.98
            delta = delta_radius * np.exp(2j * np.pi * rng.random())
            eta = (rng.normal() + 1j * rng.normal()) * 1.3
            theta = -delta * np.conj(eta)
            gap = 1 - abs(theta) ** 2
            if gap <= 0:
                continue
            kappa = eta / gap
            lam = -theta * np.conj(kappa)
            if abs(lam) >= 1:
                continue
            mu = (kappa - lam * np.conj(kappa)) / (1 - abs(lam) ** 2)
            if abs(mu) >= 1:
                continue
            alpha = (1 - abs(delta) ** 2) * eta
            break

        for phase in rng.random(4) * 2 * np.pi:
            counts: list[int] = []
            for radius in np.linspace(0, 0.999, 101):
                c = radius * np.exp(1j * phase)
                a = alpha + c * np.conj(delta)
                b = delta + c * np.conj(alpha)
                roots = np.roots([1, a, 0, 0, b, c])
                counts.append(int(np.sum(np.abs(c + b * roots) < 1 - 1e-8)))

            track_count += 1
            inward = False
            for left, right in zip(counts, counts[1:]):
                if right > left:
                    inward = True
                elif right < left:
                    outward_crossings += left - right
            inward_crossing_tracks += int(inward)

    assert track_count == 320
    assert inward_crossing_tracks == 0
    assert outward_crossings > 0
    return {
        "status": "no_falsifier_found",
        "radial_tracks": track_count,
        "outward_tail_crossings": outward_crossings,
        "inward_crossing_tracks": inward_crossing_tracks,
        "claim_boundary": (
            "bounded computation only; the crossing-derivative sign remains "
            "an analytic obligation"
        ),
    }


def main() -> None:
    payload = {
        "schema": "erdos1041_primitive_quintic_boundary_tail_audit_v1",
        "status": "pass",
        "exact_separator_algebra": exact_separator_algebra(),
        "paraorthogonal_example": boundary_example(),
        "radial_continuation_probe": radial_continuation_probe(),
        "proof_authority": (
            "Newton identities, the cubic separator proof, and the Lean kernel; "
            "this script is a numerical and exact-rational replay"
        ),
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
