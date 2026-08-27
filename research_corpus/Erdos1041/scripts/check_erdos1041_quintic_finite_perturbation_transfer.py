#!/usr/bin/env python3
"""Actual-polynomial stress replay for the radial quintic finite transfer."""

from __future__ import annotations

import json

import numpy as np


CONFIGURATIONS = 1_000
ARM_GRID = 1_201
CHORD_GRID = 401


def values_on_segment(roots: np.ndarray, start: complex, end: complex, count: int) -> np.ndarray:
    parameter = np.linspace(0.0, 1.0, count)
    z = start + parameter * (end - start)
    return np.abs(np.prod(z[:, None] - roots[None, :], axis=1))


def main() -> None:
    rng = np.random.default_rng(1041_50)
    primitive = np.exp(2j * np.pi / 5)
    omega = primitive ** np.arange(5)
    largest_arm = 0.0
    largest_chord = 0.0
    smallest_radial_ratio = np.inf
    checked_arms = 0
    checked_chords = 0

    for _ in range(CONFIGURATIONS):
        delta = float(10 ** rng.uniform(-12, np.log10(1 / 4096)))
        phase1, phase2 = rng.uniform(-np.pi, np.pi, 2)
        amplitude1 = rng.random() * (delta / 4) ** (4 / 3) * (2 / 5)
        amplitude2 = rng.random() * delta / 10
        k = np.arange(5)
        perturbation = (
            -delta / 5
            + amplitude1 * np.cos(2 * np.pi * k / 5 + phase1)
            + amplitude2 * np.cos(4 * np.pi * k / 5 + phase2)
        )
        roots = omega * (1 + perturbation)
        modes = np.array([
            np.sum(perturbation * primitive ** (-m * k)) for m in range(5)
        ])
        measured_delta = float(-modes[0].real)
        rho = max(abs(modes[1]) ** (1 / 4), abs(modes[2]) ** (1 / 3))
        if measured_delta + 1e-15 < 4 * rho**3:
            raise AssertionError("generator left radial-dominant cone")
        smallest_radial_ratio = min(smallest_radial_ratio, measured_delta / max(rho**3, 1e-300))

        directions = roots / np.abs(roots)
        truncation = measured_delta / 10
        for index in range(5):
            arm = values_on_segment(
                roots,
                truncation * directions[index],
                roots[index],
                ARM_GRID,
            )
            largest_arm = max(largest_arm, float(np.max(arm)))
            checked_arms += 1
        for first in range(5):
            for second in range(first + 1, 5):
                chord = values_on_segment(
                    roots,
                    truncation * directions[first],
                    truncation * directions[second],
                    CHORD_GRID,
                )
                largest_chord = max(largest_chord, float(np.max(chord)))
                checked_chords += 1

    result = {
        "schema": "erdos1041_quintic_finite_perturbation_transfer_check_v1",
        "configuration_count": CONFIGURATIONS,
        "checked_arm_count": checked_arms,
        "checked_chord_count": checked_chords,
        "arm_grid": ARM_GRID,
        "chord_grid": CHORD_GRID,
        "largest_sampled_arm_value": largest_arm,
        "largest_sampled_chord_value": largest_chord,
        "smallest_delta_over_rho_cubed": smallest_radial_ratio,
    }
    passed = largest_arm < 1 and largest_chord < 1 and smallest_radial_ratio >= 4 - 1e-9
    result["status"] = "PASS" if passed else "FAIL"
    print(json.dumps(result, indent=2, sort_keys=True))
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
