#!/usr/bin/env python3
"""Deterministic replay for the explicit near-Fekete logarithmic remainder."""

from __future__ import annotations

import json
import math
import random

import numpy as np


SEED = 1041_20260825


def direct_product(z: complex, roots: np.ndarray) -> complex:
    return complex(np.prod(z - roots))


def run() -> dict[str, object]:
    rng = random.Random(SEED)
    checked = 0
    max_factorization_relative_error = 0.0
    max_bound_ratio = 0.0
    max_anchored_bound_ratio = 0.0
    max_finite_resummation_error = 0.0
    failed_rows: list[dict[str, object]] = []

    for n in range(4, 13):
        omega = np.exp(2j * np.pi / n)
        base = omega ** np.arange(n)
        for trial in range(36):
            r = rng.uniform(0.08, 0.82)
            eta_cap = 0.45 * (1.0 - r)
            raw = np.array(
                [complex(rng.uniform(-1, 1), rng.uniform(-1, 1)) for _ in range(n)]
            )
            raw_norm = max(abs(x) for x in raw)
            eta = eta_cap * rng.uniform(0.05, 1.0)
            e = raw * (eta / raw_norm)
            roots = base * (1.0 + e)
            M = rng.randrange(0, n)

            radius = r * math.sqrt(rng.random())
            angle = 2.0 * math.pi * rng.random()
            z = radius * complex(math.cos(angle), math.sin(angle))

            fz = direct_product(z, roots)
            w = e / (1.0 - z * np.conjugate(base))
            factorized = (z**n - 1.0) * np.prod(1.0 + w)
            scale = max(1.0, abs(fz), abs(factorized))
            factor_error = abs(fz - factorized) / scale
            max_factorization_relative_error = max(
                max_factorization_relative_error, factor_error
            )

            modes = np.array(
                [np.sum(e * omega ** (-m * np.arange(n))) for m in range(M + 1)]
            )
            model = sum((modes[m] * z**m).real for m in range(M + 1)) - (z**n).real
            actual = math.log(abs(fz))

            alpha = eta / (1.0 - r)
            tail = n * eta * r ** (M + 1) / (1.0 - r)
            factor_log = n * alpha * alpha / (2.0 * (1.0 - alpha))
            baseline_log = r ** (2 * n) / (2.0 * (1.0 - r**n))
            bound = tail + factor_log + baseline_log
            residual = abs(actual - model)
            ratio = residual / bound if bound else 0.0
            max_bound_ratio = max(max_bound_ratio, ratio)

            all_modes = np.array(
                [np.sum(e * omega ** (-m * np.arange(n))) for m in range(n)]
            )
            finite_numerator = all_modes[0] * z**n + sum(
                all_modes[m] * z**m for m in range(1, n)
            )
            finite_potential = finite_numerator / (1.0 - z**n)
            infinite_potential = np.sum(w - e)
            resummation_error = abs(finite_potential - infinite_potential)
            max_finite_resummation_error = max(
                max_finite_resummation_error, resummation_error
            )

            f0 = direct_product(0.0j, roots)
            anchored_model = (
                math.log(abs(f0))
                + math.log(abs(1.0 - z**n))
                + finite_potential.real
            )
            anchored_bound = (
                n
                * eta
                * eta
                * r
                / ((1.0 - r) ** 2 * (1.0 - alpha))
            )
            anchored_residual = abs(actual - anchored_model)
            anchored_ratio = anchored_residual / anchored_bound if anchored_bound else 0.0
            max_anchored_bound_ratio = max(max_anchored_bound_ratio, anchored_ratio)

            ok = (
                factor_error < 2e-12
                and resummation_error < 2e-12
                and residual <= bound * (1.0 + 2e-12) + 2e-14
                and anchored_residual
                <= anchored_bound * (1.0 + 3e-12) + 3e-14
            )
            if not ok:
                failed_rows.append(
                    {
                        "n": n,
                        "trial": trial,
                        "M": M,
                        "factor_error": factor_error,
                        "residual": residual,
                        "bound": bound,
                        "resummation_error": resummation_error,
                        "anchored_residual": anchored_residual,
                        "anchored_bound": anchored_bound,
                    }
                )
            checked += 1

    # Required transition negative control: the lexicographically first mode
    # can be negligible compared with a later mode on every useful outer scale.
    n = 7
    epsilon = 1e-12
    E1 = epsilon**4
    E2 = epsilon
    rho1 = abs(E1) ** (1.0 / (n - 1))
    rho2 = abs(E2) ** (1.0 / (n - 2))
    transition_ratio = rho2 / rho1
    transition_control = E1 != 0.0 and transition_ratio > 1e5

    # Root-disk geometry: the radial deficit absorbs quadratic energy and pairs
    # high and low Fourier modes up to twice that deficit.
    disk_rng = random.Random(SEED + 1)
    max_radial_energy_ratio = 0.0
    max_pairing_identity_error = 0.0
    max_pairing_over_bound = 0.0
    for n_disk in range(4, 18):
        omega_disk = np.exp(2j * np.pi / n_disk)
        k = np.arange(n_disk)
        for _ in range(24):
            inward = np.array([disk_rng.uniform(1e-8, 3e-3) for _ in k])
            angles = np.array([disk_rng.uniform(-3e-3, 3e-3) for _ in k])
            e_disk = (1.0 - inward) * np.exp(1j * angles) - 1.0
            delta = -float(np.sum(e_disk).real)
            energy = float(np.sum(np.abs(e_disk) ** 2))
            if delta > 0:
                max_radial_energy_ratio = max(
                    max_radial_energy_ratio, energy / (2.0 * delta)
                )
            x = e_disk.real
            y = e_disk.imag
            for m in range(1, n_disk):
                E_m = np.sum(e_disk * omega_disk ** (-m * k))
                E_pair = np.sum(e_disk * omega_disk ** (-(n_disk - m) * k))
                R_m = np.sum(x * omega_disk ** (-m * k))
                identity = E_pair + np.conjugate(E_m) - 2.0 * np.conjugate(R_m)
                lhs = abs(E_pair + np.conjugate(E_m))
                max_pairing_identity_error = max(
                    max_pairing_identity_error, abs(identity)
                )
                if delta > 0:
                    max_pairing_over_bound = max(
                        max_pairing_over_bound, lhs / (2.0 * delta)
                    )

    disk_geometry_control = bool(
        max_radial_energy_ratio <= 1.0 + 2e-12
        and max_pairing_identity_error < 2e-12
        and max_pairing_over_bound <= 1.0 + 2e-12
    )

    result = {
        "schema": "erdos1041_form_a_cut_quantitative_expansion_check_v1",
        "status": (
            "PASS"
            if not failed_rows and transition_control and disk_geometry_control
            else "FAIL"
        ),
        "seed": SEED,
        "checked_configurations": checked,
        "max_factorization_relative_error": max_factorization_relative_error,
        "max_residual_over_explicit_bound": max_bound_ratio,
        "max_anchored_residual_over_explicit_bound": max_anchored_bound_ratio,
        "max_finite_resummation_error": max_finite_resummation_error,
        "transition_negative_control": {
            "n": n,
            "E1": E1,
            "E2": E2,
            "rho1": rho1,
            "rho2": rho2,
            "rho2_over_rho1": transition_ratio,
            "first_nonzero_mode_is_not_dominant": transition_control,
        },
        "root_disk_geometry": {
            "max_quadratic_energy_over_twice_radial_deficit": max_radial_energy_ratio,
            "max_pairing_identity_error": max_pairing_identity_error,
            "max_pairing_left_side_over_twice_radial_deficit": max_pairing_over_bound,
            "control_passed": disk_geometry_control,
        },
        "failed_rows": failed_rows,
        "claim_boundary": (
            "Checks the exact product coordinates and the explicit finite remainder; "
            "it does not prove a multiscale spoke selector or Erdős #1041."
        ),
    }
    return result


if __name__ == "__main__":
    receipt = run()
    print(json.dumps(receipt, indent=2, sort_keys=True))
    raise SystemExit(0 if receipt["status"] == "PASS" else 1)
