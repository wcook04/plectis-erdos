#!/usr/bin/env python3
"""Falsification checks for the Erdős 1041 barycentric disc envelope."""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

import numpy as np


@dataclass
class Stats:
    descent_ratio_max: float = 0.0
    envelope_error_max: float = 0.0
    ellipse_ratio_max: float = 0.0
    hub_value_max: float = 0.0
    spoke_witness_error: float = 0.0
    checks: int = 0


def value(roots: np.ndarray, z: complex) -> complex:
    return complex(np.prod(z - roots))


def sample_disc(rng: np.random.Generator, center: complex, radius: float) -> complex:
    radial = radius * math.sqrt(float(rng.random()))
    angle = 2.0 * math.pi * float(rng.random())
    return center + radial * np.exp(1j * angle)


def roots_trial(rng: np.random.Generator, n: int) -> np.ndarray:
    radii = 0.999 * np.sqrt(rng.random(n))
    angles = 2.0 * math.pi * rng.random(n)
    return (radii * np.exp(1j * angles)).astype(np.complex128)


def check_roots(
    rng: np.random.Generator, roots: np.ndarray, samples: int, stats: Stats
) -> None:
    n = len(roots)
    for _ in range(samples):
        z = complex(2.4 * rng.random() - 1.2, 2.4 * rng.random() - 1.2)
        delta = z - roots
        distances2 = np.abs(delta) ** 2
        if np.min(distances2) < 1.0e-14:
            continue
        fz = abs(value(roots, z))
        inverse = 1.0 / distances2
        total = float(np.sum(inverse))
        center = complex(np.sum(inverse * roots) / total)
        radius = abs(z - center)
        for _ in range(8):
            y = sample_disc(rng, center, radius)
            stats.descent_ratio_max = max(
                stats.descent_ratio_max, abs(value(roots, y)) / max(fz, 1.0e-300)
            )
        u2 = float(np.prod(distances2) ** (1.0 / n))
        weights = u2 / distances2
        stats.envelope_error_max = max(
            stats.envelope_error_max,
            abs(float(np.prod(weights)) - 1.0),
            abs(float(np.mean(weights * distances2)) - u2),
        )
        stats.checks += 1

    critical = np.roots(np.polyder(np.poly(roots)))
    for c in critical:
        distances = np.sort(np.abs(c - roots))
        fc = abs(value(roots, complex(c)))
        if fc < 1.0e-280 or distances[0] < 1.0e-8:
            continue
        rho = fc ** (1.0 / n)
        stats.ellipse_ratio_max = max(
            stats.ellipse_ratio_max, float((distances[0] + distances[1]) / (2 * rho))
        )
        if fc < 1.0 - 1.0e-10:
            raw = np.abs(c - roots)
            total = float(np.sum(1.0 / raw**2))
            hub_radius = math.sqrt(max(0.0, n * (1.0 - rho**2) / (total * rho**2)))
            for _ in range(12):
                y = sample_disc(rng, complex(c), hub_radius)
                stats.hub_value_max = max(stats.hub_value_max, abs(value(roots, y)))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=1041)
    parser.add_argument("--trials", type=int, default=500)
    parser.add_argument("--max-degree", type=int, default=16)
    parser.add_argument("--samples", type=int, default=30)
    args = parser.parse_args()
    rng = np.random.default_rng(args.seed)
    stats = Stats()
    for _ in range(args.trials):
        n = int(rng.integers(2, args.max_degree + 1))
        check_roots(rng, roots_trial(rng, n), args.samples, stats)

    # Exact six-root spoke obstruction, evaluated at r=1 before scaling.
    witness = abs((0.5**2 - 1.0) * (0.5**4 + 1.2 * 0.5**2 + 1.0))
    stats.spoke_witness_error = abs(witness - 327.0 / 320.0)
    passed = (
        stats.descent_ratio_max <= 1.0 + 3.0e-8
        and stats.envelope_error_max <= 3.0e-8
        and stats.ellipse_ratio_max <= 1.0 + 8.0e-7
        and stats.hub_value_max <= 1.0 + 3.0e-7
        and stats.spoke_witness_error <= 1.0e-15
    )
    print("PASS" if passed else "FAIL")
    print(f"scalar checks: {stats.checks}")
    print(f"max descent ratio: {stats.descent_ratio_max:.12g}")
    print(f"max envelope error: {stats.envelope_error_max:.12g}")
    print(f"max ellipse ratio: {stats.ellipse_ratio_max:.12g}")
    print(f"max hub-disc |f|: {stats.hub_value_max:.12g}")
    print(f"exact spoke-witness error: {stats.spoke_witness_error:.12g}")
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
