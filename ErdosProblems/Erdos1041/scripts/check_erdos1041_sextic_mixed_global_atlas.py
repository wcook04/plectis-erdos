#!/usr/bin/env python3
"""Adversarial scout for the normalized sextic mixed-model connector atlas.

This first stage is deliberately not proof authority.  It maximizes the best
sampled complete-connector score over each coefficient-boundary face of

    H(z) = Re(A z + B z^2 + C z^3 - z^6),
    max(|A|, |B|, |C|) = 1.

The output either falsifies the proposed finite-atlas route with a robust
positive witness or identifies the exceptional strata that an exact atlas
must remove before interval subdivision.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import math

import numpy as np
from scipy.optimize import differential_evolution


@dataclass(frozen=True)
class Candidate:
    first: int
    second: int
    radius: float


class SexticScout:
    def __init__(
        self, radius_count: int, sample_count: int, minimum_radius: float, maximum_radius: float
    ) -> None:
        omega = np.exp(2j * np.pi * np.arange(6) / 6)
        radii = np.unique(
            np.concatenate(
                (
                    np.geomspace(minimum_radius, 0.25, radius_count // 2),
                    np.linspace(0.25, maximum_radius, radius_count * 2),
                    np.array([(7 + 4 * math.sqrt(3)) / 27]) ** 0.25,
                )
            )
        )
        chord_t = np.linspace(0, 1, sample_count)
        ray_y = np.linspace(1, 2, sample_count // 2 + 1)
        candidates: list[Candidate] = []
        point_rows: list[np.ndarray] = []
        for first in range(6):
            for gap in (1, 2):
                second = (first + gap) % 6
                for radius in radii:
                    chord = radius * (
                        (1 - chord_t) * omega[first] + chord_t * omega[second]
                    )
                    first_ray = radius * ray_y * omega[first]
                    second_ray = radius * ray_y * omega[second]
                    point_rows.append(np.concatenate((chord, first_ray, second_ray)))
                    candidates.append(Candidate(first, second, float(radius)))
        self.candidates = candidates
        points = np.asarray(point_rows)
        self.z1 = points
        self.z2 = points**2
        self.z3 = points**3
        self.fixed = -(points**6)

    @staticmethod
    def coefficients(face: int, parameters: np.ndarray) -> tuple[complex, complex, complex]:
        unit = np.exp(1j * parameters[0])
        other_one = parameters[1] * np.exp(1j * parameters[2])
        other_two = parameters[3] * np.exp(1j * parameters[4])
        values = [other_one, other_two]
        values.insert(face, unit)
        return values[0], values[1], values[2]

    def score(self, face: int, parameters: np.ndarray) -> tuple[float, int]:
        a, b, c = self.coefficients(face, parameters)
        values = np.real(a * self.z1 + b * self.z2 + c * self.z3 + self.fixed)
        connector_scores = np.max(values, axis=1)
        index = int(np.argmin(connector_scores))
        return float(connector_scores[index]), index


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--radius-count", type=int, default=52)
    parser.add_argument("--sample-count", type=int, default=81)
    parser.add_argument("--maxiter", type=int, default=90)
    parser.add_argument("--popsize", type=int, default=12)
    parser.add_argument("--minimum-radius", type=float, default=1e-4)
    parser.add_argument("--maximum-radius", type=float, default=3.0)
    parser.add_argument("--faces", default="0,1,2")
    args = parser.parse_args()

    scout = SexticScout(
        args.radius_count, args.sample_count, args.minimum_radius, args.maximum_radius
    )
    bounds = [
        (-math.pi, math.pi),
        (0, 1),
        (-math.pi, math.pi),
        (0, 1),
        (-math.pi, math.pi),
    ]
    rows = []
    for face in [int(value) for value in args.faces.split(",")]:
        result = differential_evolution(
            lambda parameters: -scout.score(face, parameters)[0],
            bounds,
            seed=20260825 + face,
            maxiter=args.maxiter,
            popsize=args.popsize,
            polish=True,
            workers=1,
            updating="immediate",
            tol=1e-9,
        )
        score, candidate_index = scout.score(face, result.x)
        candidate = scout.candidates[candidate_index]
        coefficients = scout.coefficients(face, result.x)
        rows.append((face, score, candidate, coefficients, result.nfev))
        print(
            "face/worst-score/pair/radius/nfev:",
            face,
            f"{score:.12e}",
            (candidate.first, candidate.second),
            f"{candidate.radius:.12f}",
            result.nfev,
        )
        print("coefficients:", *(f"{value.real:+.12f}{value.imag:+.12f}i" for value in coefficients))

    worst = max(row[1] for row in rows)
    if worst > 2e-4:
        print("FALSIFIER: robust positive sampled minimax score", worst)
        raise SystemExit(2)
    print("SCOUT PASS: no robust positive minimax score; exact atlas still required")


if __name__ == "__main__":
    main()
