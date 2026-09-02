#!/usr/bin/env python3
"""Deterministic numerical falsifier for finite-capacity continuation.

This is deliberately a probe, not a certificate.  It searches the compact
normalized radial region for a nonregular equality/contact configuration.
"""

from __future__ import annotations

import argparse
import math

import numpy as np
from scipy.optimize import minimize_scalar


def regular_barrier(n: int, p: float) -> float:
    s = p ** (1 / 3)

    def negative_log(q):
        return -(-n * math.log(q) + math.log(q**3 - p) - math.log(1 - p * q**3))

    result = minimize_scalar(negative_log, bounds=(s * (1 + 1e-12), 1.0), method="bounded")
    return math.exp(-result.fun)


def ray_barrier(n: int, roots: np.ndarray, index: int) -> float:
    radius = abs(roots[index])
    direction = roots[index] / radius

    def negative_log(q):
        point = q * direction
        numerator = np.abs(point - roots)
        denominator = np.abs(1 - q * np.conjugate(roots) * direction)
        return -(-n * math.log(q) + float(np.log(numerator).sum() - np.log(denominator).sum()))

    left = radius * (1 + 1e-12)
    grid = np.linspace(left, 1.0, 161)
    values = np.array([negative_log(q) for q in grid])
    best = float(values.min())
    for grid_index in range(1, len(grid) - 1):
        if values[grid_index] <= values[grid_index - 1] and values[grid_index] <= values[grid_index + 1]:
            result = minimize_scalar(
                negative_log,
                bounds=(grid[grid_index - 1], grid[grid_index + 1]),
                method="bounded",
            )
            best = min(best, float(result.fun))
    return max(1.0, math.exp(-best))


def speed_ceiling(roots: np.ndarray) -> float:
    angles = np.linspace(0.0, 2 * math.pi, 721, endpoint=False)
    boundary = np.exp(1j * angles)
    values = np.zeros_like(angles)
    for root in roots:
        values += (1 - abs(root) ** 2) / np.abs(boundary - root) ** 2
    seed = int(values.argmax())
    step = 2 * math.pi / 721
    centre = angles[seed]

    def negative(phi):
        z = np.exp(1j * phi)
        return -float(sum((1 - abs(root) ** 2) / abs(z - root) ** 2 for root in roots))

    result = minimize_scalar(negative, bounds=(centre - step, centre + step), method="bounded")
    return -result.fun


def regular_distance(log_radii: np.ndarray, directions: np.ndarray) -> float:
    cosines = np.array(
        [
            (directions[0] * np.conjugate(directions[1])).real,
            (directions[0] * np.conjugate(directions[2])).real,
            (directions[1] * np.conjugate(directions[2])).real,
        ]
    )
    return float(math.sqrt(np.dot(log_radii, log_radii) + np.dot(cosines + 0.5, cosines + 0.5)))


def capacities(n: int):
    endpoint = ((n - 3) / (n + 3)) ** (1 / 3)
    return np.linspace(0.08, 0.97 * endpoint, 9)


def run_degree(n: int, samples: int, seed: int):
    rng = np.random.default_rng(seed + n)
    T = 1.150373553831 if n == 5 else 1.099043672132
    logT = math.log(T)
    rows = []
    for scale in capacities(n):
        p = scale**3
        regular = regular_barrier(n, p)
        best = (-math.inf, None)
        best_away = (-math.inf, None)
        admissible = 0
        for _ in range(samples):
            x, y = rng.uniform(-2 * logT, logT, size=2)
            logs = np.array([x, y, -x - y])
            if logs.min() <= -2 * logT or logs.max() >= logT:
                continue
            radii = scale * np.exp(logs)
            if radii.max() >= 1:
                continue
            angles = np.array([0.0, rng.uniform(0, 2 * math.pi), rng.uniform(0, 2 * math.pi)])
            directions = np.exp(1j * angles)
            roots = radii * directions
            if speed_ceiling(roots) >= n:
                continue
            admissible += 1
            barriers = np.array([ray_barrier(n, roots, index) for index in range(3)])
            ratio = float(barriers.min() / regular)
            distance = regular_distance(logs, directions)
            record = (ratio, distance, logs.copy(), angles.copy(), barriers.copy())
            if ratio > best[0]:
                best = (ratio, record)
            if distance >= 0.10 and ratio > best_away[0]:
                best_away = (ratio, record)
        row = {
            "scale": scale,
            "admissible": admissible,
            "best": best[0],
            "best_distance": None if best[1] is None else best[1][1],
            "best_away": best_away[0],
            "best_away_record": best_away[1],
        }
        rows.append(row)
        print(
            f"n={n} scale={scale:.6f} admissible={admissible} "
            f"best={best[0]:.9f} distance={row['best_distance']} "
            f"best_dist>=.10={best_away[0]:.9f}"
        )
    finite_rows = [row for row in rows if math.isfinite(row["best_away"])]
    tight = max(finite_rows, key=lambda row: row["best_away"])
    print(f"n={n} tight-away scale={tight['scale']:.9f} ratio={tight['best_away']:.12f}")
    print(f"n={n} tight-away record={tight['best_away_record']}")
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=600)
    parser.add_argument("--seed", type=int, default=1041)
    args = parser.parse_args()
    for degree in (5, 6):
        run_degree(degree, args.samples, args.seed)


if __name__ == "__main__":
    main()
