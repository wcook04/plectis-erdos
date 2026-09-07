#!/usr/bin/env python3
"""Deterministic adaptive singleton-cluster probe for Erdős 1041.

This is numerical candidate evidence. Root continuation and arclength use
floating-point arithmetic; the script deliberately does not promote the
observed strict margins to a universal theorem.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

import numpy as np
from scipy.optimize import linear_sum_assignment


def _load_partial_cluster_module():
    source = Path(__file__).with_name(
        "check_erdos1041_partial_critical_cluster_monodromy.py"
    )
    spec = importlib.util.spec_from_file_location("partial_cluster", source)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {source}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


PC = _load_partial_cluster_module()


def singleton_lollipop_mean(
    roots: np.ndarray,
    critical_value: complex,
    circle_radius: float,
    *,
    stem_steps: int,
    circle_steps: int,
) -> float:
    coefficients = np.poly(roots)
    angle = float(np.angle(-critical_value)) if abs(critical_value) > 1e-14 else 0.0
    base = critical_value + circle_radius * np.exp(1j * angle)
    stem = (np.linspace(0.0, 1.0, stem_steps + 1) ** 1.7) * base
    circle = critical_value + circle_radius * np.exp(
        1j * (angle + np.linspace(0.0, 2.0 * np.pi, circle_steps + 1))
    )
    values = np.concatenate((stem, circle[1:], stem[-2::-1]))

    current = roots.copy()
    lengths = np.zeros(len(roots))
    tail = coefficients[:-1]
    for value in values[1:]:
        candidates = np.roots(
            np.concatenate((tail, [coefficients[-1] - value]))
        )
        _, assignment = linear_sum_assignment(
            np.abs(current[:, None] - candidates[None, :])
        )
        following = candidates[assignment]
        lengths += np.abs(following - current)
        current = following

    _, assignment = linear_sum_assignment(
        np.abs(current[:, None] - roots[None, :])
    )
    cycles = PC._cycles(tuple(int(index) for index in assignment))
    moved = [cycle for cycle in cycles if len(cycle) > 1]
    if len(moved) != 1 or len(moved[0]) != 2:
        raise AssertionError(f"singleton contour did not induce one transposition: {cycles}")
    return float(np.mean(lengths[moved[0]]))


def best_singleton(
    roots: np.ndarray,
    *,
    stem_steps: int,
    circle_steps: int,
) -> tuple[float, complex, float]:
    coefficients = np.poly(roots)
    critical_points = np.roots(np.polyder(coefficients))
    critical_values = np.polyval(coefficients, critical_points)
    rows: list[tuple[float, complex, float]] = []
    for index, value in enumerate(critical_values):
        if abs(value) >= 1.0:
            continue
        separation = min(
            [
                1.0 - abs(value),
                *[
                    abs(value - other)
                    for other_index, other in enumerate(critical_values)
                    if other_index != index
                ],
            ]
        )
        radius = max(1e-10, 0.002 * separation)
        mean = singleton_lollipop_mean(
            roots,
            value,
            radius,
            stem_steps=stem_steps,
            circle_steps=circle_steps,
        )
        rows.append((mean, complex(value), radius))
    if not rows:
        raise AssertionError("configuration has no admissible critical value")
    return min(rows)


def generated_configurations() -> list[tuple[int, str, int, np.ndarray]]:
    rng = np.random.default_rng(1041)
    rows: list[tuple[int, str, int, np.ndarray]] = []
    for degree in range(3, 10):
        for family in ("near_regular", "random_circle", "two_cluster"):
            for repetition in range(12):
                if family == "near_regular":
                    angles = (
                        2.0 * np.pi * np.arange(degree) / degree
                        + rng.normal(0.0, 0.035, degree)
                    )
                elif family == "random_circle":
                    angles = np.sort(rng.uniform(0.0, 2.0 * np.pi, degree))
                else:
                    angles = np.concatenate(
                        (
                            rng.normal(0.0, 0.12, degree // 2),
                            np.pi + rng.normal(0.0, 0.12, degree - degree // 2),
                        )
                    )
                radii = 0.985 - rng.uniform(0.0, 0.015, degree)
                roots = radii * np.exp(1j * angles)
                rows.append((degree, family, repetition, roots))

    for degree, encoded in PC._load_witnesses().items():
        roots = np.array(
            [
                complex(float.fromhex(real), float.fromhex(imaginary))
                for real, imaginary in encoded
            ],
            dtype=complex,
        )
        rows.append((degree, "pinned_hard", 0, roots))
    return rows


def main() -> None:
    coarse_rows = []
    for degree, family, repetition, roots in generated_configurations():
        mean, value, radius = best_singleton(
            roots, stem_steps=140, circle_steps=280
        )
        coarse_rows.append((mean, degree, family, repetition, roots, value, radius))
    coarse_rows.sort(reverse=True, key=lambda row: row[0])

    fine_rows = []
    for coarse in coarse_rows[:8]:
        _, degree, family, repetition, roots, _, _ = coarse
        mean, value, radius = best_singleton(
            roots, stem_steps=800, circle_steps=1600
        )
        fine_rows.append((mean, degree, family, repetition, value, radius))

    worst_coarse = coarse_rows[0]
    worst_fine = max(fine_rows, key=lambda row: row[0])
    pinned = {
        degree: mean
        for mean, degree, family, _, _, _, _ in coarse_rows
        if family == "pinned_hard"
    }
    assert len(coarse_rows) == 254
    assert worst_coarse[0] < 1.93
    assert worst_fine[0] < 1.93
    assert all(mean < 1.90 for mean in pinned.values())
    assert abs(worst_fine[0] - worst_coarse[0]) < 0.01

    print("ADAPTIVE SINGLETON-CLUSTER SELECTION: PASS (NUMERICAL EVIDENCE ONLY)")
    print(f"configuration_count={len(coarse_rows)}")
    print(
        "worst_coarse="
        f"{worst_coarse[0]:.12f} degree={worst_coarse[1]} "
        f"family={worst_coarse[2]} repetition={worst_coarse[3]}"
    )
    print(
        "worst_fine="
        f"{worst_fine[0]:.12f} degree={worst_fine[1]} "
        f"family={worst_fine[2]} repetition={worst_fine[3]}"
    )
    for degree in sorted(pinned):
        print(f"pinned_hard_degree_{degree}_coarse={pinned[degree]:.12f}")


if __name__ == "__main__":
    main()
