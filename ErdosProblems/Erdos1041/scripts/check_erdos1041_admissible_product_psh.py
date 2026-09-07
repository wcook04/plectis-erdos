#!/usr/bin/env python3
"""Numerical regressions for the cellwise psh admissible-product reduction.

The proof is analytic and lives in AdmissibleCriticalArcProductPshReduction.md.
This checker only probes the sub-mean inequality on guarded degree-five disks
and the exact similarity covariance at floating precision.
"""

from __future__ import annotations

import math

import numpy as np

from system.lib.formal_math_lemniscate import merging_pair_tree


ROOT_FIXTURES = (
    (
        0.10285801156787167 + 0.8164585917476148j,
        -0.2734071434342692 - 0.32111612834697867j,
        0.03276177309963192 - 0.7060330946412124j,
        -0.7747169777581391 - 0.002917659230037242j,
        0.7705402611578948 - 0.10341750628797934j,
    ),
    (
        0.5000063178369887 + 0.5410398821611554j,
        -0.6852173890401616 - 0.4062609986908367j,
        0.004359618501283923 + 0.5771049645801558j,
        0.3361210246369925 - 0.7559845660378866j,
        -0.3159931762266857 - 0.12574796515063108j,
    ),
    (
        0.6235277537099866 - 0.339320713499377j,
        -0.664580117249292 + 0.10916334479228092j,
        -0.08135160760955894 - 0.7044745560013933j,
        0.45159757802520967 + 0.04243361062563081j,
        0.5102067267103177 + 0.6500314162982026j,
    ),
    (
        0.15340152923421568 - 0.4840639094989709j,
        0.8832026572786785 + 0.13911459620150804j,
        -0.519706336143277 + 0.2187712506453635j,
        -0.32812205142978895 - 0.09548786262280712j,
        0.4020261779024648 - 0.7951421445800285j,
    ),
)


def segment_distance(point: complex, endpoint: complex) -> float:
    if abs(endpoint) == 0.0:
        return abs(point)
    parameter = float((point * np.conj(endpoint)).real / abs(endpoint) ** 2)
    parameter = max(0.0, min(1.0, parameter))
    return abs(point - parameter * endpoint)


def guards(roots: np.ndarray) -> tuple[float, float, float, float, float]:
    coefficients = np.poly(roots)
    critical_points = np.roots(np.polyder(coefficients))
    values = np.polyval(coefficients, critical_points)
    separation = min(
        abs(values[left] - values[right])
        for left in range(len(values))
        for right in range(left)
    )
    wall_clearance = min(
        segment_distance(values[left], values[right]) / abs(values[right])
        for left in range(len(values))
        for right in range(len(values))
        if left != right
    )
    return (
        min(abs(value) for value in values),
        min(abs(abs(value) - 1.0) for value in values),
        separation,
        wall_clearance,
        1.0 - max(abs(root) for root in roots),
    )


def log_admissible_product(roots: np.ndarray) -> tuple[float, int]:
    rows = merging_pair_tree(roots)
    if rows is None or len(rows) != len(roots) - 1:
        raise AssertionError("complete merge tree was not recovered")
    admissible = [row for row in rows if row["critical_value_modulus"] < 1.0]
    if not admissible:
        raise AssertionError("guarded fixture has no admissible critical point")
    degree = len(roots)
    logarithm = sum(
        math.log(
            row["total_length"]
            / (2.0 * row["critical_value_modulus"] ** (1.0 / degree))
        )
        for row in admissible
    )
    return logarithm, len(admissible)


def perturbation_direction(index: int, degree: int) -> np.ndarray:
    # Deterministic complex directions; normalization makes the disk radius
    # directly comparable across fixtures.
    direction = np.array(
        [
            complex(
                math.cos((j + 1) * (index + 2)),
                math.sin((j + 2) * (index + 1)),
            )
            for j in range(degree)
        ],
        dtype=complex,
    )
    return direction / max(abs(entry) for entry in direction)


def terminal_torus_probe() -> tuple[int, float, str]:
    """Run a bounded falsifier search on the first psh terminal family."""

    rng = np.random.default_rng(2026083002)
    records: list[tuple[float, str]] = []
    degree = 5

    accepted = 0
    while accepted < 30:
        angles = np.sort(2.0 * np.pi * rng.random(degree))
        gaps = np.diff(np.concatenate((angles, [angles[0] + 2.0 * np.pi])))
        if min(gaps) < 0.055:
            continue
        logarithm, _ = log_admissible_product(np.exp(1j * angles))
        records.append((math.exp(logarithm), "broad"))
        accepted += 1

    base = 2.0 * np.pi * np.arange(degree) / degree
    for epsilon in (3.0e-1, 1.0e-1, 3.0e-2, 1.0e-2, 3.0e-3, 1.0e-3):
        for _ in range(8):
            perturbation = rng.normal(size=degree)
            perturbation -= float(np.mean(perturbation))
            perturbation /= max(abs(entry) for entry in perturbation)
            logarithm, _ = log_admissible_product(
                np.exp(1j * (base + epsilon * perturbation))
            )
            records.append((math.exp(logarithm), f"near_{epsilon:g}"))

    largest_product, family = max(records)
    assert largest_product < 1.001
    return len(records), largest_product, family


def main() -> None:
    defects: list[float] = []
    all_guards: list[tuple[float, float, float, float, float]] = []
    products: list[float] = []
    sample_count = 20
    epsilon = 0.0025

    for index, fixture in enumerate(ROOT_FIXTURES):
        center = np.array(fixture, dtype=complex)
        direction = perturbation_direction(index, len(center))
        center_log, center_count = log_admissible_product(center)
        boundary_logs: list[float] = []
        counts: set[int] = set()
        disk_guards: list[tuple[float, float, float, float, float]] = []
        for sample in range(sample_count):
            phase = np.exp(2j * np.pi * sample / sample_count)
            roots = center + epsilon * phase * direction
            logarithm, count = log_admissible_product(roots)
            boundary_logs.append(logarithm)
            counts.add(count)
            disk_guards.append(guards(roots))

        defect = float(np.mean(boundary_logs) - center_log)
        assert counts == {center_count} == {4}
        assert defect > 1.0e-7
        defects.append(defect)
        all_guards.extend(disk_guards)
        products.append(math.exp(center_log))

    minima = tuple(min(row[column] for row in all_guards) for column in range(5))
    assert minima[0] > 0.03       # critical values stay away from zero
    assert minima[1] > 0.68       # admissible set stays fixed, far below cut 1
    assert minima[2] > 0.04       # critical values remain separated
    assert minima[3] > 0.07       # no foreign value approaches a descent segment
    assert minima[4] > 0.10       # every root stays in the open unit disk

    # Each fixed-label q_k, and their product while the admissible set stays
    # fixed, is similarity invariant.  Numerical continuation is the only
    # reason this replay is not bit-exact.
    fixture = np.array(ROOT_FIXTURES[0], dtype=complex)
    base_log, _ = log_admissible_product(fixture)
    scale = 0.73 * np.exp(0.41j)
    shifted_log, _ = log_admissible_product(0.12 - 0.08j + scale * fixture)
    similarity_relative_error = (
        abs(math.exp(base_log) - math.exp(shifted_log)) / math.exp(base_log)
    )
    assert similarity_relative_error < 1.0e-7

    terminal_count, terminal_maximum, terminal_family = terminal_torus_probe()

    print("ADMISSIBLE PRODUCT PSH: PASS")
    for index, (product, defect) in enumerate(zip(products, defects)):
        print(
            f"disk {index}: center product={product:.12f}, "
            f"submean defect={defect:.12e}"
        )
    print(
        "guard minima: "
        f"critical modulus={minima[0]:.6f}, cut margin={minima[1]:.6f}, "
        f"value separation={minima[2]:.6f}, wall clearance={minima[3]:.6f}, "
        f"root room={minima[4]:.6f}"
    )
    print(f"similarity relative error={similarity_relative_error:.3e}")
    print(
        f"terminal torus rows={terminal_count}, "
        f"max product={terminal_maximum:.12f}, family={terminal_family}"
    )


if __name__ == "__main__":
    main()
