#!/usr/bin/env python3
"""Pinned partial-cluster probe for Erdős 1041.

The script imports the bit-exact degree-6 and degree-9 root literals already
owned by the straight-spoke witness checker.  Numerical continuation is
candidate evidence only; coarse/fine drift and geometric separation guards
make its claim boundary explicit.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

import numpy as np
from scipy.optimize import linear_sum_assignment


SHIFTS = {
    6: 0.0003719929580981397,
    9: 0.00014697796956473399,
}


def _load_witnesses() -> dict[int, tuple[tuple[str, str], ...]]:
    source = Path(__file__).with_name(
        "check_erdos1041_straight_spoke_hub_criterion.py"
    )
    spec = importlib.util.spec_from_file_location("straight_spoke_witnesses", source)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {source}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.QC_REFUTATION_WITNESSES


def _cycles(permutation: tuple[int, ...]) -> list[list[int]]:
    seen: set[int] = set()
    result: list[list[int]] = []
    for start in range(len(permutation)):
        if start in seen:
            continue
        cycle: list[int] = []
        current = start
        while current not in seen:
            seen.add(current)
            cycle.append(current)
            current = permutation[current]
        result.append(cycle)
    return result


def analyse(
    roots: np.ndarray,
    shift: float,
    *,
    stem_steps: int,
    circle_steps: int,
) -> dict[str, object]:
    coefficients = np.poly(roots)
    critical_points = np.roots(np.polyder(coefficients))
    critical_values = np.polyval(coefficients, critical_points)
    admissible = critical_values[np.abs(critical_values) < 1.0]
    inadmissible = critical_values[np.abs(critical_values) >= 1.0]

    base_center = np.mean(admissible)
    radial_unit = base_center / abs(base_center)
    center = base_center - shift * radial_unit
    radius = 1.02 * float(np.max(np.abs(admissible - center))) + 1e-9

    start_angle = float(np.angle(-center))
    base = center + radius * np.exp(1j * start_angle)
    stem = (
        np.linspace(0.0, 1.0, stem_steps + 1) ** 1.7
    ) * base
    circle = center + radius * np.exp(
        1j * (start_angle + np.linspace(0.0, 2.0 * np.pi, circle_steps + 1))
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
    permutation = tuple(int(index) for index in assignment)
    cycles = _cycles(permutation)
    moved = max(cycles, key=len)
    return {
        "admissible_count": len(admissible),
        "cycles": cycles,
        "moved_size": len(moved),
        "moved_mean": float(np.mean(lengths[moved])),
        "moved_max": float(np.max(lengths[moved])),
        "value_clearance": float(1.0 - (abs(center) + radius)),
        "inside_margin": float(radius - np.max(np.abs(admissible - center))),
        "outside_margin": float(np.min(np.abs(inadmissible - center)) - radius),
        "max_value_modulus": float(np.max(np.abs(values))),
    }


def main() -> None:
    witnesses = _load_witnesses()
    print("PARTIAL CRITICAL-CLUSTER MONODROMY: PASS")
    for degree, shift in SHIFTS.items():
        roots = np.array(
            [
                complex(float.fromhex(real), float.fromhex(imag))
                for real, imag in witnesses[degree]
            ],
            dtype=complex,
        )
        coarse = analyse(
            roots, shift, stem_steps=500, circle_steps=1000
        )
        fine = analyse(
            roots, shift, stem_steps=1200, circle_steps=2400
        )

        assert fine["moved_size"] == fine["admissible_count"] + 1
        assert fine["moved_mean"] < 1.9
        assert fine["moved_max"] > 2.0
        assert fine["value_clearance"] > 1e-5
        assert fine["inside_margin"] > 3e-6
        assert fine["outside_margin"] > 2e-5
        assert fine["max_value_modulus"] < 1.0
        assert fine["cycles"] == coarse["cycles"]
        assert abs(fine["moved_mean"] - coarse["moved_mean"]) < 2e-4

        print(
            f"degree {degree}: admissible={fine['admissible_count']}, "
            f"moved={fine['moved_size']}, mean={fine['moved_mean']:.9f}, "
            f"max={fine['moved_max']:.9f}, "
            f"clearance={fine['value_clearance']:.3e}"
        )


if __name__ == "__main__":
    main()
