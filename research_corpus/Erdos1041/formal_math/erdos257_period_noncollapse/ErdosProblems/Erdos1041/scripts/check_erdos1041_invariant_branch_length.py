#!/usr/bin/env python3
"""Erdős #1041: the surviving admissible-hub length obligation.

The target fixes both a geometric disk and the polynomial-value threshold
``|f| < 1``.  The latter cannot be discarded under coordinate normalisation:
only a critical point with ``|f(c)| < 1`` gives a descending branch pair
contained in the target lemniscate.  The correct geometric form is

        min over |f(c)| < 1 of L(c)  <=  2 R,                              (*)

where ``R`` is the root circumradius.  This implies the target because roots
in the open unit disk give ``R < 1``.  Length and circumradius scale together,
but admissibility must be carried along with the level threshold.

This probe records three things.

**Equality is attained, and by an identifiable family.**  Every monic quadratic
gives equality exactly: with ``c = (z1+z2)/2`` and ``d = (z1-z2)/2`` we have
``f(c+u) = u^2 - d^2`` and ``f(c) = -d^2``, so ``f^{-1}([0,-d^2])`` is the
segment ``{c + t d : |t| <= 1}`` from ``z2`` to ``z1``, of length
``|z1 - z2| = 2R``.  The family ``z^n - r^n`` gives equality too, with the two
branches a pair of radii.  Both are ``f`` affinely conjugate to ``z^n - 1``.

That matters for how the numerical evidence should be read.  A supremum pinned
just below a threshold is worthless on its own -- the straight-spoke criterion
was pinned at 1.9999... across degrees three to twelve and turned out false.
Here the supremum sits at 1 *because an equality family reaches it*, which is a
different and much stronger situation than an unexplained near miss.

**No hub-by-hub argument can work.**  The per-hub strengthening
``L(c) <= 2 max_k |z_k - c|`` is tight on both equality families and false in
general, so the minimum over hubs is load-bearing rather than a convenience.

**The selection over hubs is genuinely global.**  The hub of least ``|f(c)|``
attains the minimum branch length on the adversarial optima reported below, but
this is not a uniform selection theorem.  A pinned quartic has first-merge
branch length about ``1.042608`` while a later hub has length about ``0.841236``.
Thus the target must retain a global minimum over admissible hubs; replacing
it by the least-critical-value hub is false.

Numerical continuation is candidate evidence.  The equality statements for
quadratics and for ``z^n - r^n`` are ordinary proofs; nothing here settles the
admissible-hub inequality or Erdős #1041.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any

import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)
from system.lib.formal_math_lemniscate import (  # noqa: E402
    critical_table,
    descending_pair,
)

SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/"
    "check_erdos1041_invariant_branch_length.py"
)
ENGINE_REF = "system/lib/formal_math_lemniscate.py"
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "StraightSpokeHubCriterionLab.md"
)
CHARGE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "CriticalTreeLengthCharge.md"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/research_packet.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1041_invariant_branch_length_receipt.json"
)

BRANCH_TOLERANCES = {"relative_tolerance": 1.0e-10, "absolute_tolerance": 1.0e-12}

#: Pinned witness for the falsity of the per-hub strengthening
#: ``L(c) <= 2 max_k |z_k - c|``.  Exact IEEE-754 literals so it round-trips bit
#: for bit.  All four roots sit well inside the unit disk (max modulus 0.783),
#: so this is not a boundary-degeneracy artefact, and the hub is admissible with
#: ``|f(c)| = 0.0318`` -- comfortably away from the level-one wall too.
PER_HUB_WITNESS: tuple[tuple[str, str], ...] = (
    ("0x1.4300f197dcb95p-1", "-0x1.dad653a1eece1p-2"),
    ("0x1.7a7710b6c327dp-1", "-0x1.b50d56fa9c066p-3"),
    ("-0x1.a0d99c1a2a10fp-4", "-0x1.1805c2801e06bp-3"),
    ("-0x1.6311110c80115p-11", "0x1.8cc46c689b15ep-4"),
)

#: Pinned witness that least critical-value modulus does not select the
#: shortest descending branch pair.  Exact IEEE-754 literals make the
#: computational no-go independently replayable.
LEAST_VALUE_SELECTION_WITNESS: tuple[tuple[str, str], ...] = (
    ("0x1.2f5bb5d03def3p-1", "0x1.6c6238cf25677p-1"),
    ("-0x1.8d85fb38788f5p-1", "-0x1.1e48ce955082ap-2"),
    ("-0x1.6663c411e2bcfp-4", "-0x1.f5adc7f4bd554p-1"),
    ("-0x1.a97560146ca3ap-3", "0x1.112c3b2f14fa7p-1"),
)


def circumcircle(points: np.ndarray) -> tuple[complex, float]:
    """Centre and radius of the smallest enclosing circle (Welzl, incremental)."""

    values = [complex(point) for point in points]

    def two(a: complex, b: complex) -> tuple[complex, float]:
        return (a + b) / 2, abs(a - b) / 2

    def three(a: complex, b: complex, c: complex) -> tuple[complex, float]:
        ax, ay, bx, by, cx, cy = a.real, a.imag, b.real, b.imag, c.real, c.imag
        determinant = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
        if abs(determinant) < 1.0e-18:
            best: tuple[complex, float] = (0j, float("inf"))
            for left, right in ((a, b), (a, c), (b, c)):
                centre, radius = two(left, right)
                if radius < best[1] and all(
                    abs(point - centre) <= radius + 1.0e-12 for point in (a, b, c)
                ):
                    best = (centre, radius)
            return best
        ux = (
            (ax * ax + ay * ay) * (by - cy)
            + (bx * bx + by * by) * (cy - ay)
            + (cx * cx + cy * cy) * (ay - by)
        ) / determinant
        uy = (
            (ax * ax + ay * ay) * (cx - bx)
            + (bx * bx + by * by) * (ax - cx)
            + (cx * cx + cy * cy) * (bx - ax)
        ) / determinant
        centre = complex(ux, uy)
        return centre, abs(a - centre)

    centre, radius = values[0], 0.0
    for i in range(1, len(values)):
        if abs(values[i] - centre) <= radius + 1.0e-12:
            continue
        centre, radius = values[i], 0.0
        for j in range(i):
            if abs(values[j] - centre) <= radius + 1.0e-12:
                continue
            centre, radius = two(values[i], values[j])
            for k in range(j):
                if abs(values[k] - centre) <= radius + 1.0e-12:
                    continue
                centre, radius = three(values[i], values[j], values[k])
    return complex(centre), float(radius)


def circumradius(points: np.ndarray) -> float:
    """Radius of the smallest enclosing circle."""

    return circumcircle(points)[1]


def hub_rows(roots: np.ndarray) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for row in critical_table(roots):
        if row["critical_value_modulus"] <= 1.0e-13:
            continue
        pair = descending_pair(roots, row["critical_point"], **BRANCH_TOLERANCES)
        if pair is None or pair["maximum_endpoint_error"] > 1.0e-7:
            continue
        rows.append(
            {
                "critical_value_modulus": row["critical_value_modulus"],
                "admissible": row["admissible"],
                "length": pair["total_length"],
                "critical_point": complex(row["critical_point"]),
                "critical_value": complex(row["critical_value"]),
                "root_pair": tuple(pair["root_pair"]),
                "branches": tuple(pair["branches"]),
                "farthest_root_distance": float(
                    np.abs(np.asarray(roots) - row["critical_point"]).max()
                ),
            }
        )
    return rows


def tangent_support_terms(
    roots: np.ndarray, centre: complex, radius: float, row: dict[str, Any]
) -> dict[str, float]:
    """Exact edge identity terms, evaluated from the numerical branch length."""

    coefficients = np.poly(roots)
    derivative = np.polyder(coefficients)
    value = complex(np.polyval(coefficients, row["critical_point"]))
    ray = value / abs(value)
    endpoint_term = 0.0
    for root_index in row["root_pair"]:
        root = complex(roots[root_index])
        root_to_hub_tangent = ray / complex(np.polyval(derivative, root))
        root_to_hub_tangent /= abs(root_to_hub_tangent)
        endpoint_term -= float(
            np.real(np.conj(root - centre) * root_to_hub_tangent)
        )
    curvature_support = endpoint_term - row["length"]
    endpoint_deficit = 2 * radius - endpoint_term
    return {
        "endpoint_term": endpoint_term,
        "curvature_support": curvature_support,
        "endpoint_deficit": endpoint_deficit,
        "budget_charge": endpoint_deficit + curvature_support,
    }


def root_star_half_charges(
    roots: np.ndarray, centre: complex, radius: float, row: dict[str, Any]
) -> dict[int, float]:
    """Allocate ``2R-L(c)`` to its two root incidences through the critical tangent."""

    coefficients = np.poly(roots)
    level = coefficients.astype(np.complex128, copy=True)
    level[-1] -= (1.0 - 1.0e-6**2) * row["critical_value"]
    starts = sorted(
        np.roots(level), key=lambda point: abs(point - row["critical_point"])
    )[:2]
    second_derivative = np.polyder(coefficients, 2)
    local_direction = np.sqrt(
        -2 * row["critical_value"]
        / complex(np.polyval(second_derivative, row["critical_point"]))
    )
    local_direction /= abs(local_direction)
    available_directions = [complex(local_direction), complex(-local_direction)]
    charges: dict[int, float] = {}
    for start, branch in zip(starts, row["branches"], strict=True):
        observed_direction = complex(start - row["critical_point"])
        observed_direction /= abs(observed_direction)
        direction_index = int(
            np.argmax(
                [
                    np.real(np.conj(observed_direction) * candidate)
                    for candidate in available_directions
                ]
            )
        )
        critical_to_root = available_directions.pop(direction_index)
        root_to_critical_tangent = -critical_to_root
        critical_support = float(
            np.real(
                np.conj(row["critical_point"] - centre)
                * root_to_critical_tangent
            )
        )
        root_index = int(branch["root_index"])
        charges[root_index] = radius + critical_support - float(branch["length"])
    return charges


def component_charge_rows(
    roots: np.ndarray,
    radius: float,
    admissible: list[dict[str, Any]],
    terms: list[dict[str, float]],
) -> list[dict[str, float | int]]:
    """Group the exact edge charges by admissible root-graph component."""

    degree = len(roots)
    parents = list(range(degree))

    def find(index: int) -> int:
        while parents[index] != index:
            parents[index] = parents[parents[index]]
            index = parents[index]
        return index

    def union(left: int, right: int) -> None:
        left_root, right_root = find(left), find(right)
        if left_root != right_root:
            parents[right_root] = left_root

    for row in admissible:
        union(int(row["root_pair"][0]), int(row["root_pair"][1]))
    charges: dict[int, float] = {}
    lengths: dict[int, float] = {}
    edge_counts: dict[int, int] = {}
    vertices: dict[int, set[int]] = {}
    for row, term in zip(admissible, terms, strict=True):
        component = find(int(row["root_pair"][0]))
        charges[component] = charges.get(component, 0.0) + term["budget_charge"]
        lengths[component] = lengths.get(component, 0.0) + float(row["length"])
        edge_counts[component] = edge_counts.get(component, 0) + 1
        vertices.setdefault(component, set()).update(int(i) for i in row["root_pair"])
    out: list[dict[str, float | int]] = []
    for component, charge in charges.items():
        component_radius = circumradius(
            np.asarray([roots[index] for index in sorted(vertices[component])])
        )
        out.append({
            "component_root": component,
            "edge_count": edge_counts[component],
            "normalized_charge": charge / (2 * radius * edge_counts[component]),
            "component_root_circumradius": component_radius,
            "normalized_local_radius_charge": 1.0
            - lengths[component] / (2 * component_radius * edge_counts[component]),
        })
    return out


def quadratic_equality_rows(seed: int = 23, trials: int = 60) -> dict[str, Any]:
    """Every monic quadratic attains equality in (*) -- an ordinary proof."""

    rng = np.random.default_rng(seed)
    worst = 0.0
    counted = 0
    for _ in range(trials):
        roots = np.asarray(
            [
                complex(rng.standard_normal(), rng.standard_normal()),
                complex(rng.standard_normal(), rng.standard_normal()),
            ],
            dtype=np.complex128,
        )
        if abs(roots[0] - roots[1]) < 1.0e-3:
            continue
        rows = hub_rows(roots)
        if len(rows) != 1:
            continue
        ratio = rows[0]["length"] / (2 * circumradius(roots))
        worst = max(worst, abs(ratio - 1.0))
        counted += 1
    return {
        "statement": (
            "f(c+u) = u^2 - d^2 with c the midpoint and d the half-difference, so "
            "f^{-1}([0, f(c)]) is exactly the segment between the roots and "
            "L(c) = |z1 - z2| = 2R"
        ),
        "quadratics_checked": counted,
        "maximum_deviation_from_equality": worst,
    }


def pure_power_equality_rows() -> list[dict[str, Any]]:
    """``z^n - r^n`` attains equality: the branches are two radii."""

    rows: list[dict[str, Any]] = []
    for degree in (3, 4, 5, 6, 8):
        for radius in (0.9, 0.99):
            roots = radius * np.exp(2j * np.pi * np.arange(degree) / degree)
            # perturb minutely so the degenerate critical point splits and the
            # simple-saddle branch integration applies
            roots = roots * np.exp(1.0e-6 * np.arange(degree))
            entries = hub_rows(roots)
            if not entries:
                continue
            shortest = min(entry["length"] for entry in entries)
            rows.append(
                {
                    "degree": degree,
                    "radius": radius,
                    "minimum_branch_length": shortest,
                    "two_circumradius": 2 * circumradius(roots),
                    "ratio": shortest / (2 * circumradius(roots)),
                }
            )
    return rows


def per_hub_witness_row() -> dict[str, Any]:
    """The pinned configuration on which the per-hub strengthening fails."""

    roots = np.asarray(
        [complex(float.fromhex(re), float.fromhex(im)) for re, im in PER_HUB_WITNESS],
        dtype=np.complex128,
    )
    rows = hub_rows(roots)
    if not rows:
        raise AssertionError("per-hub witness produced no usable hub")
    worst = max(rows, key=lambda row: row["length"] / (2 * row["farthest_root_distance"]))
    return {
        "root_hex_literals": [list(pair) for pair in PER_HUB_WITNESS],
        "maximum_root_modulus": float(np.abs(roots).max()),
        "roots_strictly_inside_unit_disk": bool(np.all(np.abs(roots) < 1.0)),
        "critical_value_modulus": worst["critical_value_modulus"],
        "admissible": worst["admissible"],
        "branch_length": worst["length"],
        "twice_farthest_root_distance": 2 * worst["farthest_root_distance"],
        "per_hub_ratio": worst["length"] / (2 * worst["farthest_root_distance"]),
        "admissible_minimum_ratio_at_this_configuration": (
            min(row["length"] for row in rows) / (2 * circumradius(roots))
        ),
    }


def least_value_selection_witness_row() -> dict[str, Any]:
    """Least critical-value modulus need not minimize branch-pair length."""

    roots = np.asarray(
        [
            complex(float.fromhex(re), float.fromhex(im))
            for re, im in LEAST_VALUE_SELECTION_WITNESS
        ],
        dtype=np.complex128,
    )
    rows = hub_rows(roots)
    if len(rows) < 2:
        raise AssertionError("least-value selection witness produced too few hubs")
    least_value = min(rows, key=lambda row: row["critical_value_modulus"])
    shortest = min(rows, key=lambda row: row["length"])
    if least_value["length"] <= shortest["length"] * 1.05:
        raise AssertionError("least-value selection witness lost its strict gap")
    if least_value["critical_value_modulus"] >= shortest["critical_value_modulus"]:
        raise AssertionError("selected shorter hub is no longer later in level order")
    return {
        "root_hex_literals": [list(pair) for pair in LEAST_VALUE_SELECTION_WITNESS],
        "roots_strictly_inside_unit_disk": bool(np.all(np.abs(roots) < 1.0)),
        "least_critical_value_modulus": least_value["critical_value_modulus"],
        "least_value_hub_branch_length": least_value["length"],
        "shorter_later_critical_value_modulus": shortest["critical_value_modulus"],
        "shorter_later_hub_branch_length": shortest["length"],
        "length_ratio": least_value["length"] / shortest["length"],
    }


def sampled_rows(seed: int = 31415, trials: int = 110) -> list[dict[str, Any]]:
    """Sweep the admissible minimum, per-hub, and aggregate ratios."""

    rng = np.random.default_rng(seed)
    out: list[dict[str, Any]] = []
    for degree in (3, 4, 5, 6, 8):
        best_admissible_minimum = -1.0
        best_per_hub = -1.0
        best_aggregate = -1.0
        best_aggregate_decomposition: dict[str, float] | None = None
        minimum_curvature_support_ratio = float("inf")
        minimum_curvature_support_witness: dict[str, Any] | None = None
        minimum_root_star_charge_ratio = float("inf")
        minimum_root_star_witness: dict[str, Any] | None = None
        root_star_failures = 0
        maximum_root_star_identity_error = 0.0
        minimum_component_charge_ratio = float("inf")
        negative_component_charges = 0
        minimum_component_charge_witness: dict[str, Any] | None = None
        per_hub_failures = 0
        complete_hub_sets = 0
        admissible_hubs = 0
        hubs = 0
        cases = 0
        for _ in range(trials):
            style = rng.integers(0, 3)
            if style == 0:
                roots = np.sqrt(rng.random(degree)) * np.exp(2j * np.pi * rng.random(degree))
            elif style == 1:
                base = rng.choice([0.999, 0.99, 0.9]) * np.exp(
                    2j * np.pi * np.arange(degree) / degree
                )
                scale = rng.choice([3.0e-1, 1.0e-1, 1.0e-2])
                roots = base * np.exp(
                    scale * (rng.standard_normal(degree) + 1j * rng.standard_normal(degree))
                )
            else:
                roots = np.sqrt(rng.random(degree)) * np.exp(2j * np.pi * rng.random(degree))
                roots = 0.3 * roots + complex(
                    rng.standard_normal() * 0.2, rng.standard_normal() * 0.2
                )
            rows = hub_rows(roots)
            if not rows:
                continue
            admissible = [row for row in rows if row["admissible"]]
            if not admissible:
                continue
            cases += 1
            hubs += len(rows)
            admissible_hubs += len(admissible)
            centre, radius = circumcircle(roots)
            if radius <= 0:
                continue
            best_admissible_minimum = max(
                best_admissible_minimum,
                min(row["length"] for row in admissible) / (2 * radius),
            )
            if len(rows) == degree - 1:
                complete_hub_sets += 1
                terms = [
                    tangent_support_terms(roots, centre, radius, row)
                    for row in admissible
                ]
                component_rows = component_charge_rows(
                    roots, radius, admissible, terms
                )
                for component_row in component_rows:
                    component_ratio = float(component_row["normalized_charge"])
                    if component_ratio < minimum_component_charge_ratio:
                        minimum_component_charge_ratio = component_ratio
                        minimum_component_charge_witness = {
                            "normalized_component_charge": component_ratio,
                            "component_edge_count": component_row["edge_count"],
                            "roots_hex": [
                                [float(root.real).hex(), float(root.imag).hex()]
                                for root in roots
                            ],
                        }
                    negative_component_charges += int(component_ratio < -1.0e-7)
                root_star_charges = np.zeros(degree, dtype=float)
                for row in admissible:
                    for root_index, charge in root_star_half_charges(
                        roots, centre, radius, row
                    ).items():
                        root_star_charges[root_index] += charge
                star_identity_error = abs(
                    float(root_star_charges.sum())
                    - sum(term["budget_charge"] for term in terms)
                )
                maximum_root_star_identity_error = max(
                    maximum_root_star_identity_error, star_identity_error
                )
                root_index = int(np.argmin(root_star_charges))
                root_star_ratio = float(root_star_charges[root_index]) / radius
                if root_star_ratio < minimum_root_star_charge_ratio:
                    minimum_root_star_charge_ratio = root_star_ratio
                    minimum_root_star_witness = {
                        "root_index": root_index,
                        "charge_over_R": root_star_ratio,
                        "roots_hex": [
                            [float(root.real).hex(), float(root.imag).hex()]
                            for root in roots
                        ],
                    }
                root_star_failures += int(np.count_nonzero(root_star_charges < -1.0e-7))
                scale = 2 * radius * len(admissible)
                aggregate_ratio = sum(row["length"] for row in admissible) / scale
                curvature_support_ratio = (
                    sum(term["curvature_support"] for term in terms) / scale
                )
                if curvature_support_ratio < minimum_curvature_support_ratio:
                    minimum_curvature_support_ratio = curvature_support_ratio
                    minimum_curvature_support_witness = {
                        "normalized_curvature_support": curvature_support_ratio,
                        "roots_hex": [
                            [float(root.real).hex(), float(root.imag).hex()]
                            for root in roots
                        ],
                    }
                if aggregate_ratio > best_aggregate:
                    best_aggregate = aggregate_ratio
                    best_aggregate_decomposition = {
                        "normalized_endpoint_term": (
                            sum(term["endpoint_term"] for term in terms) / scale
                        ),
                        "normalized_curvature_support": curvature_support_ratio,
                        "normalized_endpoint_deficit": (
                            sum(term["endpoint_deficit"] for term in terms) / scale
                        ),
                        "normalized_budget_slack": (
                            sum(term["budget_charge"] for term in terms) / scale
                        ),
                    }
            for row in admissible:
                ratio = row["length"] / (2 * row["farthest_root_distance"])
                best_per_hub = max(best_per_hub, ratio)
                if ratio > 1.0:
                    per_hub_failures += 1
        out.append(
            {
                "degree": degree,
                "configurations": cases,
                "hubs": hubs,
                "admissible_hubs": admissible_hubs,
                "maximum_admissible_minimum_ratio": best_admissible_minimum,
                "admissible_minimum_holds_on_sample": bool(
                    best_admissible_minimum <= 1.0
                ),
                "maximum_per_hub_ratio": best_per_hub,
                "per_hub_failures": per_hub_failures,
                "complete_admissible_hub_sets": complete_hub_sets,
                "maximum_admissible_aggregate_ratio": best_aggregate,
                "maximum_aggregate_decomposition": best_aggregate_decomposition,
                "minimum_normalized_curvature_support": minimum_curvature_support_ratio,
                "minimum_curvature_support_witness": minimum_curvature_support_witness,
                "minimum_root_star_charge_over_R": minimum_root_star_charge_ratio,
                "minimum_root_star_witness": minimum_root_star_witness,
                "negative_root_star_charges": root_star_failures,
                "maximum_root_star_identity_error": maximum_root_star_identity_error,
                "minimum_normalized_component_charge": minimum_component_charge_ratio,
                "negative_component_charges": negative_component_charges,
                "minimum_component_charge_witness": minimum_component_charge_witness,
            }
        )
    return out


def separated_component_rows(seed: int = 1041) -> list[dict[str, Any]]:
    """Stress the component charge on two root clusters separated above level one."""

    rng = np.random.default_rng(seed)
    out: list[dict[str, Any]] = []
    for left_count, right_count in ((2, 4),):
        degree = left_count + right_count
        configurations = 0
        multi_component_configurations = 0
        minimum_component_charge = float("inf")
        minimum_local_radius_charge = float("inf")
        minimum_local_radius_witness: dict[str, Any] | None = None
        maximum_component_count = 0
        for epsilon in (0.025,):
            for _ in range(1):
                rotation_left, rotation_right = rng.random(2) * 2 * np.pi
                left_angles = rotation_left + 2 * np.pi * np.arange(left_count) / left_count
                right_angles = (
                    rotation_right + 2 * np.pi * np.arange(right_count) / right_count
                )
                left = -0.96 + epsilon * np.exp(1j * left_angles) * (
                    1 + 0.08 * rng.standard_normal(left_count)
                )
                right = 0.96 + epsilon * np.exp(1j * right_angles) * (
                    1 + 0.08 * rng.standard_normal(right_count)
                )
                roots = np.asarray([*left, *right], dtype=np.complex128)
                if not np.all(np.abs(roots) < 1):
                    continue
                expected_admissible = sum(
                    1
                    for row in critical_table(roots)
                    if row["admissible"] and row["critical_value_modulus"] > 1.0e-13
                )
                rows = hub_rows(roots)
                admissible = [row for row in rows if row["admissible"]]
                if not admissible or len(admissible) != expected_admissible:
                    continue
                centre, radius = circumcircle(roots)
                terms = [
                    tangent_support_terms(roots, centre, radius, row)
                    for row in admissible
                ]
                component_rows = component_charge_rows(
                    roots, radius, admissible, terms
                )
                configurations += 1
                maximum_component_count = max(
                    maximum_component_count, len(component_rows)
                )
                if len(component_rows) >= 2:
                    multi_component_configurations += 1
                minimum_component_charge = min(
                    minimum_component_charge,
                    *(float(row["normalized_charge"]) for row in component_rows),
                )
                local_row = min(
                    component_rows,
                    key=lambda row: float(row["normalized_local_radius_charge"]),
                )
                local_charge = float(local_row["normalized_local_radius_charge"])
                if local_charge < minimum_local_radius_charge:
                    minimum_local_radius_charge = local_charge
                    minimum_local_radius_witness = {
                        "normalized_local_radius_charge": local_charge,
                        "component_edge_count": local_row["edge_count"],
                        "component_root_circumradius": local_row[
                            "component_root_circumradius"
                        ],
                        "roots_hex": [
                            [float(root.real).hex(), float(root.imag).hex()]
                            for root in roots
                        ],
                    }
        out.append(
            {
                "degree": degree,
                "cluster_split": [left_count, right_count],
                "configurations": configurations,
                "multi_component_configurations": multi_component_configurations,
                "maximum_component_count": maximum_component_count,
                "minimum_normalized_component_charge": minimum_component_charge,
                "minimum_normalized_local_radius_charge": minimum_local_radius_charge,
                "minimum_local_radius_witness": minimum_local_radius_witness,
            }
        )
    return out


ADVERSARIAL_SELECTION_SUPREMA = {
    "note": (
        "Legacy evolutionary comparisons of three hub-selection objectives. Only the "
        "admissible-hubs-only column corresponds to the corrected target. Coordinate "
        "normalisation does not preserve admissibility unless the level threshold is "
        "carried along. Values are lower bounds from the explored basins, not proof."
    ),
    "free": {"3": 0.999999995, "4": 0.999998909, "5": 0.999934458},
    "least_critical_value_hub": {"3": 0.999999996, "4": 0.999998909, "5": 0.999940557},
    "admissible_hubs_only": {"3": 0.999999994, "4": 0.999997843, "5": 0.999934458},
}

ADVERSARIAL_AGGREGATE_SUPREMA = {
    "note": (
        "Evolutionary maxima of the packet's priority-one aggregate "
        "sum_c L(c) / (2 * number of admissible hubs), under a free objective, an "
        "objective penalised toward few admissible hubs, and a coalesced-critical-"
        "value seeding. The hardest case is a single admissible hub, where the "
        "aggregate reduces to L(c)/2 with no averaging help."
    ),
    "free": {"3": 0.999999845, "4": 0.999997627, "5": 0.999912748, "6": 0.999448305},
    "few_hubs": {"3": 0.997058913, "4": 0.987899596, "5": 0.999912748, "6": 0.999448305},
    "admissible_hub_count_at_few_hubs_optimum": {"3": 1, "4": 2, "5": 4, "6": 5},
}


def build_payload() -> dict[str, Any]:
    quadratics = quadratic_equality_rows()
    powers = pure_power_equality_rows()
    sampled = sampled_rows()
    separated_components = separated_component_rows()
    per_hub = per_hub_witness_row()
    selection = least_value_selection_witness_row()

    if quadratics["quadratics_checked"] < 20:
        raise AssertionError("too few usable quadratics in the equality check")
    if quadratics["maximum_deviation_from_equality"] > 1.0e-6:
        raise AssertionError("quadratics no longer attain equality in (*)")
    if not powers:
        raise AssertionError("pure-power equality family produced no rows")
    for row in powers:
        if row["ratio"] > 1.0 + 1.0e-6:
            raise AssertionError(
                f"pure power degree {row['degree']} exceeds the admissible-hub bound"
            )
    for row in sampled:
        if not row["admissible_minimum_holds_on_sample"]:
            raise AssertionError(
                f"admissible minimum failed on the sample at degree {row['degree']}"
            )
        if row["complete_admissible_hub_sets"] == 0:
            raise AssertionError(
                f"no complete admissible-hub sets at degree {row['degree']}"
            )
        if row["maximum_admissible_aggregate_ratio"] > 1.0:
            raise AssertionError(
                f"admissible-hub aggregate failed on the sample at degree {row['degree']}"
            )
        decomposition = row["maximum_aggregate_decomposition"]
        if decomposition is None:
            raise AssertionError(f"missing charge decomposition at degree {row['degree']}")
        if decomposition["normalized_endpoint_deficit"] < -1.0e-10:
            raise AssertionError(f"negative endpoint deficit at degree {row['degree']}")
        expected_slack = 1.0 - row["maximum_admissible_aggregate_ratio"]
        if abs(decomposition["normalized_budget_slack"] - expected_slack) > 1.0e-9:
            raise AssertionError(f"charge identity drift at degree {row['degree']}")
        if row["maximum_root_star_identity_error"] > 1.0e-8:
            raise AssertionError(f"root-star charge identity drift at degree {row['degree']}")
    if not any(row["minimum_normalized_curvature_support"] < -1.0e-3 for row in sampled):
        raise AssertionError("the signed-curvature-only shortcut was not falsified")
    if not any(row["negative_root_star_charges"] > 0 for row in sampled):
        raise AssertionError("the root-star nonnegative allocation was not falsified")
    for row in separated_components:
        if row["multi_component_configurations"] == 0:
            raise AssertionError(
                f"component stress did not separate the degree {row['degree']} forest"
            )
        if row["minimum_normalized_component_charge"] < -1.0e-7:
            raise AssertionError(
                f"component charge failed at degree {row['degree']}"
            )
    if not any(
        row["minimum_normalized_local_radius_charge"] < -1.0e-5
        for row in separated_components
    ):
        raise AssertionError("the component-local circumradius shortcut was not falsified")
    if not per_hub["roots_strictly_inside_unit_disk"]:
        raise AssertionError("per-hub witness left the unit disk")
    if per_hub["per_hub_ratio"] <= 1.0:
        raise AssertionError("per-hub witness no longer falsifies the per-hub bound")
    if per_hub["admissible_minimum_ratio_at_this_configuration"] > 1.0:
        raise AssertionError(
            "per-hub witness must still satisfy the admissible minimum it is scoped against"
        )
    if not selection["roots_strictly_inside_unit_disk"]:
        raise AssertionError("least-value selection witness left the unit disk")

    return {
        "admissible_hub_statement": (
            "min over admissible critical points c, namely |f(c)| < 1, of L(c) "
            "<= 2 R, with R the circumradius of the root set. This implies the "
            "target statement because roots in the open unit disk give R < 1. "
            "Admissibility cannot be dropped during affine normalisation."
        ),
        "quadratic_equality_family": quadratics,
        "pure_power_equality_family": powers,
        "sampled_sweep": sampled,
        "separated_component_sweep": separated_components,
        "per_hub_falsifying_witness": per_hub,
        "least_value_selection_falsifying_witness": selection,
        "adversarial_selection_suprema": ADVERSARIAL_SELECTION_SUPREMA,
        "adversarial_aggregate_suprema": ADVERSARIAL_AGGREGATE_SUPREMA,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--print-only", action="store_true")
    args = parser.parse_args()

    payload = build_payload()
    worst_per_hub = max(row["maximum_per_hub_ratio"] for row in payload["sampled_sweep"])
    worst_admissible_minimum = max(
        row["maximum_admissible_minimum_ratio"] for row in payload["sampled_sweep"]
    )
    most_negative_curvature = min(
        row["minimum_normalized_curvature_support"] for row in payload["sampled_sweep"]
    )
    most_negative_root_star = min(
        row["minimum_root_star_charge_over_R"] for row in payload["sampled_sweep"]
    )

    contract = build_experiment_contract(
        problem_id="erdos_1041",
        target_statement=(
            "If a monic polynomial f(z)=product_i(z-z_i) has all roots in the open unit "
            "disk, prove that two roots can be joined by a curve of length less than 2 "
            "contained in the open lemniscate |f|<1."
        ),
        claim_ceiling=(
            "States the surviving obligation with its load-bearing admissibility condition, "
            "proves that equality is attained by every quadratic and by z^n - r^n, and "
            "eliminates both the per-hub strengthening and least-critical-value "
            "selection as a uniform rule. The admissible-hub inequality itself is "
            "supported by finite evidence only. Erdos #1041 remains open."
        ),
        hypothesis_id="admissible_branch_length_bound",
        hypothesis_statement=(
            "min over admissible critical points of the descending-branch pair length "
            "is at most twice the circumradius of the root set, with equality exactly "
            "on the affine geometric models of z^n - 1. A sufficient stronger target "
            "is sum over admissible c of L(c) <= 2R times their multiplicity count."
        ),
        probe_id="erdos1041_invariant_branch_length",
        probe_question=(
            "Does the admissible-hub obligation have an identifiable equality family, "
            "and can it be reduced to a per-hub or aggregate statement?"
        ),
        computation=(
            "Descending branch pairs are integrated in the substitution "
            "f(z(u)) = (1-u^2) f(c), which removes the square-root branch point, with "
            "endpoint and level residual gates. The circumradius is the exact smallest "
            "enclosing circle. Equality is checked on random quadratics and on "
            "z^n - r^n; the admissible minimum, per-hub, and complete admissible-hub "
            "aggregate ratios are swept deterministically. The exact endpoint-deficit "
            "plus signed-curvature charge is evaluated, together with two proposed "
            "uniform sign shortcuts."
        ),
        falsifier=(
            "The target form fails if any configuration gives min over admissible c of "
            "L(c) > 2R. The admissible aggregate fails if its normalized mean exceeds "
            "one. The "
            "equality claim fails if a quadratic deviates from ratio one. The per-hub "
            "elimination fails if no configuration exceeds the per-hub bound. The "
            "curvature-only and root-star shortcuts are falsified by negative charges."
        ),
        stop_condition=(
            "Stop once equality is exhibited on both families and the per-hub form is "
            "falsified. Further sampling of the admissible-minimum ratio is a longer horizon; "
            "the open question needs a proof, not more configurations."
        ),
        survival_consequence=(
            "The obligation left by the straight-spoke eliminations has a sharp "
            "geometric ratio with a single conjectural equality class, but coordinate "
            "normalisation must retain the level threshold. A proof must be global over "
            "the admissible critical forest rather than local at one hub."
        ),
        falsification_consequence=(
            "A configuration with min over admissible c of L(c) > 2R would refute this "
            "sufficient branch mechanism. It would not by itself refute Erdos #1041, "
            "because a shorter noncanonical path could still exist."
        ),
        consumer_ref=PACKET_REF,
        analysis_refs=[ANALYSIS_REF, CHARGE_REF],
        source_refs=[SOURCE_REF, ENGINE_REF],
        result_status="mixed",
        result_summary=(
            "Every quadratic attains equality in the admissible-hub bound (maximum deviation "
            f"{payload['quadratic_equality_family']['maximum_deviation_from_equality']:.2e}), "
            "and z^n - r^n attains it too. The per-hub strengthening is false: a pinned "
            "degree-four witness with all roots inside the disk (max modulus "
            f"{payload['per_hub_falsifying_witness']['maximum_root_modulus']:.6f}) reaches "
            f"ratio {payload['per_hub_falsifying_witness']['per_hub_ratio']:.9f}, while its "
            "own admissible-minimum ratio stays at "
            f"{payload['per_hub_falsifying_witness']['admissible_minimum_ratio_at_this_configuration']:.6f}. "
            "A separate quartic makes the least-critical-value branch pair longer than "
            "a later pair by factor "
            f"{payload['least_value_selection_falsifying_witness']['length_ratio']:.6f}. "
            f"The sampled sweep reaches per-hub ratio {worst_per_hub:.6f}. "
            "The admissible-hub bound itself held on every sampled "
            f"configuration, worst ratio {worst_admissible_minimum:.6f}, and adversarial search "
            "under three independent min-objectives pinned it at one without crossing. "
            f"The signed-curvature-only shortcut reaches {most_negative_curvature:.6f}, "
            f"and the nonnegative root-star allocation reaches {most_negative_root_star:.6f}; "
            "both simpler sign lemmas are therefore eliminated."
        ),
        resource_bounds={
            "maximum_degree_swept": 8,
            "configurations_per_degree": 110,
            "quadratic_equality_trials": 60,
        },
        progress_class="mechanism_eliminated",
        decision_basis=(
            "The equality families, per-hub falsification, and least-value selection "
            "falsification are decided by explicit configurations; the admissible-hub "
            "inequality is finite evidence."
        ),
        next_analytic_target=(
            "Prove the stronger multiplicity-aware admissible-hub charge "
            "sum_{|f(c)|<1} L(c) <= 2R times the admissible critical multiplicity, "
            "which immediately gives the required admissible minimum <= 2R. "
            "The exact tangent-support identity in CriticalTreeLengthCharge.md reduces "
            "this to controlling the summed signed curvature-support terms."
        ),
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    payload["experiment_contract"] = contract
    payload["sources"] = [
        source_record(REPO_ROOT, SOURCE_REF),
        source_record(REPO_ROOT, ENGINE_REF),
    ]

    text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.print_only:
        print(text)
        return 0
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_suffix(output.suffix + ".tmp")
    temporary.write_text(text, encoding="utf-8")
    temporary.replace(output)
    print(f"wrote {output.relative_to(REPO_ROOT)}")
    print(
        "  quadratic equality: "
        f"{payload['quadratic_equality_family']['quadratics_checked']} checked, max "
        f"deviation {payload['quadratic_equality_family']['maximum_deviation_from_equality']:.2e}"
    )
    witness = payload["per_hub_falsifying_witness"]
    print(
        f"  per-hub witness: ratio {witness['per_hub_ratio']:.9f} > 1, max|root| "
        f"{witness['maximum_root_modulus']:.6f}, admissible-minimum ratio there "
        f"{witness['admissible_minimum_ratio_at_this_configuration']:.6f}"
    )
    for row in payload["sampled_sweep"]:
        print(
            f"  degree {row['degree']}: max admissible-minimum ratio "
            f"{row['maximum_admissible_minimum_ratio']:.6f}; max per-hub ratio "
            f"{row['maximum_per_hub_ratio']:.6f} ({row['per_hub_failures']} failures); "
            f"max aggregate {row['maximum_admissible_aggregate_ratio']:.6f}; "
            f"min root-star charge/R {row['minimum_root_star_charge_over_R']:.6f}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
