#!/usr/bin/env python3
"""Probe the admissible critical-arc product conjecture for Erdős 1041.

The continuation and arclength computations are floating-point evidence only.
The exact conjectural ratio for a simple polynomial is

    prod_{|f(c)|<1} L(c) / (2^m prod_{|f(c)|<1}|f(c)|^(1/n)).

A value above one is a numerical falsifier candidate.  Survival is not a proof.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
from dataclasses import dataclass
from pathlib import Path

import numpy as np

from system.lib.formal_math_lemniscate import merging_pair_tree


def _load_singleton_lab():
    source = Path(__file__).with_name(
        "check_erdos1041_adaptive_cluster_selection.py"
    )
    spec = importlib.util.spec_from_file_location("adaptive_singleton", source)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {source}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


SINGLETON = _load_singleton_lab()


@dataclass(frozen=True)
class AdmissibleDiagnostics:
    product_ratio: float
    max_factor: float
    count: int
    min_factor: float
    ascending_prefix_max_log: float
    ascending_prefix_max_index: int
    ascending_prefix_next_log: float
    ascending_prefix_next_scale_gap: float
    descending_prefix_max_log: float
    linearized_charge_bridge_margin: float
    arithmetic_bridge_ratio: float


def _circumcircle(a: complex, b: complex, c: complex) -> tuple[complex, float] | None:
    matrix = np.array(
        [
            [2.0 * (b.real - a.real), 2.0 * (b.imag - a.imag)],
            [2.0 * (c.real - a.real), 2.0 * (c.imag - a.imag)],
        ],
        dtype=float,
    )
    determinant = float(np.linalg.det(matrix))
    if abs(determinant) < 1.0e-12:
        return None
    target = np.array(
        [abs(b) ** 2 - abs(a) ** 2, abs(c) ** 2 - abs(a) ** 2],
        dtype=float,
    )
    coordinates = np.linalg.solve(matrix, target)
    center = complex(float(coordinates[0]), float(coordinates[1]))
    return center, max(abs(center - a), abs(center - b), abs(center - c))


def minimum_enclosing_radius(roots: np.ndarray) -> float:
    """Return the brute-force planar minimum-enclosing-circle radius."""

    candidates: list[tuple[complex, float]] = [(complex(root), 0.0) for root in roots]
    for left in range(len(roots)):
        for right in range(left + 1, len(roots)):
            center = complex((roots[left] + roots[right]) / 2.0)
            candidates.append((center, abs(roots[left] - roots[right]) / 2.0))
    for first in range(len(roots)):
        for second in range(first + 1, len(roots)):
            for third in range(second + 1, len(roots)):
                candidate = _circumcircle(
                    complex(roots[first]), complex(roots[second]), complex(roots[third])
                )
                if candidate is not None:
                    candidates.append(candidate)

    admissible = [
        radius
        for center, radius in candidates
        if max(abs(complex(root) - center) for root in roots) <= radius + 1.0e-9
    ]
    if not admissible:
        raise AssertionError("minimum enclosing circle candidate set was empty")
    return min(admissible)


def controlled_near_regular_shells() -> list[tuple[int, str, int, np.ndarray]]:
    rows: list[tuple[int, str, int, np.ndarray]] = []
    for degree in range(3, 8):
        base = 2.0 * np.pi * np.arange(degree) / degree
        for index, epsilon in enumerate((1.0e-2, 3.0e-3, 1.0e-3)):
            angles = base + epsilon * np.cos(base + 0.37)
            roots = 0.995 * np.exp(1j * angles)
            rows.append((degree, "controlled_near_regular", index, roots))
    return rows


def pinned_near_tie_quartic() -> list[tuple[int, str, int, np.ndarray]]:
    """Return the source-current strong-first-prefix falsifier.

    The normalized polynomial is the PIN arm of
    ``check_erdos1041_affine_normalised_moduli.py``.  Its constant term is one,
    so we similarity-scale its roots into the open unit disk.  The normalized
    factors ``L(c)/(2|f(c)|^(1/n))`` are unchanged by that scaling.
    """

    coefficients = np.array(
        [
            1.0 + 0.0j,
            -0.199341957743 - 0.409216378485j,
            -0.000225877943 + 0.000866621978j,
            0.0 + 0.0j,
            1.0 + 0.0j,
        ]
    )
    roots = np.roots(coefficients)
    roots *= 0.995 / max(abs(root) for root in roots)
    return [(4, "pinned_near_tie_prefix_falsifier", 0, roots)]


def admissible_diagnostics(
    roots: np.ndarray,
    *,
    stem_steps: int,
    circle_steps: int,
) -> AdmissibleDiagnostics:
    coefficients = np.poly(roots)
    critical_points = np.roots(np.polyder(coefficients))
    critical_values = np.polyval(coefficients, critical_points)
    logarithms: list[float] = []
    normalized_factors: list[float] = []
    factor_rows: list[tuple[float, float, float]] = []
    degree = len(roots)

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
        if separation <= 0.0:
            raise AssertionError("critical values were not numerically separated")
        radius = max(1.0e-12, 0.001 * separation)
        length = SINGLETON.singleton_lollipop_mean(
            roots,
            complex(value),
            radius,
            stem_steps=stem_steps,
            circle_steps=circle_steps,
        )
        factor = length / (2.0 * abs(value) ** (1.0 / degree))
        scale = abs(value) ** (1.0 / degree)
        normalized_factors.append(factor)
        logarithms.append(math.log(factor))
        factor_rows.append((scale, factor, length))

    if not logarithms:
        raise AssertionError("configuration has no admissible critical point")
    ascending_log = 0.0
    ascending_prefixes: list[tuple[float, int]] = []
    ordered_factor_rows = sorted(factor_rows)
    for index, (_, factor, _) in enumerate(ordered_factor_rows, start=1):
        ascending_log += math.log(factor)
        ascending_prefixes.append((ascending_log, index))
    descending_log = 0.0
    descending_prefixes: list[float] = []
    for _, factor, _ in sorted(factor_rows, reverse=True):
        descending_log += math.log(factor)
        descending_prefixes.append(descending_log)

    radius = minimum_enclosing_radius(roots)
    charge_units = sum(1.0 - length / (2.0 * radius) for _, _, length in factor_rows)
    log_scale_deficit = sum(math.log(radius / scale) for scale, _, _ in factor_rows)
    geometric_scale = math.exp(
        sum(math.log(scale) for scale, _, _ in factor_rows) / len(factor_rows)
    )
    arithmetic_bridge_ratio = sum(length for _, _, length in factor_rows) / (
        2.0 * len(factor_rows) * geometric_scale
    )
    max_prefix_log, max_prefix_index = max(ascending_prefixes)
    if max_prefix_index < len(ascending_prefixes):
        next_prefix_log = ascending_prefixes[max_prefix_index][0]
        left_scale = ordered_factor_rows[max_prefix_index - 1][0]
        right_scale = ordered_factor_rows[max_prefix_index][0]
        next_scale_gap = right_scale / left_scale - 1.0
    else:
        next_prefix_log = float("nan")
        next_scale_gap = float("nan")
    return AdmissibleDiagnostics(
        product_ratio=math.exp(sum(logarithms)),
        max_factor=max(normalized_factors),
        count=len(logarithms),
        min_factor=min(normalized_factors),
        ascending_prefix_max_log=max_prefix_log,
        ascending_prefix_max_index=max_prefix_index,
        ascending_prefix_next_log=next_prefix_log,
        ascending_prefix_next_scale_gap=next_scale_gap,
        descending_prefix_max_log=max(descending_prefixes),
        linearized_charge_bridge_margin=charge_units - log_scale_deficit,
        arithmetic_bridge_ratio=arithmetic_bridge_ratio,
    )


def product_row(
    roots: np.ndarray,
    *,
    stem_steps: int,
    circle_steps: int,
) -> tuple[float, float, int, float]:
    diagnostics = admissible_diagnostics(
        roots, stem_steps=stem_steps, circle_steps=circle_steps
    )
    return (
        diagnostics.product_ratio,
        diagnostics.max_factor,
        diagnostics.count,
        diagnostics.min_factor,
    )


def inadmissible_complement_row(
    roots: np.ndarray,
    *,
    stem_steps: int,
    circle_steps: int,
) -> tuple[float, float, int, float] | None:
    coefficients = np.poly(roots)
    critical_points = np.roots(np.polyder(coefficients))
    critical_values = np.polyval(coefficients, critical_points)
    logarithms: list[float] = []
    normalized_factors: list[float] = []
    degree = len(roots)

    for index, value in enumerate(critical_values):
        if abs(value) < 1.0:
            continue
        separation = min(
            [
                abs(value),
                *[
                    abs(value - other)
                    for other_index, other in enumerate(critical_values)
                    if other_index != index
                ],
            ]
        )
        if separation <= 0.0:
            raise AssertionError("critical values were not numerically separated")
        radius = max(1.0e-12, 0.001 * separation)
        length = SINGLETON.singleton_lollipop_mean(
            roots,
            complex(value),
            radius,
            stem_steps=stem_steps,
            circle_steps=circle_steps,
        )
        factor = length / (2.0 * abs(value) ** (1.0 / degree))
        normalized_factors.append(factor)
        logarithms.append(math.log(factor))

    if not logarithms:
        return None
    return (
        math.exp(sum(logarithms)),
        max(normalized_factors),
        len(logarithms),
        min(normalized_factors),
    )


def merge_subtree_block_diagnostics(roots: np.ndarray) -> dict[str, float | int]:
    """Evaluate the exact merge-tree normalization with numerical lengths.

    If ``v`` is an admissible merge node, ``k_v`` its descendant-root count,
    and ``r_v`` its level divided by the next admissible ancestor level (or by
    the virtual cut level one), put

        h_v = (L(v)/2) / r_v^((k_v-1)/n).

    The truncated merge-tree product identity makes the product of all ``h_v``
    exactly the full admissible product.  This routine also tests the stronger
    candidate that the product over every complete rooted merger subtree is at
    most one.  Lengths remain floating-point continuation evidence.
    """

    degree = len(roots)
    merge_rows = merging_pair_tree(roots)
    if merge_rows is None or len(merge_rows) != degree - 1:
        raise AssertionError("complete merge tree was not recovered")

    nodes: dict[int, dict[str, object]] = {
        index: {
            "size": 1,
            "birth": 0.0,
            "parent": None,
            "length": None,
            "children": [],
        }
        for index in range(degree)
    }
    union_find = list(range(degree))
    active = {index: index for index in range(degree)}
    created: list[int] = []

    def find(index: int) -> int:
        while union_find[index] != index:
            union_find[index] = union_find[union_find[index]]
            index = union_find[index]
        return index

    for row in merge_rows:
        left_root, right_root = map(int, row["root_pair"])
        left_component = find(left_root)
        right_component = find(right_root)
        if left_component == right_component:
            raise AssertionError("merge row joined an already connected component")
        left_node = active[left_component]
        right_node = active[right_component]
        node = degree + len(created)
        nodes[node] = {
            "size": int(nodes[left_node]["size"]) + int(nodes[right_node]["size"]),
            "birth": float(row["critical_value_modulus"]),
            "parent": None,
            "length": float(row["total_length"]),
            "children": [left_node, right_node],
        }
        nodes[left_node]["parent"] = node
        nodes[right_node]["parent"] = node
        union_find[right_component] = left_component
        active[left_component] = node
        del active[right_component]
        created.append(node)

    node_factors: dict[int, float] = {}
    parent_levels: dict[int, float] = {}
    direct_product = 1.0
    for node in created:
        birth = float(nodes[node]["birth"])
        if birth >= 1.0:
            continue
        parent = nodes[node]["parent"]
        if parent is None or float(nodes[int(parent)]["birth"]) >= 1.0:
            parent_level = 1.0
        else:
            parent_level = float(nodes[int(parent)]["birth"])
        parent_levels[node] = parent_level
        size = int(nodes[node]["size"])
        length = float(nodes[node]["length"])
        node_factors[node] = (length / 2.0) / (
            (birth / parent_level) ** ((size - 1.0) / degree)
        )
        direct_product *= (length / 2.0) / (birth ** (1.0 / degree))

    subtree_products: dict[int, float] = {}
    for node in created:
        if node not in node_factors:
            continue
        product = node_factors[node]
        for child in nodes[node]["children"]:
            child_index = int(child)
            if child_index in subtree_products:
                product *= subtree_products[child_index]
        subtree_products[node] = product

    block_product = math.prod(node_factors.values())
    cherry_nodes = [
        node for node in node_factors if int(nodes[node]["size"]) == 2
    ]
    grafting_nodes = [
        node for node in node_factors if int(nodes[node]["size"]) > 2
    ]
    cherry_bergman_costs = []
    for node in cherry_nodes:
        birth = float(nodes[node]["birth"])
        parent_level = parent_levels[node]
        ratio = birth / parent_level
        cherry_bergman_costs.append(
            parent_level ** (2.0 / degree)
            * math.log((1.0 + ratio) / (1.0 - ratio))
            / (2.0 * ((degree - 1.0) * ratio) ** (2.0 / degree))
        )
    cherry_bergman_cost_by_node = dict(zip(cherry_nodes, cherry_bergman_costs))
    uncertified_cherry_nodes = [
        node
        for node in cherry_nodes
        if cherry_bergman_cost_by_node[node] > 1.0
    ]
    uncertified_internal_cherry_nodes = [
        node
        for node in uncertified_cherry_nodes
        if nodes[node]["parent"] is not None
        and int(nodes[node]["parent"]) in node_factors
    ]
    uncertified_virtual_cut_cherry_nodes = [
        node
        for node in uncertified_cherry_nodes
        if node not in uncertified_internal_cherry_nodes
    ]
    identity_relative_error = abs(block_product - direct_product) / max(
        direct_product, 1.0e-300
    )
    return {
        "admissible_node_count": len(node_factors),
        "node_factor_gt_one_count": sum(value > 1.0 for value in node_factors.values()),
        "largest_node_factor": max(node_factors.values(), default=0.0),
        "cherry_count": len(cherry_nodes),
        "cherry_violation_count": sum(
            node_factors[node] > 1.0 + 1.0e-8 for node in cherry_nodes
        ),
        "largest_cherry_product": max(
            (node_factors[node] for node in cherry_nodes), default=0.0
        ),
        "bergman_certified_cherry_count": sum(
            cost <= 1.0 for cost in cherry_bergman_costs
        ),
        "bergman_uncertified_cherry_count": sum(
            cost > 1.0 for cost in cherry_bergman_costs
        ),
        "bergman_uncertified_internal_cherry_count": len(
            uncertified_internal_cherry_nodes
        ),
        "bergman_uncertified_virtual_cut_cherry_count": len(
            uncertified_virtual_cut_cherry_nodes
        ),
        "largest_uncertified_internal_cherry_product": max(
            (node_factors[node] for node in uncertified_internal_cherry_nodes),
            default=0.0,
        ),
        "largest_uncertified_virtual_cut_cherry_product": max(
            (node_factors[node] for node in uncertified_virtual_cut_cherry_nodes),
            default=0.0,
        ),
        "largest_cherry_bergman_cost": max(cherry_bergman_costs, default=0.0),
        "grafting_count": len(grafting_nodes),
        "grafting_violation_count": sum(
            subtree_products[node] > 1.0 + 1.0e-8 for node in grafting_nodes
        ),
        "largest_grafting_product": max(
            (subtree_products[node] for node in grafting_nodes), default=0.0
        ),
        "node_overspend_repaid_by_descendants_count": sum(
            node_factors[node] > 1.0
            and subtree_products[node] <= 1.0 + 1.0e-8
            for node in grafting_nodes
        ),
        "subtree_count": len(subtree_products),
        "subtree_violation_count": sum(
            value > 1.0 + 1.0e-8 for value in subtree_products.values()
        ),
        "largest_subtree_product": max(subtree_products.values(), default=0.0),
        "full_block_product": block_product,
        "direct_product": direct_product,
        "identity_relative_error": identity_relative_error,
    }


def run_deterministic_subtree_stress() -> None:
    """Run a wider fixed-seed falsifier search for the rooted-subtree bound."""

    rng = np.random.default_rng(104120260828)
    rows: list[tuple[float, int, str, int, float, float, int]] = []
    diagnostic_rows: list[dict[str, float | int]] = []
    families = (
        "random_disk",
        "random_shell",
        "near_regular",
        "multi_cluster",
        "near_collinear",
    )
    for degree in range(3, 11):
        for family in families:
            for repetition in range(20):
                if family == "random_disk":
                    roots = np.sqrt(rng.random(degree)) * np.exp(
                        2j * np.pi * rng.random(degree)
                    )
                elif family == "random_shell":
                    roots = (0.85 + 0.145 * rng.random(degree)) * np.exp(
                        2j * np.pi * rng.random(degree)
                    )
                elif family == "near_regular":
                    epsilon = 10.0 ** rng.uniform(-5.0, -0.5)
                    angles = (
                        2.0 * np.pi * np.arange(degree) / degree
                        + epsilon * rng.normal(size=degree)
                    )
                    roots = 0.995 * np.exp(1j * angles)
                elif family == "multi_cluster":
                    cluster_count = int(rng.integers(2, min(4, degree) + 1))
                    centers = 0.65 * np.exp(
                        2j * np.pi * rng.random(cluster_count)
                    )
                    roots = np.array(
                        [
                            centers[index % cluster_count]
                            + 0.18 * (rng.normal() + 1j * rng.normal())
                            for index in range(degree)
                        ]
                    )
                else:
                    roots = rng.uniform(-0.98, 0.98, degree) + 1j * (
                        10.0 ** rng.uniform(-5.0, -1.0)
                    ) * rng.normal(size=degree)
                maximum_radius = max(abs(root) for root in roots)
                if maximum_radius >= 0.999:
                    roots *= 0.995 / maximum_radius
                diagnostics = merge_subtree_block_diagnostics(roots)
                diagnostic_rows.append(diagnostics)
                rows.append(
                    (
                        float(diagnostics["largest_subtree_product"]),
                        degree,
                        family,
                        repetition,
                        float(diagnostics["largest_node_factor"]),
                        float(diagnostics["full_block_product"]),
                        int(diagnostics["subtree_violation_count"]),
                    )
                )
    rows.sort(reverse=True)
    violation_count = sum(row[6] > 0 for row in rows)
    cherry_count = sum(int(row["cherry_count"]) for row in diagnostic_rows)
    cherry_violation_count = sum(
        int(row["cherry_violation_count"]) for row in diagnostic_rows
    )
    certified_cherry_count = sum(
        int(row["bergman_certified_cherry_count"]) for row in diagnostic_rows
    )
    uncertified_internal_cherry_count = sum(
        int(row["bergman_uncertified_internal_cherry_count"])
        for row in diagnostic_rows
    )
    uncertified_virtual_cut_cherry_count = sum(
        int(row["bergman_uncertified_virtual_cut_cherry_count"])
        for row in diagnostic_rows
    )
    largest_uncertified_virtual_cut_cherry_product = max(
        float(row["largest_uncertified_virtual_cut_cherry_product"])
        for row in diagnostic_rows
    )
    grafting_count = sum(int(row["grafting_count"]) for row in diagnostic_rows)
    grafting_violation_count = sum(
        int(row["grafting_violation_count"]) for row in diagnostic_rows
    )
    assert len(rows) == 800
    assert violation_count == 0
    assert cherry_violation_count == 0
    assert grafting_violation_count == 0
    assert (
        uncertified_internal_cherry_count
        + uncertified_virtual_cut_cherry_count
        == cherry_count - certified_cherry_count
    )
    assert uncertified_virtual_cut_cherry_count == 2
    assert largest_uncertified_virtual_cut_cherry_product < 1.0
    assert rows[0][0] > 0.998
    assert rows[0][0] < 1.0
    print("MERGE-SUBTREE STRESS: PASS (NUMERICAL EVIDENCE ONLY)")
    print(f"stress_configuration_count={len(rows)}")
    print(f"stress_subtree_violation_configuration_count={violation_count}")
    print(f"stress_cherry_count={cherry_count}")
    print(f"stress_cherry_violation_count={cherry_violation_count}")
    print(f"stress_bergman_certified_cherry_count={certified_cherry_count}")
    print(
        "stress_bergman_uncertified_cherry_count="
        f"{cherry_count-certified_cherry_count}"
    )
    print(
        "stress_bergman_uncertified_internal_cherry_count="
        f"{uncertified_internal_cherry_count}"
    )
    print(
        "stress_bergman_uncertified_virtual_cut_cherry_count="
        f"{uncertified_virtual_cut_cherry_count}"
    )
    print(
        "stress_largest_uncertified_virtual_cut_cherry_product="
        f"{largest_uncertified_virtual_cut_cherry_product:.12f}"
    )
    print(f"stress_grafting_count={grafting_count}")
    print(f"stress_grafting_violation_count={grafting_violation_count}")
    print(
        "stress_largest_subtree_product="
        f"{rows[0][0]:.12f} degree={rows[0][1]} family={rows[0][2]} "
        f"repetition={rows[0][3]} largest_node_factor={rows[0][4]:.12f} "
        f"full_product={rows[0][5]:.12f}"
    )


def main() -> None:
    configurations = [
        *SINGLETON.generated_configurations(),
        *controlled_near_regular_shells(),
        *pinned_near_tie_quartic(),
    ]
    coarse_rows = []
    complement_rows = []
    subtree_block_rows = []
    for degree, family, repetition, roots in configurations:
        diagnostics = admissible_diagnostics(
            roots, stem_steps=60, circle_steps=120
        )
        coarse_rows.append(
            (
                diagnostics.product_ratio,
                diagnostics.max_factor,
                degree,
                family,
                repetition,
                diagnostics.count,
                diagnostics.min_factor,
                roots,
                diagnostics.ascending_prefix_max_log,
                diagnostics.ascending_prefix_max_index,
                diagnostics.descending_prefix_max_log,
                diagnostics.linearized_charge_bridge_margin,
                diagnostics.arithmetic_bridge_ratio,
            )
        )
        complement = inadmissible_complement_row(
            roots, stem_steps=60, circle_steps=120
        )
        if complement is not None:
            complement_rows.append(
                (
                    complement[0],
                    complement[1],
                    degree,
                    family,
                    repetition,
                    complement[2],
                    complement[3],
                    roots,
                )
            )
        subtree_block_rows.append(
            (
                merge_subtree_block_diagnostics(roots),
                degree,
                family,
                repetition,
            )
        )
    coarse_rows.sort(reverse=True, key=lambda row: row[0])

    fine_rows = []
    for coarse in coarse_rows[:8]:
        _, _, degree, family, repetition, _, _, roots, *_ = coarse
        diagnostics = admissible_diagnostics(
            roots, stem_steps=360, circle_steps=720
        )
        fine_rows.append(
            (
                diagnostics.product_ratio,
                diagnostics.max_factor,
                degree,
                family,
                repetition,
                diagnostics.count,
                diagnostics.min_factor,
                diagnostics.ascending_prefix_max_log,
                diagnostics.ascending_prefix_max_index,
            )
        )
    fine_rows.sort(reverse=True, key=lambda row: row[0])
    complement_rows.sort(key=lambda row: row[0])
    complement_fine_rows = []
    for coarse in complement_rows[:3]:
        _, _, degree, family, repetition, _, _, roots = coarse
        refined = inadmissible_complement_row(
            roots, stem_steps=800, circle_steps=1600
        )
        if refined is None:
            raise AssertionError("inadmissible complement disappeared on replay")
        complement_fine_rows.append(
            (
                refined[0],
                refined[1],
                degree,
                family,
                repetition,
                refined[2],
                refined[3],
            )
        )
    complement_fine_rows.sort(key=lambda row: row[0])

    worst_coarse = coarse_rows[0]
    worst_fine = fine_rows[0]
    largest_factor = max(coarse_rows, key=lambda row: row[1])
    (
        largest_factor_fine_ratio,
        largest_factor_fine,
        largest_factor_fine_count,
        _,
    ) = product_row(
        largest_factor[7], stem_steps=800, circle_steps=1600
    )
    factorwise_failures = sum(row[1] > 1.0 for row in coarse_rows)
    product_violations = sum(row[0] > 1.0 for row in coarse_rows)
    compensation_failures = sum(row[0] < 1.0 for row in complement_rows)
    descending_prefix_violations = sum(row[10] > 1.0e-10 for row in coarse_rows)
    linearized_charge_bridge_failures = sum(row[11] < 0.0 for row in coarse_rows)
    arithmetic_bridge_failures = sum(row[12] > 1.0 for row in coarse_rows)
    subtree_count = sum(int(row[0]["subtree_count"]) for row in subtree_block_rows)
    subtree_violations = sum(
        int(row[0]["subtree_violation_count"]) for row in subtree_block_rows
    )
    node_factor_gt_one_count = sum(
        int(row[0]["node_factor_gt_one_count"]) for row in subtree_block_rows
    )
    configurations_with_node_factor_gt_one = sum(
        int(row[0]["node_factor_gt_one_count"]) > 0 for row in subtree_block_rows
    )
    cherry_count = sum(int(row[0]["cherry_count"]) for row in subtree_block_rows)
    cherry_violations = sum(
        int(row[0]["cherry_violation_count"]) for row in subtree_block_rows
    )
    bergman_certified_cherries = sum(
        int(row[0]["bergman_certified_cherry_count"])
        for row in subtree_block_rows
    )
    bergman_uncertified_cherries = sum(
        int(row[0]["bergman_uncertified_cherry_count"])
        for row in subtree_block_rows
    )
    bergman_uncertified_internal_cherries = sum(
        int(row[0]["bergman_uncertified_internal_cherry_count"])
        for row in subtree_block_rows
    )
    bergman_uncertified_virtual_cut_cherries = sum(
        int(row[0]["bergman_uncertified_virtual_cut_cherry_count"])
        for row in subtree_block_rows
    )
    largest_uncertified_virtual_cut_cherry_product = max(
        float(row[0]["largest_uncertified_virtual_cut_cherry_product"])
        for row in subtree_block_rows
    )
    largest_cherry_row = max(
        subtree_block_rows, key=lambda row: float(row[0]["largest_cherry_product"])
    )
    grafting_count = sum(
        int(row[0]["grafting_count"]) for row in subtree_block_rows
    )
    grafting_violations = sum(
        int(row[0]["grafting_violation_count"]) for row in subtree_block_rows
    )
    overspend_repaid_count = sum(
        int(row[0]["node_overspend_repaid_by_descendants_count"])
        for row in subtree_block_rows
    )
    largest_node_factor_row = max(
        subtree_block_rows, key=lambda row: float(row[0]["largest_node_factor"])
    )
    largest_subtree_row = max(
        subtree_block_rows, key=lambda row: float(row[0]["largest_subtree_product"])
    )
    block_identity_max_relative_error = max(
        float(row[0]["identity_relative_error"]) for row in subtree_block_rows
    )
    pinned_subtree_row = next(
        row
        for row in subtree_block_rows
        if row[2] == "pinned_near_tie_prefix_falsifier"
    )

    filtration_boundary = next(
        row for row in coarse_rows if row[3] == "pinned_near_tie_prefix_falsifier"
    )
    filtration_boundary_fine = admissible_diagnostics(
        filtration_boundary[7], stem_steps=6000, circle_steps=1600
    )
    factorwise_failures = sum(
        row[1] > 1.0
        for row in coarse_rows
        if row[3] != "pinned_near_tie_prefix_falsifier"
    ) + int(filtration_boundary_fine.max_factor > 1.0)
    ascending_prefix_violations = sum(
        row[8] > 1.0e-10
        for row in coarse_rows
        if row[3] != "pinned_near_tie_prefix_falsifier"
    ) + int(filtration_boundary_fine.ascending_prefix_max_log > 1.0e-10)
    linearized_bridge_failure = min(coarse_rows, key=lambda row: row[11])
    linearized_bridge_failure_fine = admissible_diagnostics(
        linearized_bridge_failure[7], stem_steps=800, circle_steps=1600
    )

    assert len(configurations) == 270
    assert product_violations == 0
    assert worst_coarse[0] < 1.0
    assert worst_fine[0] < 1.0
    assert factorwise_failures > 0
    assert largest_factor[1] > 1.001
    assert largest_factor_fine > 1.05
    assert len(complement_rows) == 62
    assert compensation_failures >= 50
    assert complement_fine_rows[0][0] < 0.4
    assert ascending_prefix_violations > 0
    assert filtration_boundary[3] == "pinned_near_tie_prefix_falsifier"
    assert filtration_boundary_fine.ascending_prefix_max_log > 0.002
    assert filtration_boundary_fine.product_ratio < 0.9
    assert descending_prefix_violations > 0
    assert linearized_charge_bridge_failures > 0
    assert linearized_bridge_failure_fine.linearized_charge_bridge_margin < -1.0
    assert arithmetic_bridge_failures > 0
    assert subtree_count > 1000
    assert subtree_violations == 0
    assert cherry_count > 400
    assert cherry_violations == 0
    assert bergman_certified_cherries > 300
    assert bergman_uncertified_cherries > 100
    assert (
        bergman_uncertified_internal_cherries
        + bergman_uncertified_virtual_cut_cherries
        == bergman_uncertified_cherries
    )
    assert bergman_uncertified_internal_cherries == bergman_uncertified_cherries
    assert bergman_uncertified_virtual_cut_cherries == 0
    assert largest_uncertified_virtual_cut_cherry_product == 0.0
    assert float(largest_cherry_row[0]["largest_cherry_product"]) > 0.98
    assert grafting_count > 800
    assert grafting_violations == 0
    assert overspend_repaid_count > 100
    assert configurations_with_node_factor_gt_one > 100
    assert node_factor_gt_one_count > configurations_with_node_factor_gt_one
    assert float(largest_node_factor_row[0]["largest_node_factor"]) > 5.0
    assert float(largest_subtree_row[0]["largest_subtree_product"]) < 1.0
    assert block_identity_max_relative_error < 1.0e-12
    assert float(pinned_subtree_row[0]["largest_subtree_product"]) < 1.0

    print("ADMISSIBLE CRITICAL-ARC PRODUCT: PASS (NUMERICAL EVIDENCE ONLY)")
    print(f"configuration_count={len(configurations)}")
    print(f"product_violation_count={product_violations}")
    print(f"factorwise_q_gt_one_configuration_count={factorwise_failures}")
    print(f"configuration_count_with_inadmissible_critical_points={len(complement_rows)}")
    print(f"inadmissible_compensation_product_below_one_count={compensation_failures}")
    print(f"ascending_critical_scale_prefix_violation_count={ascending_prefix_violations}")
    print(f"descending_critical_scale_prefix_violation_count={descending_prefix_violations}")
    print(f"linearized_charge_bridge_failure_count={linearized_charge_bridge_failures}")
    print(f"arithmetic_bridge_failure_count={arithmetic_bridge_failures}")
    print(f"admissible_merge_subtree_count={subtree_count}")
    print(f"merge_subtree_product_violation_count={subtree_violations}")
    print(f"admissible_cherry_count={cherry_count}")
    print(f"admissible_cherry_violation_count={cherry_violations}")
    print(f"bergman_certified_cherry_count={bergman_certified_cherries}")
    print(f"bergman_uncertified_cherry_count={bergman_uncertified_cherries}")
    print(
        "bergman_uncertified_internal_cherry_count="
        f"{bergman_uncertified_internal_cherries}"
    )
    print(
        "bergman_uncertified_virtual_cut_cherry_count="
        f"{bergman_uncertified_virtual_cut_cherries}"
    )
    print(
        "largest_uncertified_virtual_cut_cherry_product="
        f"{largest_uncertified_virtual_cut_cherry_product:.12f}"
    )
    print(
        "largest_cherry_product="
        f"{float(largest_cherry_row[0]['largest_cherry_product']):.12f} "
        f"degree={largest_cherry_row[1]} family={largest_cherry_row[2]} "
        f"repetition={largest_cherry_row[3]}"
    )
    print(f"admissible_grafting_count={grafting_count}")
    print(f"admissible_grafting_violation_count={grafting_violations}")
    print(f"node_overspend_repaid_by_descendants_count={overspend_repaid_count}")
    print(f"node_block_factor_gt_one_count={node_factor_gt_one_count}")
    print(
        "configuration_count_with_node_block_factor_gt_one="
        f"{configurations_with_node_factor_gt_one}"
    )
    print(
        "largest_node_block_factor="
        f"{float(largest_node_factor_row[0]['largest_node_factor']):.12f} "
        f"degree={largest_node_factor_row[1]} family={largest_node_factor_row[2]} "
        f"repetition={largest_node_factor_row[3]} "
        f"full_product={float(largest_node_factor_row[0]['full_block_product']):.12f}"
    )
    print(
        "largest_merge_subtree_product="
        f"{float(largest_subtree_row[0]['largest_subtree_product']):.12f} "
        f"degree={largest_subtree_row[1]} family={largest_subtree_row[2]} "
        f"repetition={largest_subtree_row[3]} "
        f"full_product={float(largest_subtree_row[0]['full_block_product']):.12f}"
    )
    print(
        "pinned_merge_subtree_product="
        f"{float(pinned_subtree_row[0]['largest_subtree_product']):.12f} "
        f"largest_node_factor={float(pinned_subtree_row[0]['largest_node_factor']):.12f} "
        f"full_product={float(pinned_subtree_row[0]['full_block_product']):.12f}"
    )
    print(
        "merge_block_identity_max_relative_error="
        f"{block_identity_max_relative_error:.3e}"
    )
    print(
        "worst_coarse_product_ratio="
        f"{worst_coarse[0]:.12f} degree={worst_coarse[2]} "
        f"family={worst_coarse[3]} repetition={worst_coarse[4]} "
        f"admissible_count={worst_coarse[5]}"
    )
    print(
        "worst_fine_product_ratio="
        f"{worst_fine[0]:.12f} degree={worst_fine[2]} "
        f"family={worst_fine[3]} repetition={worst_fine[4]} "
        f"admissible_count={worst_fine[5]}"
    )
    print(
        "largest_single_q="
        f"{largest_factor[1]:.12f} degree={largest_factor[2]} "
        f"family={largest_factor[3]} repetition={largest_factor[4]} "
        f"product_ratio={largest_factor[0]:.12f}"
    )
    print(
        "largest_single_q_fine="
        f"{largest_factor_fine:.12f} degree={largest_factor[2]} "
        f"family={largest_factor[3]} repetition={largest_factor[4]} "
        f"admissible_count={largest_factor_fine_count} "
        f"product_ratio={largest_factor_fine_ratio:.12f}"
    )
    print(
        "filtration_prefix_fine_max_log="
        f"{filtration_boundary_fine.ascending_prefix_max_log:.12f} "
        f"prefix_index={filtration_boundary_fine.ascending_prefix_max_index} "
        f"next_prefix_log={filtration_boundary_fine.ascending_prefix_next_log:.12f} "
        f"next_scale_relative_gap="
        f"{filtration_boundary_fine.ascending_prefix_next_scale_gap:.12e} "
        f"full_product_ratio={filtration_boundary_fine.product_ratio:.12f} "
        f"degree={filtration_boundary[2]} family={filtration_boundary[3]} "
        f"repetition={filtration_boundary[4]}"
    )
    print(
        "linearized_charge_bridge_fine_margin="
        f"{linearized_bridge_failure_fine.linearized_charge_bridge_margin:.12f} "
        f"degree={linearized_bridge_failure[2]} family={linearized_bridge_failure[3]} "
        f"repetition={linearized_bridge_failure[4]} "
        f"product_ratio={linearized_bridge_failure_fine.product_ratio:.12f}"
    )
    for row in fine_rows:
        print(
            "fine_row="
            f"{row[0]:.12f} degree={row[2]} family={row[3]} "
            f"repetition={row[4]} admissible_count={row[5]} "
            f"max_q={row[1]:.12f} min_q={row[6]:.12f}"
        )
    for row in complement_fine_rows:
        print(
            "inadmissible_complement_fine_row="
            f"{row[0]:.12f} degree={row[2]} family={row[3]} "
            f"repetition={row[4]} inadmissible_count={row[5]} "
            f"max_q={row[1]:.12f} min_q={row[6]:.12f}"
        )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--stress-subtrees-only", action="store_true")
    arguments = parser.parse_args()
    if arguments.stress_subtrees_only:
        run_deterministic_subtree_stress()
    else:
        main()
