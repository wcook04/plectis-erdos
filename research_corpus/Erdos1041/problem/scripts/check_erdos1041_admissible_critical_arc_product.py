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
    arithmetic_mean_factor: float
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
        arithmetic_mean_factor=sum(normalized_factors) / len(normalized_factors),
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
    direct_factor_by_node: dict[int, float] = {}
    parent_levels: dict[int, float] = {}
    direct_factors: list[float] = []
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
        direct_factor = (length / 2.0) / (birth ** (1.0 / degree))
        direct_factor_by_node[node] = direct_factor
        direct_factors.append(direct_factor)
        direct_product *= direct_factor

    maximal_admissible_nodes = [
        node
        for node in direct_factor_by_node
        if nodes[node]["parent"] is None
        or int(nodes[node]["parent"]) not in direct_factor_by_node
    ]
    component_arithmetic_means: list[float] = []
    for root in maximal_admissible_nodes:
        stack = [root]
        component_factors: list[float] = []
        while stack:
            node = stack.pop()
            if node not in direct_factor_by_node:
                continue
            component_factors.append(direct_factor_by_node[node])
            stack.extend(int(child) for child in nodes[node]["children"])
        component_arithmetic_means.append(
            sum(component_factors) / len(component_factors)
        )

    # Test the topology-first induction strengthening of CAQ: every complete
    # admissible rooted merge subtree, not only each maximal level-one
    # component, has arithmetic mean of the direct q-factors at most one.
    # This is deliberately independent of the multiplicative ``h_v`` subtree
    # probe below.  A failure identifies the exact point where any naive
    # bottom-up arithmetic induction must carry debt through an ancestor.
    subtree_arithmetic_means: dict[int, float] = {}
    subtree_arithmetic_sizes: dict[int, int] = {}
    for node in created:
        if node not in direct_factor_by_node:
            continue
        factor_sum = direct_factor_by_node[node]
        factor_count = 1
        for child in nodes[node]["children"]:
            child_index = int(child)
            if child_index in subtree_arithmetic_means:
                factor_sum += (
                    subtree_arithmetic_means[child_index]
                    * subtree_arithmetic_sizes[child_index]
                )
                factor_count += subtree_arithmetic_sizes[child_index]
        subtree_arithmetic_means[node] = factor_sum / factor_count
        subtree_arithmetic_sizes[node] = factor_count

    largest_subtree_arithmetic_node = max(
        subtree_arithmetic_means,
        key=subtree_arithmetic_means.__getitem__,
        default=None,
    )
    cut_scaled_subtree_arithmetic_means = {
        node: parent_levels[node] ** (1.0 / degree) * mean
        for node, mean in subtree_arithmetic_means.items()
    }
    largest_cut_scaled_subtree_arithmetic_node = max(
        cut_scaled_subtree_arithmetic_means,
        key=cut_scaled_subtree_arithmetic_means.__getitem__,
        default=None,
    )
    cut_scaled_subtree_slacks = {
        node: subtree_arithmetic_sizes[node]
        * (1.0 - cut_scaled_subtree_arithmetic_means[node])
        for node in cut_scaled_subtree_arithmetic_means
    }
    graft_debts: dict[int, float] = {}
    graft_recurrence_errors: list[float] = []
    child_slack_minus_graft_debt: dict[int, float] = {}
    child_slack_minus_convexity_gap: dict[int, float] = {}
    child_slack_minus_local_overspend: dict[int, float] = {}
    half_child_slack_minus_convexity_gap: dict[int, float] = {}
    half_child_slack_minus_local_overspend: dict[int, float] = {}
    child_slack_minus_positive_liabilities: dict[int, float] = {}
    convexity_slack_ratios: list[float] = []
    overspend_slack_ratios: list[float] = []
    combined_liability_slack_ratios: list[float] = []
    for node in cut_scaled_subtree_arithmetic_means:
        birth = float(nodes[node]["birth"])
        parent_level = parent_levels[node]
        node_count = subtree_arithmetic_sizes[node]
        scale_ratio = (birth / parent_level) ** (1.0 / degree)
        graft_debt = (
            float(nodes[node]["length"]) / 2.0
            + node_count
            - 1.0
            - node_count * scale_ratio
        )
        convexity_gap = scale_ratio**node_count - (
            node_count * scale_ratio - node_count + 1.0
        )
        local_overspend = max(
            0.0,
            float(nodes[node]["length"]) / 2.0 - scale_ratio**node_count,
        )
        child_slack = sum(
            cut_scaled_subtree_slacks[int(child)]
            for child in nodes[node]["children"]
            if int(child) in cut_scaled_subtree_slacks
        )
        alpha = 1.0 / scale_ratio
        graft_debts[node] = graft_debt
        child_slack_minus_graft_debt[node] = child_slack - graft_debt
        child_slack_minus_convexity_gap[node] = child_slack - convexity_gap
        child_slack_minus_local_overspend[node] = child_slack - local_overspend
        half_child_slack_minus_convexity_gap[node] = (
            0.5 * child_slack - convexity_gap
        )
        half_child_slack_minus_local_overspend[node] = (
            0.5 * child_slack - local_overspend
        )
        child_slack_minus_positive_liabilities[node] = (
            child_slack - convexity_gap - local_overspend
        )
        if child_slack > 1.0e-12:
            convexity_slack_ratios.append(convexity_gap / child_slack)
            overspend_slack_ratios.append(local_overspend / child_slack)
            combined_liability_slack_ratios.append(
                (convexity_gap + local_overspend) / child_slack
            )
        graft_recurrence_errors.append(
            abs(
                cut_scaled_subtree_slacks[node]
                - alpha * (child_slack - graft_debt)
            )
        )

    ordered_direct_nodes = sorted(
        direct_factor_by_node, key=lambda node: float(nodes[node]["birth"])
    )
    adjacent_repayment_failures: list[float] = []
    for index, node in enumerate(ordered_direct_nodes):
        factor = direct_factor_by_node[node]
        if factor <= 1.0 + 1.0e-8:
            continue
        if index + 1 == len(ordered_direct_nodes):
            adjacent_repayment_failures.append(factor)
            continue
        next_factor = direct_factor_by_node[ordered_direct_nodes[index + 1]]
        pair_mean = (factor + next_factor) / 2.0
        if pair_mean > 1.0 + 1.0e-8:
            adjacent_repayment_failures.append(pair_mean)

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
    certified_cherry_nodes = [
        node for node in cherry_nodes if cherry_bergman_cost_by_node[node] <= 1.0
    ]
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
    # Replace every certified cherry's numerically integrated factor by the
    # rigorous Bergman--Polya upper bound sqrt(cost).  Leave all other nodes at
    # their measured factor.  This hybrid is not a proof—the grafting factors
    # remain numerical—but it asks the decision-changing question: does the
    # actually proved cherry slack still pay the observed open grafting debt?
    hybrid_node_factors = dict(node_factors)
    for node in certified_cherry_nodes:
        hybrid_node_factors[node] = math.sqrt(cherry_bergman_cost_by_node[node])
    hybrid_subtree_products: dict[int, float] = {}
    for node in created:
        if node not in hybrid_node_factors:
            continue
        product = hybrid_node_factors[node]
        for child in nodes[node]["children"]:
            child_index = int(child)
            if child_index in hybrid_subtree_products:
                product *= hybrid_subtree_products[child_index]
        hybrid_subtree_products[node] = product
    hybrid_block_product = math.prod(hybrid_node_factors.values())
    largest_hybrid_node = max(
        hybrid_subtree_products,
        key=hybrid_subtree_products.__getitem__,
        default=None,
    )
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
        "bergman_certified_bound_numerical_violation_count": sum(
            node_factors[node]
            > math.sqrt(cherry_bergman_cost_by_node[node]) + 1.0e-6
            for node in certified_cherry_nodes
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
        "hybrid_grafting_violation_count": sum(
            hybrid_subtree_products[node] > 1.0 + 1.0e-8
            for node in grafting_nodes
        ),
        "hybrid_subtree_violation_count": sum(
            value > 1.0 + 1.0e-8
            for value in hybrid_subtree_products.values()
        ),
        "largest_hybrid_subtree_product": max(
            hybrid_subtree_products.values(), default=0.0
        ),
        "largest_hybrid_subtree_size": (
            int(nodes[largest_hybrid_node]["size"])
            if largest_hybrid_node is not None
            else 0
        ),
        "largest_hybrid_subtree_actual_product": (
            subtree_products[largest_hybrid_node]
            if largest_hybrid_node is not None
            else 0.0
        ),
        "largest_hybrid_subtree_bound_inflation": (
            hybrid_subtree_products[largest_hybrid_node]
            / max(subtree_products[largest_hybrid_node], 1.0e-300)
            if largest_hybrid_node is not None
            else 0.0
        ),
        "hybrid_full_block_product": hybrid_block_product,
        "hybrid_to_actual_full_block_ratio": hybrid_block_product
        / max(block_product, 1.0e-300),
        "subtree_count": len(subtree_products),
        "subtree_violation_count": sum(
            value > 1.0 + 1.0e-8 for value in subtree_products.values()
        ),
        "largest_subtree_product": max(subtree_products.values(), default=0.0),
        "full_block_product": block_product,
        "direct_product": direct_product,
        "arithmetic_mean_direct_factor": sum(direct_factors) / len(direct_factors),
        "admissible_component_count": len(component_arithmetic_means),
        "component_arithmetic_mean_violation_count": sum(
            value > 1.0 + 1.0e-8 for value in component_arithmetic_means
        ),
        "largest_component_arithmetic_mean": max(
            component_arithmetic_means, default=0.0
        ),
        "subtree_arithmetic_mean_violation_count": sum(
            value > 1.0 + 1.0e-8 for value in subtree_arithmetic_means.values()
        ),
        "largest_subtree_arithmetic_mean": max(
            subtree_arithmetic_means.values(), default=0.0
        ),
        "largest_subtree_arithmetic_mean_size": (
            subtree_arithmetic_sizes[largest_subtree_arithmetic_node]
            if largest_subtree_arithmetic_node is not None
            else 0
        ),
        "cut_scaled_subtree_arithmetic_mean_violation_count": sum(
            value > 1.0 + 1.0e-8
            for value in cut_scaled_subtree_arithmetic_means.values()
        ),
        "largest_cut_scaled_subtree_arithmetic_mean": max(
            cut_scaled_subtree_arithmetic_means.values(), default=0.0
        ),
        "largest_cut_scaled_subtree_arithmetic_mean_size": (
            subtree_arithmetic_sizes[largest_cut_scaled_subtree_arithmetic_node]
            if largest_cut_scaled_subtree_arithmetic_node is not None
            else 0
        ),
        "positive_graft_debt_count": sum(
            debt > 1.0e-10 for debt in graft_debts.values()
        ),
        "positive_graft_debt_paid_count": sum(
            graft_debts[node] > 1.0e-10
            and child_slack_minus_graft_debt[node] >= -1.0e-8
            for node in graft_debts
        ),
        "largest_graft_debt": max(graft_debts.values(), default=0.0),
        "smallest_child_slack_minus_graft_debt": min(
            child_slack_minus_graft_debt.values(), default=0.0
        ),
        "convexity_gap_violation_count": sum(
            margin < -1.0e-8
            for margin in child_slack_minus_convexity_gap.values()
        ),
        "local_overspend_violation_count": sum(
            margin < -1.0e-8
            for margin in child_slack_minus_local_overspend.values()
        ),
        "half_slack_convexity_violation_count": sum(
            margin < -1.0e-8
            for margin in half_child_slack_minus_convexity_gap.values()
        ),
        "half_slack_local_overspend_violation_count": sum(
            margin < -1.0e-8
            for margin in half_child_slack_minus_local_overspend.values()
        ),
        "positive_liability_split_violation_count": sum(
            margin < -1.0e-8
            for margin in child_slack_minus_positive_liabilities.values()
        ),
        "smallest_child_slack_minus_convexity_gap": min(
            child_slack_minus_convexity_gap.values(), default=0.0
        ),
        "smallest_child_slack_minus_local_overspend": min(
            child_slack_minus_local_overspend.values(), default=0.0
        ),
        "smallest_half_slack_minus_convexity_gap": min(
            half_child_slack_minus_convexity_gap.values(), default=0.0
        ),
        "smallest_half_slack_minus_local_overspend": min(
            half_child_slack_minus_local_overspend.values(), default=0.0
        ),
        "smallest_child_slack_minus_positive_liabilities": min(
            child_slack_minus_positive_liabilities.values(), default=0.0
        ),
        "largest_convexity_slack_ratio": max(
            convexity_slack_ratios, default=0.0
        ),
        "largest_overspend_slack_ratio": max(
            overspend_slack_ratios, default=0.0
        ),
        "largest_combined_liability_slack_ratio": max(
            combined_liability_slack_ratios, default=0.0
        ),
        "graft_slack_recurrence_max_abs_error": max(
            graft_recurrence_errors, default=0.0
        ),
        "adjacent_scale_repayment_failure_count": len(
            adjacent_repayment_failures
        ),
        "largest_adjacent_scale_repayment_failure": max(
            adjacent_repayment_failures, default=0.0
        ),
        "identity_relative_error": identity_relative_error,
    }


def run_deterministic_subtree_stress() -> None:
    """Run a wider fixed-seed falsifier search for the rooted-subtree bound."""

    rng = np.random.default_rng(104120260828)
    rows = []
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
                        float(diagnostics["largest_hybrid_subtree_product"]),
                        int(diagnostics["largest_hybrid_subtree_size"]),
                        float(diagnostics["largest_hybrid_subtree_actual_product"]),
                        float(diagnostics["largest_hybrid_subtree_bound_inflation"]),
                        float(diagnostics["arithmetic_mean_direct_factor"]),
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
    hybrid_subtree_violation_count = sum(
        int(row["hybrid_subtree_violation_count"]) for row in diagnostic_rows
    )
    arithmetic_mean_violation_count = sum(row[11] > 1.0 + 1.0e-8 for row in rows)
    largest_arithmetic_mean_row = max(rows, key=lambda row: row[11])
    admissible_component_count = sum(
        int(row["admissible_component_count"]) for row in diagnostic_rows
    )
    component_arithmetic_mean_violation_count = sum(
        int(row["component_arithmetic_mean_violation_count"])
        for row in diagnostic_rows
    )
    largest_component_arithmetic_mean = max(
        float(row["largest_component_arithmetic_mean"])
        for row in diagnostic_rows
    )
    subtree_arithmetic_mean_violation_count = sum(
        int(row["subtree_arithmetic_mean_violation_count"])
        for row in diagnostic_rows
    )
    largest_subtree_arithmetic_row = max(
        zip(rows, diagnostic_rows),
        key=lambda pair: float(pair[1]["largest_subtree_arithmetic_mean"]),
    )
    cut_scaled_subtree_arithmetic_mean_violation_count = sum(
        int(row["cut_scaled_subtree_arithmetic_mean_violation_count"])
        for row in diagnostic_rows
    )
    largest_cut_scaled_subtree_arithmetic_row = max(
        zip(rows, diagnostic_rows),
        key=lambda pair: float(
            pair[1]["largest_cut_scaled_subtree_arithmetic_mean"]
        ),
    )
    positive_graft_debt_count = sum(
        int(row["positive_graft_debt_count"]) for row in diagnostic_rows
    )
    positive_graft_debt_paid_count = sum(
        int(row["positive_graft_debt_paid_count"]) for row in diagnostic_rows
    )
    graft_slack_recurrence_max_abs_error = max(
        float(row["graft_slack_recurrence_max_abs_error"])
        for row in diagnostic_rows
    )
    probe_fields = (
        "convexity_gap_violation_count",
        "local_overspend_violation_count",
        "half_slack_convexity_violation_count",
        "half_slack_local_overspend_violation_count",
        "positive_liability_split_violation_count",
    )
    probe_counts = {
        field: sum(int(row[field]) for row in diagnostic_rows)
        for field in probe_fields
    }
    probe_margin_fields = (
        "smallest_child_slack_minus_convexity_gap",
        "smallest_child_slack_minus_local_overspend",
        "smallest_half_slack_minus_convexity_gap",
        "smallest_half_slack_minus_local_overspend",
        "smallest_child_slack_minus_positive_liabilities",
    )
    probe_margins = {
        field: min(float(row[field]) for row in diagnostic_rows)
        for field in probe_margin_fields
    }
    probe_ratio_fields = (
        "largest_convexity_slack_ratio",
        "largest_overspend_slack_ratio",
        "largest_combined_liability_slack_ratio",
    )
    probe_ratios = {
        field: max(float(row[field]) for row in diagnostic_rows)
        for field in probe_ratio_fields
    }
    adjacent_scale_repayment_failure_count = sum(
        int(row["adjacent_scale_repayment_failure_count"])
        for row in diagnostic_rows
    )
    largest_adjacent_scale_repayment_failure = max(
        float(row["largest_adjacent_scale_repayment_failure"])
        for row in diagnostic_rows
    )
    certified_bound_numerical_violation_count = sum(
        int(row["bergman_certified_bound_numerical_violation_count"])
        for row in diagnostic_rows
    )
    largest_hybrid_row = max(
        rows,
        key=lambda row: row[7],
    )
    assert len(rows) == 800
    assert violation_count == 0
    assert cherry_violation_count == 0
    assert grafting_violation_count == 0
    assert certified_bound_numerical_violation_count == 0
    assert hybrid_subtree_violation_count > 0
    assert arithmetic_mean_violation_count == 0
    assert component_arithmetic_mean_violation_count == 0
    assert subtree_arithmetic_mean_violation_count >= 0
    assert cut_scaled_subtree_arithmetic_mean_violation_count == 0
    assert positive_graft_debt_paid_count == positive_graft_debt_count
    assert graft_slack_recurrence_max_abs_error < 1.0e-10
    assert adjacent_scale_repayment_failure_count > 0
    assert largest_adjacent_scale_repayment_failure > 1.05
    assert largest_hybrid_row[7] > 1.05
    assert largest_hybrid_row[9] < 0.9
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
        "stress_hybrid_subtree_violation_count="
        f"{hybrid_subtree_violation_count}"
    )
    print(
        "stress_largest_hybrid_subtree_product="
        f"{largest_hybrid_row[7]:.12f} degree={largest_hybrid_row[1]} "
        f"family={largest_hybrid_row[2]} repetition={largest_hybrid_row[3]} "
        f"subtree_size={largest_hybrid_row[8]} "
        f"actual_product={largest_hybrid_row[9]:.12f} "
        f"bound_inflation={largest_hybrid_row[10]:.12f}"
    )
    print(
        "stress_largest_subtree_product="
        f"{rows[0][0]:.12f} degree={rows[0][1]} family={rows[0][2]} "
        f"repetition={rows[0][3]} largest_node_factor={rows[0][4]:.12f} "
        f"full_product={rows[0][5]:.12f}"
    )
    print(f"stress_arithmetic_mean_q_violation_count={arithmetic_mean_violation_count}")
    print(
        "stress_largest_arithmetic_mean_q="
        f"{largest_arithmetic_mean_row[11]:.12f} "
        f"degree={largest_arithmetic_mean_row[1]} "
        f"family={largest_arithmetic_mean_row[2]} "
        f"repetition={largest_arithmetic_mean_row[3]}"
    )
    print(f"stress_admissible_component_count={admissible_component_count}")
    print(
        "stress_component_arithmetic_mean_q_violation_count="
        f"{component_arithmetic_mean_violation_count}"
    )
    print(
        "stress_largest_component_arithmetic_mean_q="
        f"{largest_component_arithmetic_mean:.12f}"
    )
    print(
        "stress_subtree_arithmetic_mean_q_violation_count="
        f"{subtree_arithmetic_mean_violation_count}"
    )
    print(
        "stress_largest_subtree_arithmetic_mean_q="
        f"{float(largest_subtree_arithmetic_row[1]['largest_subtree_arithmetic_mean']):.12f} "
        f"degree={largest_subtree_arithmetic_row[0][1]} "
        f"family={largest_subtree_arithmetic_row[0][2]} "
        f"repetition={largest_subtree_arithmetic_row[0][3]} "
        f"subtree_size={int(largest_subtree_arithmetic_row[1]['largest_subtree_arithmetic_mean_size'])}"
    )
    print(
        "stress_cut_scaled_subtree_arithmetic_mean_q_violation_count="
        f"{cut_scaled_subtree_arithmetic_mean_violation_count}"
    )
    print(
        "stress_largest_cut_scaled_subtree_arithmetic_mean_q="
        f"{float(largest_cut_scaled_subtree_arithmetic_row[1]['largest_cut_scaled_subtree_arithmetic_mean']):.12f} "
        f"degree={largest_cut_scaled_subtree_arithmetic_row[0][1]} "
        f"family={largest_cut_scaled_subtree_arithmetic_row[0][2]} "
        f"repetition={largest_cut_scaled_subtree_arithmetic_row[0][3]} "
        f"subtree_size={int(largest_cut_scaled_subtree_arithmetic_row[1]['largest_cut_scaled_subtree_arithmetic_mean_size'])}"
    )
    print(
        "stress_positive_graft_debt_paid_count="
        f"{positive_graft_debt_paid_count}/{positive_graft_debt_count}"
    )
    print(
        "stress_graft_slack_recurrence_max_abs_error="
        f"{graft_slack_recurrence_max_abs_error:.3e}"
    )
    for field in probe_fields:
        print(f"stress_{field}={probe_counts[field]}")
    for field in probe_margin_fields:
        print(f"stress_{field}={probe_margins[field]:.12f}")
    for field in probe_ratio_fields:
        print(f"stress_{field}={probe_ratios[field]:.12f}")
    print(
        "stress_adjacent_scale_repayment_failure_count="
        f"{adjacent_scale_repayment_failure_count}"
    )
    print(
        "stress_largest_adjacent_scale_repayment_failure="
        f"{largest_adjacent_scale_repayment_failure:.12f}"
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
                diagnostics.arithmetic_mean_factor,
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
    arithmetic_mean_q_violations = sum(row[13] > 1.0 + 1.0e-8 for row in coarse_rows)
    largest_arithmetic_mean_q_row = max(coarse_rows, key=lambda row: row[13])
    admissible_component_count = sum(
        int(row[0]["admissible_component_count"]) for row in subtree_block_rows
    )
    component_arithmetic_mean_q_violations = sum(
        int(row[0]["component_arithmetic_mean_violation_count"])
        for row in subtree_block_rows
    )
    largest_component_arithmetic_mean_q = max(
        float(row[0]["largest_component_arithmetic_mean"])
        for row in subtree_block_rows
    )
    subtree_arithmetic_mean_q_violations = sum(
        int(row[0]["subtree_arithmetic_mean_violation_count"])
        for row in subtree_block_rows
    )
    largest_subtree_arithmetic_mean_q_row = max(
        subtree_block_rows,
        key=lambda row: float(row[0]["largest_subtree_arithmetic_mean"]),
    )
    cut_scaled_subtree_arithmetic_mean_q_violations = sum(
        int(row[0]["cut_scaled_subtree_arithmetic_mean_violation_count"])
        for row in subtree_block_rows
    )
    largest_cut_scaled_subtree_arithmetic_mean_q_row = max(
        subtree_block_rows,
        key=lambda row: float(
            row[0]["largest_cut_scaled_subtree_arithmetic_mean"]
        ),
    )
    positive_graft_debt_count = sum(
        int(row[0]["positive_graft_debt_count"])
        for row in subtree_block_rows
    )
    positive_graft_debt_paid_count = sum(
        int(row[0]["positive_graft_debt_paid_count"])
        for row in subtree_block_rows
    )
    graft_slack_recurrence_max_abs_error = max(
        float(row[0]["graft_slack_recurrence_max_abs_error"])
        for row in subtree_block_rows
    )
    base_probe_fields = (
        "convexity_gap_violation_count",
        "local_overspend_violation_count",
        "half_slack_convexity_violation_count",
        "half_slack_local_overspend_violation_count",
        "positive_liability_split_violation_count",
    )
    base_probe_counts = {
        field: sum(int(row[0][field]) for row in subtree_block_rows)
        for field in base_probe_fields
    }
    base_probe_ratio_fields = (
        "largest_convexity_slack_ratio",
        "largest_overspend_slack_ratio",
        "largest_combined_liability_slack_ratio",
    )
    base_probe_ratios = {
        field: max(float(row[0][field]) for row in subtree_block_rows)
        for field in base_probe_ratio_fields
    }
    adjacent_scale_repayment_failures = sum(
        int(row[0]["adjacent_scale_repayment_failure_count"])
        for row in subtree_block_rows
    )
    largest_adjacent_scale_repayment_failure = max(
        float(row[0]["largest_adjacent_scale_repayment_failure"])
        for row in subtree_block_rows
    )
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
    hybrid_subtree_violations = sum(
        int(row[0]["hybrid_subtree_violation_count"])
        for row in subtree_block_rows
    )
    certified_bound_numerical_violations = sum(
        int(row[0]["bergman_certified_bound_numerical_violation_count"])
        for row in subtree_block_rows
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
    largest_hybrid_subtree_row = max(
        subtree_block_rows,
        key=lambda row: float(row[0]["largest_hybrid_subtree_product"]),
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
    assert arithmetic_mean_q_violations == 0
    assert component_arithmetic_mean_q_violations == 0
    assert subtree_arithmetic_mean_q_violations >= 0
    assert cut_scaled_subtree_arithmetic_mean_q_violations == 0
    assert positive_graft_debt_paid_count == positive_graft_debt_count
    assert graft_slack_recurrence_max_abs_error < 1.0e-10
    assert base_probe_counts["convexity_gap_violation_count"] == 0
    assert base_probe_counts["local_overspend_violation_count"] == 0
    assert base_probe_counts["positive_liability_split_violation_count"] == 0
    assert base_probe_ratios["largest_combined_liability_slack_ratio"] <= 1.0 + 1.0e-8
    assert adjacent_scale_repayment_failures > 0
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
    assert certified_bound_numerical_violations == 0
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
    print(f"arithmetic_mean_q_violation_count={arithmetic_mean_q_violations}")
    print(
        "largest_arithmetic_mean_q="
        f"{largest_arithmetic_mean_q_row[13]:.12f} "
        f"degree={largest_arithmetic_mean_q_row[2]} "
        f"family={largest_arithmetic_mean_q_row[3]} "
        f"repetition={largest_arithmetic_mean_q_row[4]}"
    )
    print(f"admissible_component_count={admissible_component_count}")
    print(
        "component_arithmetic_mean_q_violation_count="
        f"{component_arithmetic_mean_q_violations}"
    )
    print(
        "largest_component_arithmetic_mean_q="
        f"{largest_component_arithmetic_mean_q:.12f}"
    )
    print(
        "subtree_arithmetic_mean_q_violation_count="
        f"{subtree_arithmetic_mean_q_violations}"
    )
    print(
        "largest_subtree_arithmetic_mean_q="
        f"{float(largest_subtree_arithmetic_mean_q_row[0]['largest_subtree_arithmetic_mean']):.12f} "
        f"degree={largest_subtree_arithmetic_mean_q_row[1]} "
        f"family={largest_subtree_arithmetic_mean_q_row[2]} "
        f"repetition={largest_subtree_arithmetic_mean_q_row[3]} "
        f"subtree_size={int(largest_subtree_arithmetic_mean_q_row[0]['largest_subtree_arithmetic_mean_size'])}"
    )
    print(
        "cut_scaled_subtree_arithmetic_mean_q_violation_count="
        f"{cut_scaled_subtree_arithmetic_mean_q_violations}"
    )
    print(
        "largest_cut_scaled_subtree_arithmetic_mean_q="
        f"{float(largest_cut_scaled_subtree_arithmetic_mean_q_row[0]['largest_cut_scaled_subtree_arithmetic_mean']):.12f} "
        f"degree={largest_cut_scaled_subtree_arithmetic_mean_q_row[1]} "
        f"family={largest_cut_scaled_subtree_arithmetic_mean_q_row[2]} "
        f"repetition={largest_cut_scaled_subtree_arithmetic_mean_q_row[3]} "
        f"subtree_size={int(largest_cut_scaled_subtree_arithmetic_mean_q_row[0]['largest_cut_scaled_subtree_arithmetic_mean_size'])}"
    )
    print(
        "positive_graft_debt_paid_count="
        f"{positive_graft_debt_paid_count}/{positive_graft_debt_count}"
    )
    print(
        "graft_slack_recurrence_max_abs_error="
        f"{graft_slack_recurrence_max_abs_error:.3e}"
    )
    for field in base_probe_fields:
        print(f"{field}={base_probe_counts[field]}")
    for field in base_probe_ratio_fields:
        print(f"{field}={base_probe_ratios[field]:.12f}")
    print(
        "adjacent_scale_repayment_failure_count="
        f"{adjacent_scale_repayment_failures}"
    )
    print(
        "largest_adjacent_scale_repayment_failure="
        f"{largest_adjacent_scale_repayment_failure:.12f}"
    )
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
    print(f"hybrid_subtree_violation_count={hybrid_subtree_violations}")
    print(
        "largest_hybrid_subtree_product="
        f"{float(largest_hybrid_subtree_row[0]['largest_hybrid_subtree_product']):.12f} "
        f"degree={largest_hybrid_subtree_row[1]} "
        f"family={largest_hybrid_subtree_row[2]} "
        f"repetition={largest_hybrid_subtree_row[3]}"
    )
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
