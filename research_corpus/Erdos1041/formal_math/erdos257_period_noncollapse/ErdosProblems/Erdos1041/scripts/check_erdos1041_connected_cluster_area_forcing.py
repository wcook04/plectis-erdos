#!/usr/bin/env python3
"""Falsifier and replay for fixed-level connected-cluster area forcing.

The analytic theorem is the finite area pigeonhole argument in the companion
note.  This script uses numerical descending-branch continuation only to ask a
separate structural question: is its merge-tree scalar hypothesis universal?
The near-regular rows answer no.  They do not refute the sharper area-aware CDF.
"""

from __future__ import annotations

import argparse
import json
import math

import numpy as np

from system.lib.formal_math_lemniscate import merging_pair_tree


def logarithmic_barrier(cluster_size: int, ratio: float) -> float:
    x = ratio ** (2.0 / cluster_size)
    return math.log1p(x) - math.log1p(-x)


def discriminant_ratio(roots: np.ndarray) -> float:
    degree = len(roots)
    product = 1.0
    for i in range(degree):
        for j in range(i):
            product *= abs(roots[i] - roots[j]) ** 2
    return product / degree**degree


def merge_area_forcing_score(
    degree: int, rows: list[dict[str, object]], ceiling: float = 1.0
) -> dict[str, object] | None:
    parent = list(range(degree))
    size = [1] * degree
    birth = [0.0] * degree

    def find(index: int) -> int:
        while parent[index] != index:
            parent[index] = parent[parent[index]]
            index = parent[index]
        return index

    def score(level: float) -> tuple[float, list[dict[str, float | int]]]:
        seen: set[int] = set()
        total = 0.0
        components: list[dict[str, float | int]] = []
        for index in range(degree):
            root = find(index)
            if root in seen or size[root] < 2:
                continue
            seen.add(root)
            ratio = birth[root] / level
            term = 2.0 / logarithmic_barrier(size[root], ratio)
            total += term
            components.append(
                {"cluster_size": size[root], "ratio": ratio, "term": term}
            )
        return total, components

    best_score = 0.0
    best_level = ceiling
    best_components: list[dict[str, float | int]] = []
    for row in rows:
        critical_level = float(row["critical_value_modulus"])
        if critical_level >= ceiling:
            break
        before = critical_level * (1.0 - 2.0e-12)
        if before > 0.0:
            current, components = score(before)
            if current > best_score:
                best_score, best_level, best_components = (
                    current,
                    before,
                    components,
                )
        left_index, right_index = row["root_pair"]
        left, right = find(int(left_index)), find(int(right_index))
        if left == right:
            return None
        if size[left] < size[right]:
            left, right = right, left
        parent[right] = left
        size[left] += size[right]
        birth[left] = critical_level

    current, components = score(ceiling)
    if current > best_score:
        best_score, best_level, best_components = current, ceiling, components
    return {
        "max_area_forcing_score": best_score,
        "maximizing_level": best_level,
        "components": best_components,
    }


def configuration(tag: str, degree: int, family: str) -> dict[str, object]:
    if family == "bulk":
        rng = np.random.default_rng(104100 + degree)
        roots = (
            0.98
            * np.sqrt(rng.random(degree))
            * np.exp(2j * math.pi * rng.random(degree))
        )
    elif family == "near_regular":
        rng = np.random.default_rng(44000 + degree)
        angles = np.arange(degree) / degree + rng.normal(0.0, 1.0e-3, degree)
        roots = 0.999 * np.exp(2j * math.pi * angles)
    else:
        raise ValueError(f"unknown family {family}")

    tree = merging_pair_tree(roots)
    if tree is None:
        return {"tag": tag, "passed_trace_gates": False}
    score = merge_area_forcing_score(degree, tree)
    if score is None:
        return {"tag": tag, "passed_trace_gates": False}
    max_endpoint_error = max(float(row["maximum_endpoint_error"]) for row in tree)
    max_level_residual = max(float(row["maximum_level_residual"]) for row in tree)
    return {
        "tag": tag,
        "family": family,
        "degree": degree,
        "tree_edge_count": len(tree),
        "max_endpoint_error": max_endpoint_error,
        "max_level_residual": max_level_residual,
        "passed_trace_gates": (
            len(tree) == degree - 1
            and max_endpoint_error <= 2.0e-8
            and max_level_residual <= 2.0e-8
        ),
        "discriminant_ratio": discriminant_ratio(roots),
        **score,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    rows = [
        configuration(f"bulk degree {degree}", degree, "bulk")
        for degree in (4, 6, 8)
    ] + [
        configuration(f"near-regular degree {degree}", degree, "near_regular")
        for degree in (4, 6, 8, 10)
    ]
    traces_pass = all(bool(row.get("passed_trace_gates")) for row in rows)
    bulk_scores = [
        float(row["max_area_forcing_score"])
        for row in rows
        if row.get("family") == "bulk"
    ]
    near_scores = [
        float(row["max_area_forcing_score"])
        for row in rows
        if row.get("family") == "near_regular"
    ]
    passed = traces_pass and min(bulk_scores) > 1.0 and max(near_scores) < 1.0
    receipt = {
        "schema": "erdos1041_connected_cluster_area_forcing_probe_v1",
        "passed": passed,
        "rows": rows,
        "bulk_min_score": min(bulk_scores),
        "near_regular_max_score": max(near_scores),
        "analytic_claim": (
            "If normalized component areas sum to at most one and the sum of "
            "two divided by each positive Bergman barrier is at least one, "
            "some component satisfies its area-times-barrier certificate."
        ),
        "falsified_claim": (
            "The reciprocal-barrier merge-tree sum is always at least one."
        ),
        "claim_boundary": (
            "The theorem is analytic and Lean-checks only its finite scalar "
            "kernel and composition. Merge trees here use numerical branch "
            "continuation. Near-regular scores below one refute only universal "
            "area-sum forcing, not CDF, CE-GM, or Erdos #1041."
        ),
    }
    print(json.dumps(receipt, indent=2, sort_keys=True) if args.json else receipt)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
