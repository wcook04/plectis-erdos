#!/usr/bin/env python3
"""Exact and numerical replay for MergeTreeDiscriminantDichotomy.md.

Exact arithmetic checks the truncated-tree telescoping identity.  Numerical
actual merge trees are used only to discriminate where the new Bergman
threshold fires; they are not proof of universality.
"""

from __future__ import annotations

from fractions import Fraction
import json
import math

import numpy as np

from system.lib.formal_math_lemniscate import merging_pair_tree


def theta(n: int, k: int) -> float:
    return math.tanh(((2 * n - k) / k) ** (2 / n)) ** (k / 2)


def tree_shapes(leaves: int):
    if leaves == 1:
        yield None
        return
    for left_size in range(1, leaves):
        for left in tree_shapes(left_size):
            for right in tree_shapes(leaves - left_size):
                yield (left, right)


def exact_tree_check(tree, parent: Fraction, seed: int = 2):
    """Return (leaf count, critical product, edge product, next seed)."""

    if tree is None:
        return 1, Fraction(1), Fraction(1), seed
    left, right = tree
    # Every child level is a strict rational fraction of its parent.
    level = parent * Fraction(seed, seed + 1)
    kl, pl, el, seed = exact_tree_check(left, level, seed + 1)
    kr, pr, er, seed = exact_tree_check(right, level, seed + 1)
    k = kl + kr
    critical_product = level * pl * pr
    edge_product = (level / parent) ** (k - 1) * el * er
    return k, critical_product, edge_product, seed


def exact_replay(max_leaves: int = 9) -> dict[str, int]:
    checked = 0
    for leaves in range(2, max_leaves + 1):
        cut = Fraction(7, 5)
        for tree in tree_shapes(leaves):
            k, critical_product, edge_product, _ = exact_tree_check(tree, cut)
            assert k == leaves
            assert critical_product == cut ** (leaves - 1) * edge_product
            checked += 1
    return {"max_leaves": max_leaves, "ordered_tree_count": checked}


def roots_for(degree: int, family: str) -> np.ndarray:
    if family == "bulk":
        rng = np.random.default_rng(104100 + degree)
        return (
            0.98
            * np.sqrt(rng.random(degree))
            * np.exp(2j * math.pi * rng.random(degree))
        )
    rng = np.random.default_rng(44000 + degree)
    angles = np.arange(degree) / degree + rng.normal(0.0, 1.0e-3, degree)
    return 0.999 * np.exp(2j * math.pi * angles)


def analyse_actual_tree(roots: np.ndarray) -> dict[str, object]:
    n = len(roots)
    rows = merging_pair_tree(roots)
    assert rows is not None and len(rows) == n - 1

    nodes = {i: {"size": 1, "birth": 0.0, "parent": None} for i in range(n)}
    uf = list(range(n))
    active = {i: i for i in range(n)}
    created: list[int] = []

    def find(index: int) -> int:
        while uf[index] != index:
            uf[index] = uf[uf[index]]
            index = uf[index]
        return index

    for row in rows:
        i, j = map(int, row["root_pair"])
        ri, rj = find(i), find(j)
        assert ri != rj
        ni, nj = active[ri], active[rj]
        node = n + len(created)
        nodes[node] = {
            "size": int(nodes[ni]["size"]) + int(nodes[nj]["size"]),
            "birth": float(row["critical_value_modulus"]),
            "parent": None,
        }
        nodes[ni]["parent"] = node
        nodes[nj]["parent"] = node
        uf[rj] = ri
        active[ri] = node
        del active[rj]
        created.append(node)

    root = created[-1]
    product_critical = math.prod(
        float(row["critical_value_modulus"]) for row in rows
    )
    full_telescoping = float(nodes[root]["birth"]) ** (n - 1)
    for node in created[:-1]:
        parent = int(nodes[node]["parent"])
        full_telescoping *= (
            float(nodes[node]["birth"]) / float(nodes[parent]["birth"])
        ) ** (int(nodes[node]["size"]) - 1)
    relative_error = abs(product_critical - full_telescoping) / max(
        product_critical, 1.0e-300
    )
    assert relative_error < 2.0e-12

    proper = []
    for node in created[:-1]:
        parent = int(nodes[node]["parent"])
        birth = float(nodes[node]["birth"])
        top = min(1.0, float(nodes[parent]["birth"]))
        if not birth < top:
            continue
        k = int(nodes[node]["size"])
        ratio = birth / top
        threshold = theta(n, k)
        proper.append(
            {
                "k": k,
                "ratio": ratio,
                "threshold": threshold,
                "bergman_certificate": ratio <= threshold,
            }
        )

    return {
        "degree": n,
        "proper_node_count": len(proper),
        "certificate_count": sum(
            bool(row["bergman_certificate"]) for row in proper
        ),
        "minimum_ratio_over_threshold": min(
            (float(row["ratio"]) / float(row["threshold"]) for row in proper),
            default=None,
        ),
        "critical_product_telescoping_relative_error": relative_error,
        "nodes": proper,
    }


def main() -> int:
    exact = exact_replay()
    terminal_errors = [
        abs(theta(n, n) - math.tanh(1.0) ** (n / 2)) for n in range(2, 81)
    ]
    assert max(terminal_errors) < 2.0e-15

    actual = []
    for family in ("bulk", "near_regular"):
        for degree in (4, 6, 8, 10):
            row = analyse_actual_tree(
                roots_for(degree, "bulk" if family == "bulk" else "near_regular")
            )
            row["family"] = family
            actual.append(row)

    bulk = [row for row in actual if row["family"] == "bulk"]
    near = [row for row in actual if row["family"] == "near_regular"]
    assert all(int(row["certificate_count"]) >= 1 for row in bulk)
    assert all(int(row["certificate_count"]) == 0 for row in near)

    receipt = {
        "schema": "erdos1041_merge_tree_discriminant_dichotomy_v1",
        "passed": True,
        "exact_ordered_binary_trees": exact,
        "terminal_threshold_max_error": max(terminal_errors),
        "actual_merge_tree_rows": actual,
        "claim_boundary": (
            "Exact arithmetic checks the abstract telescoping identity and Lean "
            "checks its local exponent kernel. Numerical merge trees only show "
            "that the strengthened metric certificate separates these bulk and "
            "near-regular fixtures; they do not prove unrestricted Erdos 1041."
        ),
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
