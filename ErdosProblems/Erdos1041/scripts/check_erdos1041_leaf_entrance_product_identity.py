#!/usr/bin/env python3
"""Exact replay and actual-polynomial regression for leaf entrance products."""

from __future__ import annotations

from fractions import Fraction
import json
import math

import numpy as np

from system.lib.formal_math_lemniscate import merging_pair_tree


def tree_shapes(leaves: int):
    if leaves == 1:
        yield None
        return
    for left_size in range(1, leaves):
        for left in tree_shapes(left_size):
            for right in tree_shapes(leaves - left_size):
                yield (left, right)


def labelled_tree_data(tree, next_label: int = 2):
    """Return leaf count, node rows, leaf-parent labels, and next label."""
    if tree is None:
        return 1, [], [], next_label
    left, right = tree
    kl, left_rows, left_parents, next_label = labelled_tree_data(left, next_label)
    kr, right_rows, right_parents, next_label = labelled_tree_data(right, next_label)
    # Labels need only be positive for the algebraic identity.  Distinct primes
    # make accidental cancellations impossible in the exact replay.
    level = Fraction(next_label, next_label + 1)
    next_label += 1
    leaf_children = int(left is None) + int(right is None)
    parents = list(left_parents) + list(right_parents)
    if left is None:
        parents.append(level)
    if right is None:
        parents.append(level)
    rows = left_rows + right_rows + [(level, leaf_children)]
    return kl + kr, rows, parents, next_label


def exact_replay(max_leaves: int = 10) -> dict[str, int]:
    checked = 0
    comb_checked = 0
    for leaves in range(2, max_leaves + 1):
        for tree in tree_shapes(leaves):
            n, rows, leaf_parents, _ = labelled_tree_data(tree)
            assert n == leaves
            cherries = [level for level, ell in rows if ell == 2]
            mixed = [level for level, ell in rows if ell == 1]
            pure = [level for level, ell in rows if ell == 0]
            assert len(cherries) == len(pure) + 1
            sigma_product = math.prod(leaf_parents)
            critical_product = math.prod(level for level, _ in rows)
            resultant_product = Fraction(n**n) * critical_product
            entrance_product = sigma_product / resultant_product
            node_quotient = (
                math.prod(cherries) / (Fraction(n**n) * math.prod(pure))
            )
            assert entrance_product == node_quotient
            assert entrance_product**2 == node_quotient**2
            if not pure and len(cherries) == 1:
                assert entrance_product == cherries[0] / Fraction(n**n)
                comb_checked += 1
            checked += 1
    return {
        "max_leaves": max_leaves,
        "ordered_binary_trees": checked,
        "comb_or_reverse_comb_rows": comb_checked,
    }


def actual_polynomial_replay() -> dict[str, float | int]:
    checked = 0
    max_relative_error = 0.0
    for degree in range(3, 9):
        for sample in range(4):
            rng = np.random.default_rng(1041000 + 100 * degree + sample)
            roots = (
                (0.72 + 0.25 * rng.random(degree))
                * np.exp(2j * np.pi * rng.random(degree))
            )
            rows = merging_pair_tree(roots)
            assert rows is not None and len(rows) == degree - 1

            parent = list(range(degree))
            active_leaves = {i: [i] for i in range(degree)}
            active_node = {i: None for i in range(degree)}
            leaf_sigma = [None] * degree
            cherries: list[float] = []
            pure: list[float] = []

            def find(index: int) -> int:
                while parent[index] != index:
                    parent[index] = parent[parent[index]]
                    index = parent[index]
                return index

            for row in rows:
                i, j = map(int, row["root_pair"])
                ri, rj = find(i), find(j)
                assert ri != rj
                level = float(row["critical_value_modulus"])
                left_internal = active_node[ri] is not None
                right_internal = active_node[rj] is not None
                ell = int(not left_internal) + int(not right_internal)
                if ell == 2:
                    cherries.append(level)
                elif ell == 0:
                    pure.append(level)
                for leaf in active_leaves[ri] if not left_internal else []:
                    leaf_sigma[leaf] = level
                for leaf in active_leaves[rj] if not right_internal else []:
                    leaf_sigma[leaf] = level
                parent[rj] = ri
                active_leaves[ri] = active_leaves[ri] + active_leaves[rj]
                active_node[ri] = len(cherries) + len(pure) + checked + 1
                del active_leaves[rj]
                del active_node[rj]

            assert all(value is not None for value in leaf_sigma)
            derivatives = [
                math.prod(abs(roots[i] - roots[j]) for j in range(degree) if j != i)
                for i in range(degree)
            ]
            lhs = math.prod(float(value) for value in leaf_sigma) / math.prod(derivatives)
            rhs = math.prod(cherries) / (degree**degree * math.prod(pure))
            relative_error = abs(lhs - rhs) / max(abs(lhs), abs(rhs), 1.0e-300)
            assert relative_error < 2.0e-8
            max_relative_error = max(max_relative_error, relative_error)
            checked += 1
    return {
        "actual_polynomial_rows": checked,
        "max_relative_error": max_relative_error,
    }


def main() -> None:
    receipt = {
        "schema": "erdos1041_leaf_entrance_product_identity_check_v1",
        "status": "pass",
        "exact_tree_replay": exact_replay(),
        "actual_polynomial_regression": actual_polynomial_replay(),
        "claim_boundary": (
            "exact for separated binary merge trees; numerical polynomial rows "
            "are regression evidence, not proof"
        ),
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
