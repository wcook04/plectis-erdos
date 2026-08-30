#!/usr/bin/env python3
"""Exact tree replay for root-indexed entrance ancestry."""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
import math
from pathlib import Path

import numpy as np

from system.lib.formal_math_lemniscate import merging_pair_tree


ROOT = Path(__file__).resolve().parents[5]
RECEIPT = ROOT / "source-provenance://private-authoring-project/receipts/erdos1041_root_indexed_entrance_ancestry_receipt.json"


def tree_shapes(leaves: int):
    if leaves == 1:
        yield None
        return
    for left_size in range(1, leaves):
        for left in tree_shapes(left_size):
            for right in tree_shapes(leaves - left_size):
                yield (left, right)


def annotate(tree, next_leaf=0, nodes=None, paths=None):
    if nodes is None:
        nodes, paths = [], {}
    if tree is None:
        paths[next_leaf] = []
        return {next_leaf}, next_leaf + 1, nodes, paths
    left, right = tree
    ls, next_leaf, nodes, paths = annotate(left, next_leaf, nodes, paths)
    rs, next_leaf, nodes, paths = annotate(right, next_leaf, nodes, paths)
    node_id = len(nodes)
    level = Fraction(node_id + 2, node_id + 3)
    nodes.append((ls, rs, level))
    for i in ls:
        paths[i].append((node_id, rs))
    for i in rs:
        paths[i].append((node_id, ls))
    return ls | rs, next_leaf, nodes, paths


def exact_tree_replay(max_leaves=9):
    checked = weighted = blocks = mixed_cuts = 0
    for n in range(2, max_leaves + 1):
        for tree in tree_shapes(n):
            leaves, _, nodes, paths = annotate(tree)
            assert leaves == set(range(n))
            distances = {
                (i, j): Fraction((i + 2) * (j + 3) + len(nodes), (i + 3) * (j + 4) + 1)
                for i in range(n) for j in range(i + 1, n)
            }
            dist = lambda i, j: distances[tuple(sorted((i, j)))]
            parent = {i: nodes[paths[i][0][0]][2] for i in range(n)}
            derivative = {i: math.prod(dist(i, j) for j in range(n) if j != i) for i in range(n)}
            ancestor = {
                i: math.prod(dist(i, j) for _, sibling in paths[i] for j in sibling)
                for i in range(n)
            }
            assert derivative == ancestor
            q = {i: parent[i] / derivative[i] for i in range(n)}

            weights = {i: (3 * i + n) % 5 for i in range(n)}
            lhs = math.prod(q[i] ** weights[i] for i in range(n))
            rhs = math.prod(parent[i] ** weights[i] for i in range(n)) / math.prod(
                dist(i, j) ** (weights[i] + weights[j])
                for i in range(n) for j in range(i + 1, n)
            )
            assert lhs == rhs
            weighted += 1

            for left, right, _ in nodes:
                for subset in (left, right, left | right):
                    numerator = math.prod(parent[i] for i in subset)
                    internal = math.prod(
                        dist(i, j) ** 2 for i in subset for j in subset if i < j
                    )
                    boundary = math.prod(
                        dist(i, j) for i in subset for j in range(n) if j not in subset
                    )
                    assert math.prod(q[i] for i in subset) == numerator / (internal * boundary)
                    blocks += 1
                if len(left) == 1 or len(right) == 1:
                    mixed_cuts += 1
            checked += 1
    return {
        "max_leaves": max_leaves,
        "ordered_binary_trees": checked,
        "nonconstant_weight_rows": weighted,
        "subtree_block_rows": blocks,
        "mixed_or_cherry_cut_rows": mixed_cuts,
    }


def actual_polynomial_replay():
    rows_checked = path_checks = 0
    max_relative_error = 0.0
    for degree in range(3, 9):
        for sample in range(4):
            rng = np.random.default_rng(1041700 + 100 * degree + sample)
            roots = (0.70 + 0.28 * rng.random(degree)) * np.exp(2j * np.pi * rng.random(degree))
            merges = merging_pair_tree(roots)
            assert merges is not None and len(merges) == degree - 1
            parent = list(range(degree))
            members = {i: {i} for i in range(degree)}
            siblings = {i: [] for i in range(degree)}
            sigma = [None] * degree

            def find(i):
                while parent[i] != i:
                    parent[i] = parent[parent[i]]
                    i = parent[i]
                return i

            for row in merges:
                i, j = map(int, row["root_pair"])
                ri, rj = find(i), find(j)
                assert ri != rj
                left, right = set(members[ri]), set(members[rj])
                level = float(row["critical_value_modulus"])
                for leaf in left:
                    siblings[leaf].append(right)
                    if sigma[leaf] is None:
                        sigma[leaf] = level
                for leaf in right:
                    siblings[leaf].append(left)
                    if sigma[leaf] is None:
                        sigma[leaf] = level
                parent[rj] = ri
                members[ri] = left | right
                del members[rj]

            for i in range(degree):
                direct = math.prod(abs(roots[i] - roots[j]) for j in range(degree) if j != i)
                ancestry = math.prod(abs(roots[i] - roots[j]) for block in siblings[i] for j in block)
                error = abs(direct - ancestry) / max(direct, ancestry, 1e-300)
                assert error < 2e-13
                max_relative_error = max(max_relative_error, error)
                assert sigma[i] is not None
                path_checks += 1
            rows_checked += 1
    return {
        "actual_polynomial_rows": rows_checked,
        "root_path_checks": path_checks,
        "max_relative_error": max_relative_error,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write-receipt", action="store_true")
    args = parser.parse_args()
    receipt = {
        "schema": "erdos1041_root_indexed_entrance_ancestry_check_v1",
        "status": "pass",
        "exact_tree_replay": exact_tree_replay(),
        "actual_polynomial_regression": actual_polynomial_replay(),
        "claim_boundary": "exact ancestry and weighted/block identities; no metric allocation inequality is claimed",
    }
    if args.write_receipt:
        RECEIPT.parent.mkdir(parents=True, exist_ok=True)
        RECEIPT.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
