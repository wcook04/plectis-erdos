#!/usr/bin/env python3
"""Exact exponent and actual-polynomial replay for the entrance-energy bridge."""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
import math
from pathlib import Path

import numpy as np

from system.lib.formal_math_lemniscate import merging_pair_tree


ROOT = Path(__file__).resolve().parents[5]
RECEIPT = ROOT / "state/formal_math/erdos257_period_noncollapse/erdos1041_entrance_energy_ratio_bridge_receipt.json"


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
    nodes.append((ls, rs))
    parent_size = len(ls | rs)
    for i in ls:
        paths[i].append((node_id, len(ls), parent_size))
    for i in rs:
        paths[i].append((node_id, len(rs), parent_size))
    return ls | rs, next_leaf, nodes, paths


def add_exp(row, key, value):
    row[key] = row.get(key, Fraction(0)) + value
    if row[key] == 0:
        del row[key]


def exact_exponent_replay(max_leaves=9):
    trees = incidences = strict_age_rows = 0
    for n in range(2, max_leaves + 1):
        for tree in tree_shapes(n):
            leaves, _, nodes, paths = annotate(tree)
            assert leaves == set(range(n))
            # Appending parents after their children makes node ids increase
            # strictly along every ancestor path, so these are valid ordered
            # symbolic birth levels.
            for i, path in paths.items():
                q = {"D": Fraction(-1), f"b{path[0][0]}": Fraction(1)}
                y = {"D": Fraction(-1)}
                for r, (node_id, child_size, parent_size) in enumerate(path):
                    add_exp(y, f"b{node_id}", Fraction(1, child_size) - Fraction(1, parent_size))
                    rhs = dict(y)
                    add_exp(rhs, f"b{node_id}", Fraction(1, parent_size))
                    for s in range(1, r + 1):
                        prev_id, _, prev_size = path[s - 1]
                        curr_id, _, _ = path[s]
                        add_exp(rhs, f"b{curr_id}", -Fraction(1, prev_size))
                        add_exp(rhs, f"b{prev_id}", Fraction(1, prev_size))
                    assert rhs == q, (n, i, r, rhs, q)
                    incidences += 1
                    strict_age_rows += int(r > 0)
            trees += 1
    return {
        "max_leaves": max_leaves,
        "ordered_binary_trees": trees,
        "leaf_ancestor_incidences": incidences,
        "positive_age_symbolic_rows": strict_age_rows,
    }


def actual_polynomial_replay():
    rows = incidences = 0
    max_relative_error = 0.0
    max_aggregate_error = 0.0
    for degree in range(3, 9):
        for sample in range(4):
            rng = np.random.default_rng(1041800 + 100 * degree + sample)
            roots = (0.70 + 0.28 * rng.random(degree)) * np.exp(2j * np.pi * rng.random(degree))
            merges = merging_pair_tree(roots)
            assert merges is not None and len(merges) == degree - 1
            parent = list(range(degree))
            members = {i: {i} for i in range(degree)}
            derivative = np.array([
                math.prod(abs(roots[i] - roots[j]) for j in range(degree) if j != i)
                for i in range(degree)
            ])
            y = 1.0 / derivative
            q = np.full(degree, np.nan)
            first_beta = np.full(degree, np.nan)
            previous_beta = np.full(degree, np.nan)
            previous_size = np.ones(degree, dtype=int)
            age = np.zeros(degree)

            def find(i):
                while parent[i] != i:
                    parent[i] = parent[parent[i]]
                    i = parent[i]
                return i

            for merge in merges:
                i, j = map(int, merge["root_pair"])
                ri, rj = find(i), find(j)
                assert ri != rj
                left, right = set(members[ri]), set(members[rj])
                beta = float(merge["critical_value_modulus"])
                union = left | right
                parent_size = len(union)
                for block in (left, right):
                    child_size = len(block)
                    for leaf in block:
                        if math.isnan(first_beta[leaf]):
                            first_beta[leaf] = beta
                            q[leaf] = beta / derivative[leaf]
                        else:
                            age[leaf] += math.log(beta / previous_beta[leaf]) / previous_size[leaf]
                        y[leaf] *= beta ** (1.0 / child_size - 1.0 / parent_size)
                        expected = beta ** (1.0 / parent_size) * y[leaf] * math.exp(-age[leaf])
                        error = abs(q[leaf] - expected) / max(abs(q[leaf]), abs(expected), 1e-300)
                        assert error < 3e-11
                        max_relative_error = max(max_relative_error, error)
                        previous_beta[leaf] = beta
                        previous_size[leaf] = parent_size
                        incidences += 1
                lhs = float(np.nansum(q[list(union)] ** 2))
                rhs = beta ** (2.0 / parent_size) * sum(
                    math.exp(-2 * age[leaf]) * y[leaf] ** 2 for leaf in union
                )
                aggregate_error = abs(lhs - rhs) / max(abs(lhs), abs(rhs), 1e-300)
                assert aggregate_error < 3e-11
                max_aggregate_error = max(max_aggregate_error, aggregate_error)
                parent[rj] = ri
                members[ri] = union
                del members[rj]
            rows += 1
    return {
        "actual_polynomial_rows": rows,
        "leaf_ancestor_incidences": incidences,
        "max_relative_error": max_relative_error,
        "max_aggregate_error": max_aggregate_error,
    }


def sharp_scalar_boundary():
    beta0 = Fraction(1, 10)
    beta1 = Fraction(9, 10)
    attenuation_squared = beta1 / beta0
    assert attenuation_squared == 9
    return {
        "child_size": 2,
        "parent_size": 3,
        "beta_child": str(beta0),
        "beta_parent": str(beta1),
        "entrance_to_undiscounted_ratio": "1/3",
        "squared_ratio": "1/9",
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write-receipt", action="store_true")
    args = parser.parse_args()
    receipt = {
        "schema": "erdos1041_entrance_energy_ratio_bridge_check_v1",
        "status": "pass",
        "exact_exponent_replay": exact_exponent_replay(),
        "actual_polynomial_regression": actual_polynomial_replay(),
        "sharp_scalar_boundary": sharp_scalar_boundary(),
        "claim_boundary": "exact ratio ledger and discounted-energy identity; no universal attachment-age bound or metric allocation is claimed",
    }
    if args.write_receipt:
        RECEIPT.parent.mkdir(parents=True, exist_ok=True)
        RECEIPT.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
