#!/usr/bin/env python3
"""High-precision replay for the attachment-age/lifetime Orlicz transform."""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np

from system.lib.formal_math_lemniscate import merging_pair_tree


ROOT = Path(__file__).resolve().parents[5]
RECEIPT = ROOT / "source-provenance://private-authoring-project/receipts/erdos1041_attachment_age_lifetime_orlicz_receipt.json"
mp.mp.dps = 60


def kernel(t: mp.mpf) -> mp.mpf:
    if t == 0:
        return mp.mpf("0")
    return 1 / mp.log(mp.coth(t))


def phi(x: mp.mpf) -> mp.mpf:
    if x == 0:
        return mp.mpf("0")
    return mp.quad(kernel, [0, x])


def lifetime(k: int, r: mp.mpf) -> mp.mpf:
    def integrand(q: mp.mpf) -> mp.mpf:
        u = q ** (mp.mpf(2) / k)
        if u >= 1:
            return mp.mpf("0")
        return 1 / (q * mp.log((1 + u) / (1 - u)))

    return mp.quad(integrand, [r, 1])


def universal_transform_grid() -> dict[str, object]:
    max_relative_error = mp.mpf("0")
    checked = 0
    for k in range(1, 13):
        for x_text in ("1e-7", "1e-5", "0.001", "0.01", "0.1", "0.4", "1.0", "2.0"):
            x = mp.mpf(x_text)
            r = mp.exp(-k * x)
            lhs = lifetime(k, r)
            rhs = k * phi(x)
            error = abs(lhs - rhs) / max(abs(lhs), abs(rhs), mp.mpf("1e-100"))
            assert error < mp.mpf("1e-45"), (k, x, lhs, rhs, error)
            max_relative_error = max(max_relative_error, error)
            checked += 1
    return {"checked_rows": checked, "max_relative_error": float(max_relative_error)}


def shape_and_bounds() -> dict[str, object]:
    grid = [mp.mpf(i) / 100 for i in range(1, 401)]
    kernels = [kernel(x) for x in grid]
    assert all(a < b for a, b in zip(kernels, kernels[1:]))

    phi_rows = [phi(x) for x in grid]
    slopes = [(phi_rows[i + 1] - phi_rows[i]) / (grid[i + 1] - grid[i]) for i in range(len(grid) - 1)]
    assert all(a < b for a, b in zip(slopes, slopes[1:]))

    half_interval_margin = mp.inf
    for x in grid:
        bound = x / (2 * mp.log(mp.coth(x / 2)))
        margin = phi(x) - bound
        assert margin >= -mp.mpf("1e-48")
        half_interval_margin = min(half_interval_margin, margin)

    no_go_rows = []
    for k in (1, 2, 5, 20):
        for exponent in (5, 10, 20, 40):
            x = mp.mpf(10) ** (-exponent)
            ratio = k * phi(x) / x
            upper = k / mp.log(mp.coth(x))
            assert ratio <= upper
            no_go_rows.append({"k": k, "x": f"1e-{exponent}", "lifetime_per_age": float(ratio)})
        assert no_go_rows[-1]["lifetime_per_age"] < no_go_rows[-4]["lifetime_per_age"]

    return {
        "monotonicity_rows": len(grid),
        "strict_convexity_slope_rows": len(slopes),
        "minimum_half_interval_margin": float(half_interval_margin),
        "linear_no_go_rows": no_go_rows,
    }


def jensen_replay() -> dict[str, object]:
    rng = np.random.default_rng(1041006)
    max_weighted_defect = mp.mpf("0")
    max_coarse_defect = mp.mpf("0")
    rows = 0
    for m in range(1, 12):
        for _ in range(30):
            sizes = [int(v) for v in rng.integers(2, 40, size=m)]
            ages = [mp.mpf(str(v)) for v in rng.uniform(1e-5, 2.0, size=m)]
            total_age = sum(ages)
            total_size = sum(sizes)
            weighted_age = sum(k * x for k, x in zip(sizes, ages))
            cost = sum(k * phi(x) for k, x in zip(sizes, ages))
            weighted_bound = total_size * phi(weighted_age / total_size)
            floor_bound = total_size * phi(2 * total_age / total_size)
            coarse_bound = 2 * m * phi(total_age / m)
            assert cost + mp.mpf("1e-45") >= weighted_bound >= floor_bound
            assert cost + mp.mpf("1e-45") >= coarse_bound
            max_weighted_defect = max(max_weighted_defect, weighted_bound - cost)
            max_coarse_defect = max(max_coarse_defect, coarse_bound - cost)
            rows += 1
    return {
        "checked_chains": rows,
        "maximum_weighted_bound_defect": float(max_weighted_defect),
        "maximum_coarse_bound_defect": float(max_coarse_defect),
    }


def tree_shapes(leaves: int):
    if leaves == 1:
        yield None
        return
    for left_size in range(1, leaves):
        for left in tree_shapes(left_size):
            for right in tree_shapes(leaves - left_size):
                yield (left, right)


def exact_root_sum_replay(max_leaves: int = 9) -> dict[str, object]:
    trees = component_rows = selector_rows = 0

    def visit(tree, next_leaf=0, edge_seed=1):
        nonlocal component_rows, selector_rows
        if tree is None:
            return {next_leaf}, {next_leaf: Fraction(0)}, Fraction(0), next_leaf + 1, edge_seed
        left, right = tree
        ls, la, ledges, next_leaf, edge_seed = visit(left, next_leaf, edge_seed)
        rs, ra, redges, next_leaf, edge_seed = visit(right, next_leaf, edge_seed)
        ages = dict(la)
        ages.update(ra)
        edge_sum = ledges + redges
        for block, child in ((ls, left), (rs, right)):
            if child is not None:
                x = Fraction((edge_seed % 7) + 1, (edge_seed % 5) + 2)
                edge_seed += 1
                for leaf in block:
                    ages[leaf] += x
                edge_sum += len(block) * x
        leaves = ls | rs
        total_age = sum((ages[i] for i in leaves), Fraction(0))
        assert total_age == edge_sum
        ordered = sorted(ages[i] for i in leaves)
        assert ordered[1] <= total_age / (len(leaves) - 1)
        component_rows += 1
        selector_rows += 1
        return leaves, ages, edge_sum, next_leaf, edge_seed

    for n in range(2, max_leaves + 1):
        for tree in tree_shapes(n):
            leaves, _, _, next_leaf, _ = visit(tree)
            assert leaves == set(range(n)) and next_leaf == n
            trees += 1
    return {
        "max_leaves": max_leaves,
        "ordered_binary_trees": trees,
        "component_double_count_rows": component_rows,
        "two_young_root_selector_rows": selector_rows,
    }


def actual_polynomial_replay() -> dict[str, object]:
    rows = incidences = 0
    max_relative_error = mp.mpf("0")
    for degree in range(3, 9):
        for sample in range(4):
            rng = np.random.default_rng(1041900 + 100 * degree + sample)
            roots = (0.70 + 0.28 * rng.random(degree)) * np.exp(2j * np.pi * rng.random(degree))
            merges = merging_pair_tree(roots)
            assert merges is not None and len(merges) == degree - 1
            parent = list(range(degree))
            members = {i: {i} for i in range(degree)}
            previous_beta = [None] * degree
            previous_size = [1] * degree
            age = [mp.mpf("0")] * degree
            path_cost = [mp.mpf("0")] * degree
            log_product_sum = {i: mp.mpf("0") for i in range(degree)}

            def find(i: int) -> int:
                while parent[i] != i:
                    parent[i] = parent[parent[i]]
                    i = parent[i]
                return i

            for merge in merges:
                i, j = map(int, merge["root_pair"])
                ri, rj = find(i), find(j)
                left, right = set(members[ri]), set(members[rj])
                beta = mp.mpf(str(float(merge["critical_value_modulus"])))
                union = left | right
                component_log_sum = log_product_sum[ri] + log_product_sum[rj]
                for block in (left, right):
                    child_size = len(block)
                    if child_size > 1:
                        component_log_sum += mp.log(beta / previous_beta[next(iter(block))])
                    for leaf in block:
                        if previous_beta[leaf] is not None:
                            r = previous_beta[leaf] / beta
                            x = mp.log(1 / r) / previous_size[leaf]
                            age[leaf] += x
                            direct = lifetime(previous_size[leaf], r)
                            transformed = previous_size[leaf] * phi(x)
                            error = abs(direct - transformed) / max(abs(direct), abs(transformed), mp.mpf("1e-100"))
                            assert error < mp.mpf("1e-40")
                            max_relative_error = max(max_relative_error, error)
                            path_cost[leaf] += transformed
                            incidences += 1
                        previous_beta[leaf] = beta
                        previous_size[leaf] = len(union)
                total_age = sum(age[leaf] for leaf in union)
                assert abs(total_age - component_log_sum) < mp.mpf("1e-45")
                second_age = sorted(age[leaf] for leaf in union)[1]
                assert second_age <= component_log_sum / (len(union) - 1) + mp.mpf("1e-45")
                parent[rj] = ri
                members[ri] = union
                log_product_sum[ri] = component_log_sum
                del members[rj]
                del log_product_sum[rj]
            rows += 1
    return {
        "actual_polynomial_rows": rows,
        "nontrivial_age_edges": incidences,
        "max_relative_error": float(max_relative_error),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write-receipt", action="store_true")
    args = parser.parse_args()
    receipt = {
        "schema": "erdos1041_attachment_age_lifetime_orlicz_check_v1",
        "status": "pass",
        "universal_transform": universal_transform_grid(),
        "shape_and_bounds": shape_and_bounds(),
        "jensen_chain_bounds": jensen_replay(),
        "root_summed_age_product": exact_root_sum_replay(),
        "actual_polynomial_regression": actual_polynomial_replay(),
        "claim_boundary": "exact universal Orlicz transform, nonlinear chain bounds, and unweighted two-young-root selector; no energy-weighted compatible pair or unrestricted Erdős 1041 solution is claimed",
    }
    if args.write_receipt:
        RECEIPT.parent.mkdir(parents=True, exist_ok=True)
        RECEIPT.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps(receipt, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
