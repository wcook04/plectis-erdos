#!/usr/bin/env python3
"""Exact and high-precision checks for AttachmentCoupledEnergySelector20260826."""

from __future__ import annotations

import argparse
from decimal import Decimal, getcontext
from fractions import Fraction
import json
import random


def quartic_certificate() -> dict[str, str | bool]:
    a = Fraction(1, 10)
    b = Fraction(1, 2)
    delta = b * b - a * a
    alpha = a * a * b * b
    beta = delta * delta / 4
    derivative_a = 2 * a * delta
    derivative_b = 2 * b * delta
    energy_a = alpha / (derivative_a * derivative_a)
    energy_b = beta / (derivative_b * derivative_b)
    fraction = 2 * energy_b / (2 * energy_a + 2 * energy_b)
    assert (alpha, beta) == (Fraction(1, 400), Fraction(9, 625))
    assert (derivative_a, derivative_b) == (Fraction(6, 125), Fraction(6, 25))
    assert (energy_a, energy_b) == (Fraction(625, 576), Fraction(1, 4))
    assert fraction == Fraction(144, 769) < Fraction(1, 2)
    return {
        "alpha": str(alpha),
        "beta": str(beta),
        "terminal_inner_ratio": str(beta / alpha),
        "old_leaf_energy": str(energy_a),
        "young_leaf_energy": str(energy_b),
        "young_energy_fraction": str(fraction),
        "strict_deficit": str(Fraction(1, 2) - fraction),
        "pass": True,
    }


def random_tree_clusters(leaves: tuple[int, ...], rng: random.Random) -> list[tuple[frozenset[int], Fraction]]:
    if len(leaves) <= 1:
        return []
    cut = rng.randrange(1, len(leaves))
    left = leaves[:cut]
    right = leaves[cut:]
    rows = random_tree_clusters(left, rng) + random_tree_clusters(right, rng)
    rows.append((frozenset(left), Fraction(rng.randrange(1, 30), rng.randrange(1, 20))))
    rows.append((frozenset(right), Fraction(rng.randrange(1, 30), rng.randrange(1, 20))))
    return rows


def check_tree(k: int, rng: random.Random, lam: Decimal) -> Decimal:
    weights = [Fraction(rng.randrange(1, 500), rng.randrange(1, 100)) for _ in range(k)]
    edges = random_tree_clusters(tuple(range(k)), rng)
    total = sum(weights)
    diversity = 1 - sum((weight / total) ** 2 for weight in weights)
    variance = sum(
        length * (energy := sum(weights[i] for i in cluster)) * (total - energy)
        for cluster, length in edges
    )

    def distance(i: int, j: int) -> Fraction:
        return sum(length for cluster, length in edges if (i in cluster) != (j in cluster))

    # This is the load-bearing edge-separation expectation, checked exactly.
    lhs_age = sum(
        (weights[i] / total) * (weights[j] / total) * distance(i, j)
        for i in range(k) for j in range(k) if i != j
    )
    assert lhs_age == 2 * variance / (total * total)

    d = lambda value: Decimal(value.numerator) / Decimal(value.denominator)
    log_terms = [
        d(weights[i]).ln() + d(weights[j]).ln() - lam * d(distance(i, j))
        for i in range(k) for j in range(k) if i != j
    ]
    log_lhs = max(log_terms)
    log_rhs = (
        d(diversity * total * total / (k * (k - 1))).ln()
        - 2 * lam * d(variance) / d(diversity * total * total)
    )
    assert log_lhs + Decimal("1e-65") >= log_rhs
    return log_lhs - log_rhs


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--trials", type=int, default=250)
    args = parser.parse_args()
    getcontext().prec = 80
    rng = random.Random(20260826)
    margins = [
        check_tree(k, rng, Decimal(2))
        for k in range(2, 11)
        for _ in range(args.trials)
    ]
    payload = {
        "schema": "erdos1041_attachment_coupled_energy_selector_check_v1",
        "quartic": quartic_certificate(),
        "tree_trials": len(margins),
        "minimum_log_margin": str(min(margins)),
        "returned_float_checker_regression": "replaced_by_80_digit_log_space_comparison",
        "pass": True,
    }
    print(json.dumps(payload, indent=2) if args.json else "PASS " + json.dumps(payload, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
