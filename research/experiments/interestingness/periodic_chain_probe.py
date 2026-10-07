#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact finite checks for the periodic-chain Mahler equation.

The left side is generated from the original successive-ratio recurrence,
then the Lambert divisor identity. The right side uses the independently
derived block products. Finite agreement is not an infinite-equation proof;
the paper proves the support decomposition and invokes Nishioka's theorem.
Run with --output PATH to retain the JSON receipt; otherwise print it.
"""

import argparse
from itertools import cycle
import json
from math import prod
from pathlib import Path


def chain_coefficients(ratios, degree):
    """Enumerate chain exponents, then count their divisibility independently."""
    coefficients = [0] * (degree + 1)
    support = []
    exponent = 1
    for ratio in ratios:
        if exponent > degree:
            break
        if ratio < 2:
            raise ValueError("Successive ratios must be integers at least two")
        support.append(exponent)
        for multiple in range(exponent, degree + 1, exponent):
            coefficients[multiple] += 1
        exponent *= ratio
    return support, coefficients


def first_failure(coefficients, scale, prefixes):
    for n in range(1, len(coefficients)):
        left = coefficients[n]
        if n % scale == 0:
            left -= coefficients[n // scale]
        right = sum(n % prefix == 0 for prefix in prefixes)
        if left != right:
            return {"degree": n, "left_coefficient": left,
                    "right_coefficient": right}
    return None


def thue_morse_ratios():
    """A specified nonperiodic ratio word, not inferred from a finite sample."""
    n = 0
    while True:
        yield 2 + (n.bit_count() % 2)
        n += 1


def run(degree=100_000):
    words = [(2, 3), (3, 2), (2, 2, 3), (3, 3), (2, 3, 4)]
    positive = []
    for word in words:
        support, coefficients = chain_coefficients(cycle(word), degree)
        prefixes = [prod(word[:i]) for i in range(len(word))]
        scale = prod(word)
        failure = first_failure(coefficients, scale, prefixes)
        assert failure is None, (word, failure)
        positive.append({
            "ratio_block": word, "mahler_base": scale,
            "prefix_exponents": prefixes, "support_prefix": support[:12],
            "coefficients_checked": degree, "first_failure": failure,
        })

    _, alternating = chain_coefficients(cycle((2, 3)), degree)
    doubling_failure = first_failure(alternating, 2, [1])
    assert doubling_failure == {
        "degree": 4, "left_coefficient": 0, "right_coefficient": 1,
    }
    _, nonperiodic = chain_coefficients(thue_morse_ratios(), degree)
    nonperiodic_failure = first_failure(nonperiodic, 6, [1, 2])
    assert nonperiodic_failure == {
        "degree": 12, "left_coefficient": 1, "right_coefficient": 2,
    }
    return {
        "schema": "periodic_chain_probe_v1",
        "source_checkpoint": "827cba0b890f12583195681e8ab59d86d81297cf",
        "paper_source": "paper/synthesis/optimal-sparse-perturbations.tex",
        "paper_anchor": "thm:chains",
        "evidence": "exact_finite_coefficient_checks",
        "equation": "G(z) - G(z^Q) = sum_i z^e_i/(1-z^e_i)",
        "coefficient_method": "successive_ratio_support_then_divisor_count",
        "positive_cases": positive,
        "negative_controls": [
            {"support": "alternating ratios 2,3", "candidate_base": 2,
             "candidate_prefixes": [1], "first_failure": doubling_failure},
            {"support": "ratio[j] = 2 + parity(popcount(j)), j >= 0",
             "candidate_base": 6, "candidate_prefixes": [1, 2],
             "first_failure": nonperiodic_failure},
        ],
        "boundary": (
            "Finite coefficient checks neither prove the infinite identity nor "
            "transcendence. The ordinary paper proof supplies the block "
            "decomposition and uses Nishioka's theorem. A rejected candidate "
            "equation does not exclude other functional equations. No Lean "
            "verification or historical novelty is claimed."
        ),
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    rendered = json.dumps(run(), indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    else:
        print(rendered, end="")
