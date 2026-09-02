#!/usr/bin/env python3
"""Exact finite checks for SeparateCriticalContourNoGo.md.

The ordinary proof is the authority.  This script replays the finite
permutation lemma and the rational squared inequalities used by the cubic and
quartic examples; it performs no floating-point quadrature.
"""

from __future__ import annotations

import itertools
from fractions import Fraction


def compose(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(left[right[i]] for i in range(len(left)))


def transposition(n: int, edge: tuple[int, int]) -> tuple[int, ...]:
    value = list(range(n))
    a, b = edge
    value[a], value[b] = value[b], value[a]
    return tuple(value)


def is_tree(n: int, edges: tuple[tuple[int, int], ...]) -> bool:
    reached = {0}
    while True:
        enlarged = reached | {
            b for a, b in edges if a in reached
        } | {
            a for a, b in edges if b in reached
        }
        if enlarged == reached:
            return len(reached) == n
        reached = enlarged


def is_full_cycle(permutation: tuple[int, ...]) -> bool:
    reached = set()
    current = 0
    while current not in reached:
        reached.add(current)
        current = permutation[current]
    return current == 0 and len(reached) == len(permutation)


def check_tree_transposition_products() -> int:
    checked = 0
    # Exhaustive through degree 6: 1+3*2+16*6+125*24+1296*120
    # ordered tree products.  The general statement is proved by leaf removal.
    for n in range(2, 7):
        all_edges = tuple(itertools.combinations(range(n), 2))
        for edges in itertools.combinations(all_edges, n - 1):
            if not is_tree(n, edges):
                continue
            for order in itertools.permutations(edges):
                permutation = tuple(range(n))
                for edge in order:
                    permutation = compose(
                        transposition(n, edge), permutation
                    )
                assert is_full_cycle(permutation), (n, edges, order, permutation)
                checked += 1
    return checked


def check_exact_margins() -> None:
    r = Fraction(99, 100)

    # Triangle: (r sqrt(3))^2 > (3/2)^2, so every tree edge
    # has length > 3/2 and 2 sum(edges)/3 > 2.
    assert 3 * r * r > Fraction(3, 2) ** 2
    assert Fraction(16, 3) * r * r > 4  # (4 r sqrt(3)/3)^2 > 2^2

    # Square: (r sqrt(2))^2 > (4/3)^2, so every tree edge
    # has length > 4/3 and 2 sum(edges)/4 > 2.
    assert 2 * r * r > Fraction(4, 3) ** 2
    assert Fraction(9, 2) * r * r > 4  # (3 r sqrt(2)/2)^2 > 2^2

    # The fixed-block variational identity then makes the optimized quadratic
    # product strictly greater than 4.
    assert Fraction(16, 3) * r * r > 4
    assert Fraction(9, 2) * r * r > 4


def main() -> None:
    checked = check_tree_transposition_products()
    check_exact_margins()
    print("SEPARATE-CRITICAL CONTOUR NO-GO: PASS")
    print(f"ordered tree-transposition products checked exactly: {checked}")
    print("cubic and quartic chord/average margins: exact rational squares")


if __name__ == "__main__":
    main()
