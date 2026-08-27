#!/usr/bin/env python3
"""Exact finite checks for the 2026-08-26 Erdős 1041 Type-B assimilation.

The script checks algebraic kernels only.  It does not replace isoperimetry,
the area formula, Jensen's formula, or any missing global selector.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
import math
import random

import sympy as sp


@dataclass(frozen=True)
class Node:
    leaves: tuple[int, ...]
    children: tuple["Node", ...] = ()

    @property
    def size(self) -> int:
        return len(self.leaves)


def random_tree(leaves: tuple[int, ...], rng: random.Random) -> Node:
    if len(leaves) == 1:
        return Node(leaves)
    arity = rng.randint(2, min(4, len(leaves)))
    cuts = sorted(rng.sample(range(1, len(leaves)), arity - 1))
    blocks: list[tuple[int, ...]] = []
    start = 0
    for stop in cuts + [len(leaves)]:
        blocks.append(leaves[start:stop])
        start = stop
    return Node(leaves, tuple(random_tree(block, rng) for block in blocks))


def internal_nodes(node: Node) -> list[Node]:
    if not node.children:
        return []
    return [node] + [item for child in node.children for item in internal_nodes(child)]


def check_merge_exponents() -> None:
    rng = random.Random(1041)
    for n in range(2, 25):
        for _ in range(100):
            root = random_tree(tuple(range(n)), rng)
            for node in internal_nodes(root):
                exponent = sum(
                    Fraction(child.size) *
                    (Fraction(1, child.size) - Fraction(1, node.size))
                    for child in node.children
                )
                assert exponent == len(node.children) - 1
    # At a regular forest cut with component sizes k_j, the critical
    # multiplicity internal to the components is sum(k_j-1)=n-s; the
    # complementary multiplicity above the cut is therefore s-1.
    for n in range(2, 100):
        for s in range(1, n + 1):
            sizes = [1] * s
            for index in range(n - s):
                sizes[index % s] += 1
            assert sum(size - 1 for size in sizes) == n - s
            assert (n - 1) - sum(size - 1 for size in sizes) == s - 1


def check_resultants() -> None:
    z = sp.symbols("z")
    rng = random.Random(1041)
    for n in range(2, 9):
        for _ in range(12):
            roots = rng.sample(range(-30, 31), n)
            polynomial = sp.prod(z - root for root in roots).expand()
            derivative = sp.diff(polynomial, z)
            product_at_roots = sp.prod(abs(derivative.subs(z, root)) for root in roots)
            resultant = abs(sp.resultant(polynomial, derivative, z))
            assert sp.simplify(product_at_roots - resultant) == 0


def exact_coefficients(roots: list[tuple[Fraction, Fraction]]) -> list[sp.Expr]:
    z = sp.symbols("z")
    gaussian = [sp.Rational(a.numerator, a.denominator) +
                sp.I * sp.Rational(b.numerator, b.denominator) for a, b in roots]
    polynomial = sp.Poly(sp.prod(z - root for root in gaussian), z)
    return list(reversed(polynomial.all_coeffs()))


def check_reciprocal_coefficient_identity() -> None:
    rng = random.Random(1041)
    for n in range(2, 9):
        roots: list[tuple[Fraction, Fraction]] = []
        for _ in range(n):
            # Gaussian rationals strictly inside the unit disk.
            while True:
                a = Fraction(rng.randint(-7, 7), 10)
                b = Fraction(rng.randint(-7, 7), 10)
                if a * a + b * b < 1:
                    roots.append((a, b))
                    break
        coeffs = exact_coefficients(roots)
        c0 = coeffs[0]
        deficit = sp.simplify(1 - c0 * sp.conjugate(c0))
        for k in range(n + 1):
            difference = sp.simplify(coeffs[k] - c0 * sp.conjugate(coeffs[n - k]))
            # Squaring avoids approximate complex absolute values.
            assert sp.simplify(
                difference * sp.conjugate(difference)
                - math.comb(n, k) ** 2 * deficit ** 2
            ) <= 0


def check_root_ray_factor_identity() -> None:
    t, ar, ai, br, bi = sp.symbols("t ar ai br bi", real=True)
    a = ar + sp.I * ai
    b = br + sp.I * bi
    lhs = sp.expand_complex((1 - t * a * sp.conjugate(b)) *
                            (1 - t * sp.conjugate(a) * b)
                            - (t * a - b) * (t * sp.conjugate(a) - sp.conjugate(b)))
    rhs = (1 - b * sp.conjugate(b)) * (1 - t**2 * a * sp.conjugate(a))
    assert sp.simplify(sp.expand_complex(lhs - rhs)) == 0


def classify_worst_phase(n: int, d: int) -> str:
    g = math.gcd(n, d)
    N, D = n // g, d // g
    strict_min = g * ((N - 1) // 2)
    if strict_min > d:
        return "noncentral"
    if N == 2 and D == 1:
        return "even-half-core"
    if N % 2 == 1 and N == 2 * D + 1:
        return "odd-quintic-family"
    if N % 2 == 0 and D == N // 2 - 1:
        assert N % 4 == 0
        return "even-quartic-family"
    raise AssertionError((n, d, g, N, D, strict_min))


def check_cyclic_classification() -> dict[str, int]:
    counts: dict[str, int] = {}
    for n in range(2, 1001):
        for d in range(1, n // 2 + 1):
            kind = classify_worst_phase(n, d)
            counts[kind] = counts.get(kind, 0) + 1
    return counts


def check_cubic_no_go() -> None:
    alpha = sp.Rational(1)
    speeds = (sp.Rational(3, 2) / alpha, sp.Rational(3) / alpha,
              sp.Rational(3, 2) / alpha)
    assert min(a + b for a, b in combinations(speeds, 2)) == 3 > 2
    y = sp.symbols("y", real=True)
    z = -1 + sp.I * y
    q = -z**3 + alpha * z - 1
    assert sp.simplify(sp.re(q) - (-alpha - 3 * y**2)) == 0
    assert 4 - 2 * sp.sqrt(3) > 0


def main() -> None:
    check_merge_exponents()
    check_resultants()
    check_reciprocal_coefficient_identity()
    check_root_ray_factor_identity()
    counts = check_cyclic_classification()
    check_cubic_no_go()
    print("PASS: merge exponents and resultants")
    print("PASS: reciprocal coefficient and root-ray factor identities")
    print("PASS: cyclic classification through degree 1000", counts)
    print("PASS: exact cubic pointwise no-go and connector margin")


if __name__ == "__main__":
    main()
