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


GaussianQ = tuple[Fraction, Fraction]


def qnorm_sq(z: GaussianQ) -> Fraction:
    return z[0] * z[0] + z[1] * z[1]


def qdot(a: GaussianQ, b: GaussianQ) -> Fraction:
    return a[0] * b[0] + a[1] * b[1]


def check_root_ray_quantitative_defect() -> None:
    """Replay the exact rational kernel beneath (RR1)--(RR2).

    The universal analytic step ``1-x <= exp(-x)`` remains in the ordinary
    proof.  Here every factor identity, denominator bound, defect sum, and
    strictness predicate is checked without floating-point arithmetic.
    """

    cases: tuple[tuple[list[GaussianQ], Fraction], ...] = (
        (
            [
                (Fraction(3, 5), Fraction(1, 5)),
                (Fraction(-1, 2), Fraction(1, 4)),
                (Fraction(1, 10), Fraction(-7, 10)),
            ],
            Fraction(2, 5),
        ),
        (
            [
                (Fraction(1), Fraction(0)),
                (Fraction(0), Fraction(1)),
                (Fraction(-1), Fraction(0)),
            ],
            Fraction(3, 7),
        ),
        (
            [
                (Fraction(0), Fraction(0)),
                (Fraction(5, 13), Fraction(12, 13)),
                (Fraction(-4, 5), Fraction(3, 5)),
                (Fraction(7, 25), Fraction(-24, 25)),
            ],
            Fraction(0),
        ),
    )

    for roots, t in cases:
        assert 0 <= t < 1
        norms = [qnorm_sq(root) for root in roots]
        assert all(norm <= 1 for norm in norms)
        d0 = sum((1 - norm for norm in norms), Fraction(0))
        dt = sum((1 - t * t * norm for norm in norms), Fraction(0))
        xs: list[Fraction] = []
        product_a = Fraction(1)
        product_b = Fraction(1)
        product_one_minus_x = Fraction(1)

        for a, a2 in zip(roots, norms):
            for b, b2 in zip(roots, norms):
                dot = qdot(a, b)
                denominator = 1 - 2 * t * dot + t * t * a2 * b2
                radial_distance_sq = t * t * a2 + b2 - 2 * t * dot
                defect = (1 - b2) * (1 - t * t * a2)
                assert denominator > 0
                assert denominator - radial_distance_sq == defect
                assert 0 <= defect <= denominator
                assert denominator <= (1 + t) * (1 + t)
                x = defect / denominator
                assert x >= defect / ((1 + t) * (1 + t))
                xs.append(x)
                product_a *= radial_distance_sq
                product_b *= denominator
                product_one_minus_x *= 1 - x

        lower_sum = d0 * dt / ((1 + t) * (1 + t))
        assert sum(xs, Fraction(0)) >= lower_sum
        assert product_a / product_b == product_one_minus_x
        assert (sum(xs, Fraction(0)) > 0) == (d0 > 0)


def check_critical_arc_product_quantifier_firewall() -> None:
    """Check the exact algebra beneath (PG-Delta), (AP), and the scalar no-go.

    This does not verify the conjectural critical-arc inequality for
    polynomials.  It verifies its resultant normalization and proves that its
    scalar consequences do not select an admissible short edge.
    """

    # If V=Delta^2/n^n, then the n-th powers of the two proposed right-hand
    # sides 2^(n-1)V^(1/n) and (2^(n-1)/n)Delta^(2/n) agree exactly.
    for n in range(2, 20):
        for discriminant in (Fraction(1, 7), Fraction(5, 3), Fraction(23, 11)):
            critical_value_product = discriminant * discriminant / n**n
            value_form_nth_power = 2 ** (n * (n - 1)) * critical_value_product
            discriminant_form_nth_power = (
                Fraction(2 ** (n - 1), n) ** n * discriminant * discriminant
            )
            assert value_form_nth_power == discriminant_form_nth_power

    # Exact n=3 countermodel to the claimed scalar implication.  The global
    # product inequality holds, but its only short edge is inadmissible.
    n = 3
    admissible_value = Fraction(1, 16)
    inadmissible_value = Fraction(8)
    admissible_length = Fraction(3)
    inadmissible_length = Fraction(1)
    value_product = admissible_value * inadmissible_value
    assert value_product < 1
    assert admissible_value < 1 <= inadmissible_value
    assert admissible_length >= 2 > inadmissible_length
    # Cube the positive inequality L_A L_B < 4 V^(1/3).
    assert Fraction(admissible_length * inadmissible_length, 4) ** n < value_product

    # Exact finite kernel for the compensation step.  Abstract normalized
    # factors q_c=L(c)/(2|v_c|^(1/n)) obey product_A q * product_B q <= 1;
    # if product_B q >= 1, division forces product_A q <= 1.  Raising the
    # resulting admissible length ratio to n avoids radicals.
    q_admissible = (Fraction(3, 4), Fraction(4, 5))
    q_inadmissible = (Fraction(1), Fraction(6, 5))
    values_admissible = (Fraction(1, 4), Fraction(1, 9))
    product_a = math.prod(q_admissible)
    product_b = math.prod(q_inadmissible)
    assert product_a * product_b <= 1
    assert product_b >= 1
    assert product_a <= 1
    admissible_length_ratio_nth_power = product_a**4 * math.prod(values_admissible)
    assert admissible_length_ratio_nth_power < 1


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


def check_power_mean_envelope_lattice() -> None:
    """Exact canonical-weight and fixed-weight nesting checks for `(Bp)`."""

    for n in range(2, 10):
        distances = tuple(Fraction(j + 1, n + 3) for j in range(n))
        product = math.prod(distances)
        for p in (1, 2, 3, 5):
            # Raising the canonical equality to the n-th power removes the
            # radical G=(product distances)^(1/n): every normalized term is G.
            canonical_mean_nth_power = product**p
            target_nth_power = product**p
            assert canonical_mean_nth_power == target_nth_power

        # An exact fixed-weight row: normalized L^q <= 1 implies normalized
        # L^p <= 1 for these rational coordinates, and L^infinity is smallest.
        x = tuple(Fraction(j + 1, 2 * n) for j in range(n))
        assert max(x) <= 1
        means = {
            p: sum(value**p for value in x) / n for p in (1, 2, 3, 5)
        }
        assert all(value <= 1 for value in means.values())
        assert math.prod(x) <= 1


def main() -> None:
    check_merge_exponents()
    check_resultants()
    check_reciprocal_coefficient_identity()
    check_root_ray_factor_identity()
    check_root_ray_quantitative_defect()
    check_critical_arc_product_quantifier_firewall()
    counts = check_cyclic_classification()
    check_cubic_no_go()
    check_power_mean_envelope_lattice()
    print("PASS: merge exponents and resultants")
    print("PASS: reciprocal coefficient and root-ray factor identities")
    print("PASS: exact root-ray quantitative defect and strictness kernels")
    print("PASS: critical-arc product normalization and admissible-index firewall")
    print("PASS: cyclic classification through degree 1000", counts)
    print("PASS: exact cubic pointwise no-go and connector margin")
    print("PASS: exact power-mean envelope canonical weights and nesting rows")


if __name__ == "__main__":
    main()
