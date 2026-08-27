#!/usr/bin/env python3
"""Exact checker for the five-root counterexample to Conjecture U."""

from fractions import Fraction as F


def unit_point(q: F) -> tuple[F, F]:
    return (1 - q * q) / (1 + q * q), 2 * q / (1 + q * q)


root_parameters = [F(9, 13), F(47, 20), F(-3), F(-11, 13), F(-1, 45)]
test_parameters = [F(47, 20), F(100), F(-3), F(-3, 10), F(-1, 45)]
roots = [unit_point(q) for q in root_parameters]
tests = [unit_point(q) for q in test_parameters]
s = F(3, 20)
threshold_sq = (1 + s**5) ** 2


def cross(a: tuple[F, F], b: tuple[F, F]) -> F:
    return a[0] * b[1] - a[1] * b[0]


def product_norm_sq(x: tuple[F, F]) -> F:
    z = s * x[0], s * x[1]
    out = F(1)
    for w in roots:
        out *= (z[0] - w[0]) ** 2 + (z[1] - w[1]) ** 2
    return out


assert all(x * x + y * y == 1 for x, y in roots + tests)
assert all(cross(roots[k], roots[(k + 1) % 5]) > 0 for k in range(5))
margins = []
for k, x in enumerate(tests):
    assert cross(roots[k], x) >= 0
    assert cross(x, roots[(k + 1) % 5]) >= 0
    margin = product_norm_sq(x) - threshold_sq
    assert margin > 0
    margins.append(margin)
    print(f"gap {k}: exact_margin={margin} decimal={float(margin):.12f}")

print("PASS: every one of the five gaps exceeds the regular bound at s=3/20")
