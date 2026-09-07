#!/usr/bin/env python3
"""Exact audit for UniversalCylinderFirstCollisionNoGo.md."""

from fractions import Fraction
from math import gcd


def primitive_coefficient(a: int, b: int, n: int) -> int:
    count = 0
    for p in range(1, n // a + 1):
        remainder = n - a * p
        if remainder <= 0 or remainder % b:
            continue
        q = remainder // b
        if gcd(p, q) == 1:
            count += 1
    return count


def audit_first_collision(maximum_coordinate: int = 32) -> int:
    cases = 0
    for a in range(2, maximum_coordinate + 1):
        for b in range(a, maximum_coordinate + 1):
            g = gcd(a, b)
            first = a + b + a * b // g
            coefficients = [
                primitive_coefficient(a, b, n) for n in range(1, first + 1)
            ]
            assert all(value <= 1 for value in coefficients[:-1])
            assert coefficients[-1] == 2

            A = a // g
            B = b // g
            witnesses = ((B + 1, 1), (1, A + 1))
            for p, q in witnesses:
                assert gcd(p, q) == 1
                assert a * p + b * q == first
            cases += 1
    return cases


def audit_cut(maximum_coordinate: int = 64) -> int:
    cases = 0
    for a in range(2, maximum_coordinate + 1):
        for b in range(a, maximum_coordinate + 1):
            g = gcd(a, b)
            first = a + b + a * b // g
            depth = 2 * first

            supply_bound = Fraction(4, 9) * Fraction(1, 2 ** (b + depth))
            tax = Fraction(1, (2 ** (first - 1) - 1) * (2**first - 1))
            dyadic_separator = Fraction(1, 2 ** (2 * first - 1))

            assert supply_bound < dyadic_separator
            assert dyadic_separator < tax
            assert max(a // g, b // g) <= depth
            cases += 1
    return cases


def main() -> None:
    coefficient_cases = audit_first_collision()
    cut_cases = audit_cut()
    print(f"first-collision cases: {coefficient_cases}")
    print(f"finite-cut cases: {cut_cases}")
    print("universal cylinder first-collision audit: PASS")


if __name__ == "__main__":
    main()
