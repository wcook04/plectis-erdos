#!/usr/bin/env python3
"""Exact audit for OptimalCylinderRecutRenormalisation.md."""

from fractions import Fraction
from math import gcd, lcm


def w(n: int) -> Fraction:
    return Fraction(1, 2**n - 1)


def cylinder(a: int, b: int) -> Fraction:
    return w(a) * w(b)


def primitive_coefficient(a: int, b: int, n: int) -> int:
    count = 0
    for p in range(1, n // a + 1):
        remainder = n - a * p
        if remainder > 0 and remainder % b == 0:
            q = remainder // b
            if gcd(p, q) == 1:
                count += 1
    return count


def audit_optimal_family(maximum_a: int = 24, maximum_k: int = 16) -> int:
    cases = 0
    for a in range(2, maximum_a + 1):
        for k in range(1, maximum_k + 1):
            if gcd(a, k + 1) == 1:
                continue
            b = k * a + 1
            n = a * b + a + b
            s = (n - 1) // a
            coefficient = (2 ** (n - 1) - 1) // (2**a - 1) - 1
            bit_sum = sum(2 ** (i * a) for i in range(1, s))

            assert gcd(a, b) == 1
            assert n - 1 == a * (b + k + 1)
            assert primitive_coefficient(a, b, n - 1) == 0
            assert primitive_coefficient(a, b, n) == 2
            assert lcm(a, n - 1) == n - 1
            assert coefficient == bit_sum

            left = cylinder(a, n - a) + cylinder(b, n - b)
            right = (
                w(n - 1)
                + coefficient * cylinder(n - 1, n)
                + cylinder(n - a, n)
                + cylinder(b, n)
                + cylinder(n - b, n)
            )
            assert left == right

            assert n % 2 == 1
            successor_lower = n - 1
            assert successor_lower % 2 == 0
            assert successor_lower * (successor_lower + 3) == (
                successor_lower * (successor_lower + 1)
                + successor_lower
                + successor_lower
                + 1
                - 1
            )

            lift_fronts = {
                2 * n - 1 - i * a for i in range(1, s)
            }
            expected_fronts = {n + j * a for j in range(1, s)}
            assert lift_fronts == expected_fronts
            assert 2 * n - b in lift_fronts

            if a % 2 == 0:
                t = a // 2
                assert 2 * a + (2 * t + 1) * b == n + a
                if a == 2:
                    assert b % 4 == 3
                    t_left = (b + 1) // 4
                    assert 2 * b + (2 * t_left + 1) * a == n + a - 1
            cases += 1
    return cases


def audit_adjacent_spine(steps: int = 4) -> list[int]:
    lower = 2
    values = [lower]
    for _ in range(steps - 1):
        assert lower % 2 == 0
        upper = lower + 1
        collision = lower * upper + lower + upper
        lower = collision - 1
        assert lower == values[-1] * (values[-1] + 3)
        values.append(lower)
    assert values[:4] == [2, 10, 130, 17290]
    return values


def main() -> None:
    family_cases = audit_optimal_family()
    spine = audit_adjacent_spine()
    print(f"optimal-family cases: {family_cases}")
    print(f"adjacent spine: {spine}")
    print("optimal cylinder recut renormalisation audit: PASS")


if __name__ == "__main__":
    main()
