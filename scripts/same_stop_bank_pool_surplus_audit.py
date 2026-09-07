#!/usr/bin/env python3
"""Exact audit for the same-stop pooled bank-surplus law."""

from fractions import Fraction
from math import lcm


def w(n: int) -> Fraction:
    return Fraction(1, (1 << n) - 1)


def cylinder(a: int, b: int) -> Fraction:
    return w(a) * w(b)


def carry_tax(n: int, j: int) -> Fraction:
    return w(n - j) - (1 << j) * w(n)


def tax_sum(n: int, j: int) -> Fraction:
    return sum(
        ((1 << (j - q)) * cylinder(n - q, n - q + 1)
         for q in range(1, j + 1)),
        Fraction(0),
    )


def anchored_coefficient(a: int, n: int, j: int) -> tuple[int, int, int]:
    r = n - j
    h = lcm(n, r)
    coefficient = ((1 << h) - 1) * (
        Fraction(1 << (a + j), (1 << n) - 1)
        - Fraction((1 << a) - 1, (1 << r) - 1)
    )
    assert coefficient.denominator == 1
    return r, h, coefficient.numerator


def main() -> None:
    checks = 0
    maximum_ratio = Fraction(0)
    maximum_row = None

    for a in range(2, 25):
        for b in range(a, 38):
            n = a + b
            for j in range(0, b + 1):
                tax = carry_tax(n, j)
                assert tax == tax_sum(n, j)

                bank_surplus = (1 << j) * cylinder(a, n) - tax
                closed_form = (1 << (a + j)) * cylinder(a, n) - w(n - j)
                assert bank_surplus == closed_form
                assert bank_surplus > 0

                full_left = (1 << j) * cylinder(a, b)
                full_right = w(n - j) + bank_surplus + (1 << j) * cylinder(n, b)
                assert full_left == full_right

                r, h, coefficient = anchored_coefficient(a, n, j)
                assert coefficient > 0
                assert bank_surplus == coefficient * cylinder(a, h)
                assert all(
                    a + h - bit > r
                    for bit in range(coefficient.bit_length())
                    if (coefficient >> bit) & 1
                )
                assert b + n - j > r

                parent_load = Fraction(1 << j, 1 << b)
                child_load = Fraction(coefficient, 1 << h) + Fraction(1 << j, 1 << n)
                ratio = child_load / parent_load
                assert ratio < Fraction(31, 60)
                if ratio > maximum_ratio:
                    maximum_ratio = ratio
                    maximum_row = (a, b, j)
                checks += 1

    a, b, j = 10, 11, 8
    n = a + b
    one_bank = cylinder(a, n)
    deepest_tax = cylinder(n - j, n - j + 1)
    pooled_surplus = (1 << j) * one_bank - carry_tax(n, j)
    assert one_bank < deepest_tax
    assert pooled_surplus > 0
    assert pooled_surplus == (1 << (a + j)) * cylinder(a, n) - w(n - j)

    assert maximum_row is not None
    print(f"checked {checks} exact bank-pool rows")
    print(
        "maximum audited two-branch load ratio:",
        f"{maximum_ratio.numerator}/{maximum_ratio.denominator}",
        "at",
        maximum_row,
    )
    print("256*M(10,11): one bank misses deepest tax, pooled surplus is positive")


if __name__ == "__main__":
    main()
