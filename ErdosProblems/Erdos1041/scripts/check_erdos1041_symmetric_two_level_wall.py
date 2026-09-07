#!/usr/bin/env python3
"""Exact replay for the symmetric two-level saddle-wall family.

All decisive comparisons use ``fractions.Fraction``.  Decimal output is only
for readable diagnostics; no floating-point continuation is used.
"""

from __future__ import annotations

from decimal import Decimal, getcontext
from fractions import Fraction


def _decimal_sqrt(value: Fraction) -> Decimal:
    return (Decimal(value.numerator) / Decimal(value.denominator)).sqrt()


def _outer_power(m: int, r: Fraction) -> Fraction:
    """Return q_outer**m for the degree-2m family."""

    return (1 + r) ** m / (2 ** (m - 1) * (1 + r**m))


def _full_product_square(m: int, r: Fraction) -> Fraction:
    """Return the square of the full limiting admissible product."""

    return r ** (m - 1) * _outer_power(m, r) ** 2


def main() -> int:
    getcontext().prec = 50

    checked_rows = 0
    largest = Fraction(0)
    largest_row: tuple[int, Fraction] | None = None
    for m in range(2, 65):
        for denominator in (7, 10, 17, 31, 100):
            for numerator in range(1, denominator):
                r = Fraction(numerator, denominator)

                # Convexity/power-mean kernel used in the ordinary proof.
                assert (1 + r) ** m <= 2 ** (m - 1) * (1 + r**m)
                assert _outer_power(m, r) <= 1
                full_square = _full_product_square(m, r)
                assert full_square < 1

                # Exact critical-level ordering gamma-beta.
                a = Fraction(1)
                b = r
                beta = a**m * b**m
                gamma = ((a**m + b**m) / 2) ** 2
                assert gamma - beta == ((a**m - b**m) / 2) ** 2

                if full_square > largest:
                    largest = full_square
                    largest_row = (m, r)
                checked_rows += 1

    # Quartic pair and complete-product slack factorizations.
    for denominator in range(2, 80):
        for numerator in range(1, denominator + 1):
            r = Fraction(numerator, denominator)
            pair_slack = 2 * (1 + r**2) - r * (1 + r) ** 2
            assert pair_slack == (1 - r) * (r**2 + r + 2)
            full_slack = 4 * (1 + r**2) ** 2 - r * (1 + r) ** 4
            assert full_slack == (1 - r) * (
                r**4 + r**3 + 7 * r**2 + 3 * r + 4
            )

    # Exact counterexample to the discarded scalar T threshold.  For m=2,
    # a=1, b=9/10, its fourth power is
    #   (a+2b)^4 <= 32ab(a^2+b^2),
    # and the left-minus-right gap is strictly positive.
    r = Fraction(9, 10)
    threshold_gap = (1 + 2 * r) ** 4 - 32 * r * (1 + r**2)
    assert threshold_gap == Fraction(5836, 625)

    pair_square = r * (1 + r) ** 2 / (2 * (1 + r**2))
    assert pair_square == Fraction(3249, 3620)
    assert 1 - pair_square == Fraction(371, 3620)

    assert largest_row is not None
    print("SYMMETRIC TWO-LEVEL WALL: PASS")
    print(f"exact all-even rows={checked_rows}")
    print(
        "largest sampled full AP=",
        _decimal_sqrt(largest),
        "at m,r=",
        largest_row,
    )
    print(f"quartic threshold fourth-power gap={threshold_gap}")
    print(f"quartic true pair square={pair_square}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
