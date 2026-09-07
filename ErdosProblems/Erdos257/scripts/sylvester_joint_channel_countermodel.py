#!/usr/bin/env python3
"""Exact audit of the Sylvester joint-channel countermodel."""

from __future__ import annotations

from fractions import Fraction
from math import gcd


def sylvester(count: int) -> list[int]:
    values = [2]
    for _ in range(1, count):
        q = values[-1]
        values.append(q * (q - 1) + 1)
    return values


def main() -> None:
    qs = sylvester(8)
    product = 1
    prefix = Fraction(0)

    for index, q in enumerate(qs, start=1):
        assert all(gcd(q, old) == 1 for old in qs[: index - 1])
        product *= q
        prefix += Fraction(1, q)

        assert product == (qs[index] - 1 if index < len(qs) else product)
        assert prefix == 1 - Fraction(1, product)

        tail = 1 - prefix
        assert tail == Fraction(1, product)
        assert tail.denominator == product

        if index > 1:
            previous_product = product // q
            previous_tail = Fraction(1, previous_product)
            assert previous_tail - tail == Fraction(1, q)
            assert tail == previous_tail / q

    print("Sylvester joint-channel audit passed")
    print("first denominators:", qs[:5])
    print("eighth-tail denominator digits:", len(str(product)))


if __name__ == "__main__":
    main()
