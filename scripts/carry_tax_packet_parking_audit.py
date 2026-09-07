#!/usr/bin/env python3
"""Exact receipts for CarryTaxPacketParking.md."""

from fractions import Fraction
from math import gcd, lcm


def w(n: int) -> Fraction:
    return Fraction(1, (1 << n) - 1)


def cyl(a: int, b: int) -> Fraction:
    return w(a) * w(b)


def theta(r: int, c: int) -> Fraction:
    return Fraction(1, 1 << c) * w(r - c) - w(r)


def theta_sum(r: int, c: int) -> Fraction:
    return sum(
        (Fraction(1, 1 << s) * cyl(r - s, r - s + 1)
         for s in range(1, c + 1)),
        Fraction(),
    )


def check_tax(max_r: int = 120) -> int:
    count = 0
    for r in range(4, max_r + 1):
        for c in range(0, r - 1):
            assert theta_sum(r, c) == theta(r, c)
            if c:
                assert 2 * theta(r, c) - cyl(r - 1, r) == theta(r - 1, c - 1)
            count += 1
    return count


def check_power_packets(max_endpoint: int = 90) -> tuple[int, Fraction, tuple[int, int, int]]:
    count = 0
    max_ratio = Fraction()
    max_arg = (0, 0, 0)
    for a in range(2, max_endpoint + 1):
        for b in range(a, max_endpoint + 1):
            for j in range(0, b + 1):
                r = a + b - j
                c = b - j
                packet = (1 << j) * cyl(a, b)
                assert packet > w(r)
                assert packet < 2 * w(r)
                surplus = packet - w(r)
                assert surplus > theta(r, c)
                if c + 1 < r:
                    assert surplus < theta(r, c + 1)
                assert surplus < w(a + r - 2)

                numerator = (1 << a) + (1 << b) - (1 << j) - 1
                ratio = Fraction(
                    numerator * (1 << c),
                    ((1 << b) - 1) * ((1 << (a + c)) - 1),
                )
                assert ratio <= Fraction(8, 15)
                if ratio > max_ratio:
                    max_ratio = ratio
                    max_arg = (a, b, j)
                count += 1
    assert max_ratio == Fraction(8, 15)
    assert max_arg == (2, 2, 0)
    return count, max_ratio, max_arg


def check_anchored_representations(max_endpoint: int = 30) -> int:
    count = 0
    for a in range(2, max_endpoint + 1):
        for b in range(a, max_endpoint + 1):
            for j in range(0, b + 1):
                r = a + b - j
                numerator = (1 << a) + (1 << b) - (1 << j) - 1
                product = ((1 << b) - 1) * ((1 << r) - 1)
                # A deliberately nonminimal exponent.  For every prime power
                # dividing `product`, LTE and the factor `product` in `order`
                # supply at least the required valuation.  Modular powering
                # checks divisibility without constructing 2^order.
                order = lcm(b, r) * product
                assert pow(2, order, product) == 1
                surplus = (1 << j) * cyl(a, b) - w(r)
                assert surplus == Fraction(
                    numerator,
                    ((1 << a) - 1) * product,
                )
                parent_load = Fraction(1 << j, 1 << b)
                ratio = Fraction(
                    numerator * (1 << (b - j)),
                    ((1 << b) - 1) * ((1 << r) - 1),
                )
                assert ratio <= Fraction(8, 15)
                # Since (2^order-1)/2^order < 1, this ratio strictly
                # majorizes the actual anchored load ratio B/2^order.
                assert ratio * parent_load == Fraction(numerator, product)
                count += 1
    return count


def check_first_lift() -> dict[str, object]:
    a = 340
    bits = [j for j in range(a.bit_length()) if (a >> j) & 1]
    assert bits == [2, 4, 6, 8]
    ranks = sorted(11 + 10 - j for j in bits)
    capacities = sorted(11 - j for j in bits)
    assert ranks == [13, 15, 17, 19]
    assert capacities == [3, 5, 7, 9]
    lift = a * cyl(11, 10)
    assert w(13) < lift < w(12)
    return {
        "multiplicity": a,
        "bits": bits,
        "ranks": ranks,
        "capacities": capacities,
    }


def main() -> None:
    tax_checks = check_tax()
    packet_checks, max_ratio, max_arg = check_power_packets()
    anchored_checks = check_anchored_representations()
    first_lift = check_first_lift()
    print(
        {
            "tax_checks": tax_checks,
            "power_packet_checks": packet_checks,
            "anchored_representation_checks": anchored_checks,
            "max_contraction_ratio": str(max_ratio),
            "max_contraction_arg": max_arg,
            "first_lift": first_lift,
            "global_parking_theorem": "open",
        }
    )


if __name__ == "__main__":
    main()
