#!/usr/bin/env python3
"""Exact audits for minimal Mersenne primitive-channel service height."""

from __future__ import annotations

from fractions import Fraction
from math import gcd


def mersenne(n: int) -> int:
    return (1 << n) - 1


def audit_one_descendant() -> None:
    # For a=2,4,8,16 these are the complete primitive parts.
    primitive_parts = {2: 3, 4: 5, 8: 17, 16: 257}
    for anchor, primitive_part in primitive_parts.items():
        multiplier = primitive_part - 1
        assert (1 + pow(multiplier, -1, primitive_part)) % primitive_part == 0
        assert all(
            (1 + pow(k, -1, primitive_part)) % primitive_part != 0
            for k in range(2, multiplier)
            if gcd(k, primitive_part) == 1
        )

        total = Fraction(1, mersenne(anchor)) + Fraction(
            1, mersenne(anchor * multiplier)
        )
        assert total.denominator % primitive_part != 0

        ratio = Fraction(mersenne(anchor), mersenne(anchor * multiplier))
        assert ratio < Fraction(1, 1 << (anchor * (primitive_part - 2) - 1))


def audit_accumulated_preservation() -> None:
    primitive_parts = [3, 5, 17, 257]
    accumulated = 1
    for primitive_part in primitive_parts:
        accumulated *= primitive_part

    lower = (accumulated - 1) // 2
    upper = (accumulated + 1) // 2
    assert lower + upper == accumulated
    assert gcd(lower * upper, accumulated) == 1
    assert (
        pow(lower, -1, accumulated) + pow(upper, -1, accumulated)
    ) % accumulated == 0
    assert max(lower, upper) == (accumulated + 1) // 2

    # No pair with smaller maximum can have positive sum divisible by R.
    height = (accumulated - 1) // 2
    assert 2 * height < accumulated

    for primitive_part in primitive_parts:
        assert (
            pow(lower, -1, primitive_part)
            + pow(upper, -1, primitive_part)
        ) % primitive_part == 0


def audit_many_descendant_height_bound() -> None:
    modulus = 3 * 5 * 17
    multipliers = [1, 254, 2, 253, 4, 251, 8, 247]
    assert all(gcd(k, modulus) == 1 for k in multipliers)
    assert sum(pow(k, -1, modulus) for k in multipliers) % modulus == 0
    cleared = sum(
        _product(multipliers[:j] + multipliers[j + 1 :])
        for j in range(len(multipliers))
    )
    assert cleared % modulus == 0
    height = max(multipliers)
    assert modulus <= len(multipliers) * height ** (len(multipliers) - 1)


def _product(values: list[int]) -> int:
    result = 1
    for value in values:
        result *= value
    return result


def main() -> None:
    audit_one_descendant()
    audit_accumulated_preservation()
    audit_many_descendant_height_bound()
    print("Mersenne service-height reversal audit passed")


if __name__ == "__main__":
    main()
