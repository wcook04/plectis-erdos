#!/usr/bin/env python3
"""Exact audits for CRT compression of Mersenne primitive channels."""

from __future__ import annotations

from fractions import Fraction
from math import gcd


def crt(residues: list[int], moduli: list[int]) -> int:
    modulus = 1
    for q in moduli:
        modulus *= q
    value = 0
    for residue, q in zip(residues, moduli, strict=True):
        partial = modulus // q
        value += residue * partial * pow(partial, -1, q)
    return value % modulus


def two_units(target: int, modulus: int) -> tuple[int, int]:
    for first in range(1, modulus):
        second = (target - first) % modulus
        if gcd(first, modulus) == gcd(second, modulus) == 1:
            return first, second
    raise AssertionError((target, modulus))


def channel_residue(support: set[int], anchor: int, primitive_part: int) -> int:
    total = 0
    for n in support:
        if n % anchor == 0:
            multiplier = n // anchor
            assert gcd(multiplier, primitive_part) == 1
            total += pow(multiplier, -1, primitive_part)
    return total % primitive_part


def service_pair(
    support: set[int], primitive_parts: dict[int, int], *, shift: int = 0
) -> tuple[int, int]:
    anchors = sorted(support)
    largest = max(anchors)
    # The audit supports the power-of-two initial family, whose lcm is largest.
    assert all(largest % a == 0 for a in anchors)
    moduli = [primitive_parts[a] for a in anchors]
    assert all(gcd(moduli[i], moduli[j]) == 1 for i in range(len(moduli)) for j in range(i))

    first_inverse_residues: list[int] = []
    second_inverse_residues: list[int] = []
    for a, modulus in zip(anchors, moduli, strict=True):
        d = largest // a
        current = channel_residue(support, a, modulus)
        target = (-d * current) % modulus
        u, v = two_units(target, modulus)
        first_inverse_residues.append(u)
        second_inverse_residues.append(v)

    k1 = crt([pow(u, -1, q) for u, q in zip(first_inverse_residues, moduli, strict=True)], moduli)
    k2 = crt([pow(v, -1, q) for v, q in zip(second_inverse_residues, moduli, strict=True)], moduli)
    combined_modulus = 1
    for q in moduli:
        combined_modulus *= q
    k1 += (shift + 1) * combined_modulus
    k2 += (shift + 2) * combined_modulus
    assert k1 != k2 and k1 > 1 and k2 > 1
    return largest * k1, largest * k2


def exact_small_audit() -> None:
    primitive_parts = {2: 3, 4: 5, 8: 17}
    support = set(primitive_parts)
    n1, n2 = service_pair(support, primitive_parts)
    extended = support | {n1, n2}

    for a, primitive_part in primitive_parts.items():
        assert channel_residue(extended, a, primitive_part) == 0

    # Here the descendants remain small enough to form the actual Mersenne
    # fractions.  Reduced denominators lose every audited primitive prime.
    total = sum((Fraction(1, (1 << n) - 1) for n in extended), Fraction(0))
    for primitive_part in primitive_parts.values():
        assert total.denominator % primitive_part != 0


def arbitrary_demand_count_audit() -> None:
    # For a=2^i, the primitive parts are the displayed Fermat factors.
    primitive_parts = {2: 3, 4: 5, 8: 17, 16: 257, 32: 65537}
    support = set(primitive_parts)
    n1, n2 = service_pair(support, primitive_parts, shift=3)
    extended = support | {n1, n2}
    for a, primitive_part in primitive_parts.items():
        assert channel_residue(extended, a, primitive_part) == 0


def main() -> None:
    exact_small_audit()
    arbitrary_demand_count_audit()
    print("Mersenne CRT shared-descendant audit passed")


if __name__ == "__main__":
    main()
