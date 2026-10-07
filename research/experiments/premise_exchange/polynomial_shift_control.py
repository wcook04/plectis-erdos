#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact finite residue control for the Q-selected rational orbit.

The eight residues exhaust the two modular calculations used in the paper.
The proof that Q has a root modulo every prime and the general polynomial
criterion remain mathematical arguments, not outcomes of this script.
"""

from fractions import Fraction


def q(n: int) -> int:
    return (n * n - 2) * (n * n - 3) * (n * n - 6)


residues = tuple(q(n) % 8 for n in range(8))
assert residues == (4, 6, 4, 6, 4, 6, 4, 6)
assert pow(2, 8, 255) == 1

for shift_residue, index_residue, expected in (
    (4, 3, Fraction(120, 255)),
    (6, 1, Fraction(126, 255)),
):
    numerator = (pow(2, index_residue, 255) * (pow(2, shift_residue, 255) - 1)) % 255
    distance = Fraction(min(numerator, 255 - numerator), 255)
    assert distance == expected
    assert distance > Fraction(7, 16)
    print(f"h ≡ {shift_residue} (mod 8), N ≡ {index_residue} (mod 8): distance = {distance}")

print("Q(n) mod 8 for n = 0,...,7:", residues)
