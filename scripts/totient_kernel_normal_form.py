#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact normal form for the 43 base-six totient sections through depth two.

Run, for example::

    python3 scripts/totient_kernel_normal_form.py --term 2:6:1 --term 1:1:-2

Each term is LEVEL:RESIDUE:INTEGER_COEFFICIENT. The 37 retained coordinates
and six relation coordinates describe the proposed combination exactly. A
nonzero combination has a displayed counterexample with 0 <= n <= 36.
This finite-level result does not decide the irrationality of the totient
series in Erdos problem 249.
"""

from __future__ import annotations

import argparse
import json
from math import isqrt


BASE = 6
DEPTH = 2
MODULUS = 101
ALL_CHANNELS = [(j, r) for j in range(DEPTH + 1) for r in range(BASE**j)]
RETAINED = [(0, 0), (1, 0)] + [(1, r) for r in range(1, BASE)] + [
    (2, r) for r in range(1, BASE**2) if r % BASE != 0
]
# F_omitted = multiplier * F_retained. These follow from the totient
# prime-factor formula and hold for every n >= 0, including phi(0) = 0.
REDUCTIONS = {
    (2, 0): ((1, 0), 6),
    (2, 6): ((1, 1), 2),
    (2, 12): ((1, 2), 4),
    (2, 18): ((1, 3), 3),
    (2, 24): ((1, 4), 4),
    (2, 30): ((1, 5), 2),
}


def totient(n: int) -> int:
    """Euler's totient, with the paper's convention phi(0) = 0."""
    if n == 0:
        return 0
    result = n
    divisor = 2
    while divisor <= isqrt(n):
        if n % divisor == 0:
            result -= result // divisor
            while n % divisor == 0:
                n //= divisor
        divisor += 1
    if n > 1:
        result -= result // n
    return result


def value(channel: tuple[int, int], n: int) -> int:
    j, r = channel
    return totient(BASE**j * n + r)


def determinant_mod_prime(rows: list[list[int]], prime: int) -> int:
    """Compute the ordered evaluation determinant by field elimination."""
    matrix = [[x % prime for x in row] for row in rows]
    size = len(matrix)
    determinant = 1
    for column in range(size):
        pivot = next((i for i in range(column, size) if matrix[i][column]), None)
        if pivot is None:
            return 0
        if pivot != column:
            matrix[column], matrix[pivot] = matrix[pivot], matrix[column]
            determinant = -determinant
        pivot_value = matrix[column][column]
        determinant = determinant * pivot_value % prime
        inverse = pow(pivot_value, -1, prime)
        for row in range(column + 1, size):
            factor = matrix[row][column] * inverse % prime
            for col in range(column, size):
                matrix[row][col] = (matrix[row][col] - factor * matrix[column][col]) % prime
    return determinant % prime


def evaluation_matrix() -> list[list[int]]:
    return [[value(channel, n) for channel in RETAINED] for n in range(37)]


def normalize(terms: dict[tuple[int, int], int]) -> dict[str, object]:
    """Return exact canonical/relation coordinates and an exact witness."""
    invalid = set(terms) - set(ALL_CHANNELS)
    if invalid:
        raise ValueError(f"channel outside base-six depth-two family: {sorted(invalid)}")
    matrix = evaluation_matrix()
    determinant = determinant_mod_prime(matrix, MODULUS)
    if determinant != 17:
        raise ArithmeticError(f"base-six certificate changed: determinant mod 101 = {determinant}")

    coordinates = {channel: terms.get(channel, 0) for channel in RETAINED}
    relation_coordinates = {}
    for omitted, (retained, multiplier) in REDUCTIONS.items():
        coefficient = terms.get(omitted, 0)
        relation_coordinates[omitted] = coefficient
        coordinates[retained] += coefficient * multiplier

    witness = None
    if any(coordinates.values()):
        for n, row in enumerate(matrix):
            total = sum(coordinates[channel] * entry for channel, entry in zip(RETAINED, row))
            if total:
                witness = {"n": n, "exact_value": total}
                break
        if witness is None:
            raise ArithmeticError("nonzero coordinates contradict the determinant certificate")

    def label(channel: tuple[int, int]) -> str:
        return f"{channel[0]}:{channel[1]}"

    return {
        "family": "F_j,r(n) = phi(6^j n + r), 0 <= j <= 2, phi(0) = 0",
        "ordered_retained_channels": [label(channel) for channel in RETAINED],
        "canonical_coefficients": [coordinates[channel] for channel in RETAINED],
        "ordered_omitted_channels": [label(channel) for channel in REDUCTIONS],
        "relation_coefficients": [relation_coordinates[channel] for channel in REDUCTIONS],
        "identity": witness is None,
        "counterexample": witness,
        "certificate": {"rows": "n = 0,...,36", "determinant_mod_101": determinant},
    }


def parse_term(raw: str) -> tuple[tuple[int, int], int]:
    try:
        j, r, coefficient = (int(part) for part in raw.split(":"))
    except ValueError as exc:
        raise argparse.ArgumentTypeError("term must be LEVEL:RESIDUE:INTEGER_COEFFICIENT") from exc
    channel = (j, r)
    if channel not in ALL_CHANNELS:
        raise argparse.ArgumentTypeError(f"channel {j}:{r} is outside the depth-two family")
    return channel, coefficient


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--term", type=parse_term, action="append", required=True)
    args = parser.parse_args()
    terms: dict[tuple[int, int], int] = {}
    for channel, coefficient in args.term:
        terms[channel] = terms.get(channel, 0) + coefficient
    print(json.dumps(normalize(terms), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
