#!/usr/bin/env python3
"""Exact regressions for the scalar-localisation and dyadic-height no-go.

The script is diagnostic evidence only; the exported mathematical authority
lives in ``AdelicHeightObstruction.lean``.  All calculations use ``Fraction``
and every displayed inequality is asserted before the receipt is printed.
"""

from __future__ import annotations

import json
from fractions import Fraction
from math import gcd


def mersenne(n: int) -> int:
    return (1 << n) - 1


def v2_int(n: int) -> int:
    if n == 0:
        raise ValueError("v2(0) is not finite")
    n = abs(n)
    return (n & -n).bit_length() - 1


def v2_fraction(x: Fraction) -> int:
    return v2_int(x.numerator) - v2_int(x.denominator)


def odd_rational_mod(x: Fraction, modulus: int) -> int:
    assert x.denominator % 2 == 1
    return x.numerator * pow(x.denominator, -1, modulus) % modulus


def block_receipt(name: str, exponents: list[int]) -> dict[str, int | str]:
    length = len(exponents)
    r = v2_int(length)
    assert length == 1 << r
    m = exponents[0]
    assert length < m
    block = sum((Fraction(1, mersenne(n)) for n in exponents), Fraction())
    denominator = block.denominator
    channel = gcd(denominator, mersenne(m))
    complement = denominator // channel
    assert v2_fraction(block) == r
    assert denominator > 1 << (m + r - 1)
    assert complement > 1 << (r - 1)
    return {
        "family": name,
        "block": f"{exponents[0]}..{exponents[-1]}",
        "length": length,
        "r": r,
        "numerator_v2": v2_fraction(block),
        "denominator_bits": denominator.bit_length(),
        "channel_bits": channel.bit_length(),
        "complement_bits": complement.bit_length(),
        "complement_floor": 1 << (r - 1),
    }


def target_den_parity_receipt() -> dict[str, object]:
    exponents = list(range(10, 80))
    prefixes = [Fraction()]
    for n in exponents:
        prefixes.append(prefixes[-1] + Fraction(1, mersenne(n)))

    even_target = Fraction(1, 2)
    even_vals = [v2_fraction(even_target - s) for s in prefixes]
    assert set(even_vals) == {-1}

    odd_target = Fraction(1, 3)
    matches: dict[int, int] = {}
    for r in range(1, 7):
        modulus = 1 << r
        # Start after exponent r; the next 2^r prefix states must be complete.
        start = max(0, r - exponents[0] + 1)
        residues = [odd_rational_mod(prefixes[start + t], modulus) for t in range(modulus)]
        assert len(set(residues)) == modulus
        target_residue = odd_rational_mod(odd_target, modulus)
        offset = residues.index(target_residue)
        k = start + offset
        assert v2_fraction(odd_target - prefixes[k]) >= r
        matches[r] = k

    return {
        "even_target": str(even_target),
        "even_tail_v2_values": sorted(set(even_vals)),
        "odd_target": str(odd_target),
        "synchronizing_prefix_by_depth": matches,
    }


def main() -> None:
    rows = [
        block_receipt("dense", list(range(17, 33))),
        block_receipt("odd_dense", list(range(33, 64, 2))),
        block_receipt(
            "primes",
            [59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131],
        ),
        block_receipt("fibonacci", [55, 89, 144, 233, 377, 610, 987, 1597]),
        block_receipt("powers_of_two", [16, 32, 64, 128]),
    ]
    print(
        json.dumps(
            {
                "schema": "adelic_height_obstruction_exact_receipt_v0",
                "status": "pass",
                "target_den_parity": target_den_parity_receipt(),
                "block_channel_complement": rows,
                "claim_boundary": "finite exact diagnostics; not an irrationality proof",
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
