#!/usr/bin/env python3
"""Exact receipts for the primitive-prime divisor-height exclusion."""

from math import isqrt

from sympy import cyclotomic_poly, factorint, n_order


def divisors(value: int) -> list[int]:
    result: list[int] = []
    for divisor in range(1, isqrt(value) + 1):
        if value % divisor == 0:
            result.append(divisor)
            if divisor * divisor != value:
                result.append(value // divisor)
    return sorted(result)


def lift_factor(height: int, rank: int) -> int:
    assert height % rank == 0
    return ((1 << height) - 1) // ((1 << rank) - 1)


def primitive_prime(height: int) -> int:
    value = int(cyclotomic_poly(height, 2))
    for prime in factorint(value):
        prime = int(prime)
        if n_order(2, prime) == height:
            return prime
    raise AssertionError(f"no primitive prime found at height {height}")


def height_receipt(height: int) -> dict[str, object]:
    assert height % 15 == 0
    prime = primitive_prime(height)
    assert prime > 3
    assert n_order(2, prime) == height

    root_coefficient = 1510 * lift_factor(height, 15)
    if height == 15:
        assert prime == 151
        assert 1510 % prime == 0
    else:
        assert lift_factor(height, 15) % prime == 0
    assert root_coefficient % prime == 0

    proper_divisors = [rank for rank in divisors(height) if rank < height]
    assert all(lift_factor(height, rank) % prime == 0 for rank in proper_divisors)

    # Subtracting any Boolean collection of proper-divisor atoms leaves
    # residue 0 modulo p.  Optionally subtracting w_H changes it to -3.
    possible_residues = {0, (-3) % prime}
    assert 6 % prime not in possible_residues

    # At its own height, coefficient 6 is the only integral coefficient in
    # the fatal interval [2 w_H, w_(H-1)).
    upper_numerator = 3 * ((1 << height) - 1)
    upper_denominator = (1 << (height - 1)) - 1
    assert 6 * upper_denominator < upper_numerator
    assert upper_numerator <= 7 * upper_denominator

    return {
        "height": height,
        "primitive_prime": prime,
        "proper_divisor_count": len(proper_divisors),
        "root_coefficient_mod_prime": root_coefficient % prime,
        "possible_residual_classes_mod_prime": sorted(possible_residues),
        "fatal_coefficient": 6,
        "fatal_coefficient_excluded": True,
    }


def main() -> None:
    heights = [15, 30, 45, 60, 75, 90, 105, 120]
    print(
        {
            "receipts": [height_receipt(height) for height in heights],
            "symbolic_input": (
                "Bang-Zsigmondy supplies a primitive prime divisor for "
                "every height divisible by 15"
            ),
            "divisor_rank_coefficient_six_corridor_reachable": False,
        }
    )


if __name__ == "__main__":
    main()
