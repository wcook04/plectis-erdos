#!/usr/bin/env python3
"""Exact checks for AnchorFourFiveReciprocalPowerCeilingNoGo.md."""

from fractions import Fraction
from math import gcd


TARGET_DENOMINATOR = 465
SOURCE_RANK = 9
SOURCE_MERSENNE = (1 << SOURCE_RANK) - 1
A = 472
G = 193


def reciprocal_take(z: Fraction, rank: int) -> Fraction:
    mersenne = (1 << rank) - 1
    assert z < mersenne
    return z * mersenne / (mersenne - z)


def reciprocal_take_inverse(z: Fraction, rank: int) -> Fraction:
    mersenne = (1 << rank) - 1
    return mersenne * z / (mersenne + z)


def boundary_map(P: int, delta: Fraction) -> Fraction:
    return ((4 * P - 1) * delta - P) / (P - 1 + delta)


def audit_instance(m: int) -> dict[str, object]:
    assert m >= 30 and m % 20 == 10
    P = 1 << m
    C = A * P - G
    z = Fraction(C, A)
    delta = Fraction(G, A)

    assert C % TARGET_DENOMINATOR == 0
    assert C % 2 == 1
    assert gcd(C, A) == 1
    assert Fraction(3, 8) < delta < Fraction(1, 2)
    assert P - 1 < z < P
    assert (z.numerator + z.denominator - 1) // z.denominator == P

    predecessor = reciprocal_take_inverse(z, SOURCE_RANK)
    assert Fraction(1 << (SOURCE_RANK - 1)) < predecessor < SOURCE_MERSENNE
    assert reciprocal_take(predecessor, SOURCE_RANK) == z
    assert predecessor.numerator % TARGET_DENOMINATOR == 0
    assert predecessor.denominator % 2 == 1

    # The post-rank-9 state skips 10,...,m.  Rows below m are dyadically safe;
    # row m is the first unsafe row in this local block.
    for rank in range(10, m):
        assert z > (1 << rank)
        assert z > (1 << rank) - 1
    assert (1 << m) - 1 < z < (1 << m)

    common_height = C // TARGET_DENOMINATOR
    residual = 1 / z
    assert residual == Fraction(A, TARGET_DENOMINATOR * common_height)
    assert residual < Fraction(1, TARGET_DENOMINATOR)

    # Algebraic conjugacy can be checked at arbitrary rational coordinates.
    probe = Fraction(2, 5)
    mapped_z = reciprocal_take(Fraction(P) - probe, m + 1)
    assert mapped_z == Fraction(2 * P) - boundary_map(P, probe)

    return {
        "rank": m,
        "power_bits": P.bit_length(),
        "reciprocal_numerator_bits": C.bit_length(),
        "delta": f"{G}/{A}",
        "predecessor_numerator_divisible_by_465": True,
        "predecessor_denominator_odd": True,
        "first_unsafe_rank_in_local_block": m,
    }


def main() -> None:
    assert pow(2, 20, TARGET_DENOMINATOR) == 1
    assert pow(2, 10, TARGET_DENOMINATOR) == 94
    assert (A * 94 - G) % TARGET_DENOMINATOR == 0
    assert gcd(A, TARGET_DENOMINATOR) == 1
    assert gcd(SOURCE_MERSENNE, TARGET_DENOMINATOR) == 1

    rows = [audit_instance(m) for m in (30, 50, 70, 90, 110)]
    print({"status": "ok", "instances": rows})


if __name__ == "__main__":
    main()
