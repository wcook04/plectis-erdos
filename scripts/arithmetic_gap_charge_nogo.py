#!/usr/bin/env python3
"""Exact arithmetic for finite survivor cylinders of the 1/21 greedy orbit."""

from fractions import Fraction
from math import gcd


NAMED_PRIMES = (7, 31, 151)


def q(rank: int) -> int:
    return (1 << rank) - 1


def valuation(value: int, prime: int) -> int:
    value = abs(value)
    if value == 0:
        raise ValueError("the valuation of zero is not used here")
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


def multiplicative_order_two(prime: int) -> int:
    residue = 2 % prime
    order = 1
    while residue != 1:
        residue = (2 * residue) % prime
        order += 1
    return order


def orbit(stop_rank: int):
    """Return unreduced (A_r,D_r,B_r) before the decision at each rank r."""
    rank = 2
    numerator = 1
    denominator = 21
    rows = {}
    while rank <= stop_rank:
        gap = 2 * denominator - q(rank) * numerator
        bit = int(q(rank) * numerator >= denominator)
        rows[rank] = (numerator, denominator, gap, bit)
        if rank == stop_rank:
            break
        numerator = q(rank) * numerator - bit * denominator
        denominator = q(rank) * denominator
        rank += 1
    return rows


def verify_one_step(rows) -> None:
    for rank in range(2, max(rows)):
        numerator, denominator, gap, bit = rows[rank]
        next_numerator, next_denominator, next_gap, _ = rows[rank + 1]
        next_q = q(rank + 1)
        assert next_denominator == q(rank) * denominator
        assert next_numerator == q(rank) * numerator - bit * denominator
        coefficient = 1 if bit else next_q + 1
        assert next_gap == next_q * gap - coefficient * denominator


def verify_six_step(rows) -> None:
    for rank in range(2, max(rows) - 5, 6):
        numerator, denominator, gap, _ = rows[rank]
        next_numerator, next_denominator, next_gap, _ = rows[rank + 6]
        bits = [rows[rank + i][3] for i in range(6)]
        product = 1
        for i in range(6):
            product *= q(rank + i)
        digit_sum = sum(
            bits[i] * (product // q(rank + i)) for i in range(6)
        )
        assert next_denominator == denominator * product
        assert next_numerator == product * numerator - denominator * digit_sum

        multiplier = q(rank + 6) * product // q(rank)
        correction = (
            2 * product
            - 2 * multiplier
            + q(rank + 6) * digit_sum
        )
        assert next_gap == multiplier * gap + denominator * correction


def primitive_charge(gap: int, denominator: int) -> int:
    return gap // gcd(abs(gap), denominator)


def step(y: Fraction, z: Fraction):
    bit = int(y >= 1)
    return (2 + z) * (y - bit), z / (2 + z), bit


def branch_offset(z: Fraction, bits) -> Fraction:
    offset = Fraction(0)
    power = 1
    for bit in bits:
        offset += Fraction(bit, power + (power - 1) * z)
        power *= 2
    return offset


def verify_opposite_sign_pair() -> None:
    bits = (0, 0, 0, 1, 0, 1)
    z = Fraction(1, 3)
    dilation = 64 + 63 * z
    prime_product = 7 * 31 * 151
    clearing_denominator = 1_000_000_007
    assert gcd(prime_product, clearing_denominator) == 1
    offset = branch_offset(z, bits)

    charges = (1, 1 - prime_product)
    for charge in charges:
        terminal_y = 2 - Fraction(charge, clearing_denominator)
        y = offset + terminal_y / dilation
        assert 0 <= y < 2
        observed = []
        current_y, current_z = y, z
        for _ in range(6):
            current_y, current_z, bit = step(current_y, current_z)
            observed.append(bit)
        assert tuple(observed) == bits
        assert current_y == terminal_y
        cleared_gap = (2 - current_y) * clearing_denominator
        assert cleared_gap == charge
        assert all(valuation(int(cleared_gap), p) == 0 for p in NAMED_PRIMES)
        assert all(int(cleared_gap) % p == 1 for p in NAMED_PRIMES)
    assert charges[0] > 0 > charges[1]
    assert all(charges[0] % p == charges[1] % p for p in NAMED_PRIMES)


def main() -> None:
    rows = orbit(50)
    verify_one_step(rows)
    verify_six_step(rows)
    verify_opposite_sign_pair()

    print("fixed-prime absorption thresholds")
    for prime in NAMED_PRIMES:
        order = multiplicative_order_two(prime)
        threshold = 2 * order
        assert all(rows[r][2] % prime == 0 for r in range(threshold, 51))
        print(f"p={prime:3d} ord_p(2)={order:2d}  B_r divisible for r>={threshold}")

    print("\naligned six-step orbit")
    print("r bits    v_p(B)       v_p(D)       primitive residues (7,31,151)")
    for rank in range(2, 45, 6):
        numerator, denominator, gap, _ = rows[rank]
        assert numerator > 0 and gap > 0
        bits = "".join(str(rows[rank + i][3]) for i in range(6))
        bvals = tuple(valuation(gap, p) for p in NAMED_PRIMES)
        dvals = tuple(valuation(denominator, p) for p in NAMED_PRIMES)
        charge = primitive_charge(gap, denominator)
        residues = tuple(charge % p for p in NAMED_PRIMES)
        print(f"{rank:2d} {bits}  {bvals!s:13s} {dvals!s:13s} {residues}")

    print("\nsame-itinerary opposite-sign witness verified exactly")
    print("bits=000101, cleared terminal gaps=+1 and -32766 modulo 32767")


if __name__ == "__main__":
    main()
