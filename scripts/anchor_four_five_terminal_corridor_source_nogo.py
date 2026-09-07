#!/usr/bin/env python3
"""Exact audit for the M(4,5) terminal-corridor source-clock no-go."""

from __future__ import annotations

from fractions import Fraction
from math import gcd


DENOMINATOR = 465
PERIOD = 20
PERIOD_NUMERATOR = ((1 << PERIOD) - 1) // DENOMINATOR


def target_bit(rank: int) -> int:
    shift = PERIOD - 1 - ((rank - 1) % PERIOD)
    return (PERIOD_NUMERATOR >> shift) & 1


def raw_lattice_count(rank: int) -> int:
    return sum(
        1
        for i in range(1, rank // 4 + 1)
        if rank - 4 * i > 0 and (rank - 4 * i) % 5 == 0
    )


def primitive_coefficient(rank: int) -> int:
    return sum(
        1
        for i in range(1, rank // 4 + 1)
        if rank - 4 * i > 0
        and (rank - 4 * i) % 5 == 0
        and gcd(i, (rank - 4 * i) // 5) == 1
    )


def quotient(horizon: int, rank: int) -> int:
    return (1 << horizon) // ((1 << rank) - 1)


def target_quotient(horizon: int) -> int:
    return (1 << horizon) // DENOMINATOR


def weight(rank: int) -> Fraction:
    return Fraction(1, (1 << rank) - 1)


def main() -> None:
    ones = {rank for rank in range(1, PERIOD + 1) if target_bit(rank)}
    assert ones == {9, 13, 14, 17, 18, 19, 20}

    carry = 0
    for rank in range(1, 401):
        carry = 2 * carry + target_bit(rank) - raw_lattice_count(rank)
        assert carry == rank // PERIOD

    primitive20 = {
        rank: primitive_coefficient(rank)
        for rank in range(1, 21)
        if primitive_coefficient(rank)
    }
    assert primitive20 == {9: 1, 13: 1, 14: 1, 17: 1, 19: 1}

    for base in range(9, 129):
        # The complete cofinite value is bounded by 2/(2^(B+1)-1).
        assert 2 * DENOMINATOR < (1 << (base + 1)) - 1

        upper_sum = sum(
            quotient(2 * base, rank)
            for rank in range(base + 1, 2 * base + 1)
        )
        assert upper_sum == (1 << base) - 1

        defect = target_quotient(2 * base) - upper_sum
        assert defect >= 1
        repayment = -defect
        assert repayment < 0

    prefix102 = {
        9, 13, 14, 17, 19, 21, 22, 23, 24, 25, 28, 29,
        34, 35, 36, 37, 42, 43, 47, 48, 52, 54, 55, 59,
        61, 63, 64, 68, 70, 72, 74, 76, 77, 79, 83, 84,
        88, 92, 94, 98, 99, 100, 102,
    }
    residual = Fraction(1, DENOMINATOR) - sum(
        (weight(rank) for rank in prefix102), Fraction()
    )
    assert residual >= weight(105)
    assert residual < weight(104)

    for base in range(106, 129):
        tail_bound = Fraction(2, (1 << (base + 1)) - 1)
        assert tail_bound < weight(105) <= residual

        head = sum(quotient(2 * base, rank) for rank in prefix102)
        upper = sum(
            quotient(2 * base, rank)
            for rank in range(base + 1, 2 * base + 1)
        )
        assert upper == (1 << base) - 1
        defect = target_quotient(2 * base) - head - upper
        assert defect > 0

    print("period-20 raw carry K_N=floor(N/20): PASS")
    print("primitive horizon 20: {9,13,14,17,19}: PASS")
    print("cofinite Boolean family below 1/465: exact bound PASS")
    print("all half-row repayment states are strictly negative: PASS")
    print("prefix-through-102 strengthening with front 105: PASS")


if __name__ == "__main__":
    main()
