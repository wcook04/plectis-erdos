#!/usr/bin/env python3
"""Exact refinement no-go for P + lambda (K-Q) owner charges."""

from fractions import Fraction
from math import gcd


def weight(rank: int) -> Fraction:
    return Fraction(1, 2**rank - 1)


def cylinder(a: int, b: int) -> Fraction:
    return weight(a) * weight(b)


def quotient(rank: int, atom: int) -> int:
    return 2**rank // (2**atom - 1)


def target_quotient(rank: int) -> int:
    return 2**rank // 465


def primitive_coefficient(rank: int) -> int:
    return sum(
        1
        for i in range(1, rank // 4 + 1)
        if rank - 4 * i > 0
        and (rank - 4 * i) % 5 == 0
        and gcd(i, (rank - 4 * i) // 5) == 1
    )


def prefix_count(coefficients: dict[int, int], horizon: int) -> int:
    return sum(value for rank, value in coefficients.items() if rank <= horizon)


def defect(coefficients: dict[int, int], horizon: int) -> int:
    return target_quotient(horizon) - sum(
        value * quotient(horizon, rank)
        for rank, value in coefficients.items()
        if rank <= horizon
    )


def charge(
    coefficients: dict[int, int], horizon: int, raw_carry: int, slope: int
) -> int:
    return prefix_count(coefficients, horizon) + slope * (
        raw_carry - defect(coefficients, horizon)
    )


def main() -> None:
    refinement_coefficient = (
        (2**8 - 1) // (2**4 - 1) * (2**10 - 1) // (2**5 - 1)
    )
    assert refinement_coefficient == 561
    assert cylinder(4, 5) == refinement_coefficient * cylinder(8, 10)

    # The ordinary primitive expansion of M(4,5) has its first atom at 9.
    raw9 = {rank: primitive_coefficient(rank) for rank in range(1, 10)}
    raw9 = {rank: value for rank, value in raw9.items() if value}
    assert raw9 == {9: 1}
    raw_carry9 = defect(raw9, 9)
    assert target_quotient(9) == 1
    assert raw_carry9 == 0

    # The refined cylinder M(8,10) has first primitive rank 18, regardless
    # of its coefficient 561.  Its coefficient word is empty at horizon 9.
    refined9: dict[int, int] = {}
    assert defect(refined9, 9) == 1
    for slope in (1, 5):
        before = charge(raw9, 9, raw_carry9, slope)
        after = charge(refined9, 9, raw_carry9, slope)
        assert before == 1
        assert after == -slope
        assert after - before == -(slope + 1)

    # Rank 9 is the minimal possible failure horizon.
    for horizon in range(1, 9):
        assert target_quotient(horizon) == 0
        assert prefix_count(raw9, horizon) == 0
        assert defect({}, horizon) == 0

    # The observed sharp slope five has a genuine, separate source: at the
    # fundamental horizon 20 the primitive triangle contains exactly five
    # atoms and the raw binary carry is exactly one.
    raw20 = {
        rank: primitive_coefficient(rank)
        for rank in range(1, 21)
        if primitive_coefficient(rank)
    }
    assert raw20 == {9: 1, 13: 1, 14: 1, 17: 1, 19: 1}
    assert prefix_count(raw20, 20) == 5
    assert defect(raw20, 20) == 1

    print("exact refinement: M(4,5) = 561 M(8,10)")
    print("minimal horizon 9: charge slope 1 drops 1 -> -1")
    print("minimal horizon 9: charge slope 5 drops 1 -> -5")
    print("fundamental horizon 20: primitive count 5, raw carry 1")
    print("refinement-gauge charge no-go: PASS")


if __name__ == "__main__":
    main()
