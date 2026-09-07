#!/usr/bin/env python3
"""Exact receipts for AnchoredSubstitutionCollisionCocycle.md."""

from collections import Counter
from fractions import Fraction
from math import lcm


def w(n: int) -> Fraction:
    return Fraction(1, (1 << n) - 1)


def packet(b: int, j: int) -> Fraction:
    """The anchor-two power packet 2^j M(2,b)."""
    return Fraction(1 << j, 3 * ((1 << b) - 1))


def arrival(b: int, j: int) -> int:
    return 2 + b - j


def bits(n: int) -> list[int]:
    return [j for j in range(n.bit_length()) if (n >> j) & 1]


def unary_children(b: int, j: int) -> tuple[int, int, list[int]]:
    r = arrival(b, j)
    height = lcm(b, r)
    reserve = packet(b, j) - w(r)
    coefficient = reserve * 3 * ((1 << height) - 1)
    assert coefficient.denominator == 1
    child_bits = bits(coefficient.numerator)
    assert sum((packet(height, h) for h in child_bits), Fraction()) == reserve
    assert all(arrival(height, h) > r for h in child_bits)
    return r, height, child_bits


def carry_reencode(
    leaves: list[tuple[int, int]], output_rank: int
) -> dict[str, object]:
    """Carry a complete component and reencode its positive reserve."""
    value = sum((packet(b, j) for b, j in leaves), Fraction())
    mass = sum(
        (Fraction(1 << j, 1 << b) for b, j in leaves),
        Fraction(),
    )
    reserve = value - w(output_rank)
    height = lcm(output_rank, *(b for b, _ in leaves))
    coefficient = reserve * 3 * ((1 << height) - 1)
    assert reserve > 0
    assert reserve < w(output_rank)
    assert coefficient.denominator == 1
    child_bits = bits(coefficient.numerator)
    child_load = Fraction(coefficient.numerator, 1 << height)
    assert sum((packet(height, h) for h in child_bits), Fraction()) == reserve
    assert all(arrival(height, h) > output_rank for h in child_bits)
    alpha = 3 * value / mass
    load_proxy = alpha - 3 * w(output_rank) / mass
    assert child_load / mass < load_proxy
    assert load_proxy < Fraction(7, 12)
    return {
        "output_rank": output_rank,
        "height": height,
        "child_count": len(child_bits),
        "minimum_child_arrival": min(arrival(height, h) for h in child_bits),
        "distortion": alpha,
        "load_ratio": child_load / mass,
        "load_proxy": load_proxy,
    }


def check_cocycle(max_b: int = 80) -> int:
    checks = 0
    for b in range(2, max_b + 1):
        for j in range(b + 1):
            r = arrival(b, j)
            mass = Fraction(1 << j, 1 << b)
            alpha = 3 * packet(b, j) / mass
            assert alpha == Fraction(1 << b, (1 << b) - 1)
            assert 1 < alpha <= Fraction(4, 3)
            assert 3 * w(r) / mass > Fraction(3, 4)
            checks += 1
    return checks


def check_root_collision() -> dict[str, object]:
    # M(2,3) = w_5 + 1510 M(2,15).
    root_reserve = Fraction(1510, 1) * packet(15, 0)
    assert w(2) * w(3) == w(5) + root_reserve
    root_bits = bits(1510)
    assert root_bits == [1, 2, 5, 6, 7, 8, 10]
    root_alpha_bound = Fraction(1 << 15, (1 << 15) - 1)
    root_contraction_bound = root_alpha_bound - Fraction(3, 4)
    assert root_contraction_bound == Fraction(32771, 131068)
    assert root_contraction_bound < Fraction(251, 1000)

    first_ranks = {j: arrival(15, j) for j in root_bits}
    assert first_ranks[7] == 10
    assert first_ranks[8] == 9

    _, height, child_bits = unary_children(15, 10)
    assert height == 105
    assert {95, 96, 97}.issubset(child_bits)
    child_ranks = Counter(arrival(height, h) for h in child_bits)
    assert child_ranks[10] == 1
    assert child_ranks[11] == 1
    assert child_ranks[12] == 1

    # The new rank-ten child collides with the first-wave rank-ten packet.
    first_carry = carry_reencode([(15, 7), (105, 97)], output_rank=9)
    assert first_carry["height"] == 315
    assert first_carry["minimum_child_arrival"] == 12

    # Its rank-nine front then collides with the first-wave rank-nine packet.
    second_carry = carry_reencode(
        [(15, 7), (105, 97), (15, 8)], output_rank=8
    )
    assert second_carry["height"] == 840
    assert second_carry["minimum_child_arrival"] == 11

    return {
        "root_bits": root_bits,
        "hereditary_height_divisor": 15,
        "root_specific_contraction": f"strictly less than {root_contraction_bound}",
        "first_wave_ranks": sorted(first_ranks.values()),
        "child_bits_from_(15,10)": [95, 96, 97],
        "first_collision": {
            key: (str(value) if isinstance(value, Fraction) else value)
            for key, value in first_carry.items()
        },
        "second_collision": {
            key: (str(value) if isinstance(value, Fraction) else value)
            for key, value in second_carry.items()
        },
    }


def main() -> None:
    print(
        {
            "cocycle_checks": check_cocycle(),
            "uniform_composite_contraction": "strictly less than 7/12",
            "root_collision": check_root_collision(),
            "flat_irrevocable_emission_automaton": "fails at ranks 10 then 9",
            "persistent_reserve_ownership": "still required",
        }
    )


if __name__ == "__main__":
    main()
