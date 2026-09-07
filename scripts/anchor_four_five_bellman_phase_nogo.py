#!/usr/bin/env python3
"""Exact receipt for the 1/465 Bellman phase-monotonicity no-go."""

from __future__ import annotations

from fractions import Fraction


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


def divisors_selected(rank: int, bits: list[int]) -> int:
    return sum(bits[d] for d in range(1, rank + 1) if rank % d == 0)


def main() -> None:
    depth = 49
    residual = Fraction(1, DENOMINATOR)
    bits = [0] * (depth + 1)
    scaled_residual = [Fraction()] * (depth + 1)
    raw_carry = [0] * (depth + 1)
    defect = [0] * (depth + 1)
    surplus = [0] * (depth + 1)
    bellman = [Fraction()] * (depth + 1)

    scaled_residual[0] = residual
    bellman[0] = 1 - residual
    for rank in range(1, depth + 1):
        weight = Fraction(1, (1 << rank) - 1)
        if residual >= weight:
            residual -= weight
            bits[rank] = 1
        scaled_residual[rank] = (1 << rank) * residual

        pulse = divisors_selected(rank, bits)
        raw_carry[rank] = (
            2 * raw_carry[rank - 1]
            + target_bit(rank)
            - raw_lattice_count(rank)
        )
        defect[rank] = (
            2 * defect[rank - 1] + target_bit(rank) - pulse
        )
        surplus[rank] = raw_carry[rank] - defect[rank]
        bellman[rank] = surplus[rank] + 1 - scaled_residual[rank]

        gamma = Fraction(1 << rank, (1 << rank) - 1)
        assert scaled_residual[rank] == (
            2 * scaled_residual[rank - 1] - gamma * bits[rank]
        )
        assert surplus[rank] == (
            2 * surplus[rank - 1]
            + pulse
            - raw_lattice_count(rank)
        )
        assert bellman[rank] == (
            2 * bellman[rank - 1]
            + pulse
            - raw_lattice_count(rank)
            - 1
            + gamma * bits[rank]
        )
        assert raw_carry[rank] == rank // PERIOD

    assert [rank for rank in range(30, 50) if bits[rank]] == [
        34, 35, 36, 37, 42, 43, 47, 48
    ]
    assert surplus[29] == surplus[49] == 1
    residual_increase = scaled_residual[49] - scaled_residual[29]
    assert residual_increase > 0
    assert bellman[49] - bellman[29] == -residual_increase < 0

    print(
        {
            "target": "1/465",
            "exact_depth": depth,
            "E_29": surplus[29],
            "E_49": surplus[49],
            "y_49_minus_y_29": str(residual_increase),
            "V_49_minus_V_29": str(-residual_increase),
            "periodic_gauge_monotonicity": False,
            "V_positive_all_depth_claimed": False,
        }
    )


if __name__ == "__main__":
    main()
