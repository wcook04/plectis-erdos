#!/usr/bin/env python3
"""Exact receipts for SixStepBellmanFatCantorNoGo.md."""

from fractions import Fraction
from itertools import product


def w(n: int) -> Fraction:
    return Fraction(1, (1 << n) - 1)


def clock_after(z: Fraction, steps: int) -> Fraction:
    return z / ((1 << steps) + ((1 << steps) - 1) * z)


def step(y: Fraction, z: Fraction) -> tuple[Fraction, Fraction, int]:
    bit = int(y >= 1)
    return (2 + z) * (y - bit), z / (2 + z), bit


def branch_offset(z: Fraction, bits: tuple[int, ...]) -> Fraction:
    return sum(
        (
            Fraction(bit, (1 << i) + ((1 << i) - 1) * z)
            for i, bit in enumerate(bits)
        ),
        Fraction(),
    )


def branch_map(y: Fraction, z: Fraction, bits: tuple[int, ...]) -> tuple[Fraction, Fraction]:
    scale = (1 << len(bits)) + ((1 << len(bits)) - 1) * z
    return scale * (y - branch_offset(z, bits)), z / scale


def direct_branch_map(y: Fraction, z: Fraction, bits: tuple[int, ...]) -> tuple[Fraction, Fraction]:
    for bit in bits:
        assert int(y >= 1) == bit
        y, z, _ = step(y, z)
    return y, z


def check_clock_formula() -> int:
    checks = 0
    for n in range(2, 40):
        z = w(n)
        for steps in range(7):
            assert clock_after(z, steps) == w(n + steps)
            checks += 1
    return checks


def check_all_six_branch_formulas() -> int:
    # Use the midpoint of the exact inverse image of y_tail=1.  It realizes
    # each prescribed itinerary because 1 lies in the survivor strip [0,2).
    checks = 0
    for n in range(2, 14):
        z = w(n)
        z6 = clock_after(z, 6)
        scale = 64 + 63 * z
        for raw_bits in product((0, 1), repeat=6):
            bits = tuple(raw_bits)
            y = branch_offset(z, bits) + Fraction(1, 1) / scale
            direct_y, direct_z = direct_branch_map(y, z, bits)
            formula_y, formula_z = branch_map(y, z, bits)
            assert (direct_y, direct_z) == (formula_y, formula_z)
            assert direct_y == 1
            assert direct_z == z6
            checks += 1
    return checks


def check_root_block() -> dict[str, object]:
    y = Fraction(1, 7)
    z = Fraction(1, 3)
    bits: list[int] = []
    for _ in range(6):
        y, z, bit = step(y, z)
        bits.append(bit)
    assert bits == [0, 0, 0, 1, 0, 1]
    assert y == Fraction(52_615, 27_559)
    assert z == Fraction(1, 255)
    return {"bits_at_ranks_2_through_7": bits, "y_8": str(y), "z_8": str(z)}


def finite_survival_measure(z: Fraction, steps: int) -> Fraction:
    z_i = z
    retained = Fraction(2, 1)
    for _ in range(steps):
        retained *= Fraction(2, 1) / (2 + z_i)
        z_i = z_i / (2 + z_i)
    return retained


def check_measure_products(max_steps: int = 100) -> int:
    checks = 0
    for z in [Fraction(1, 3), Fraction(1, 7), Fraction(2, 5)]:
        for steps in range(max_steps + 1):
            measured = finite_survival_measure(z, steps)
            z_steps = clock_after(z, steps)
            closed = Fraction(2 * (1 << steps), 1) * z_steps / z
            assert measured == closed
            assert measured > Fraction(2, 1) / (1 + z)
            checks += 1
    return checks


def main() -> None:
    print(
        {
            "clock_formula_checks": check_clock_formula(),
            "six_branch_formula_checks": check_all_six_branch_formulas(),
            "root_first_return": check_root_block(),
            "finite_measure_product_checks": check_measure_products(),
            "root_survivor_measure": "3/2",
            "root_membership_proved": False,
            "interval_trapping_region_possible": False,
        }
    )


if __name__ == "__main__":
    main()
