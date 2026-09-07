#!/usr/bin/env python3
"""Exact receipts for primitive-prime height-change charges."""

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


def primitive_prime(period: int) -> int:
    for prime in factorint(int(cyclotomic_poly(period, 2))):
        prime = int(prime)
        if n_order(2, prime) == period:
            return prime
    raise AssertionError(f"no primitive prime at period {period}")


def projected_lift_formula(
    old_height: int, new_height: int
) -> dict[str, object]:
    assert new_height % old_height == 0
    multiplier = new_height // old_height
    prime = primitive_prime(old_height)

    rows = []
    for rank in divisors(new_height):
        actual = lift_factor(new_height, rank) % prime
        if rank % old_height:
            predicted = 0
            pulse_kind = "transverse_zero"
        else:
            quotient = rank // old_height
            assert multiplier % quotient == 0
            predicted = (multiplier // quotient) % prime
            pulse_kind = "vertical_multiple"
        assert actual == predicted
        rows.append(
            {
                "rank": rank,
                "pulse_kind": pulse_kind,
                "projected_coefficient": actual,
            }
        )

    # A lifted old coefficient C is multiplied by `multiplier` in the old
    # primitive charge.  Check the formula with a nonzero test coefficient.
    coefficient = 37
    lifted = coefficient * lift_factor(new_height, old_height)
    assert lifted % prime == (multiplier * coefficient) % prime

    fresh_prime = primitive_prime(new_height)
    assert lift_factor(new_height, old_height) % fresh_prime == 0
    assert all(
        lift_factor(new_height, rank) % fresh_prime == 0
        for rank in divisors(new_height)
        if rank < new_height
    )

    return {
        "old_height": old_height,
        "new_height": new_height,
        "height_multiplier": multiplier,
        "old_primitive_prime": prime,
        "fresh_primitive_prime": fresh_prime,
        "old_charge_lift_multiplier": multiplier % prime,
        "rank_pulses": rows,
        "fresh_charge_before_rank_new_height": 0,
    }


def adjacent_clock_receipt(old_height: int, new_height: int) -> list[dict[str, object]]:
    assert new_height % old_height == 0
    multiplier = new_height // old_height
    prime = primitive_prime(old_height)
    rows = []
    for rank in range(3, new_height):
        if new_height % rank or new_height % (rank - 1):
            continue
        lower = 6 * lift_factor(new_height, rank) % prime
        upper = 3 * lift_factor(new_height, rank - 1) % prime
        lower_active = rank % old_height == 0
        upper_active = (rank - 1) % old_height == 0
        assert not (lower_active and upper_active)
        if lower_active:
            assert lower == 6 * (multiplier // (rank // old_height)) % prime
        else:
            assert lower == 0
        if upper_active:
            assert upper == 3 * (
                multiplier // ((rank - 1) // old_height)
            ) % prime
        else:
            assert upper == 0
        rows.append(
            {
                "rank": rank,
                "lower_clock_residue": lower,
                "upper_clock_residue": upper,
                "lower_clock_active": lower_active,
                "upper_clock_active": upper_active,
            }
        )
    return rows


def main() -> None:
    transitions = [(15, 30), (15, 60), (15, 210), (30, 210), (45, 630)]
    receipts = [projected_lift_formula(old, new) for old, new in transitions]
    print(
        {
            "height_change_receipts": receipts,
            "adjacent_clock_receipt_15_to_210": adjacent_clock_receipt(15, 210),
            "law": (
                "old primitive charge sees only new ranks divisible by the "
                "old height; the two adjacent fatal clocks never pulse "
                "simultaneously in one primitive coordinate"
            ),
        }
    )


if __name__ == "__main__":
    main()
