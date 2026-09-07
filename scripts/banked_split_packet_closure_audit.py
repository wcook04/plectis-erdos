#!/usr/bin/env python3
"""Exact receipts for pooled banked-split packet closure."""

from __future__ import annotations

import json
from fractions import Fraction
from math import ceil, lcm


def weight(rank: int) -> Fraction:
    return Fraction(1, (1 << rank) - 1)


def cylinder(a: int, b: int) -> Fraction:
    return weight(a) * weight(b)


def carry_tax(stop: int, exponent: int) -> Fraction:
    return sum(
        (
            (1 << (exponent - level))
            * cylinder(stop - level, stop - level + 1)
            for level in range(1, exponent + 1)
        ),
        Fraction(),
    )


def theta(rank: int, capacity: int) -> Fraction:
    return sum(
        (
            Fraction(1, 1 << level)
            * cylinder(rank - level, rank - level + 1)
            for level in range(1, capacity + 1)
        ),
        Fraction(),
    )


def packet_residual(a: int, b: int, exponent: int) -> Fraction:
    return (1 << exponent) * cylinder(a, b) - weight(a + b - exponent)


def generalized_domination(a: int, b: int, c: int, d: int) -> tuple[int, int, int]:
    left_coordinate = lcm(a, c)
    right_coordinate = lcm(b, d)
    left_coefficient = (
        ((1 << left_coordinate) - 1) // ((1 << a) - 1)
        * (((1 << right_coordinate) - 1) // ((1 << b) - 1))
    )
    right_coefficient = (
        ((1 << left_coordinate) - 1) // ((1 << c) - 1)
        * (((1 << right_coordinate) - 1) // ((1 << d) - 1))
    )
    difference = left_coefficient - right_coefficient
    assert cylinder(a, b) - cylinder(c, d) == difference * cylinder(
        left_coordinate, right_coordinate
    )
    assert (difference > 0) == (cylinder(a, b) > cylinder(c, d))
    return left_coordinate, right_coordinate, difference


def audit_domination_grid(maximum: int = 12) -> int:
    checks = 0
    for a in range(2, maximum + 1):
        for b in range(2, maximum + 1):
            for c in range(2, maximum + 1):
                for d in range(2, maximum + 1):
                    generalized_domination(a, b, c, d)
                    checks += 1
    return checks


def audit_pooled_identity(maximum: int = 28) -> int:
    checks = 0
    for a in range(2, maximum + 1):
        for b in range(a, maximum + 1):
            stop = a + b
            for exponent in range(b + 1):
                rank = stop - exponent
                capacity = b - exponent
                tax = carry_tax(stop, exponent)
                bank_residual = (1 << exponent) * cylinder(a, stop) - tax
                expected = packet_residual(a, stop, a + exponent)
                other_child = (1 << exponent) * cylinder(stop, b)

                assert tax == weight(rank) - (1 << exponent) * weight(stop)
                assert bank_residual == expected > 0
                assert (
                    (1 << exponent) * cylinder(a, b)
                    == weight(rank) + bank_residual + other_child
                )
                assert bank_residual >= theta(rank, capacity)
                if capacity < rank - 1:
                    assert bank_residual < theta(rank, capacity + 1)

                parent_load = Fraction(1 << exponent, 1 << b)
                other_load = Fraction(1 << exponent, 1 << stop)
                assert other_load / parent_load == Fraction(1, 1 << a)
                assert Fraction(8, 15) + Fraction(1, 1 << a) <= Fraction(47, 60)
                checks += 1
    return checks


def raw_depth(reserve: Fraction, rank: int) -> int:
    depth = 0
    while rank - depth - 1 >= 1 and reserve >= cylinder(
        rank - depth - 1, rank - depth
    ):
        depth += 1
    return depth


def stop_21_receipt() -> dict[str, object]:
    a, b, stop, exponent = 10, 11, 21, 8
    rank = stop - exponent
    bank = cylinder(a, stop)
    tax = carry_tax(stop, exponent)
    bank_residual = (1 << exponent) * bank - tax
    other_child = (1 << exponent) * cylinder(stop, b)
    full_residual = bank_residual + other_child

    costs = []
    for level in range(1, exponent + 1):
        tax_cylinder = cylinder(stop - level, stop - level + 1)
        multiplicity = 1 << (exponent - level)
        banks_per_tax = ceil(tax_cylinder / bank)
        costs.append(
            {
                "level": level,
                "tax_cylinder": f"M({stop-level},{stop-level+1})",
                "multiplicity": multiplicity,
                "banks_per_tax": banks_per_tax,
                "whole_banks_required": multiplicity * banks_per_tax,
            }
        )
    one_shot_total = sum(row["whole_banks_required"] for row in costs)
    assert [row["whole_banks_required"] for row in costs] == [
        128,
        64,
        32,
        16,
        8,
        4,
        8,
        16,
    ]
    assert one_shot_total == 276 > 256

    assert bank_residual == packet_residual(10, 21, 18)
    assert bank_residual == Fraction(1836031, 17572852409343)
    assert full_residual == 256 * cylinder(10, 11) - weight(13)
    assert full_residual == Fraction(2815, 17152617471)
    assert bank_residual >= theta(rank, 3)
    assert bank_residual < theta(rank, 4)
    assert raw_depth(bank_residual, rank) == 1
    assert raw_depth(full_residual, rank) == 2

    # Anchor-preserving integer-cylinder encoding of D_(10,21,18).
    anchor_height = lcm(21, 13)
    product = ((1 << 21) - 1) * ((1 << 13) - 1)
    assert ((1 << anchor_height) - 1) % product == 0
    anchored_coefficient = (
        ((1 << 10) + (1 << 21) - (1 << 18) - 1)
        * (((1 << anchor_height) - 1) // product)
    )
    assert bank_residual == anchored_coefficient * cylinder(10, anchor_height)

    parent_load = Fraction(1 << 8, 1 << 11)
    bank_load = Fraction(anchored_coefficient, 1 << anchor_height)
    other_load = Fraction(1 << 8, 1 << 21)
    assert bank_load / parent_load < Fraction(8, 15)
    assert other_load / parent_load == Fraction(1, 1 << 10)
    assert (bank_load + other_load) / parent_load < (
        Fraction(8, 15) + Fraction(1, 1 << 10)
    )

    return {
        "block": "256*M(10,11)",
        "leading_atom": "w_13",
        "tax": str(tax),
        "whole_bank_matching": {
            "available": 256,
            "required": one_shot_total,
            "level_costs": costs,
            "verdict": "fails",
        },
        "pooled_bank_residual": str(bank_residual),
        "pooled_packet_capacity": 3,
        "pooled_packet_deadline": 10,
        "pooled_bank_raw_depth": raw_depth(bank_residual, rank),
        "full_residual_raw_depth": raw_depth(full_residual, rank),
        "other_child": "256*M(21,11)",
        "anchored_residual_height": anchor_height,
        "protected_child_load_ratio_upper_bound": "8/15 + 1/1024",
    }


def generated_lift_capacity_receipt(maximum_endpoint: int = 26) -> int:
    """Check the symbolic fresh-lift bound on a representative exact grid."""
    checks = 0
    for endpoint in range(2, maximum_endpoint + 1):
        for new_stop in range(endpoint + 2, maximum_endpoint + 3):
            lift = lcm(endpoint, new_stop - 1)
            coefficient = (
                ((1 << lift) - 1) // ((1 << endpoint) - 1)
                - ((1 << lift) - 1) // ((1 << (new_stop - 1)) - 1)
            )
            if coefficient <= 0:
                continue
            assert coefficient < (1 << (lift - 1))
            for exponent in range(coefficient.bit_length()):
                if coefficient & (1 << exponent):
                    assert exponent <= lift - 2
                    assert lift - exponent >= 2
                    checks += 1
    return checks


def main() -> None:
    output = {
        "theorem": (
            "Every power block has the protected positive rewrite "
            "2^j*M(a,b)=w_(a+b-j)+D_(a,a+b,a+j)+2^j*M(a+b,b)."
        ),
        "generalized_domination_checks": audit_domination_grid(),
        "pooled_identity_checks": audit_pooled_identity(),
        "generated_lift_bit_checks": generated_lift_capacity_receipt(),
        "stop_21": stop_21_receipt(),
        "uniform_protected_load_bound": "8/15 + 2^-a <= 47/60",
        "boundary": (
            "Local generated-cohort closure is exact; global cross-stop "
            "deadline Hall scheduling and fixed-rank stabilization remain open."
        ),
    }
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
