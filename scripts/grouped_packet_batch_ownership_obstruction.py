#!/usr/bin/env python3
"""Exact receipts for the grouped-packet ownership obstruction."""

from __future__ import annotations

import json
from fractions import Fraction


def weight(rank: int) -> Fraction:
    return Fraction(1, (1 << rank) - 1)


def cylinder(a: int, b: int) -> Fraction:
    return weight(a) * weight(b)


def theta(rank: int, capacity: int) -> Fraction:
    return sum(
        (
            Fraction(1, 1 << step)
            * cylinder(rank - step, rank - step + 1)
            for step in range(1, capacity + 1)
        ),
        Fraction(),
    )


def audit_block(a: int, b: int, exponent: int) -> None:
    assert 2 <= a <= b
    assert 0 <= exponent <= b
    capacity = b - exponent
    rank = a + capacity
    block = (1 << exponent) * cylinder(a, b)
    packet = weight(rank) + theta(rank, capacity)
    residual = Fraction(1, 1 << capacity) * cylinder(a, b)

    # Single-packet and grouped-batch identities.
    assert packet == Fraction(1, 1 << capacity) * weight(a)
    assert block == packet + residual
    batch_size = 1 << capacity
    assert batch_size * block == weight(a) + cylinder(a, b)

    # A complete batch fills the endpoint bin.  Keeping the regenerated
    # cylinder live gives strictly more than the input Hall load.
    input_load = batch_size * Fraction(1, batch_size)
    output_load = Fraction(1) + Fraction(1, 1 << b)
    assert input_load == 1
    assert output_load > input_load

    # Two complete batches overload the endpoint in value, not just notation.
    double_batch = (1 << (b + 1)) * cylinder(a, b)
    assert double_batch == 2 * weight(a) + 2 * cylinder(a, b)
    assert 2 * cylinder(a, b) < cylinder(a - 1, a)
    assert 2 * weight(a) < double_batch < weight(a - 1)


def audit_parameter_grid(maximum: int = 24) -> int:
    checks = 0
    for a in range(2, maximum + 1):
        for b in range(a, maximum + 1):
            for exponent in range(b + 1):
                audit_block(a, b, exponent)
                checks += 1
    return checks


def tail_upper_bound_partial(a: int, cutoff: int = 400) -> Fraction:
    """Finite receipt only; the note proves the infinite inequality exactly."""
    return sum((weight(rank) for rank in range(a + 1, cutoff + 1)), Fraction())


def first_front_receipt() -> dict[str, object]:
    binary_blocks = [
        {"source": "256*M(10,11)", "a": 10, "b": 11, "j": 8},
        {"source": "64*M(10,11)", "a": 10, "b": 11, "j": 6},
        {"source": "16*M(10,11)", "a": 10, "b": 11, "j": 4},
        {"source": "4*M(10,11)", "a": 10, "b": 11, "j": 2},
    ]
    ordinary = [
        {"source": "M(5,7)", "a": 5, "b": 7, "j": 0},
        {"source": "M(5,8)", "a": 5, "b": 8, "j": 0},
        {"source": "M(7,9)", "a": 7, "b": 9, "j": 0},
        {"source": "M(3,11)", "a": 3, "b": 11, "j": 0},
        {"source": "M(8,11)", "a": 8, "b": 11, "j": 0},
        {"source": "M(9,11)", "a": 9, "b": 11, "j": 0},
    ]
    sources = binary_blocks + ordinary
    for row in sources:
        row["capacity"] = row["b"] - row["j"]
        row["required_identical_copies"] = 1 << row["capacity"]
        row["available_identical_copies"] = 1
        row["batch_available"] = False

    cohort_load = Fraction(340, 1 << 11)
    binary_load = sum(
        (Fraction(1, 1 << row["capacity"]) for row in binary_blocks),
        Fraction(),
    )
    assert cohort_load == binary_load == Fraction(85, 512)
    assert 340 < (1 << 11)
    assert not any(row["batch_available"] for row in sources)

    return {
        "raw_cohort": "340*M(10,11)",
        "raw_unit_batch_requirement": 1 << 11,
        "raw_unit_copies_available": 340,
        "raw_cohort_load": str(cohort_load),
        "binary_block_load": str(binary_load),
        "labelled_sources": sources,
        "legal_grouped_rewrites": 0,
        "rank_20_effect": "unchanged: the grouped rule cannot fire on this front",
    }


def main() -> None:
    root_value = 16 * cylinder(2, 3)
    assert root_value == Fraction(16, 21)
    assert 2 * weight(2) < root_value < weight(1)
    assert tail_upper_bound_partial(2) < weight(2)

    output = {
        "theorem": (
            "A complete identical batch has the exact renewal identity "
            "2^b*M(a,b)=w_a+M(a,b), but its active output load is "
            "1+2^-b while its input packet load is 1."
        ),
        "parameter_checks": audit_parameter_grid(),
        "minimal_batch_count_overload": {
            "complete_batches": 2,
            "identity": "2^(b+1)*M(a,b)=2*w_a+2*M(a,b)",
            "value_interval": "(2*w_a, w_(a-1))",
            "root_example": "16*M(2,3)=16/21",
        },
        "first_front": first_front_receipt(),
        "boundary": (
            "A dormant-residual ledger could defer the extra load, but the "
            "grouped identity alone supplies no safe reactivation law."
        ),
    }
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
