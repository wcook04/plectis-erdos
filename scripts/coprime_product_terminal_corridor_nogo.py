#!/usr/bin/env python3
"""Exact audit for CoprimeProductTerminalCorridorNoGo.md."""

from __future__ import annotations

import json
from fractions import Fraction
from math import gcd


def mersenne(rank: int) -> int:
    return (1 << rank) - 1


def lattice_count(a: int, b: int, rank: int) -> int:
    return sum(
        1
        for left in range(1, rank // a + 1)
        if rank - a * left > 0 and (rank - a * left) % b == 0
    )


def target_bit(a: int, b: int, rank: int) -> int:
    period = a * b
    denominator = mersenne(a) * mersenne(b)
    numerator = mersenne(period) // denominator
    shift = period - 1 - ((rank - 1) % period)
    return (numerator >> shift) & 1


def quotient(horizon: int, rank: int) -> int:
    return (1 << horizon) // mersenne(rank)


def boolean_ancestry_prefix(a: int, b: int) -> tuple[set[int], int]:
    """Recover the unique minimal semigroup divisors below a*b."""
    period = a * b
    selected: set[int] = set()

    for rank in range(1, period):
        source = lattice_count(a, b, rank)
        proper_load = sum(rank % divisor == 0 for divisor in selected)
        bit = source - proper_load
        assert bit in (0, 1)
        if bit:
            selected.add(rank)

    for rank in range(1, period):
        source = lattice_count(a, b, rank)
        selected_divisors = [
            divisor for divisor in selected if rank % divisor == 0
        ]
        assert len(selected_divisors) == source

        semigroup_divisors = [
            divisor
            for divisor in range(1, rank + 1)
            if rank % divisor == 0 and lattice_count(a, b, divisor) == 1
        ]
        for left_index, left in enumerate(semigroup_divisors):
            for right in semigroup_divisors[left_index:]:
                common = gcd(left, right)
                assert lattice_count(a, b, common) == 1

        target_quotient = (1 << rank) // (
            mersenne(a) * mersenne(b)
        )
        source_quotient = sum(
            quotient(rank, divisor)
            for divisor in selected
            if divisor <= rank
        )
        assert source_quotient == target_quotient

    return selected, period - 1


def greedy_prefix(a: int, b: int, stop: int) -> tuple[set[int], Fraction]:
    denominator = mersenne(a) * mersenne(b)
    residual = Fraction(1, denominator)
    selected: set[int] = set()
    for rank in range(1, stop + 1):
        coin = Fraction(1, mersenne(rank))
        if coin <= residual:
            selected.add(rank)
            residual -= coin
    return selected, residual


def check_pair(a: int, b: int) -> tuple[int, int]:
    assert gcd(a, b) == 1
    period = a * b
    denominator = mersenne(a) * mersenne(b)
    assert mersenne(period) % denominator == 0
    assert lattice_count(a, b, period) == 0

    for rank in range(1, period):
        assert lattice_count(a, b, rank) in (0, 1)
        assert target_bit(a, b, rank) == lattice_count(a, b, rank)
    assert target_bit(a, b, period) == 1

    ancestry_support, ancestry_rows = boolean_ancestry_prefix(a, b)
    real_greedy_support, real_residual = greedy_prefix(a, b, period - 1)
    assert ancestry_support == real_greedy_support
    assert real_residual > 0

    carry = 0
    checked = 0
    for rank in range(1, 4 * period + 1):
        assert (
            lattice_count(a, b, rank + period)
            == lattice_count(a, b, rank) + 1
        )
        carry = (
            2 * carry
            + target_bit(a, b, rank)
            - lattice_count(a, b, rank)
        )
        assert carry == rank // period
        checked += 1

    base = denominator.bit_length()
    assert (1 << base) > denominator
    tail_bound = Fraction(2, mersenne(base + 1))
    assert tail_bound < Fraction(1, denominator)

    upper_supply = sum(
        quotient(2 * base, rank)
        for rank in range(base + 1, 2 * base + 1)
    )
    assert upper_supply == (1 << base) - 1
    target_quotient = (1 << (2 * base)) // denominator
    assert target_quotient >= 1 << base
    assert target_quotient - upper_supply >= 1
    return checked, ancestry_rows


def explicit_twenty_one() -> dict[str, object]:
    a, b, base = 2, 3, 5
    denominator = mersenne(a) * mersenne(b)
    upper_supply = sum(
        quotient(2 * base, rank)
        for rank in range(base + 1, 2 * base + 1)
    )
    target_quotient = (1 << (2 * base)) // denominator
    assert denominator == 21
    assert upper_supply == 31
    assert target_quotient == 48
    assert target_quotient - upper_supply == 17
    return {
        "target": "M(2,3)=1/21",
        "base": base,
        "upper_half_quotient_supply": upper_supply,
        "target_quotient": target_quotient,
        "unpaid_defect": target_quotient - upper_supply,
    }


def main() -> None:
    pair_count = 0
    recurrence_rows = 0
    boolean_ancestry_rows = 0
    for a in range(2, 13):
        for b in range(a + 1, 16):
            if gcd(a, b) != 1:
                continue
            recurrence_checked, ancestry_checked = check_pair(a, b)
            recurrence_rows += recurrence_checked
            boolean_ancestry_rows += ancestry_checked
            pair_count += 1

    print(
        json.dumps(
            {
                "coprime_pairs_checked": pair_count,
                "raw_carry_recurrence_rows_checked": recurrence_rows,
                "raw_carry_formula": "K_n=floor(n/(a*b))",
                "boolean_ancestry_prefix_rows_checked": boolean_ancestry_rows,
                "boolean_ancestry_prefix_formula": (
                    "sum_{d|n,d in A_ab} 1 = 1_{n=ai+bj} for n<a*b"
                ),
                "explicit_twenty_one_counterexample": explicit_twenty_one(),
                "claim_status": (
                    "exact audit of the Boolean-prefix theorem and "
                    "universal terminal no-go"
                ),
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
