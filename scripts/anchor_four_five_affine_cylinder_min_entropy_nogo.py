#!/usr/bin/env python3
"""Exact checks for the affine-cylinder blockwise min-entropy no-go."""

from __future__ import annotations

from fractions import Fraction
import json
from math import prod


def q(rank: int) -> int:
    return (1 << rank) - 1


def w(rank: int) -> Fraction:
    return Fraction(1, q(rank))


def threshold(rank: int) -> Fraction:
    return Fraction((1 << (rank - 1)) - 1, q(rank))


def gap_step(gap: Fraction, rank: int, take: int) -> Fraction:
    if take:
        assert gap <= threshold(rank)
        return 2 * gap + Fraction(1, q(rank))
    assert gap > threshold(rank)
    return 2 * gap - 1


def block_charge(start: int, word: tuple[int, ...]) -> Fraction:
    length = len(word)
    return sum(
        (
            Fraction(1, q(start + i)) if bit else Fraction(-1)
        )
        * (1 << (length - i))
        for i, bit in enumerate(word, start=1)
    )


def cleared_charge(start: int, word: tuple[int, ...]) -> tuple[int, int]:
    selected_product = prod(
        q(start + i) for i, bit in enumerate(word, start=1) if bit
    )
    charge = block_charge(start, word)
    assert charge.denominator > 0
    cleared = charge * selected_product
    assert cleared.denominator == 1
    return selected_product, cleared.numerator


def check_concatenation(start: int, left: tuple[int, ...], right: tuple[int, ...]) -> None:
    combined = block_charge(start, left + right)
    factored = (
        (1 << len(right)) * block_charge(start, left)
        + block_charge(start + len(left), right)
    )
    assert combined == factored


def recompression_witness(rank: int, k: int) -> dict[str, object]:
    assert rank >= 40
    assert k >= 2
    endpoint = Fraction(k, k * (1 << rank) - 1)
    start_rank = rank - 20
    start_residual = endpoint + sum(
        (w(d) for d in range(rank - 19, rank)),
        Fraction(0),
    )

    assert 0 < start_residual < Fraction(1, 1 << start_rank) < w(start_rank)

    residual = start_residual
    decisions: list[int] = []
    gap = 1 - (1 << start_rank) * residual
    for current in range(start_rank + 1, rank + 1):
        take = int(residual >= w(current))
        decisions.append(take)
        next_gap = gap_step(gap, current, take)
        if take:
            residual -= w(current)
        gap = next_gap
        assert gap == 1 - (1 << current) * residual

    expected_word = [1] * 19 + [0]
    assert decisions == expected_word
    assert Fraction(1, 1 << rank) < residual < w(rank)
    assert residual == endpoint

    expected_gap = Fraction(-1, k * (1 << rank) - 1)
    assert gap == expected_gap

    word = tuple(decisions)
    charge = block_charge(start_rank, word)
    assert gap == (1 << 20) * (
        1 - (1 << start_rank) * start_residual
    ) + charge

    selected_product, integer_charge = cleared_charge(start_rank, word)
    start_gap = 1 - (1 << start_rank) * start_residual
    direct_numerator = (
        (1 << 20) * selected_product * start_gap.numerator
        * (start_gap.denominator // start_gap.denominator)
    )
    # Check the integer formula after putting both terms over D*Q.
    integer_formula_numerator = (
        (1 << 20) * selected_product * start_gap.numerator
        + start_gap.denominator * integer_charge
    )
    assert Fraction(
        integer_formula_numerator,
        start_gap.denominator * selected_product,
    ) == gap
    assert direct_numerator == (1 << 20) * selected_product * start_gap.numerator

    return {
        "rank": rank,
        "k": k,
        "start_rank": start_rank,
        "word": "".join(map(str, decisions)),
        "start_below_dyadic_cutoff": True,
        "endpoint_in_dangerous_interval": True,
        "reduced_endpoint_gap_numerator": gap.numerator,
        "reduced_endpoint_gap_denominator_bits": gap.denominator.bit_length(),
    }


def main() -> None:
    check_concatenation(40, (1, 0, 1, 1, 0, 0, 1), (0, 1, 1, 1, 0))
    witnesses = [
        recompression_witness(rank, k)
        for rank, k in ((40, 2), (41, 3), (80, 17), (200, 2))
    ]
    print(
        json.dumps(
            {
                "claim": "exact affine law and blockwise min-entropy no-go",
                "block_length": 20,
                "witnesses": witnesses,
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
