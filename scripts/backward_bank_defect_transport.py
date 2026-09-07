#!/usr/bin/env python3
"""Exact audit for the backward-bank endpoint-defect transport family."""

from __future__ import annotations

import json


def residue(rank: int, denominator_rank: int) -> int:
    height_count, remainder = divmod(rank, denominator_rank)
    half = sum(
        1 << (rank - index * denominator_rank)
        for index in range(1, height_count + 1)
    )
    value = ((1 << remainder) - 1) * half
    if 2 * remainder >= denominator_rank:
        value += 1 << (2 * remainder - denominator_rank)
    return value


def cohort(rank: int, denominator_rank: int) -> int:
    remainder = rank % denominator_rank
    assert remainder != 0
    return denominator_rank - remainder


def deficit(rank: int, denominator_rank: int) -> int:
    return (1 << (rank - cohort(rank, denominator_rank))) - residue(
        rank, denominator_rank
    )


def valuation(value: int) -> int:
    assert value != 0
    absolute = abs(value)
    return (absolute & -absolute).bit_length() - 1


def endpoint_safe(rank: int, denominator_rank: int) -> bool:
    return all(
        (2 * rank + offset) % denominator_rank != 0
        for offset in range(1, 5)
    )


def block_deficit(rank: int, denominator_rank: int) -> int:
    height_count, remainder = divmod(rank, denominator_rank)
    seam_distance = denominator_rank - remainder
    if remainder < seam_distance:
        return (1 << remainder) + ((1 << seam_distance) - 1) * sum(
            1 << (2 * remainder + index * denominator_rank)
            for index in range(height_count - 1)
        )
    return ((1 << seam_distance) - 1) * sum(
        1 << (remainder - seam_distance + index * denominator_rank)
        for index in range(height_count)
    )


def audit_row(parameter: int) -> dict[str, object]:
    assert parameter >= 50 and parameter % 42 == 8
    rank = 7 * parameter - 12
    source = 2 * parameter - 3
    earlier = (13 * parameter - 20) // 7
    later = (13 * parameter - 20) // 3
    first_block_end = (10 * parameter - 24) // 7
    occupied_source_bit = 2 * parameter - 6
    transported_valuation = (rank - 2) // 3
    post_transport_valuation = (8 * parameter - 16) // 3

    assert 7 * earlier == 13 * parameter - 20
    assert 3 * later == 13 * parameter - 20
    assert 7 * first_block_end == 10 * parameter - 24
    assert 3 * transported_valuation == rank - 2
    assert 3 * post_transport_valuation == 8 * parameter - 16
    assert (
        parameter - 2
        < first_block_end
        < occupied_source_bit
        < transported_valuation
        < post_transport_valuation
    )
    assert earlier < source < later

    # The source is label three.  Both non-pure providers are safe, including
    # the provider strictly before the source.
    assert 2 * rank + 3 == 7 * source
    assert not endpoint_safe(rank, source)
    assert endpoint_safe(rank, earlier)
    assert endpoint_safe(rank, later)
    for offset in range(1, 5):
        assert 2 * rank + offset - 7 * earlier == parameter - 4 + offset
        assert 2 * rank + offset - 3 * later == parameter - 4 + offset
        assert 0 < parameter - 4 + offset < earlier

    for denominator_rank in (source, earlier, later):
        assert deficit(rank, denominator_rank) == block_deficit(
            rank, denominator_rank
        )

    correction_exponents = [parameter - 2]
    correction_exponents.extend(
        exponent
        for exponent in range(first_block_end, transported_valuation)
        if exponent != occupied_source_bit
    )
    assert len(correction_exponents) == (
        transported_valuation - first_block_end
    )
    assert len(set(correction_exponents)) == len(correction_exponents)

    correction_ranks = [rank - exponent for exponent in correction_exponents]
    assert len(set(correction_ranks)) == len(correction_ranks)
    for exponent, denominator_rank in zip(
        correction_exponents, correction_ranks, strict=True
    ):
        assert 3 * exponent <= rank - 5
        assert endpoint_safe(rank, denominator_rank)
        assert deficit(rank, denominator_rank) == 1 << exponent
        assert block_deficit(rank, denominator_rank) == 1 << exponent

    mismatch = deficit(rank, earlier) + deficit(rank, later)
    mismatch -= deficit(rank, source)
    assert valuation(mismatch) == parameter - 2

    # This is a literal Boolean carry chain: every newly added safe pure atom
    # begins at the exact current discrepancy valuation.
    carry_valuations = []
    for exponent, denominator_rank in zip(
        correction_exponents, correction_ranks, strict=True
    ):
        assert valuation(mismatch) == exponent
        carry_valuations.append(exponent)
        mismatch += deficit(rank, denominator_rank)
    assert valuation(mismatch) == transported_valuation

    terminal_source = rank - transported_valuation
    assert 3 * terminal_source == 2 * rank + 2
    assert not endpoint_safe(rank, terminal_source)
    assert deficit(rank, terminal_source) == 1 << transported_valuation
    mismatch -= deficit(rank, terminal_source)
    assert valuation(mismatch) == post_transport_valuation

    # Closed forms underlying the proof, checked as exact integers.
    source_closed = 1 << (parameter - 3)
    source_closed += ((1 << parameter) - 1) * (
        (1 << (2 * parameter - 6)) + (1 << (4 * parameter - 9))
    )
    earlier_gap = (3 * parameter + 4) // 7
    earlier_closed = ((1 << earlier_gap) - 1) * sum(
        1 << (parameter - 4 + index * earlier) for index in range(3)
    )
    later_closed = (1 << post_transport_valuation) - (
        1 << (parameter - 4)
    )
    assert source_closed == deficit(rank, source)
    assert earlier_closed == deficit(rank, earlier)
    assert later_closed == deficit(rank, later)

    initial_mismatch = earlier_closed + later_closed - source_closed
    low_modulus = 1 << post_transport_valuation
    expected_low = (
        -(1 << (parameter - 2))
        + (1 << first_block_end)
        + (1 << occupied_source_bit)
    )
    assert initial_mismatch % low_modulus == expected_low % low_modulus
    correction_total = sum(1 << exponent for exponent in correction_exponents)
    correction_closed = (
        (1 << (parameter - 2))
        + (1 << transported_valuation)
        - (1 << first_block_end)
        - (1 << occupied_source_bit)
    )
    assert correction_total == correction_closed

    return {
        "parameter": parameter,
        "rank": rank,
        "forbidden_label_three_source": source,
        "earlier_safe_bank_rank": earlier,
        "later_safe_provider_rank": later,
        "safe_pure_correction_count": len(correction_ranks),
        "first_carry_valuation": carry_valuations[0],
        "last_safe_carry_valuation": carry_valuations[-1],
        "transported_forbidden_label_two_rank": terminal_source,
        "transported_valuation": transported_valuation,
        "post_transport_valuation": post_transport_valuation,
    }


def main() -> None:
    rows = [audit_row(42 * index + 8) for index in range(1, 31)]
    print(
        json.dumps(
            {
                "exact_family_rows": len(rows),
                "first_row": rows[0],
                "last_row": rows[-1],
                "theorem": (
                    "safe backward-bank carries transport a forbidden "
                    "label-three pivot to a forbidden label-two pivot"
                ),
                "full_negacyclic_congruence_claimed": False,
                "rational_boolean_subsum_claimed": False,
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
