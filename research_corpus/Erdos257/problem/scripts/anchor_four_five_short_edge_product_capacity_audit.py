#!/usr/bin/env python3
"""Exact audit for AnchorFourFiveShortEdgeProductCapacityNoGo.md."""

from __future__ import annotations

from fractions import Fraction


TARGET_DENOMINATOR = 465


def mersenne(rank: int) -> int:
    return (1 << rank) - 1


def prefix_integers(support: list[int]) -> tuple[int, int]:
    product = 1
    numerator = 1
    for rank in support:
        old_product = product
        product *= mersenne(rank)
        numerator = mersenne(rank) * numerator - TARGET_DENOMINATOR * old_product
    direct = product - TARGET_DENOMINATOR * sum(
        product // mersenne(rank) for rank in support
    )
    assert numerator == direct
    return product, numerator


def power_of_two(exponent: int) -> Fraction:
    if exponent >= 0:
        return Fraction(1 << exponent)
    return Fraction(1, 1 << (-exponent))


def audit_actual_selected_plateaux(depth: int = 40) -> int:
    """Check the exact selected-plateau equation on the fixed diagonal orbit."""
    loads = [0] * (2 * depth + 1)
    support: list[int] = []
    remainder = 0
    residual = Fraction(1, TARGET_DENOMINATOR)
    previous_selected: int | None = None
    checked = 0

    for rank in range(1, depth + 1):
        source_odd = (2 * pow(2, 2 * rank - 2, TARGET_DENOMINATOR)) // (
            TARGET_DENOMINATOR
        )
        source_even = (2 * pow(2, 2 * rank - 1, TARGET_DENOMINATOR)) // (
            TARGET_DENOMINATOR
        )
        source_pair = 2 * source_odd + source_even
        divisor_load = 2 * loads[2 * rank - 1] + loads[2 * rank]
        pre_remainder = 4 * remainder + source_pair - divisor_load
        weight = 5 if rank == 1 else (1 << rank) + 1
        bit = int(pre_remainder >= weight)
        remainder = pre_remainder - bit * weight

        if bit:
            if previous_selected is not None:
                old_rank = previous_selected
                gap = rank - old_rank
                old_plateau = (1 << (2 * old_rank)) * residual
                alpha = Fraction(
                    pow(4, rank, TARGET_DENOMINATOR),
                    TARGET_DENOMINATOR,
                )
                old_resolvent = sum(
                    (
                        Fraction(pow(4, rank, mersenne(selected)), mersenne(selected))
                        for selected in support
                    ),
                    Fraction(),
                )
                endpoint_correction = Fraction(
                    1 + remainder, 1 << (2 * gap)
                ) + Fraction(alpha - old_resolvent, 1 << (2 * gap))
                new_residual = residual - Fraction(1, mersenne(rank))
                next_plateau = (1 << (2 * rank)) * new_residual
                reverse_correction = Fraction(
                    next_plateau + 1 + Fraction(1, mersenne(rank)),
                    1 << (2 * gap),
                )
                assert endpoint_correction == reverse_correction
                assert old_plateau == (
                    power_of_two(2 * old_rank - rank) + endpoint_correction
                )
                checked += 1

            residual -= Fraction(1, mersenne(rank))
            support.append(rank)
            previous_selected = rank
            for multiple in range(2 * rank, 2 * depth + 1, rank):
                loads[multiple] += 1

    return checked


def audit_chain(start_rank: int, deficits: list[int]) -> int:
    assert start_rank == 23
    support = [9, 13, 14, 17, 19, 21, 22, 23]
    assert support == sorted(set(support))
    product, numerator = prefix_integers(support)
    residual = Fraction(numerator, TARGET_DENOMINATOR * product)
    height = Fraction(product, 1 << (2 * start_rank))
    initial_height = height
    plateau = (1 << (2 * start_rank)) * residual
    assert numerator == TARGET_DENOMINATOR * height * plateau

    rank = start_rank
    cumulative_multiplier = Fraction(1)
    checked = 0
    for deficit in deficits:
        next_rank = 2 * rank - deficit
        assert rank < next_rank < 2 * rank
        old_product = product
        old_numerator = numerator
        old_height = height

        product *= mersenne(next_rank)
        numerator = (
            mersenne(next_rank) * old_numerator
            - TARGET_DENOMINATOR * old_product
        )
        residual -= Fraction(1, mersenne(next_rank))
        height = Fraction(product, 1 << (2 * next_rank))
        plateau = (1 << (2 * next_rank)) * residual

        edge_multiplier = Fraction(
            (1 << deficit) * mersenne(next_rank),
            1 << next_rank,
        )
        assert edge_multiplier == Fraction(
            mersenne(next_rank),
            1 << (2 * (next_rank - rank)),
        )
        assert height == old_height * edge_multiplier
        cumulative_multiplier *= edge_multiplier
        assert height == initial_height * cumulative_multiplier
        assert numerator == TARGET_DENOMINATOR * height * plateau

        support.append(next_rank)
        rank = next_rank
        checked += 1
    return checked


def main() -> None:
    chains = [
        (23, [1, 2, 1, 3]),
        (23, [2, 3, 4]),
        (23, [1, 1, 2, 3, 5]),
    ]
    product_updates = sum(
        audit_chain(start, deficits) for start, deficits in chains
    )
    plateau_edges = audit_actual_selected_plateaux()
    print(
        "short-edge product-capacity no-go PASS: "
        f"{product_updates} exact coefficient-one product updates and "
        f"{plateau_edges} globally reachable selected plateaux audited"
    )


if __name__ == "__main__":
    main()
