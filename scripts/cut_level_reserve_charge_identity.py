#!/usr/bin/env python3
"""Exact receipts for the cut-level reserve/charge identity."""

from fractions import Fraction


def mersenne(rank: int) -> int:
    return (1 << rank) - 1


def weight(rank: int) -> Fraction:
    return Fraction(1, mersenne(rank))


def cylinder(first: int, second: int) -> Fraction:
    return weight(first) * weight(second)


def check_partition_identity() -> int:
    checks = 0
    for rank in range(16, 80):
        denominator = (
            mersenne(15) * mersenne(rank - 1) * mersenne(rank)
        )
        lower = 6 * denominator // mersenne(rank)
        upper = 3 * denominator // mersenne(rank - 1)
        corridor_samples = {
            lower,
            lower + 1,
            (lower + upper) // 2,
            upper - 2,
            upper - 1,
        }
        for coefficient in sorted(corridor_samples):
            total = Fraction(coefficient, 3 * denominator)
            # Test several exact physical partitions of the same cut.
            for numerator in (0, 1, 2, 3, 5, 8):
                protected = total * Fraction(numerator, 8)
                external = total - protected
                required = weight(rank - 1) - protected
                upper_gap = upper - coefficient
                assert required > 0
                assert required - external == Fraction(
                    upper_gap, 3 * denominator
                )
                checks += 1
    return checks


def check_first_wave() -> dict[str, str]:
    protected = 6 * cylinder(2, 15)
    assert protected == 2 * weight(15)
    tax = weight(14) - protected
    assert tax == cylinder(14, 15)

    isolated_external = Fraction()
    assert tax - isolated_external == cylinder(14, 15)

    full_external = 1504 * cylinder(2, 15)
    full_total = protected + full_external
    assert full_total == 1510 * cylinder(2, 15)
    assert full_external - tax == full_total - weight(14) > 0
    return {
        "isolated_shortfall": str(tax),
        "complete_initial_surplus": str(full_external - tax),
    }


def check_height_thirty_root_cut() -> dict[str, object]:
    root_cohort = 1510 * cylinder(2, 15)
    lifted_coefficient = root_cohort / cylinder(2, 30)
    assert lifted_coefficient.denominator == 1
    assert lifted_coefficient.numerator == 49_481_190
    assert lifted_coefficient.numerator % 8 == 6

    protected = 6 * cylinder(2, 30)
    assert protected == 2 * weight(30)
    external = root_cohort - protected
    forbidden = {30, 31}
    selected: list[int] = []
    remainder = external
    first_insolvent_rank = None
    tax = cylinder(29, 30)
    for rank in range(2, 58):
        if rank not in forbidden and weight(rank) <= remainder:
            remainder -= weight(rank)
            selected.append(rank)
        if 0 < remainder < tax and first_insolvent_rank is None:
            first_insolvent_rank = rank

    expected = [
        7, 8, 9, 10, 11, 13, 16, 18, 20, 22, 24, 29, 32, 34,
        37, 39, 42, 45, 46, 47, 49, 50, 51, 53, 54, 56, 57,
    ]
    assert selected == expected
    assert first_insolvent_rank == 57
    assert 0 < remainder < tax
    assert protected + remainder < weight(29)
    assert weight(29) + protected + remainder < weight(28)

    common_prefix = [5, 7, 8, 9, 10, 11, 13, 16, 18, 20, 22, 24]
    total_before_28 = Fraction(1, 21) - sum(
        (weight(rank) for rank in common_prefix), Fraction()
    )
    external_before_28 = total_before_28 - protected
    assert weight(29) <= external_before_28 < weight(28)
    assert weight(28) <= total_before_28 < 2 * weight(28)
    assert total_before_28 - weight(28) < weight(29)

    return {
        "lifted_coefficient": lifted_coefficient.numerator,
        "low_residue_mod_8": lifted_coefficient.numerator % 8,
        "constrained_greedy_set": selected,
        "first_insolvent_rank": first_insolvent_rank,
        "reserve_over_first_tax": str(remainder / tax),
        "first_global_lex_divergence": 28,
        "external_decision": "skip 28, take 29",
        "complete_root_decision": "take 28, then skip 29",
    }


def greedy_row(
    target: Fraction, last_rank: int, forbidden: set[int] | None = None
) -> tuple[set[int], Fraction]:
    forbidden = forbidden or set()
    selected: set[int] = set()
    remainder = target
    for rank in range(6, last_rank + 1):
        if rank not in forbidden and weight(rank) <= remainder:
            remainder -= weight(rank)
            selected.add(rank)
    return selected, remainder


def check_global_lex_veto_scout() -> list[dict[str, int]]:
    root_cohort = 1510 * cylinder(2, 15)
    horizon = 600
    tail_bound = Fraction(1, 1 << horizon) / (
        1 - Fraction(1, 1 << (horizon + 1))
    )
    insolvent_rows: list[dict[str, int]] = []
    for height in range(15, 301, 15):
        protected = 2 * weight(height)
        external = root_cohort - protected
        external_bits, remainder = greedy_row(
            external, horizon, {height, height + 1}
        )
        tax = cylinder(height - 1, height)
        if remainder < tax:
            assert remainder > 0
            full_bits, _ = greedy_row(root_cohort, height - 1)
            external_prefix = {
                rank for rank in external_bits if rank < height
            }
            first_flip = next(
                rank
                for rank in range(6, height)
                if (rank in full_bits) != (rank in external_prefix)
            )
            assert first_flip in full_bits
            assert first_flip not in external_prefix
            insolvent_rows.append(
                {"height": height, "first_global_flip": first_flip}
            )
        else:
            # The omitted tail cannot reduce the reserve to the tax corridor.
            assert remainder - tail_bound > tax

    assert insolvent_rows == [
        {"height": 30, "first_global_flip": 28},
        {"height": 75, "first_global_flip": 73},
        {"height": 120, "first_global_flip": 119},
        {"height": 135, "first_global_flip": 134},
        {"height": 255, "first_global_flip": 249},
        {"height": 300, "first_global_flip": 299},
    ]
    return insolvent_rows


def main() -> None:
    print(
        {
            "partition_checks": check_partition_identity(),
            "first_wave": check_first_wave(),
            "height_thirty_root_cut": check_height_thirty_root_cut(),
            "global_lex_veto_scout": check_global_lex_veto_scout(),
            "law": (
                "required predecessor bank minus external reserve equals "
                "the upper corridor gap divided by the common coordinate"
            ),
        }
    )


if __name__ == "__main__":
    main()
