#!/usr/bin/env python3
"""Exact receipts for divisor-corridor uniqueness and rarity."""

from fractions import Fraction
from itertools import combinations

from sympy import cyclotomic_poly


def mersenne(rank: int) -> int:
    return (1 << rank) - 1


def full_denominator(rank: int) -> int:
    value = 1
    for period in range(1, rank + 1):
        value *= int(cyclotomic_poly(period, 2))
    return value


def analytic_separation_receipt(rank: int) -> dict[str, object]:
    assert rank >= 9
    denominator = full_denominator(rank)
    width = 3 * denominator // (mersenne(rank - 1) * mersenne(rank))
    assert width * mersenne(rank - 1) * mersenne(rank) == 3 * denominator

    rows = []
    for first_difference in range(7, rank):
        reciprocal_defect = Fraction(1, mersenne(first_difference)) - sum(
            (
                Fraction(1, mersenne(later))
                for later in range(first_difference + 1, rank)
            ),
            Fraction(),
        )
        assert reciprocal_defect > 0
        scaled_defect = 3 * denominator * reciprocal_defect
        assert scaled_defect > width
        rows.append(
            {
                "first_differing_rank": first_difference,
                "scaled_defect_floor": scaled_defect.numerator
                // scaled_defect.denominator,
                "exceeds_corridor_width": True,
            }
        )
    return {
        "rank": rank,
        "denominator_bits": denominator.bit_length(),
        "corridor_width": width,
        "separation_rows": rows,
    }


def exhaustive_charge_receipt(rank: int) -> dict[str, object]:
    denominator = full_denominator(rank)
    eligible = list(range(7, rank))
    charges: list[int] = []
    for size in range(len(eligible) + 1):
        for chosen in combinations(eligible, size):
            charges.append(
                3 * sum(denominator // mersenne(n) for n in chosen)
            )
    assert len(charges) == 1 << len(eligible)

    residues = {charge % denominator for charge in charges}
    assert len(residues) == len(charges)

    ordered = sorted(charges)
    minimum_gap = min(b - a for a, b in zip(ordered, ordered[1:]))
    width = 3 * denominator // (mersenne(rank - 1) * mersenne(rank))
    assert minimum_gap > width

    bad_fraction_bound = Fraction(
        len(charges) * width,
        denominator,
    )
    exact_formula = Fraction(
        3 * (1 << len(eligible)),
        mersenne(rank - 1) * mersenne(rank),
    )
    assert bad_fraction_bound == exact_formula
    assert bad_fraction_bound < Fraction(3, 1 << (rank + 4))

    return {
        "rank": rank,
        "eligible_rank_count": len(eligible),
        "boolean_charge_count": len(charges),
        "distinct_residue_count": len(residues),
        "minimum_charge_gap": minimum_gap,
        "corridor_width": width,
        "bad_translation_fraction_bound": str(bad_fraction_bound),
        "coarse_exponential_bound": f"< 3/2^{rank + 4}",
    }


def main() -> None:
    print(
        {
            "analytic_receipts": [
                analytic_separation_receipt(rank) for rank in (16, 20, 24)
            ],
            "exhaustive_receipts": [
                exhaustive_charge_receipt(rank) for rank in (16, 20)
            ],
            "law": (
                "at most one Boolean genealogy per fatal corridor; the "
                "fraction of affine charges admitting one is exponentially "
                "small"
            ),
        }
    )


if __name__ == "__main__":
    main()
