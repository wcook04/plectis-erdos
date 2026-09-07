#!/usr/bin/env python3
"""Exact receipts for the first-wave zero-buffer solvency theorem."""

from fractions import Fraction


def weight(rank: int) -> Fraction:
    return Fraction(1, (1 << rank) - 1)


def packet(height: int, exponent: int) -> Fraction:
    """The anchor-two packet 2^exponent M(2,height)."""
    return Fraction(1 << exponent, 3 * ((1 << height) - 1))


def mersenne_tail_upper_bound(cutoff: int) -> Fraction:
    """Strict upper bound for sum_{n>cutoff} 1/(2^n-1).

    For n > cutoff,

        1/(2^n-1) < 2^-n / (1-2^-(cutoff+1)).

    Summing the dyadic tail gives the displayed rational bound.
    """

    return Fraction(1 << (cutoff + 1), (1 << (cutoff + 1)) - 1) * Fraction(
        1, 1 << cutoff
    )


def check_first_wave_solvency() -> dict[str, object]:
    height = 15
    root_bits = [1, 2, 5, 6, 7, 8, 10]
    zero_pair_bits = [1, 2]
    external_bits = [5, 6, 7, 8, 10]

    root = sum((packet(height, j) for j in root_bits), Fraction())
    zero_pair = sum((packet(height, j) for j in zero_pair_bits), Fraction())
    external = sum((packet(height, j) for j in external_bits), Fraction())
    assert root == Fraction(1510, 1) * packet(height, 0)
    assert zero_pair == Fraction(6, 1) * packet(height, 0)
    assert external == Fraction(1504, 1) * packet(height, 0)
    assert root == zero_pair + external
    assert zero_pair == 2 * weight(15)

    forbidden = {15, 16}
    remainder = external
    selected: list[int] = []
    decisions: list[dict[str, object]] = []
    for rank in range(1, 17):
        take = rank not in forbidden and weight(rank) <= remainder
        decisions.append(
            {
                "rank": rank,
                "take": take,
                "remainder_before": str(remainder),
            }
        )
        if take:
            selected.append(rank)
            remainder -= weight(rank)

    assert selected == [7, 8, 9, 10, 11, 14]
    assert remainder == Fraction(508494094946, 25001218250357195)

    # The remaining permitted tail is strictly smaller than this bound.
    tail_bound = mersenne_tail_upper_bound(16)
    assert tail_bound == Fraction(2, 131071)
    tax = weight(14) - 2 * weight(15)
    assert tax == weight(14) * weight(15)
    solvency_margin = remainder - tail_bound - tax
    assert solvency_margin > 0

    # Therefore every allowed Boolean extraction from the external value
    # leaves more than the complete rank-15 predecessor carry tax.
    assert zero_pair + (remainder - tail_bound) > weight(14)

    return {
        "root_identity": "1510 P(15,0) = 6 P(15,0) + 1504 P(15,0)",
        "zero_pair_identity": "P(15,2)+P(15,1)=2*w_15",
        "external_value": str(external),
        "greedy_allowed_prefix": selected,
        "greedy_remainder_after_rank_16": str(remainder),
        "strict_tail_upper_bound_after_rank_16": str(tail_bound),
        "rank_15_predecessor_tax": str(tax),
        "certified_margin_above_tax": str(solvency_margin),
        "isolated_zero_buffer_reachable_from_complete_first_wave": False,
    }


def main() -> None:
    print(check_first_wave_solvency())


if __name__ == "__main__":
    main()
