#!/usr/bin/env python3
"""Exact receipts for adjacent cyclotomic gaps and recut transport."""

from fractions import Fraction
from math import gcd, isqrt

from sympy import cyclotomic_poly


def divisors(value: int) -> list[int]:
    result: list[int] = []
    for divisor in range(1, isqrt(value) + 1):
        if value % divisor == 0:
            result.append(divisor)
            if divisor * divisor != value:
                result.append(value // divisor)
    return sorted(result)


def mersenne(rank: int) -> int:
    return (1 << rank) - 1


def reduced_denominator(height: int, rank: int) -> int:
    assert height % rank == 0
    assert height % (rank - 1) == 0
    value = 1
    for period in divisors(height):
        if period <= rank:
            value *= int(cyclotomic_poly(period, 2))
    return value


def positive_two_coin_solution(
    value: int, first: int, second: int
) -> tuple[int, int] | None:
    """Return positive a,b with value=a*first+b*second, if they exist."""
    shifted = value - first - second
    if shifted < 0:
        return None
    common = gcd(first, second)
    if shifted % common:
        return None
    first_reduced = first // common
    second_reduced = second // common
    shifted_reduced = shifted // common
    if first_reduced == 1:
        return (1 + shifted_reduced, 1)
    extra_second = (
        shifted_reduced * pow(second_reduced, -1, first_reduced)
    ) % first_reduced
    if extra_second * second_reduced > shifted_reduced:
        return None
    extra_first = (
        shifted_reduced - extra_second * second_reduced
    ) // first_reduced
    return (extra_first + 1, extra_second + 1)


def semigroup_receipt(height: int, rank: int) -> dict[str, object]:
    denominator = reduced_denominator(height, rank)
    width = 3 * denominator // (
        mersenne(rank - 1) * mersenne(rank)
    )
    predecessor_factor = int(cyclotomic_poly(rank - 1, 2))
    rank_factor = int(cyclotomic_poly(rank, 2))
    solution = positive_two_coin_solution(
        width, predecessor_factor, rank_factor
    )
    if solution is not None:
        a, b = solution
        assert a > 0 and b > 0
        assert width == a * predecessor_factor + b * rank_factor
    return {
        "height": height,
        "rank": rank,
        "corridor_width": width,
        "phi_predecessor": predecessor_factor,
        "phi_rank": rank_factor,
        "positive_semigroup_solution": solution,
        "corridor_excluded": solution is None,
    }


def transport_receipt(rank: int, lower_gap_multiplier: int) -> dict[str, int]:
    assert rank >= 16
    denominator = 1
    for period in range(1, rank + 1):
        denominator *= int(cyclotomic_poly(period, 2))
    theta = int(cyclotomic_poly(rank + 1, 2))
    lifted_denominator = theta * denominator

    predecessor_factor = int(cyclotomic_poly(rank - 1, 2))
    lower = 6 * denominator // mersenne(rank)
    lower_gap = lower_gap_multiplier * predecessor_factor
    old_coefficient = lower + lower_gap

    next_upper = 3 * lifted_denominator // mersenne(rank)
    take_coefficient = (
        theta * old_coefficient
        - 3 * lifted_denominator // mersenne(rank)
    )
    skip_coefficient = theta * old_coefficient
    assert take_coefficient == next_upper + theta * lower_gap
    assert take_coefficient >= next_upper
    assert skip_coefficient > next_upper

    return {
        "rank": rank,
        "height_lift_multiplier": theta,
        "old_lower_gap": lower_gap,
        "next_upper": next_upper,
        "take_branch_overshoot": take_coefficient - next_upper,
        "skip_branch_overshoot": skip_coefficient - next_upper,
    }


def adjacent_disjointness_receipt(rank: int) -> dict[str, object]:
    assert rank >= 9
    weights = {
        n: Fraction(1, mersenne(n)) for n in range(7, rank)
    }
    assert all(
        weights[n] > 2 * weights[n + 1]
        for n in range(7, rank - 1)
    )

    # The full finite-tail defect is always larger than the last weight.
    defects = {}
    for first in range(7, rank - 1):
        defect = weights[first] - sum(
            (weights[n] for n in range(first + 1, rank)),
            Fraction(),
        )
        assert defect > weights[rank - 1]
        defects[first] = defect

    required_lower = Fraction(1, mersenne(rank))
    required_upper = (
        Fraction(1, mersenne(rank - 1))
        - Fraction(2, mersenne(rank + 1))
    )
    assert 0 < required_lower < required_upper
    assert required_upper < weights[rank - 1]

    return {
        "rank": rank,
        "required_charge_interval": [
            str(required_lower),
            str(required_upper),
        ],
        "minimum_nonzero_boolean_charge_gap": str(weights[rank - 1]),
        "consecutive_fatal_transition_exists": False,
        "checked_tail_defect_count": len(defects),
    }


def one_skip_disjointness_receipt(rank: int) -> dict[str, object]:
    assert rank >= 9

    def weight(index: int) -> Fraction:
        return Fraction(1, mersenne(index))

    lower = 2 * weight(rank) - weight(rank + 1)
    upper = weight(rank - 1) - 2 * weight(rank + 2)
    assert 0 < lower < upper
    assert upper < 2 * weight(rank)

    half_scale = Fraction(1, 2 ** (rank + 1))
    two_thirds_scale = Fraction(2, 3 * 2**rank)

    # In the series for lower-T_r, the first coefficient is 1/2 and
    # every later coefficient is positive.
    shifted_lower_lower_bound = half_scale

    # For upper-T_r, bound every coefficient after ell=1 by 2^ell.
    ratio = Fraction(1, 2 ** (rank - 1))
    shifted_upper_upper_bound = (
        half_scale + ratio**2 / (1 - ratio)
    )
    assert shifted_upper_upper_bound < two_thirds_scale

    parity_rows = []
    for first_difference in range(7, rank + 1):
        if 2 * first_difference <= rank:
            delta_lower = Fraction(
                2, 3 * 2 ** (2 * first_difference)
            )
            assert delta_lower >= two_thirds_scale
            side = "above"
        else:
            delta_upper = (
                Fraction(2, 3 * 2 ** (2 * first_difference))
                + Fraction(1, 2 ** (3 * first_difference))
                / (1 - Fraction(1, 2**first_difference))
            )
            assert delta_upper < shifted_lower_lower_bound
            side = "below"
        parity_rows.append(
            {
                "first_differing_rank": first_difference,
                "side_of_required_interval": side,
            }
        )

    return {
        "rank_pair": [rank, rank + 2],
        "required_charge_interval": [str(lower), str(upper)],
        "shifted_interval_bounds": [
            f"> {shifted_lower_lower_bound}",
            f"< {shifted_upper_upper_bound}",
        ],
        "parity_rows": parity_rows,
        "two_rank_revival_exists": False,
    }


def main() -> None:
    receipts = [
        semigroup_receipt(height, rank)
        for height, rank in (
            (240, 16),
            (600, 25),
            (870, 30),
            (930, 31),
            (1140, 20),
            (1530, 18),
        )
    ]
    first = receipts[0]
    assert first["corridor_width"] == 1287
    assert first["phi_predecessor"] == 151
    assert first["phi_rank"] == 257
    assert first["corridor_excluded"] is True
    print(
        {
            "semigroup_receipts": receipts,
            "transport_receipts": [
                transport_receipt(16, 1),
                transport_receipt(20, 7),
            ],
            "adjacent_disjointness_receipts": [
                adjacent_disjointness_receipt(rank)
                for rank in (16, 20, 30)
            ],
            "one_skip_disjointness_receipts": [
                one_skip_disjointness_receipt(rank)
                for rank in (16, 17, 30)
            ],
            "law": (
                "a fatal width is a positive adjacent-cyclotomic semigroup "
                "sum, and its lower gap becomes an impossible next-rank "
                "Boolean recut debt even after one skipped rank"
            ),
        }
    )


if __name__ == "__main__":
    main()
