#!/usr/bin/env python3
"""Exact receipts for constrained cohort solvency and its scale-free no-go."""

from fractions import Fraction


def weight(rank: int) -> Fraction:
    return Fraction(1, (1 << rank) - 1)


def anchored_unit(height: int) -> Fraction:
    return Fraction(1, 3 * ((1 << height) - 1))


def tail_upper_bound(cutoff: int) -> Fraction:
    """Strict upper bound for sum_{n>cutoff} w_n."""

    return Fraction(1 << (cutoff + 1), (1 << (cutoff + 1)) - 1) * Fraction(
        1, 1 << cutoff
    )


def constrained_greedy(
    target: Fraction, forbidden: set[int], cutoff: int
) -> tuple[list[int], Fraction]:
    remainder = target
    selected: list[int] = []
    for rank in range(1, cutoff + 1):
        if rank not in forbidden and weight(rank) <= remainder:
            selected.append(rank)
            remainder -= weight(rank)
    return selected, remainder


def check_scale_free_counterexample() -> dict[str, object]:
    # The external anchored load agrees exactly with the complete first-wave
    # complement: 188/2^12 = 1504/2^15 = 47/1024.
    height = 12
    external_coefficient = 188
    forbidden = {12, 13}
    external = external_coefficient * anchored_unit(height)
    selected, remainder = constrained_greedy(external, forbidden, 22)
    assert selected == [7, 8, 9, 10, 11, 14, 16, 17, 21, 22]
    assert remainder == Fraction(
        2688127220338038597838,
        630826191904604658117352698501,
    )

    tax = weight(11) - 2 * weight(12)
    assert tax == weight(11) * weight(12)
    assert 0 < remainder < tax

    protected_pair = 6 * anchored_unit(height)
    assert protected_pair == 2 * weight(12)
    dangerous = protected_pair + remainder
    assert 2 * weight(12) < dangerous < weight(11)

    root_height = 15
    root_external_coefficient = 1504
    assert Fraction(external_coefficient, 1 << height) == Fraction(
        root_external_coefficient, 1 << root_height
    )

    # Independent receipt for the safe height-15 instance.
    root_external = root_external_coefficient * anchored_unit(root_height)
    root_selected, root_remainder = constrained_greedy(
        root_external, {15, 16}, 16
    )
    assert root_selected == [7, 8, 9, 10, 11, 14]
    root_tax = weight(14) - 2 * weight(15)
    root_margin = root_remainder - tail_upper_bound(16) - root_tax
    assert root_margin > 0

    return {
        "common_anchored_load": "47/1024",
        "unsafe_instance": {
            "height": height,
            "external_coefficient": external_coefficient,
            "forbidden_ranks": sorted(forbidden),
            "finite_greedy_extraction": selected,
            "external_remainder": str(remainder),
            "tax": str(tax),
            "dangerous_total": str(dangerous),
            "margin_below_predecessor": str(weight(11) - dangerous),
        },
        "safe_instance": {
            "height": root_height,
            "external_coefficient": root_external_coefficient,
            "finite_safe_certificate_margin": str(root_margin),
        },
        "normalized_anchored_load_is_solvency_invariant": False,
    }


def main() -> None:
    print(check_scale_free_counterexample())


if __name__ == "__main__":
    main()
