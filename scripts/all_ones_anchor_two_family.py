#!/usr/bin/env python3
"""Exact receipts for the all-ones anchor-two family."""

from __future__ import annotations

import json
from fractions import Fraction


def weight(rank: int) -> Fraction:
    return Fraction(1, (1 << rank) - 1)


def cylinder(a: int, b: int) -> Fraction:
    return weight(a) * weight(b)


def all_ones(height: int, width: int) -> Fraction:
    return ((1 << width) - 1) * cylinder(2, height)


def parity_receipt(maximum_width: int = 80) -> int:
    checks = 0
    for height in range(3, maximum_width + 3):
        for width in range(1, height + 1):
            value = all_ones(height, width)
            if width % 2 == 0:
                quotient = ((1 << width) - 1) // 3
                assert value == quotient * weight(height)
                assert quotient == sum(1 << exponent for exponent in range(0, width, 2))
            else:
                quotient = ((1 << width) - 2) // 3
                assert value == quotient * weight(height) + cylinder(2, height)
                assert quotient == sum(1 << exponent for exponent in range(1, width, 2))
            assert (((1 << width) - 1) % 7 == 0) == (width % 3 == 0)
            checks += 1
    return checks


def odd_bank_recut_receipt() -> dict[str, str]:
    value = all_ones(4, 3)
    residual = cylinder(2, 4) - cylinder(3, 4)
    assert value == 2 * weight(4) + cylinder(2, 4)
    assert 2 * weight(4) == weight(3) - cylinder(3, 4)
    assert residual == 12 * cylinder(6, 4) > 0
    assert value == weight(3) + residual
    return {
        "value": str(value),
        "emitted_atom": "w_3",
        "positive_residual": str(residual),
        "residual_cylinder": "12 M(6,4)",
    }


def diagonal_hole_receipt() -> dict[str, object]:
    height = 11
    width = 10
    value = all_ones(height, width)
    assert value == Fraction(341, 2047)
    assert value == Fraction(1, 6) - weight(height) / 6

    residual_after_three = value - weight(3)
    assert residual_after_three >= weight(6)
    assert residual_after_three < weight(5) < weight(4)
    residual = residual_after_three - weight(6)
    assert residual == Fraction(1013, 128961)

    tail_bound = Fraction(2, 255)
    assert residual - tail_bound == Fraction(131, 10961685) > 0
    assert weight(7) - residual == Fraction(310, 16378047) > 0

    # The two diagonal thresholds meet only at H=11.
    for test_height in range(5, 80):
        test_residual = Fraction(1, 126) - weight(test_height) / 6
        in_hole = tail_bound < test_residual < weight(7)
        assert in_hole == (test_height == 11)

    return {
        "height": height,
        "width": width,
        "multiplicity_of_w_11": 341,
        "multiplicity_binary_exponents": [0, 2, 4, 6, 8],
        "forced_selected_prefix": [3, 6],
        "rank_7_too_large_margin": str(weight(7) - residual),
        "entire_rank_8_tail_too_small_margin": str(residual - tail_bound),
        "boolean_representation_exists": False,
    }


def main() -> None:
    print(
        json.dumps(
            {
                "parity_and_mod_three_checks": parity_receipt(),
                "odd_bank_recut": odd_bank_recut_receipt(),
                "diagonal_h_11_hole": diagonal_hole_receipt(),
                "trivial_boolean_subfamilies": ["X_(H,2)=w_H", "X_(H,H)=w_2"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
