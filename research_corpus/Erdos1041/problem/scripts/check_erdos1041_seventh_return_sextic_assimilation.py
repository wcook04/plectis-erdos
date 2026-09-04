#!/usr/bin/env python3
"""Exact replay for the seventh-return sextic assimilation."""

from __future__ import annotations

from fractions import Fraction
from itertools import product
import json


ROOT2 = {
    0: (2, 0),
    1: (1, 1),
    2: (-1, 1),
    3: (-2, 0),
    4: (-1, -1),
    5: (1, -1),
}


def norm_sq_of_sum(indices: list[int], multiplier: int) -> Fraction:
    x = 0
    y = 0
    for index in indices:
        a, b = ROOT2[(multiplier * index) % 6]
        x += a
        y += b
    return Fraction(x * x + 3 * y * y, 4)


def selector_passports() -> dict[str, object]:
    by_parity = {}
    for parity in (0, 1):
        pairs = [
            (parity % 6, (parity + 1) % 6),
            ((parity + 2) % 6, (parity + 3) % 6),
            ((parity + 4) % 6, (parity + 5) % 6),
        ]
        passports = {
            (
                norm_sq_of_sum([pairs[r][choice[r]] for r in range(3)], 1),
                norm_sq_of_sum([pairs[r][choice[r]] for r in range(3)], 2),
            )
            for choice in product((0, 1), repeat=3)
        }
        assert passports == {
            (Fraction(0), Fraction(0)),
            (Fraction(1), Fraction(3)),
        }
        by_parity[str(parity)] = [
            [str(first), str(second)] for first, second in sorted(passports)
        ]
    return by_parity


def model_separation() -> dict[str, str]:
    t = Fraction(1, 2)
    a = -Fraction(3, 8)
    b = Fraction(1)
    low = a * t + b * t**2 - t**6
    paired = a * (t - t**5) + b * (t**2 - t**4) - t**6
    assert low == Fraction(3, 64) > 0
    assert paired == -Fraction(1, 256) < 0
    return {"low": str(low), "paired": str(paired)}


def exact_constant_checks() -> dict[str, object]:
    # sqrt(3) lies strictly between the rational bounds used in the proofs.
    assert 3 * 4 > 2 * 2
    assert 3 * 16 < 7 * 7
    assert 3 * 81 * 81 >= 140 * 140

    # The rational alpha=3/4 strengthening: C=27/4 makes the cubic chord
    # slope at least 35/4 using sqrt(3)>=140/81.
    cubic_slope_floor = Fraction(27, 4) * Fraction(3, 4) * Fraction(140, 81)
    assert cubic_slope_floor == Fraction(35, 4)

    # Paired outward-tail constants.
    q = Fraction(47, 64)
    assert 1 - q**4 <= q
    assert q + Fraction(1, 4) - 1 == -Fraction(1, 64)

    # Fixed paired radius extends exactly through C=512.
    u = Fraction(1, 64)
    assert 8 * 512 * u**2 == 1
    assert 8 * u**5 < 1

    # At alpha=1 the exact threshold simplifies to 4*sqrt(3), since
    # 4*(1+8)/(3*sqrt(3)) = 12/sqrt(3) = 4*sqrt(3).
    assert Fraction(4 * (1 + 8), 3) == 12
    assert 12 * 12 == 16 * 3 * 3

    return {
        "alpha_three_quarters_rational_threshold": "27/4",
        "alpha_one_exact_threshold": "4*sqrt(3)",
        "paired_tail_margin": "1/64",
        "fixed_radius": "1/64",
        "fixed_radius_cubic_ceiling": 512,
    }


def main() -> None:
    receipt = {
        "schema": "erdos1041_seventh_return_sextic_assimilation_check_v1",
        "status": "pass",
        "selector_passports": selector_passports(),
        "model_separation": model_separation(),
        "constants": exact_constant_checks(),
        "claim_boundary": (
            "exact finite and scalar replay; the ordinary proof owns the "
            "complex selection assembly and unrestricted Erdos 1041 remains open"
        ),
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
