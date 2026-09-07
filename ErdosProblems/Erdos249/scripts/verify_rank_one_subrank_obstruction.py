#!/usr/bin/env python3
"""Exact checks for the rank-one strict-subrank obstruction in Erdős #249.

The Lean proof is authoritative.  This dependency-free verifier reproduces
its rational constants, checks representative finite quotients, and records
the correction to the inherited four-atom tail calculation.
"""

from __future__ import annotations

import json
from fractions import Fraction


def moebius(n: int) -> int:
    if n < 1:
        raise ValueError("n must be positive")
    remaining = n
    prime_factors = 0
    p = 2
    while p * p <= remaining:
        if remaining % p == 0:
            remaining //= p
            prime_factors += 1
            if remaining % p == 0:
                return 0
            while remaining % p == 0:
                remaining //= p
        p += 1
    if remaining > 1:
        prime_factors += 1
    return -1 if prime_factors % 2 else 1


def theta_prefix(rung: int, cutoff: int) -> Fraction:
    return sum(
        (
            Fraction(moebius(d), (2**d - 1) ** rung)
            for d in range(1, cutoff + 1)
        ),
        Fraction(),
    )


def geometric_tail_bound(rung: int, cutoff: int) -> Fraction:
    """Bound the atoms d > cutoff by sum_(n>=cutoff) (2^-rung)^n."""
    q = Fraction(1, 2**rung)
    return q**cutoff / (1 - q)


def rank_one_quotient(e: int, cutoff: int) -> Fraction:
    a = theta_prefix(e + 2, cutoff)
    b = theta_prefix(2 * e + 2, cutoff)
    if b == 0:
        raise ZeroDivisionError("rank-one denominator vanished")
    return a * a / b


def record(value: Fraction) -> dict[str, int | str]:
    return {
        "numerator": value.numerator,
        "denominator": value.denominator,
        "decimal": format(float(value), ".17g"),
    }


def verify() -> dict[str, object]:
    alpha = Fraction(1429, 1512)
    prefix_error = Fraction(1, 3584)
    target_gap = Fraction(1, 480)

    # The uniform analytic inequalities used by Lean.
    assert Fraction(26, 27) - Fraction(1, 56) == alpha
    assert geometric_tail_bound(3, 4) == prefix_error
    for rung in range(3, 25):
        for cutoff in range(4, 25):
            assert geometric_tail_bound(rung, cutoff) <= prefix_error

    # The inherited text claimed 1/108 for this geometric series.  Its exact
    # value is 1/48, so Lean instead uses the already-checked five-atom split.
    inherited_four_atom_tail = geometric_tail_bound(2, 3)
    assert inherited_four_atom_tail == Fraction(1, 48)
    assert inherited_four_atom_tail != Fraction(1, 108)
    theta_two_upper = theta_prefix(2, 5) + geometric_tail_bound(2, 5)
    assert theta_two_upper < Fraction(8, 9)

    # Direct interval arithmetic gives a stronger quotient floor than the
    # two-stage 1/240-minus-perturbation presentation.
    quotient_floor = (alpha - prefix_error) ** 2 / (1 + prefix_error)
    certified_margin = quotient_floor - Fraction(8, 9)
    assert certified_margin > target_gap

    samples: list[dict[str, object]] = []
    for e in range(1, 17):
        for cutoff in range(4, 21):
            quotient = rank_one_quotient(e, cutoff)
            # A finite upper interval for Theta_2 suffices for an exact sample
            # certificate; no floating-point approximation is used.
            sample_gap = quotient - theta_two_upper
            assert sample_gap > target_gap
            if (e, cutoff) in {(1, 4), (1, 5), (2, 5), (8, 12), (16, 20)}:
                samples.append(
                    {
                        "e": e,
                        "cutoff": cutoff,
                        "quotient": record(quotient),
                        "gap_above_theta_two_upper": record(sample_gap),
                    }
                )

    # A representative positive direct sum remains above the same bound.
    weights = [Fraction(1, 3), Fraction(2, 5), Fraction(7, 11)]
    quotients = [
        rank_one_quotient(1, 5),
        rank_one_quotient(2, 7),
        rank_one_quotient(4, 9),
    ]
    weighted_average = sum(
        (w * value for w, value in zip(weights, quotients, strict=True)),
        Fraction(),
    ) / sum(weights, Fraction())
    assert weighted_average - theta_two_upper > target_gap

    # Sharp floor: unique minimiser at (e,Y)=(1,5) and uniform gap 21/320.
    # Lean uses a 7-atom enclosure of Theta_2 for the lower gap and a 6-atom
    # enclosure for the 1/15 failure.  The coarser 1/480 certificate above
    # is kept; it does not need uniqueness.
    q_one_five = rank_one_quotient(1, 5)
    q_one_five_exact = Fraction(35076077250375200, 37573118933633199)
    assert q_one_five == q_one_five_exact
    assert rank_one_quotient(1, 4) == Fraction(79049881, 84671559)
    assert rank_one_quotient(1, 6) == Fraction(
        1043700953468949889, 1117992059749781919
    )
    assert rank_one_quotient(1, 4) > q_one_five
    assert rank_one_quotient(1, 6) > q_one_five

    for e in range(1, 17):
        for cutoff in range(4, 21):
            quotient = rank_one_quotient(e, cutoff)
            if (e, cutoff) != (1, 5):
                assert quotient > q_one_five
            else:
                assert quotient == q_one_five

    e_ge_two_floor = (Fraction(6373, 6480) - Fraction(1, 61440)) ** 2 / (
        1 + Fraction(1, 61440)
    )
    assert e_ge_two_floor > q_one_five

    theta_two_seven_upper = theta_prefix(2, 7) + geometric_tail_bound(2, 7)
    assert theta_prefix(2, 7) == Fraction(53376062902, 61519376961)
    assert geometric_tail_bound(2, 7) == Fraction(1, 12288)
    sharp_gap = Fraction(21, 320)
    assert q_one_five - theta_two_seven_upper > sharp_gap
    assert Fraction(1, 16) < sharp_gap < Fraction(1, 15)

    theta_two_six_lower = theta_prefix(2, 6) - geometric_tail_bound(2, 6)
    assert theta_prefix(2, 6) == Fraction(3309559, 3814209)
    assert geometric_tail_bound(2, 6) == Fraction(1, 3072)
    assert q_one_five - theta_two_six_lower < Fraction(1, 15)
    assert not (q_one_five - theta_two_seven_upper > Fraction(1, 15))

    for e in range(1, 17):
        for cutoff in range(4, 21):
            assert rank_one_quotient(e, cutoff) - theta_two_seven_upper > sharp_gap
            assert rank_one_quotient(e, cutoff) - theta_two_seven_upper > Fraction(
                1, 16
            )

    return {
        "schema": "erdos249_rank_one_subrank_exact_verifier_v1",
        "status": "verified",
        "arithmetic": "exact_rational",
        "uniform_constants": {
            "alpha": record(alpha),
            "prefix_error": record(prefix_error),
            "quotient_floor": record(quotient_floor),
            "certified_margin_above_8_over_9": record(certified_margin),
            "target_gap": record(target_gap),
        },
        "inherited_claim_correction": {
            "claimed_geometric_tail_after_d_equals_3": record(Fraction(1, 108)),
            "actual_geometric_tail_after_d_equals_3": record(
                inherited_four_atom_tail
            ),
            "repair": (
                "use the exact first five atoms and the tail "
                "(1/4)^5/(1-1/4)=1/768"
            ),
            "theta_two_upper_from_repair": record(theta_two_upper),
        },
        "sample_rank_one_quotients": samples,
        "positive_direct_sum_sample": {
            "weighted_average": record(weighted_average),
            "gap_above_theta_two_upper": record(
                weighted_average - theta_two_upper
            ),
        },
        "sharp_floor": {
            "minimiser": {"e": 1, "cutoff": 5},
            "quotient": record(q_one_five_exact),
            "unique_on_grid": {"e_max": 16, "cutoff_max": 20},
            "e_ge_two_interval_floor": record(e_ge_two_floor),
            "theta_two_seven_atom_upper": record(theta_two_seven_upper),
            "theta_two_six_atom_lower": record(theta_two_six_lower),
            "uniform_gap": record(sharp_gap),
            "optimal_uniform_unit_fraction": record(Fraction(1, 16)),
            "one_fifteenth_fails_at_minimiser": True,
        },
    }


def main() -> int:
    print(json.dumps(verify(), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
