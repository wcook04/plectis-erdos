#!/usr/bin/env python3
"""Replay the overlap-sensitive Orlicz--Gram Pareto selector.

All finite selector inequalities use Fraction arithmetic.  Decimal arithmetic
is used only for the returned transcendental four-leaf calibration and the
optimal-threshold bisection; neither is proof authority for the general result.
"""

from __future__ import annotations

from decimal import Decimal, getcontext
from fractions import Fraction as Q
from itertools import combinations, product


def young_indices(ages: tuple[Q, ...], count: int) -> set[int]:
    return set(sorted(range(len(ages)), key=lambda i: (ages[i], i))[:count])


def check_selector_row(
    charges: tuple[Q, ...], ages: tuple[Q, ...], bad: set[int]
) -> int:
    k = len(charges)
    b = len(bad)
    total_age = sum(ages, Q(0))
    survivor_product_sq = Q(1)
    for charge in charges:
        survivor_product_sq *= charge**2

    pair_checks = 0
    if b <= k - 2:
        young = young_indices(ages, b + 2)
        good = sorted(young - bad)
        assert len(good) >= 2
        i, j = good[:2]
        assert max(ages[i], ages[j]) * (k - b - 1) <= total_age
        complement = [ell for ell in range(k) if ell not in (i, j)]
        complement_energy = sum((charges[ell] ** 2 for ell in complement), Q(0))
        lhs = survivor_product_sq * Q(k - 2) ** (k - 2)
        rhs = (charges[i] * charges[j]) ** 2 * complement_energy ** (k - 2)
        assert lhs <= rhs
        pair_checks += 1

    if b <= k - 3:
        total_energy = sum((charge**2 for charge in charges), Q(0))
        total_product = Q(1)
        for charge in charges:
            total_product *= charge
        h4 = total_product**2 * (Q(k - 2, 1) / total_energy) ** (k - 2)
        light = {i for i, charge in enumerate(charges) if charge**4 < h4}
        assert len(light) <= 1
        young = young_indices(ages, b + 3)
        good_heavy = sorted(young - bad - light)
        assert len(good_heavy) >= 2
        i, j = good_heavy[:2]
        assert max(ages[i], ages[j]) * (k - b - 2) <= total_age
        pair_checks += 1
    return pair_checks


def optimal_u(k: int, p: Decimal) -> Decimal:
    lo = Decimal(0)
    hi = Decimal(1)
    exponent = Decimal(k - 2) / 2
    for _ in range(220):
        mid = (lo + hi) / 2
        value = mid * ((Decimal(k) - 2 * mid) / Decimal(k - 2)) ** exponent
        if value < p:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def four_leaf_replay() -> dict[str, Decimal]:
    s = Decimal(1) / 1000
    beta4 = Decimal(999) / 1000
    beta3 = beta4 * (-3 * s).exp()
    beta2 = beta4 * (-5 * s).exp()
    q4 = Decimal(125) * beta2 / Decimal(864)
    charges = [Decimal(3) / 10] * 3 + [q4]
    energy = sum((q * q for q in charges), Decimal(0))
    product_q = Decimal(1)
    for q in charges:
        product_q *= q
    h_cl = product_q.sqrt() * (Decimal(2) / energy).sqrt()
    p = product_q / (energy / 4) ** 2
    u = optimal_u(4, p)
    h_opt = (energy * u / 4).sqrt()
    assert q4 < h_cl <= h_opt < Decimal(3) / 10
    assert product_q == Decimal(27) * q4 / 1000
    return {
        "beta2": beta2,
        "q4": q4,
        "h_cl": h_cl,
        "h_opt": h_opt,
    }


def main() -> int:
    getcontext().prec = 80
    charge_rows = (
        (Q(1), Q(1), Q(1)),
        (Q(1, 3), Q(1), Q(2)),
        (Q(1, 4), Q(1, 2), Q(1), Q(2)),
        (Q(1, 5), Q(1, 2), Q(1), Q(2), Q(3)),
        (Q(1, 4), Q(1, 3), Q(1, 2), Q(1), Q(2), Q(3)),
    )
    age_values = (Q(0), Q(1, 4), Q(1))
    checked_rows = 0
    checked_pairs = 0
    for charges in charge_rows:
        k = len(charges)
        for ages in product(age_values, repeat=k):
            for b in range(k):
                for bad_tuple in combinations(range(k), b):
                    checked_pairs += check_selector_row(charges, ages, set(bad_tuple))
                    checked_rows += 1

    calibration = four_leaf_replay()
    print(
        "PASS: overlap-sensitive two-tier selector and four-leaf replay; "
        f"rows={checked_rows}, tier_checks={checked_pairs}, "
        f"q4={calibration['q4']:.12f}, h_cl={calibration['h_cl']:.12f}, "
        f"h_opt={calibration['h_opt']:.12f}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
