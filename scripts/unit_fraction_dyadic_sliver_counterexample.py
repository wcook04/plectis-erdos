#!/usr/bin/env python3
"""Exact certificate falsifying the unrestricted unit-fraction sliver conjecture.

All comparisons are made after clearing denominators.  The script prints only
compact bit-length and SHA-256 receipts because the certificate integers have
about 650,000 bits.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from hashlib import sha256
from math import prod


RANK = 81_803
OFFSETS = (1, 3, 4, 7, 8, 13, 15, 16)
N = 106_907
K = 50_847
PERIOD = 106_906
AUDIT_MAX_OFFSET = 26
AUDIT_MAX_RANK = RANK - 1


def digest(value: int) -> str:
    size = max(1, (value.bit_length() + 7) // 8)
    return sha256(value.to_bytes(size, "big")).hexdigest()


def audit_smaller_offset_resonances() -> dict[str, object]:
    """Classify bounded fixed-offset second-order resonances exactly.

    For offsets A, q = 1 + sum 2^a and B = sum 4^a, an eventual sliver
    resonance must have q*s-B in {0, 1} and 2^m = s (mod q).  This audit
    enumerates every nonempty A in {1,...,26} and every admissible rank
    max(A) < m < RANK.  It is not a search over arbitrary supports.
    """

    first_moment = 0
    second_moment = 0
    previous_gray = 0
    second_order_candidates = 0
    power_hits: list[tuple[int, int, int, int, tuple[int, ...]]] = []

    for counter in range(1, 1 << AUDIT_MAX_OFFSET):
        gray = counter ^ (counter >> 1)
        changed = gray ^ previous_gray
        offset = (changed & -changed).bit_length()
        if gray & changed:
            first_moment += 1 << offset
            second_moment += 1 << (2 * offset)
        else:
            first_moment -= 1 << offset
            second_moment -= 1 << (2 * offset)
        previous_gray = gray

        q = first_moment + 1
        remainder = second_moment % q
        if remainder not in (0, q - 1):
            continue
        second_order_candidates += 1
        epsilon = 0 if remainder == 0 else 1
        residue = (second_moment + epsilon) // q
        offsets = tuple(
            index + 1
            for index in range(AUDIT_MAX_OFFSET)
            if gray & (1 << index)
        )

        value = 1
        for rank in range(AUDIT_MAX_RANK + 1):
            if rank > max(offsets) and value == residue:
                third_moment = sum(1 << (3 * item) for item in offsets)
                third_coefficient = q * residue * residue - third_moment
                power_hits.append(
                    (rank, q, epsilon, third_coefficient, offsets)
                )
                break
            value = (2 * value) % q

    expected = [(10, 23, 0, -856, (1, 2, 4))]
    assert power_hits == expected

    # This sole smaller resonance is below, rather than inside, the sliver.
    rank, q, _, _, offsets = power_hits[0]
    residue = pow(2, rank, q)
    denominator = ((1 << rank) - residue) // q
    residual = Fraction(1, denominator) - sum(
        (
            Fraction(1, (1 << (rank - offset)) - 1)
            for offset in offsets
        ),
        Fraction(),
    )
    assert 0 < residual < Fraction(1, 1 << rank)

    return {
        "offset_sets_checked": (1 << AUDIT_MAX_OFFSET) - 1,
        "second_order_candidates": second_order_candidates,
        "power_hits_before_rank_81803": tuple(power_hits),
        "viable_hits": 0,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--audit-smaller-offset-resonances",
        action="store_true",
        help="run the optional 2^26-1 bounded Gray-code classification",
    )
    args = parser.parse_args()

    two_m = 1 << RANK
    support = tuple(sorted(RANK - offset for offset in OFFSETS))

    # The small congruence is the discovery certificate for the sparse family.
    leading_sum = sum(1 << offset for offset in OFFSETS)
    quadratic_sum = sum(1 << (2 * offset) for offset in OFFSETS)
    assert leading_sum + 1 == N
    assert quadratic_sum + 1 == N * K
    assert pow(2, RANK, N) == K
    assert pow(2, PERIOD, N) == 1

    # These inequalities certify the uniform power-series bounds used in the
    # note for every m = RANK (mod PERIOD), m >= RANK.
    powers = tuple(1 << offset for offset in OFFSETS)
    largest_power = max(powers)
    cubic_sum = sum(value**3 for value in powers)
    assert largest_power > K
    assert largest_power**3 > N * K**2
    assert 3 * cubic_sum < (1 << 50) - largest_power
    assert N * K + quadratic_sum < (1 << 50) - largest_power

    denominator = (two_m - K) // N
    assert denominator > 0
    assert denominator % 2 == 1
    assert N * denominator + K == two_m

    # Before rank m-16 every atom is larger than 1/D.  From m-16 onward,
    # replay the exact greedy decisions with a dynamically cleared denominator.
    first_active_rank = RANK - max(OFFSETS)
    assert denominator > (1 << (first_active_rank - 1)) - 1
    running_product = 1
    running_numerator = 1
    actual_support: list[int] = []
    decisions: list[tuple[int, bool]] = []
    for rank in range(first_active_rank, RANK + 1):
        factor = (1 << rank) - 1
        take = running_numerator * factor >= denominator * running_product
        decisions.append((rank, take))
        if take:
            actual_support.append(rank)
            running_numerator = (
                running_numerator * factor - denominator * running_product
            )
            running_product *= factor
    assert tuple(actual_support) == support
    assert decisions[-1] == (RANK, False)

    factors = tuple((1 << rank) - 1 for rank in support)
    product_denominator = prod(factors)
    prefix_numerator = sum(product_denominator // factor for factor in factors)
    residual_numerator = product_denominator - denominator * prefix_numerator
    common_denominator = denominator * product_denominator

    # These are exactly
    #   2^(-m) < 1/D - sigma_F < 1/(2^m - 1).
    lower_gap = two_m * residual_numerator - common_denominator
    upper_gap = common_denominator - (two_m - 1) * residual_numerator
    # The full suffix satisfies T_m < 2^-m + (2/3)4^-m.  The next cleared
    # comparison proves that the residual already exceeds this upper bound.
    fatal_gap = (
        3 * (1 << (2 * RANK)) * residual_numerator
        - common_denominator * (3 * two_m + 2)
    )
    assert residual_numerator > 0
    assert lower_gap > 0
    assert upper_gap > 0
    assert fatal_gap > 0
    assert running_product == product_denominator
    assert running_numerator == residual_numerator

    print("unit-fraction dyadic-sliver counterexample: PASS")
    print(f"rank: {RANK}")
    print(f"offsets: {OFFSETS}")
    print(f"support: {support}")
    print(f"D formula: (2^{RANK} - {K}) / {N}")
    print(f"D odd: {denominator % 2 == 1}")
    print(f"D bit length: {denominator.bit_length()}")
    print(f"exact greedy support before fatal skip: {tuple(actual_support)}")
    print(f"lower cleared gap bit length: {lower_gap.bit_length()}")
    print(f"lower cleared gap sha256: {digest(lower_gap)}")
    print(f"upper cleared gap bit length: {upper_gap.bit_length()}")
    print(f"upper cleared gap sha256: {digest(upper_gap)}")
    print(f"fatal-tail cleared gap bit length: {fatal_gap.bit_length()}")
    print(f"fatal-tail cleared gap sha256: {digest(fatal_gap)}")
    print("status: exact greedily reachable fatal counterexample")
    if args.audit_smaller_offset_resonances:
        print("bounded offset-resonance audit:", audit_smaller_offset_resonances())


if __name__ == "__main__":
    main()
