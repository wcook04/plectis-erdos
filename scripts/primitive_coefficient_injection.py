#!/usr/bin/env python3
"""Exact audit for the comparison c_(2,11)(n) >= c_(10,11)(n).

The proof in PrimitiveCoefficientInjection.md is unbounded.  Its only finite
part is the range m <= 1218 in the auxiliary inequality

    c_(2,11)(5m) >= c_(2,11)(m),  5 does not divide m.

This script checks that range with integers and audits the finite
classification used to prove that no larger exceptional m can occur in the
elementary reduced-residue estimate.  The longer coefficient scans reported
below are diagnostics, not substitutes for the proof.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import gcd


def prime(number: int) -> bool:
    return number > 1 and all(
        number % divisor
        for divisor in range(2, int(number**0.5) + 1)
    )


def omega(number: int) -> int:
    count = 0
    divisor = 2
    while divisor * divisor <= number:
        if number % divisor == 0:
            count += 1
            while number % divisor == 0:
                number //= divisor
        divisor += 1
    return count + (number > 1)


def phi(number: int) -> int:
    result = number
    divisor = 2
    while divisor * divisor <= number:
        if number % divisor == 0:
            result -= result // divisor
            while number % divisor == 0:
                number //= divisor
        divisor += 1
    if number > 1:
        result -= result // number
    return result


def primitive_count(left: int, right: int, rank: int) -> int:
    return sum(
        1
        for q in range(1, rank // right + 1)
        if rank - right * q > 0
        and (rank - right * q) % left == 0
        and gcd((rank - right * q) // left, q) == 1
    )


def reduced_interval_count(rank: int) -> int:
    """Count k with rank/2 < k < 6 rank/11 and gcd(k,rank)=1."""
    return sum(
        gcd(k, rank) == 1
        for k in range(rank // 2 + 1, (6 * rank - 1) // 11 + 1)
    )


def exceptional_ratio_values() -> tuple[list[int], dict[int, int]]:
    """Enumerate m coprime to 5 with phi(m)/2^omega(m) < 22.

    The proof bounds every prime divisor by 83.  Recursion multiplies the
    exact local factor p^(e-1)(p-1)/2 until the product reaches 22.
    """
    primes = [p for p in range(2, 90) if p != 5 and prime(p)]
    values: set[int] = set()
    maximum_by_largest_prime: dict[int, int] = {}

    def visit(
        start: int,
        number: int,
        ratio: Fraction,
        largest_prime: int,
    ) -> None:
        if ratio >= 22:
            return
        values.add(number)
        maximum_by_largest_prime[largest_prime] = max(
            maximum_by_largest_prime.get(largest_prime, 0), number
        )
        for index in range(start, len(primes)):
            p = primes[index]
            next_number = number * p
            next_ratio = ratio * Fraction(p - 1, 2)
            while next_ratio < 22:
                visit(index + 1, next_number, next_ratio, p)
                next_number *= p
                next_ratio *= p

    visit(0, 1, Fraction(1), 1)
    return sorted(values), maximum_by_largest_prime


def projective_parameter_audit(depth: int) -> None:
    for rank in range(1, depth + 1):
        assert primitive_count(2, 11, rank) == reduced_interval_count(rank)


def multiplier_injection_audit(depth: int) -> None:
    """Audit the two explicit interval injections in their stated cases."""
    for rank in range(1, depth + 1):
        source = range(
            9 * rank // 10 + 1,
            (10 * rank - 1) // 11 + 1,
        )
        source = [k for k in source if gcd(k, rank) == 1]
        if rank % 5:
            images = [5 * k - 4 * rank for k in source]
        elif rank % 25 == 0:
            m = rank // 5
            images = [k - 2 * m for k in source]
        else:
            continue
        assert len(images) == len(set(images))
        assert all(
            rank / 2 < image < 6 * rank / 11
            and gcd(image, rank) == 1
            for image in images
        )


def scale_five_audit() -> dict[str, object]:
    exceptional, maxima = exceptional_ratio_values()
    assert max(exceptional) == 1218
    assert all(
        Fraction(phi(m), 1 << omega(m)) < 22 for m in exceptional
    )
    assert all(
        reduced_interval_count(5 * m) >= reduced_interval_count(m)
        for m in range(1, 1219)
        if m % 5
    )
    return {
        "exceptional_ratio_count": len(exceptional),
        "largest_exceptional_m": max(exceptional),
        "maximum_m_by_largest_prime": {
            str(key): maxima[key] for key in sorted(maxima)
        },
        "scale_five_checked_for_m_at_most": 1218,
    }


def packet_counterexample_audit(depth: int) -> dict[str, object]:
    first_children = [(8, 11), (11, 3), (2, 11), (11, 9)]
    for rank in range(1, depth + 1):
        child_coefficient = sum(
            primitive_count(left, right, rank)
            for left, right in first_children
        )
        assert child_coefficient >= primitive_count(10, 11, rank)

    forced_children = [(11, 20), (20, 9), (17, 20), (20, 3)]
    witness_rank = 39
    child_values = [
        primitive_count(left, right, witness_rank)
        for left, right in forced_children
    ]
    tax_value = primitive_count(19, 20, witness_rank)
    assert child_values == [0, 0, 0, 0]
    assert tax_value == 1

    # At the first tax rank 2n-1, M(e,n) emits iff e divides n-1.
    for stop in range(3, 80):
        for endpoint in range(2, stop):
            assert (
                primitive_count(endpoint, stop, 2 * stop - 1) == 1
            ) == ((stop - 1) % endpoint == 0)

    return {
        "first_collision_domination_checked_through": depth,
        "forced_stop_20_counterexample_rank": witness_rank,
        "forced_stop_20_child_coefficients": child_values,
        "forced_stop_20_tax_coefficient": tax_value,
        "first_tax_rank_endpoint_divisibility_checked_for_stops": [3, 79],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=5000)
    args = parser.parse_args()

    projective_parameter_audit(min(args.depth, 2000))
    multiplier_injection_audit(min(args.depth, 5000))
    scale_receipt = scale_five_audit()

    for rank in range(1, args.depth + 1):
        assert primitive_count(2, 11, rank) >= primitive_count(10, 11, rank)

    packet_receipt = packet_counterexample_audit(args.depth)
    print(
        json.dumps(
            {
                "comparison": "c_(2,11)(n) >= c_(10,11)(n)",
                "unbounded_status": (
                    "proved in PrimitiveCoefficientInjection.md; the depth "
                    "scan is diagnostic"
                ),
                "diagnostic_scan_through": args.depth,
                "scale_five": scale_receipt,
                "packet_tax": packet_receipt,
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
