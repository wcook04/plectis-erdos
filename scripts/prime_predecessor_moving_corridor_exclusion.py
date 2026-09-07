#!/usr/bin/env python3
"""Exact receipts for prime-predecessor moving-corridor exclusion."""

from itertools import combinations
from math import isqrt

from sympy import cyclotomic_poly, factorint, n_order


def divisors(value: int) -> list[int]:
    result: list[int] = []
    for divisor in range(1, isqrt(value) + 1):
        if value % divisor == 0:
            result.append(divisor)
            if divisor * divisor != value:
                result.append(value // divisor)
    return sorted(result)


def lift_factor(height: int, rank: int) -> int:
    assert height % rank == 0
    return ((1 << height) - 1) // ((1 << rank) - 1)


def primitive_prime(period: int) -> int:
    value = int(cyclotomic_poly(period, 2))
    for prime in factorint(value):
        prime = int(prime)
        if n_order(2, prime) == period:
            return prime
    raise AssertionError(f"no primitive prime at period {period}")


def reduced_data(q: int) -> dict[str, object]:
    assert q > 2
    assert q % 30 == 29
    assert factorint(q) == {q: 1}
    rank = q + 1
    height = q * rank
    small_divisors = [d for d in divisors(height) if d <= rank]
    predicted = sorted(set(divisors(rank)) | {q})
    assert small_divisors == predicted

    reduced_denominator = 1
    for d in small_divisors:
        reduced_denominator *= int(cyclotomic_poly(d, 2))
    closed_form = ((1 << rank) - 1) * ((1 << q) - 1)
    assert reduced_denominator == closed_form

    lower = 6 * reduced_denominator // ((1 << rank) - 1)
    upper = 3 * reduced_denominator // ((1 << q) - 1)
    assert upper - lower == 3

    prime = primitive_prime(rank)
    assert prime > 3
    eligible = [d for d in divisors(height) if d < rank]
    assert 15 in eligible
    terms = {
        d: reduced_denominator // ((1 << d) - 1) for d in eligible
    }
    assert all(term % prime == 0 for term in terms.values())
    assert upper % prime == 0

    return {
        "prime_predecessor": q,
        "rank": rank,
        "height": height,
        "small_divisors": small_divisors,
        "eligible_prefix_ranks": eligible,
        "reduced_corridor": [lower, upper],
        "reduced_width": upper - lower,
        "primitive_prime": prime,
        "primitive_lattice_spacing": prime,
    }


def enumerate_first_case(q: int = 29) -> dict[str, object]:
    data = reduced_data(q)
    rank = int(data["rank"])
    height = int(data["height"])
    eligible = list(data["eligible_prefix_ranks"])
    reduced_denominator = ((1 << rank) - 1) * ((1 << q) - 1)
    incoming = 1510 * reduced_denominator // ((1 << 15) - 1)
    lower, upper = data["reduced_corridor"]
    checked = 0
    for size in range(len(eligible) + 1):
        for chosen in combinations(eligible, size):
            coefficient = incoming - 3 * sum(
                reduced_denominator // ((1 << n) - 1) for n in chosen
            )
            assert not (lower <= coefficient < upper)
            checked += 1
    assert checked == 1 << len(eligible)
    return {
        "height": height,
        "rank": rank,
        "eligible_prefix_rank_count": len(eligible),
        "enumerated_boolean_prefixes": checked,
        "fatal_prefixes": 0,
    }


def main() -> None:
    receipts = [reduced_data(q) for q in (29, 59, 89)]
    print(
        {
            "symbolic_family_receipts": receipts,
            "first_case_exhaustion": enumerate_first_case(),
            "law": (
                "after the common cyclotomic quotient, the fatal corridor "
                "has width 3 while its upper gap is a positive multiple of "
                "a primitive prime greater than 3"
            ),
        }
    )


if __name__ == "__main__":
    main()
