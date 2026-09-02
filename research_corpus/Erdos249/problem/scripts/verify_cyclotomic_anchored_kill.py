#!/usr/bin/env python3
"""Dependency-free exact checks for the Erdős #249 cyclotomic anchor packet."""

from fractions import Fraction
import json


def divisors(n: int) -> list[int]:
    return [d for d in range(1, n + 1) if n % d == 0]


def mersenne(n: int) -> int:
    return 2**n - 1


def cyclotomic_at_two(n: int, cache: dict[int, int] | None = None) -> int:
    """Evaluate Phi_n(2) from 2^n-1 = product_{d|n} Phi_d(2)."""
    if cache is None:
        cache = {}
    if n not in cache:
        proper_product = 1
        for d in divisors(n):
            if d < n:
                proper_product *= cyclotomic_at_two(d, cache)
        cache[n] = mersenne(n) // proper_product
    return cache[n]


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def multiplicative_order(a: int, modulus: int) -> int:
    x = 1
    for k in range(1, modulus):
        x = x * a % modulus
        if x == 1:
            return k
    raise AssertionError("order not found")


def totients_through(limit: int) -> list[int]:
    values = list(range(limit + 1))
    for p in range(2, limit + 1):
        if values[p] == p:
            for n in range(p, limit + 1, p):
                values[n] -= values[n] // p
    return values


def window_discrepancy(h: int, n: int, depth: int, phi: list[int]) -> int:
    return sum(
        (phi[n + h + 1 + j] - phi[n + 1 + j]) * 2 ** (depth - 1 - j)
        for j in range(depth)
    )


def certificate(h: int, n: int, depth: int, phi: list[int]) -> dict[str, int | bool]:
    discrepancy = window_discrepancy(h, n, depth, phi)
    modulus = 2**depth
    residue = discrepancy % modulus
    radius = n + h + depth + 2
    return {
        "h": h,
        "N": n,
        "L": depth,
        "discrepancy": discrepancy,
        "modulus": modulus,
        "residue": residue,
        "radius": radius,
        "certified": radius < residue < modulus - radius,
    }


def main() -> None:
    phi = totients_through(400)
    natural = certificate(30, 300, 13, phi)
    anchored = certificate(30, 330, 10, phi)
    depth_sixteen = certificate(30, 300, 16, phi)

    assert cyclotomic_at_two(30) == 331
    assert is_prime(5) and is_prime(331)
    assert 331 % 30 == 1
    assert multiplicative_order(2, 331) == 30
    assert natural == {
        "h": 30,
        "N": 300,
        "L": 13,
        "discrepancy": 385374,
        "modulus": 8192,
        "residue": 350,
        "radius": 345,
        "certified": True,
    }
    assert anchored == {
        "h": 30,
        "N": 330,
        "L": 10,
        "discrepancy": 10864,
        "modulus": 1024,
        "residue": 624,
        "radius": 372,
        "certified": True,
    }
    assert depth_sixteen["residue"] == 2928
    phase_lower_bound = (
        Fraction(1)
        - Fraction(1, 2) * Fraction(7 * 183, 4096) ** 2
        - Fraction(7 * 348, 65536)
    )
    assert phase_lower_bound == Fraction(30_666_239, 33_554_432)
    assert phase_lower_bound > Fraction(9, 10)

    print(
        json.dumps(
            {
                "schema": "erdos249_cyclotomic_anchored_kill_receipt_v1",
                "phi_30_at_two": 331,
                "order_two_mod_331": 30,
                "natural_certificate": natural,
                "anchored_certificate": anchored,
                "depth_16_residue": depth_sixteen["residue"],
                "strict_nine_tenths_lower_bound": {
                    "numerator": phase_lower_bound.numerator,
                    "denominator": phase_lower_bound.denominator,
                },
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
