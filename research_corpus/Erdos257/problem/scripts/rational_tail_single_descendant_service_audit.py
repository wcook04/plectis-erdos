#!/usr/bin/env python3
"""Exact checks for rational-tail denominator transitions and CRT service."""

from fractions import Fraction
from math import gcd, lcm


def valuation(n: int, p: int) -> int:
    """Return the p-adic valuation of a nonzero integer n."""
    n = abs(n)
    out = 0
    while n % p == 0:
        n //= p
        out += 1
    return out


def prime_factors(n: int) -> dict[int, int]:
    """Factor the small integers used in this audit."""
    out: dict[int, int] = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def order_two(p: int) -> int:
    """Return the multiplicative order of 2 modulo the odd prime p."""
    value = 1
    for d in range(1, p):
        value = value * 2 % p
        if value == 1:
            return d
    raise AssertionError("order not found")


def primitive_prime_powers(a: int) -> list[tuple[int, int]]:
    """Return (p, p^mu) for the natural primitive part of 2^a-1."""
    factors = prime_factors((1 << a) - 1)
    return [(p, p**mu) for p, mu in factors.items() if order_two(p) == a]


def crt_pair(x: int, modulus: int, residue: int, new_modulus: int) -> tuple[int, int]:
    """Combine two congruences with coprime moduli."""
    step = ((residue - x) * pow(modulus, -1, new_modulus)) % new_modulus
    combined_modulus = modulus * new_modulus
    return (x + modulus * step) % combined_modulus, combined_modulus


def predicted_exponent(u: int, q: int, m: int, p: int) -> int:
    """Proposition 1's prediction for den(u/q - 1/m)."""
    alpha = valuation(q, p)
    beta = valuation(m, p)
    assert alpha > 0
    if alpha != beta:
        return max(alpha, beta)
    inside = u * (m // p**alpha) - q // p**alpha
    return max(0, alpha - valuation(inside, p))


def audit_transition_law() -> int:
    checks = 0
    for q in range(2, 60):
        for u in range(1, q):
            if gcd(u, q) != 1:
                continue
            for m in range(q // u + 1, 100):
                y = Fraction(u, q) - Fraction(1, m)
                if y <= 0:
                    continue
                for p in prime_factors(q):
                    expected = predicted_exponent(u, q, m, p)
                    actual = valuation(y.denominator, p)
                    assert actual == expected, (u, q, m, p, expected, actual)
                    checks += 1
    return checks


def service_class(b_values: list[int], u: int, q: int) -> tuple[int, int, int]:
    """Construct the unit CRT class in Theorem 3."""
    ell = lcm(*b_values)
    residue, modulus = 0, 1
    for a in b_values:
        d = ell // a
        mersenne_a = (1 << a) - 1
        for p, prime_power in primitive_prime_powers(a):
            assert gcd(d, prime_power) == 1
            assert valuation(q, p) == valuation(prime_power, p)
            q_p = q // prime_power
            w = mersenne_a // prime_power
            target = (
                pow(d, -1, prime_power)
                * pow(u, -1, prime_power)
                * q_p
                * pow(w, -1, prime_power)
            ) % prime_power
            residue, modulus = crt_pair(residue, modulus, target, prime_power)
    return ell, residue, modulus


def audit_single_descendant_service() -> int:
    b_values = [2, 4, 8]
    primitive_product = 3 * 5 * 17
    cases = [(1, primitive_product), (2, 7 * primitive_product), (11, 13 * primitive_product)]
    checks = 0
    for u, q in cases:
        assert gcd(u, q) == 1
        ell, residue, modulus = service_class(b_values, u, q)
        assert modulus == primitive_product
        assert gcd(residue, modulus) == 1
        k = residue if residue > 0 else modulus
        while k <= 1 or Fraction(1, (1 << (ell * k)) - 1) >= Fraction(u, q):
            k += modulus
        for _ in range(3):
            n = ell * k
            y = Fraction(u, q) - Fraction(1, (1 << n) - 1)
            assert y > 0
            assert gcd(y.denominator, primitive_product) == 1
            checks += 1
            k += modulus
    return checks


def main() -> None:
    transition_checks = audit_transition_law()
    service_checks = audit_single_descendant_service()
    print(
        "rational-tail single-descendant audit passed: "
        f"{transition_checks} transition checks, {service_checks} CRT checks"
    )


if __name__ == "__main__":
    main()
