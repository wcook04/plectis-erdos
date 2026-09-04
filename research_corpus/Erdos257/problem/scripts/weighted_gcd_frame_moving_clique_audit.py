#!/usr/bin/env python3
"""Exact finite checks for the weighted gcd frame and semiprime cliques."""

from fractions import Fraction
from itertools import combinations
from math import gcd, lcm


def phi(n: int) -> int:
    """Euler's totient function for the small audit inputs."""
    out = n
    p = 2
    remaining = n
    while p * p <= remaining:
        if remaining % p == 0:
            out -= out // p
            while remaining % p == 0:
                remaining //= p
        p += 1
    if remaining > 1:
        out -= out // remaining
    return out


def divisors(n: int) -> list[int]:
    """Positive divisors of n."""
    return [d for d in range(1, n + 1) if n % d == 0]


def audit_frame_identity() -> int:
    """Check Proposition 1 for several signed rational weight systems."""
    systems = [
        ({6, 10, 15}, {6: 1, 10: 1, 15: 1}),
        ({6, 14, 21, 35}, {6: 2, 14: -1, 21: 3, 35: -2}),
        ({15, 21, 35, 77}, {15: -3, 21: 1, 35: 4, 77: 2}),
    ]
    checks = 0
    for support, weights in systems:
        covariance = Fraction(0)
        for a in support:
            for b in support:
                covariance += Fraction(
                    weights[a] * weights[b] * (gcd(a, b) - 1), a * b
                )

        frame = Fraction(0)
        all_divisors = {d for a in support for d in divisors(a) if d >= 2}
        for d in all_divisors:
            coefficient = sum(
                (Fraction(weights[a], a) for a in support if a % d == 0),
                Fraction(0),
            )
            frame += phi(d) * coefficient * coefficient
        assert covariance == frame
        checks += 1
    return checks


def matching_weight(edges: tuple[tuple[int, int], ...]) -> Fraction | None:
    """Weight of a matching, or None if two edges share a vertex."""
    vertices: set[int] = set()
    weight = Fraction(0)
    for p, q in edges:
        if p in vertices or q in vertices:
            return None
        vertices.update((p, q))
        weight += Fraction(1, p * q)
    return weight


def audit_clique_blocks() -> int:
    """Check block mass, frame energy, and matching bounds exactly."""
    blocks = [
        [5, 7, 11, 13],
        [17, 19, 23, 29, 31],
        [37, 41, 43, 47, 53, 59],
    ]
    checks = 0
    for primes in blocks:
        edges = list(combinations(primes, 2))
        s = sum((Fraction(1, p) for p in primes), Fraction(0))
        t = sum((Fraction(1, p * p) for p in primes), Fraction(0))
        mass = sum((Fraction(1, p * q) for p, q in edges), Fraction(0))
        assert mass == (s * s - t) / 2

        frame_energy = sum(
            Fraction(p - 1, p * p) * (s - Fraction(1, p)) ** 2 for p in primes
        )
        direct_prime_frame = Fraction(0)
        for p in primes:
            coefficient = sum(
                (Fraction(1, a * b) for a, b in edges if p in (a, b)),
                Fraction(0),
            )
            direct_prime_frame += phi(p) * coefficient * coefficient
        assert frame_energy == direct_prime_frame

        best = Fraction(0)
        for size in range(len(edges) + 1):
            for chosen in combinations(edges, size):
                weight = matching_weight(chosen)
                if weight is not None:
                    best = max(best, weight)
        assert best <= t / 2
        checks += 1
    return checks


def audit_mersenne_lcm_bound() -> int:
    """Check the exact two-exponent Mersenne gcd/lcm lower bound."""
    checks = 0
    for a, b in [(15, 21), (35, 55), (77, 91), (143, 187)]:
        m_a = (1 << a) - 1
        m_b = (1 << b) - 1
        g = gcd(a, b)
        assert gcd(m_a, m_b) == (1 << g) - 1
        common = lcm(m_a, m_b)
        assert common > 1 << (a + b - g - 2)
        checks += 1
    return checks


def main() -> None:
    frame_checks = audit_frame_identity()
    clique_checks = audit_clique_blocks()
    lcm_checks = audit_mersenne_lcm_bound()
    print(
        "weighted gcd-frame audit passed: "
        f"{frame_checks} identities, {clique_checks} cliques, "
        f"{lcm_checks} Mersenne LCM bounds"
    )


if __name__ == "__main__":
    main()
