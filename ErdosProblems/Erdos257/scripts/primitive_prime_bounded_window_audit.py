#!/usr/bin/env python3
"""Finite audits for the bounded-window primitive-prime lemma.

The proof in PrimitivePrimeBoundedWindowNoncancellation.md is symbolic.  This
script checks its exact finite residue and height claims for representative
primitive channels and for every support pattern in small multiplier windows.
"""

from __future__ import annotations

from itertools import combinations


def prime_factors(n: int) -> list[int]:
    factors: list[int] = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            factors.append(d)
            while n % d == 0:
                n //= d
        d = 3 if d == 2 else d + 2
    if n > 1:
        factors.append(n)
    return factors


def multiplicative_order_two(p: int) -> int:
    x = 2 % p
    order = 1
    while x != 1:
        x = (2 * x) % p
        order += 1
    return order


def primitive_primes(a: int) -> list[int]:
    return [p for p in prime_factors((1 << a) - 1) if multiplicative_order_two(p) == a]


def support_patterns(T: int):
    tail = range(2, T + 1)
    for size in range(T):
        for chosen in combinations(tail, size):
            yield (1, *chosen)


def cleared_height(K: tuple[int, ...]) -> int:
    product = 1
    for k in K:
        product *= k
    return sum(product // k for k in K)


def residue(K: tuple[int, ...], p: int) -> int:
    return sum(pow(k, -1, p) for k in K) % p


def audit_window(T: int, anchors: range) -> int:
    checked = 0
    for a in anchors:
        if a <= T**T or a == 6:
            continue
        primes = primitive_primes(a)
        assert primes, (T, a, "Zsigmondy failure")
        for p in primes:
            assert p >= a + 1 > T**T
            for K in support_patterns(T):
                H = cleared_height(K)
                assert 0 < H <= T**T < p
                assert residue(K, p) != 0, (T, a, p, K, H)
                checked += 1
    return checked


def main() -> None:
    # Trial division is intentionally enough here: all tested Mersenne numbers
    # are below 2^41.  T=2 audits every support pattern for many anchors; T=3
    # crosses the nontrivial threshold 3^3=27.
    count = audit_window(2, range(5, 31))
    count += audit_window(3, range(28, 42))

    # Two adversarial endpoints: prime support gives K={1}; full support gives
    # K={1,...,T}.  Both are already included in the exhaustive patterns.
    assert residue((1,), 31) == 1
    assert cleared_height((1, 2, 3)) == 11
    assert residue((1, 2, 3), 43) == 11 * pow(6, -1, 43) % 43

    print(f"bounded-window audit passed: {count} primitive-channel patterns")


if __name__ == "__main__":
    main()
