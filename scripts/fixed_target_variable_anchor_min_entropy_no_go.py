#!/usr/bin/env python3
"""Exact audit for FixedTargetVariableAnchorMinEntropyNoGo.md."""

from fractions import Fraction
from math import prod


def mersenne(n: int) -> int:
    return (1 << n) - 1


def oriented_least(z: int, modulus: int) -> int:
    residue = z % modulus
    return min(residue, modulus - residue)


def audit_target(v: int, first_term_threshold: int, block_anchor: int) -> int:
    checks = 0

    # The exact constant-representative family.
    for n in range(first_term_threshold, first_term_threshold + 24):
        p = mersenne(n)
        r = p - v
        assert r > 2 * v * v
        assert Fraction(1, v) >= Fraction(1, p)
        assert oriented_least(v * p, r) == v * v
        checks += 1

    # Arbitrarily long deterministic all-one tail blocks.
    assert v * (2 * v + 1) * Fraction(1, 1 << (block_anchor - 2)) < 1
    for length in range(1, 13):
        indices = range(block_anchor, block_anchor + length)
        denominators = [mersenne(j) for j in indices]
        residual = Fraction(1, v)
        for denominator in denominators:
            assert residual >= Fraction(1, denominator)
            residual -= Fraction(1, denominator)
            checks += 1

        p = prod(denominators)
        a = sum(p // denominator for denominator in denominators)
        r = p - v * a
        assert residual == Fraction(r, v * p)
        assert 2 * v * v * a < r
        assert oriented_least(v * p, r) == v * v * a

        tail_bound = Fraction(1, 1 << (block_anchor - 2))
        asserted_bound = Fraction(v * v, 1) * tail_bound / (1 - v * tail_bound)
        assert Fraction(v * v * a, r) < asserted_bound
        checks += 4

    return checks


def main() -> None:
    checks_21 = audit_target(v=21, first_term_threshold=10, block_anchor=13)
    checks_465 = audit_target(v=465, first_term_threshold=19, block_anchor=22)
    print(
        "fixed-target variable-anchor no-go PASS: "
        f"{checks_21 + checks_465} exact checks "
        "for v=21 and v=465"
    )


if __name__ == "__main__":
    main()
