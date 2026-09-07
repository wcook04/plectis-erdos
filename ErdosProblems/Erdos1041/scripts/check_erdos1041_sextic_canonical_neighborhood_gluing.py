#!/usr/bin/env python3
"""Exact arithmetic replay of the canonical 6075/78 gluing gap."""

from fractions import Fraction
import random


def main() -> None:
    assert 78 * 78 == 6084
    assert 6084 - 6075 == 9
    rng = random.Random(20260825)
    rows = 0
    for _ in range(100_000):
        beta = Fraction(rng.randint(-200, 200), 137)
        coords = [Fraction(rng.randint(-20000, 20000), 211) for _ in range(3)]
        energy = sum(x * x for x in coords)
        outer = 6075 * beta**4 <= energy
        box = all(abs(x) < 78 * beta**2 for x in coords)
        assert outer or box
        rows += 1
    print("exact gap:", 78 * 78, "-", 6075, "=", 9)
    print("EXACT PASS: outer-or-box rows", rows)


if __name__ == "__main__":
    main()
