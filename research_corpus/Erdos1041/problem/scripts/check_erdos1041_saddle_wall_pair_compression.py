#!/usr/bin/env python3
"""Exact scalar replay for SaddleWallPairCompression.md.

All theorem checks use fractions. The numerical terminal-family figures in
the owner note are evidence from the existing merge-tree instrument and are
not replayed here.
"""

from __future__ import annotations

from fractions import Fraction
import random


def check_row(a: Fraction, b: Fraction, x: Fraction) -> None:
    lower = a + b
    side_a = x + a
    side_b = x + b
    total = lower + x
    short = min(side_a, side_b)

    short_slack = total**2 / 2 - lower * short
    claimed_slack = (x**2 + lower * abs(a - b)) / 2
    assert short_slack == claimed_slack
    assert short_slack >= 0

    # Squared form of lower*sqrt(side_a*side_b) <= total^2/2.
    assert lower**2 * side_a * side_b <= total**4 / 4
    assert (x + lower / 2) ** 2 - side_a * side_b == (a - b) ** 2 / 4


def main() -> None:
    rng = random.Random(20260830)
    rows = 0
    for _ in range(500):
        a = Fraction(rng.randint(1, 200), rng.randint(1, 200))
        b = Fraction(rng.randint(1, 200), rng.randint(1, 200))
        x = Fraction(rng.randint(1, 200), rng.randint(1, 200))
        check_row(a, b, x)
        rows += 1

    # Abstract equality model and strictness for every genuine X>0 wall.
    check_row(Fraction(3, 7), Fraction(3, 7), Fraction(0))
    equality_total = Fraction(6, 7)
    equality_product = Fraction(6, 7) * Fraction(3, 7)
    assert equality_product == equality_total**2 / 2

    # Exact normalized consumer. Take beta=r^n and gamma=s^n, so
    # (beta*gamma)^(1/n)=r*s. The squared threshold T^2<=8rs implies
    # q_low*q_high<=1 without evaluating radicals.
    normalized_rows = 0
    for _ in range(500):
        a = Fraction(rng.randint(1, 30), 100)
        b = Fraction(rng.randint(1, 30), 100)
        x = Fraction(rng.randint(1, 30), 100)
        r = Fraction(rng.randint(60, 100), 100)
        s = Fraction(rng.randint(60, 100), 100)
        total = a + b + x
        if total**2 > 8 * r * s:
            continue
        normalized_product = (a + b) * (x + min(a, b)) / (4 * r * s)
        assert normalized_product <= 1
        normalized_rows += 1

    assert normalized_rows >= 400
    print("SADDLE WALL PAIR COMPRESSION: PASS")
    print(f"exact positive rows={rows}")
    print("abstract equality model: A=B=3/7, X=0")
    print(f"exact normalized certificate rows={normalized_rows}")


if __name__ == "__main__":
    main()
