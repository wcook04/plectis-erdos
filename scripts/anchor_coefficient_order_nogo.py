#!/usr/bin/env python3
"""Exact audit of the static anchor-coefficient order counterfamily."""

from fractions import Fraction


ANCHOR = (1 << 25) - 1


def w(n: int) -> Fraction:
    return Fraction(1, (1 << n) - 1)


def binary_digits(x: Fraction, count: int) -> list[int]:
    assert 0 <= x < 1
    out: list[int] = []
    for _ in range(count):
        x *= 2
        bit = int(x >= 1)
        out.append(bit)
        x -= bit
    return out


def scalar_front(x: Fraction) -> int:
    n = 1
    while w(n) > x:
        n += 1
    return n


def audit_height(height: int) -> None:
    assert height > 26
    x = Fraction(2, (1 << height) - 1)
    coefficient = ((1 << height) - 1) * x
    anchor_word = ANCHOR * coefficient
    c = ANCHOR * x

    assert coefficient == 2
    assert anchor_word == 2 * ANCHOR
    assert scalar_front(x) == height
    assert x == 2 * w(height)

    digits = binary_digits(c, height + 1)
    first = height - 25
    assert digits[: first - 1] == [0] * (first - 1)
    assert digits[first - 1 : first + 24] == [1] * 25
    assert digits[first + 24] == 0
    assert first + 25 == scalar_front(x)


def main() -> None:
    for height in (27, 100, 200, 500):
        audit_height(height)
    print("static anchor-coefficient order no-go: PASS")
    print("exact infinite family: X_L = 2/(2^L-1), all L > 26")
    print("fatal equality and 25-leading-one periodic word coexist")
    print("not claimed: reachability from the 1/465 greedy orbit")


if __name__ == "__main__":
    main()
