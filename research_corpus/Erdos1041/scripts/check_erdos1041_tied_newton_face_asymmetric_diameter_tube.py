#!/usr/bin/env python3
"""Exact regression for the all-degree asymmetric diameter tube."""

from fractions import Fraction


def main() -> int:
    degree = 6
    radius = Fraction(2)
    b = Fraction(-1)
    coeff = {1: Fraction(1, 100), 3: Fraction(1, 100), 5: Fraction(1, 100)}

    inner = sum(abs(c) * radius**j for j, c in coeff.items())
    outer = sum(abs(c) / radius ** (degree - j) for j, c in coeff.items())
    assert inner == Fraction(21, 50)
    assert outer == Fraction(21, 3200)
    assert inner < -b
    assert outer <= 1

    def polynomial(x: Fraction) -> Fraction:
        return -(x**degree) + b + sum(c * x**j for j, c in coeff.items())

    # Exact rational regression on both sides of the cutoff and far into the tails.
    samples = [Fraction(k, 8) for k in range(-160, 161)]
    assert all(polynomial(x) < 0 for x in samples)
    assert all(polynomial(x) <= b + inner for x in samples)

    for x in samples:
        perturbation = sum(c * x**j for j, c in coeff.items())
        if abs(x) <= radius:
            assert abs(perturbation) <= inner
            assert b + inner < 0
        else:
            assert abs(perturbation) <= outer * abs(x) ** degree
            assert outer * abs(x) ** degree <= abs(x) ** degree

    print("PASS: all-degree asymmetric diameter tube")
    print("  exact witness P=-z^6-1+(z+z^3+z^5)/100")
    print(f"  inner budget A_2={inner}; outer budget B_2={outer}")
    print(f"  uniform real-axis upper margin: P(x)<={b + inner}<0")
    print("  the complete real-axis carrier survives three odd modes")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
