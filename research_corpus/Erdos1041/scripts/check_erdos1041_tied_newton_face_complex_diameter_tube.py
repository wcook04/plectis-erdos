#!/usr/bin/env python3
"""Exact Gaussian-rational regression for the complex diameter tube."""

from fractions import Fraction as F


def add(z: tuple[F, F], w: tuple[F, F]) -> tuple[F, F]:
    return z[0] + w[0], z[1] + w[1]


def mul(z: tuple[F, F], w: tuple[F, F]) -> tuple[F, F]:
    return z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0]


def power(z: tuple[F, F], n: int) -> tuple[F, F]:
    out = (F(1), F(0))
    for _ in range(n):
        out = mul(out, z)
    return out


def main() -> int:
    degree = 4
    u = (F(0), F(1))
    radius = F(2)
    b = (F(-1), F(0))
    c = (F(1, 100), F(1, 100))
    majorant = F(1, 50)

    assert power(u, degree) == (F(1), F(0))
    norm_sq = c[0] ** 2 + c[1] ** 2
    assert norm_sq == F(1, 5000) < majorant**2

    inner = majorant * (radius + radius**3)
    outer = majorant * (F(1, radius**3) + F(1, radius))
    assert inner == F(1, 5)
    assert outer == F(1, 80)
    assert b[0] + inner == F(-4, 5) < 0
    assert outer <= 1

    def q(z: tuple[F, F]) -> tuple[F, F]:
        lower = add(mul(c, z), mul(c, power(z, 3)))
        lead = power(z, 4)
        return add((-lead[0], -lead[1]), add(b, lower))

    for k in range(-320, 321):
        t = F(k, 16)
        z = (F(0), t)
        value = q(z)
        assert value[0] <= b[0] + inner
        assert value[0] < 0

    print("PASS: all-degree complex rotated-diameter tube")
    print("  Q=-z^4-1+(1+i)(z+z^3)/100 on the imaginary diameter")
    print(f"  coefficient norm-square={norm_sq} < (1/50)^2")
    print(f"  A_2={inner}, B_2={outer}, uniform margin={-(b[0] + inner)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
