#!/usr/bin/env python3
"""Exact replay for ThreeExteriorClosestRayLowCapacityNoGo.md."""

from fractions import Fraction as F


U = [
    (F(1), F(0)),
    (F(21, 221), F(-220, 221)),
    (F(-91, 109), F(60, 109)),
]
B = [F(1), F(24, 25), F(51, 50)]
P = B[0] * B[1] * B[2]
Y = F(4, 3)
EPS0 = F(1, 600)
J = 2


def dot(u: tuple[F, F], v: tuple[F, F]) -> F:
    return u[0] * v[0] + u[1] * v[1]


def distance_product_sq() -> F:
    out = F(1)
    for bk, uk in zip(B, U):
        out *= Y * Y + bk * bk - 2 * Y * bk * dot(U[J], uk)
    return out


def symmetric_limiting_max_sixth(n: int) -> F:
    d = n - 3
    # C_n^6 for C_n=(3/d)(d/n)^(n/3) P^(-d/3).
    return F(3, d) ** 6 * F(d, n) ** (2 * n) * P ** (-2 * d)


def audit_degree(n: int, prod_sq: F) -> tuple[F, F, F]:
    actual_sq = prod_sq / Y ** (2 * n)
    denominator = F(1)
    for bk in B:
        denominator *= 1 + EPS0 * EPS0 * Y * bk

    # The sixth power of A_n/D(EPS0).
    lower_sixth = (actual_sq / denominator**2) ** 3
    p0 = EPS0**3 * P
    # The sixth power of C_n/(1-p0).
    upper_sixth = symmetric_limiting_max_sixth(n) / (1 - p0) ** 6
    assert lower_sixth > upper_sixth
    return lower_sixth, upper_sixth, lower_sixth / upper_sixth


def main() -> None:
    for u in U:
        assert dot(u, u) == 1
    assert P == F(612, 625)
    assert B[J] == max(B)
    assert Y > B[J]  # q=epsilon*y lies beyond the selected disk zero.

    # Uniform boundary-speed majorant at epsilon=1/600.
    speed_ceiling = sum(
        ((1 + EPS0 * bk) / (1 - EPS0 * bk) for bk in B),
        F(0),
    )
    assert speed_ceiling < 5

    prod_sq = distance_product_sq()
    assert prod_sq == F(1581501847748564, 747709386328125)

    for n in (5, 6):
        lower, upper, ratio = audit_degree(n, prod_sq)
        print(
            f"n={n} speed_ceiling={float(speed_ceiling):.12f} "
            f"sixth_power_ratio={float(ratio):.12f} "
            f"margin_numerator={(lower-upper).numerator}"
        )

    print("PASS exact low-capacity closest-root selector no-go")


if __name__ == "__main__":
    main()
