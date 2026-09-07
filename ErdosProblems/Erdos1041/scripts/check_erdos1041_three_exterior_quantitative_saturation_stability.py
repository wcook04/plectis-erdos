#!/usr/bin/env python3
"""Exact replay for the three-exterior quantitative saturation collar."""

from fractions import Fraction as Q


ETA = Q(1, 10**16)


def audit_degree(n: int) -> dict[str, Q]:
    d = n - 3
    p0 = Q(d, n + 3)

    # Symbolic cross-multiplication of
    # (1-p)/(1+p)-3/n = (n+3)(p0-p)/(n(1+p)).
    # Coefficients of 1 and p after clearing n(1+p).
    lhs_coeff = (Q(n - 3), Q(-(n + 3)))
    rhs_coeff = (Q(n + 3) * p0, Q(-(n + 3)))
    assert lhs_coeff == rhs_coeff

    half = Q(n + 1, 2)
    M = Q(3) * (Q(16) * half**6 + Q(4) * half**4)
    D = Q(n + 3, n) * ETA
    lam = Q(d + 1, 3)
    H2 = Q(2) * M * n * n * lam**4 * D

    if n == 5:
        assert M == 35964
        Hup = Q(1, 50000)
        r2low = Q(39, 100)
        root_bound = Q(16, 625)
        # ((1/4)^(2/3))^3=(1/4)^2 > (39/100)^3.
        assert p0**2 > r2low**3
    elif n == 6:
        assert M == Q(180075, 2)
        Hup = Q(1, 16000)
        r2low = Q(1201, 2500)
        root_bound = Q(3, 40)
        # ((1/3)^(2/3))^3=(1/3)^2 > (1201/2500)^3.
        assert p0**2 > r2low**3
    else:
        raise ValueError(n)

    assert H2 < Hup**2

    # cot(pi/n)<2 was the only trigonometric relaxation in the rational
    # corollary, hence 2*cot(pi/n)*D < 4D.
    Egap = Q(2 * n) * (Hup + Q(4) * D)
    Ezeta = Q(2) * Egap
    Fup = Q(24) * D + (Q(12) + Q(36, n)) * Ezeta
    threshold = Q(d, 4 * n)
    assert Fup < threshold

    # Rouché radius, using the certified rational lower bound for r0^2.
    sup_radius = Q(2 * n) * Fup / (Q(n + 3) * r2low)
    assert sup_radius < root_bound
    # r0<3/4, so the certified Rouché disks remain inside |z|<1.
    assert p0 < Q(3, 4) ** 3
    assert root_bound < Q(1, 4)

    return {
        "p0": p0,
        "M": M,
        "D_upper": D,
        "H2_upper": H2,
        "H_upper": Hup,
        "gap_upper": Egap,
        "fibre_chord_upper": Ezeta,
        "F_upper": Fup,
        "rouche_threshold": threshold,
        "zero_radius_upper": sup_radius,
        "claimed_zero_radius": root_bound,
    }


def main() -> None:
    print("three-exterior quantitative saturation stability: exact replay")
    for n in (5, 6):
        row = audit_degree(n)
        print(f"n={n}")
        for key, value in row.items():
            print(f"  {key} = {value} (~{float(value):.12g})")
    print("all exact rational checks passed")


if __name__ == "__main__":
    main()
