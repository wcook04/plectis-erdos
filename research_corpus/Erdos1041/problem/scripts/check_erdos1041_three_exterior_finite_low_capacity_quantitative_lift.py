#!/usr/bin/env python3
"""Exact arithmetic for the quantitative finite lift off the equality collar."""

from fractions import Fraction as F

from sympy import expand, symbols


RHO = F(99_999_999, 100_000_000)
EPSILON_MAX = F(1, 1_000_000)
E_MAX = EPSILON_MAX**2
Q_CUT = F(1, 4)


def regular_lower(n: int):
    if n == 5:
        tbox = F(7368, 10000), F(7369, 10000)
    else:
        tbox = F(7937, 10000), F(7938, 10000)
    d = n - 3
    assert tbox[0] ** 3 < F(d, n) < tbox[1] ** 3
    return min((tt**d * (1 - tt**3)) ** 2 for tt in tbox)


def symbolic_scaled_factor_check() -> None:
    epsilon, reciprocal_q, radius, cosine = symbols("epsilon reciprocal_q radius cosine")
    physical_q = epsilon / reciprocal_q
    physical_radius = epsilon * radius
    numerator = (
        physical_q**2
        - 2 * physical_q * physical_radius * cosine
        + physical_radius**2
    )
    denominator = (
        1
        - 2 * physical_q * physical_radius * cosine
        + physical_q**2 * physical_radius**2
    )
    normalized_numerator = 1 - 2 * reciprocal_q * radius * cosine + reciprocal_q**2 * radius**2
    cleared_denominator = (
        reciprocal_q**2
        - 2 * epsilon**2 * reciprocal_q * radius * cosine
        + epsilon**4 * radius**2
    )
    assert expand(numerator - epsilon**2 * normalized_numerator / reciprocal_q**2) == 0
    assert expand(denominator - cleared_denominator / reciprocal_q**2) == 0


def check_degree(n: int, radial_upper: F) -> None:
    d = n - 3
    # On q>=1/4, each finite denominator costs at most this common factor.
    x = E_MAX * radial_upper / Q_CUT
    assert 0 < x < 1
    # Bernoulli gives (1-x)^6 >= 1-6x, and this is already stronger than
    # the uniform 10^-8 homogeneous margin certified by the two atlas replays.
    assert 1 - 6 * x > RHO
    assert (1 - x) ** 6 > RHO

    # On epsilon<=q<=1/4, use the attachment-independent tail estimate
    # q^d(1+qT)^3/(1-epsilon T)^3.  Compare its square with C_n^2.
    tail_square = (
        Q_CUT ** (2 * d)
        * (1 + Q_CUT * radial_upper) ** 6
        / (1 - EPSILON_MAX * radial_upper) ** 6
    )
    assert tail_square < regular_lower(n)
    print(
        f"n={n}: main perturbation={(1-x) ** 6 - RHO} "
        f"tail margin={regular_lower(n)-tail_square}"
    )


def main() -> None:
    symbolic_scaled_factor_check()
    check_degree(5, F(29, 25))
    check_degree(6, F(11, 10))
    print("PASS exact finite low-capacity lift outside the equality collar")


if __name__ == "__main__":
    main()
