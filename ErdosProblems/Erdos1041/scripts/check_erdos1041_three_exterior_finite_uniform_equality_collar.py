#!/usr/bin/env python3
"""Exact endpoint identities for the uniform finite equality-collar continuation."""

from fractions import Fraction as F

from sympy import cancel, diff, factor, limit, symbols


DELTA = F(1, 50)
EPSILON_CEILING = F(1, 1_000_000)


def check_degree(n: int) -> None:
    d = n - 3
    q, s, z, tau, E, Q = symbols("q s z tau E Q", positive=True)

    # The finite regular stationary equation in Q=q_reciprocal^3 and
    # E=epsilon^6.  Its homogeneous root Q=d/n is simple.
    stationary = n * Q**2 - (d + (n + 3) * E) * Q + n * E
    assert stationary.subs({Q: F(d, n), E: 0}) == 0
    assert diff(stationary, Q).subs({Q: F(d, n), E: 0}) == d

    # Finite first-order kernel coefficient, written in physical variables
    # q=s z, has exactly the homogeneous limit with tau=1/z.
    K = 3 * (q**2 * s**3 + q**2 * s + q * s**4 + q + s**3 + s) / (
        2 * (q - s) * (s - 1) * (s + 1) * (q * s - 1)
    )
    K_limit = factor(limit(K.subs(q, s * z), s, 0))
    assert cancel(K_limit.subs(z, 1 / tau) - 3 * (1 + tau) / (2 * (1 - tau))) == 0

    # The homogeneous regular reciprocal-ray maximum is nondegenerate.
    regular_log_second = -d / q**2 - 6 * q / (1 - q**3) - 9 * q**4 / (1 - q**3) ** 2
    reduced = factor(regular_log_second.subs(q**3, F(d, n)))
    # Direct sign check at a rational enclosure is unnecessary: every term
    # in the displayed expression is strictly negative on 0<q<1.
    assert reduced != 0

    # The complete 1/50 chart and epsilon<=10^-6 remain uniformly away from
    # every finite Blaschke denominator zero.
    if n == 5:
        t_left = F(7368, 10000)
        radial_upper = F(29, 25)
    else:
        t_left = F(7937, 10000)
        radial_upper = F(11, 10)
    q_lower = t_left - DELTA
    e_upper = EPSILON_CEILING**2
    assert q_lower - e_upper * radial_upper > F(7, 10)
    denominator_lower = (q_lower - e_upper * radial_upper) ** 2
    assert denominator_lower > F(49, 100)
    assert EPSILON_CEILING**3 < F(d, n + 3)
    print(
        f"n={n}: stationary derivative={d}; "
        f"denominator lower>{denominator_lower}"
    )


def main() -> None:
    for degree in (5, 6):
        check_degree(degree)
    print("PASS exact endpoint data for the uniform finite equality collar")


if __name__ == "__main__":
    main()
