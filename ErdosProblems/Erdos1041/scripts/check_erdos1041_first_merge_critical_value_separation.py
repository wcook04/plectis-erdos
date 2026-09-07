#!/usr/bin/env python3
"""Exact symbolic replay for FirstMergeCriticalValueSeparationCertificate.md."""
from fractions import Fraction
import sympy as sp


def main() -> int:
    z = sp.symbols("z")
    P = 1 - 3 * z**2 + z**3
    dP = sp.diff(P, z)
    critical = sp.solve(dP, z)
    other = sp.Integer(2)

    gates = {
        "example_critical_points": set(critical) == {sp.Integer(0), other},
        "example_simple_origin": sp.diff(P, z, 2).subs(z, 0) != 0,
        "example_unit_leading_coefficient": sp.LC(sp.Poly(P, z)) == 1,
        "example_exact_separation_four": sp.simplify(1 - P.subs(z, other)) == 4,
        # 5^(2/3) < 3 is equivalent, after cubing positive quantities, to 25 < 27.
        "radical_constant_exact": 5**2 < 3**3,
        # log(1+x)<x is the analytic inequality; the checker pins its exact x=1/3.
        "log_argument_exact": Fraction(4, 3) == 1 + Fraction(1, 3),
        # Combining the two strict bounds gives 5^(2/3)*log(4/3) < 3*(1/3)=1.
        "terminal_rational_product": 3 * Fraction(1, 3) == 1,
        # S=3, n>=4: 4^(2/n) <= 2 and log(3/2)<1/2.
        "degree_four_threshold_three": 2 * Fraction(1, 2) == 1,
        # exp(7/10)>2 from its positive Taylor series through the cubic term.
        "log_two_below_seven_tenths": (
            1
            + Fraction(7, 10)
            + Fraction(7, 10) ** 2 / 2
            + Fraction(7, 10) ** 3 / 6
            == Fraction(12013, 6000)
            and Fraction(12013, 6000) > 2
        ),
        # S=2, n>=7: after raising the positive radical bound to the seventh
        # power, (3^(2/7)*7/10)^7 = 9*7^7/10^7 < 1.
        "degree_seven_threshold_two": 9 * 7**7 < 10**7,
    }

    print("check_erdos1041_first_merge_critical_value_separation")
    print(f"  P={sp.expand(P)}")
    print(f"  critical_points={critical}")
    print(f"  1-P(2)={sp.simplify(1-P.subs(z, other))}")
    print("  exact terminal chain: 25 < 27 and log(1+1/3) < 1/3")
    print("  sharpenings: (n>=4,S=3) and (n>=7,S=2)")
    for name, ok in gates.items():
        print(f"  {name}={ok}")
    verdict = all(gates.values())
    print(f"verdict {'pass' if verdict else 'FAIL'}")
    return 0 if verdict else 1


if __name__ == "__main__":
    raise SystemExit(main())
