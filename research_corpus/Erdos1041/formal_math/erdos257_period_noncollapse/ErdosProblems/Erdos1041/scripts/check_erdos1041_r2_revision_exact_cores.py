#!/usr/bin/env python3
"""Exact rational cores for the 2026-09-06/07 Type B revision returns on Erdős #1041.

Independent of Type B's pasted programs. Every assertion is Fraction arithmetic
or an exact integer comparison. No floating-point numbers are used.

This does not replay the 13/25 dual table (that is
check_erdos1041_angular_budget_closure.py) and does not prove Rouché, winding,
or Riemann–Hurwitz. Those remain ordinary arguments consuming these cores.

R3 gates (quartic two-root-window witness, C_* < 573/100, cluster L^2 < 4,
S_∞ algebraic rearrangement) live in the same file so later agents edit here
rather than retyping probes.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from math import factorial


def exp_lower(x: Q, degree: int) -> Q:
    return sum((x**k / factorial(k) for k in range(degree + 1)), Q(0))


def exp_upper(x: Q, degree: int) -> Q:
    """Positive-term exponential with geometric tail, for 0 < x < degree+2."""
    partial = sum((x**k / factorial(k) for k in range(degree + 1)), Q(0))
    return partial + x ** (degree + 1) / factorial(degree + 1) / (1 - x / Q(degree + 2))


def atanh_log_bounds(q: Q, terms: int = 24) -> tuple[Q, Q]:
    """Positive atanh series for log q = 2 artanh((q-1)/(q+1)), q > 1."""
    x = (q - 1) / (q + 1)
    if not (0 < x < 1):
        raise ValueError(f"expected 0 < (q-1)/(q+1) < 1, got q={q}")
    lo = 2 * sum((x ** (2 * j + 1) / Q(2 * j + 1) for j in range(terms)), Q(0))
    hi = lo + 2 * x ** (2 * terms + 1) / (Q(2 * terms + 1) * (1 - x * x))
    return lo, hi


def atan_bounds(x: Q, terms: int = 12) -> tuple[Q, Q]:
    """Alternating arctan series with the unused next term as remainder bound."""
    s = sum(((-1) ** j * x ** (2 * j + 1) / Q(2 * j + 1) for j in range(terms)), Q(0))
    nxt = ((-1) ** terms) * x ** (2 * terms + 1) / Q(2 * terms + 1)
    return (s, s + nxt) if nxt >= 0 else (s + nxt, s)


def pi_bounds(terms: int = 12) -> tuple[Q, Q]:
    """Machin: π = 16 arctan(1/5) − 4 arctan(1/239)."""
    a, b = atan_bounds(Q(1, 5), terms)
    c, d = atan_bounds(Q(1, 239), terms)
    return 16 * a - 4 * d, 16 * b - 4 * c


def poly_g(z: Q) -> Q:
    return z**4 - Q(4, 15) * z**3 - Q(4, 25) * z**2 + Q(1, 750)


def poly_gp(z: Q) -> Q:
    return 4 * z**3 - Q(4, 5) * z**2 - Q(8, 25) * z


def r3_gates() -> dict[str, bool]:
    gates: dict[str, bool] = {}

    # Tied-minimum quartic g(z) = z^4 − (4/15) z^3 − (4/25) z^2 + 1/750.
    crits = (Q(-1, 5), Q(0), Q(2, 5))
    gates["quartic_gp_factor_identity"] = all(poly_gp(z) == 0 for z in crits)
    # 4z(z + 1/5)(z − 2/5) expands to 4z^3 − (4/5)z^2 − (8/25)z.
    z = Q(3, 7)
    expanded = 4 * z * (z + Q(1, 5)) * (z - Q(2, 5))
    gates["quartic_gp_factorisation"] = expanded == poly_gp(z)
    gates["quartic_g_at_minus_one_fifth"] = poly_g(Q(-1, 5)) == Q(-1, 750)
    gates["quartic_g_at_zero"] = poly_g(Q(0)) == Q(1, 750)
    gates["quartic_g_at_two_fifths"] = poly_g(Q(2, 5)) == Q(-59, 3750)
    gates["quartic_tied_minima"] = abs(poly_g(Q(-1, 5))) == abs(poly_g(Q(0)))
    gates["quartic_third_modulus_ratio"] = abs(poly_g(Q(2, 5))) / abs(poly_g(Q(0))) == Q(59, 5)
    # Rouché on |z|=1: lower-order modulus sum < 1 = |z^4|.
    lower = Q(4, 15) + Q(4, 25) + Q(1, 750)
    gates["quartic_rouche_margin"] = lower == Q(107, 250) and lower < 1
    # Four real roots by sign changes on the four monotonic intervals, all inside (-1,1).
    gates["quartic_sign_left"] = poly_g(Q(-1)) > 0 and poly_g(Q(-1, 5)) < 0
    gates["quartic_sign_middle_left"] = poly_g(Q(-1, 5)) < 0 and poly_g(Q(0)) > 0
    gates["quartic_sign_middle_right"] = poly_g(Q(0)) > 0 and poly_g(Q(2, 5)) < 0
    gates["quartic_sign_right"] = poly_g(Q(2, 5)) < 0 and poly_g(Q(1)) > 0
    # Distinct real critical points, all simple (g''(-1/5), g''(0), g''(2/5) ≠ 0).
    gpp = lambda z: 12 * z**2 - Q(8, 5) * z - Q(8, 25)
    gates["quartic_critical_points_simple"] = all(gpp(z) != 0 for z in crits)

    # C_*^2 = sqrt(2) * (2 + log 2 + 2π + π^2 / log 2) < (573/100)^2.
    # log 2 = 2 artanh(1/3).
    log2_lo, log2_hi = atanh_log_bounds(Q(2), terms=20)
    pi_lo, pi_hi = pi_bounds(terms=16)
    sqrt2_hi = Q(1414213563, 10**9)
    gates["sqrt2_upper_sq"] = sqrt2_hi**2 > 2
    b_hi = 2 + log2_hi + 2 * pi_hi + pi_hi**2 / log2_lo
    c_sq_hi = sqrt2_hi * b_hi
    target = Q(573, 100) ** 2
    gates["c_star_sq_lt_573_100_sq"] = c_sq_hi < target
    gates["c_star_margin_positive"] = target - c_sq_hi > Q(1, 1000)

    # Occupancy L^2 bound: (2/15)[2 + (sqrt(log(25/13)) + π/sqrt(log(5/3)))^2] < 4
    # using sqrt(log(25/13)) < 81/100, sqrt(log(5/3)) > 71/100, π < 22/7.
    _, log_25_13_hi = atanh_log_bounds(Q(25, 13), terms=24)
    log_5_3_lo, _ = atanh_log_bounds(Q(5, 3), terms=24)
    gates["log_25_13_lt_81_100_sq"] = log_25_13_hi < Q(81, 100) ** 2
    gates["log_5_3_gt_71_100_sq"] = log_5_3_lo > Q(71, 100) ** 2
    gates["pi_lt_22_7"] = pi_hi < Q(22, 7)
    cluster_sq = Q(2, 15) * (2 + (Q(81, 100) + Q(22, 7) / Q(71, 100)) ** 2)
    gates["cluster_length_sq_lt_four"] = cluster_sq < 4

    # 13/25 exponential endpoint, independent of the dual table.
    x_cert = Q(635762889599, 10**12)
    gates["thirteen_twentyfifths_times_exp_lt_one"] = Q(13, 25) * exp_upper(x_cert, 24) < 1

    # S_∞ algebraic rearrangement: log((S^2+S+p)/(S^2-S+p))=2
    # iff S^2 − ((e^2+1)/(e^2-1)) S + p = 0, and (e^2+1)/(e^2-1) = coth 1.
    s, p, ratio = Q(3), Q(1, 5), Q(9)
    left = (s**2 + s + p) - ratio * (s**2 - s + p)
    right = (ratio - 1) * (s**2 - ((ratio + 1) / (ratio - 1)) * s + p)
    gates["s_infty_log_quadratic_identity"] = left == -right
    # Admissibility: at S = b = max(a,1-a), S^2 − A S + a(1-a) = b(1−A).
    a = Q(2, 3)
    b = max(a, 1 - a)
    p_a = a * (1 - a)
    a_dummy = Q(3)
    quad_at_b = b**2 - a_dummy * b + p_a
    gates["s_infty_admissible_at_dummy_coth"] = quad_at_b == b * (1 - a_dummy) and quad_at_b < 0

    return gates


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--quick",
        action="store_true",
        help="Same Fraction gates; reserved so later agents can add a slower mode.",
    )
    parser.parse_args()

    gates: dict[str, bool] = {}

    # R2.1 SEP-OR cubic f = z^3 + (3/100)z - 3/4
    gates["sep_or_rouche_margin"] = Q(39, 50) < 1
    mu2 = Q(9, 16) + Q(1, 250000)
    gates["sep_or_mu_gt_thirteen_twentyfifths"] = mu2 > Q(13, 25) ** 2
    gates["sep_or_mu_gt_three_fourths"] = mu2 > Q(3, 4) ** 2
    # μ > 3/4 implies 1/(250μ) < 4/750 = 2/375
    gates["sep_or_reciprocal_from_three_fourths"] = Q(1, 250) / Q(3, 4) == Q(2, 375)
    gates["sep_or_separation_lt_two"] = Q(2, 375) < 2
    # |1 - v_-/v_+|^2 = 1/(250^2 μ^2); compare with 4
    gates["sep_or_squared_ratio_lt_four"] = Q(1, 250) ** 2 < 4 * mu2

    # R2.3 one-lobe p = z^8 - (3/2)z
    gates["one_lobe_separating_circle"] = Q(6, 5) - Q(4, 5) ** 8 > 1
    gates["one_lobe_inner_disc"] = Q(15, 16) + Q(5, 8) ** 8 < 1
    gates["one_lobe_inner_eighth_power"] = Q(5, 8) ** 8 < Q(1, 16)
    gates["one_lobe_critical_value_outside"] = 3 * 21**7 > 16**8
    # β ≤ π/2 (1+√2) < 5π/4  iff  1+√2 < 5/2  iff  √2 < 3/2  iff  2 < 9/4.
    # The comparison 1 + 3/2 = 5/2 is the ceiling of the secant bound; the
    # strict inequality is 2 < 9/4.
    gates["one_lobe_sqrt2_lt_three_halves"] = Q(2) < Q(9, 4)

    # R2.4 first-merge arity does not force a capacity gap
    gates["arity_rouche"] = Q(3, 400) + Q(3, 32) < 1
    gates["arity_unique_first_modulus"] = Q(187, 2000) < Q(47, 500)
    gates["arity_second_inside_double"] = Q(47, 500) < 2 * Q(187, 2000)
    gates["arity_mu_lt_half"] = Q(187, 2000) < Q(1, 2)

    # Paper 71/10 and Type B's alternate rationalization both close
    paper_cf = Q(66517563, 9392500)
    typeb_cf = Q(465613191, 65747500)
    gates["paper_71_10"] = paper_cf < Q(71, 10)
    gates["typeb_71_10"] = typeb_cf < Q(71, 10)
    unit_cf = Q(15668813, 2755116)
    gates["unit_5_7"] = unit_cf < Q(57, 10)

    # Type B S=3/2 cube; DiskFamily 4/3 is strictly smaller
    gates["typeb_s_three_halves_cube"] = Q(3, 2) * Q(5, 6) ** 3 == Q(125, 144)
    gates["typeb_s_three_halves_lt_one"] = Q(125, 144) < 1
    gates["exp_five_thirds_gt_five"] = exp_lower(Q(5, 3), 4) == Q(10009, 1944) and Q(
        10009, 1944
    ) > 5
    gates["disk_family_four_thirds_beats_three_halves"] = Q(4, 3) < Q(3, 2)

    # artanh vs log identity at S=3/2: log(S/(S-1)) = log 3, artanh(1/S)=(log 5)/2
    # log 3 - (log 5)/2 = (1/2) log(9/5) > 0 because 9/5 > 1
    gates["artanh_strictly_below_log_at_three_halves"] = Q(9, 5) > 1

    # 13/25 exponential closure used by the angular-budget note
    X = Q(635762889599, 10**12)
    gates["thirteen_twentyfifths_X_times_e_seed"] = X < Q(636, 1000)

    gates.update(r3_gates())

    failed = [name for name, ok in gates.items() if not ok]
    print("check_erdos1041_r2_revision_exact_cores")
    for name, ok in gates.items():
        print(f"  {name}={ok}")
    print(f"verdict {'pass' if not failed else 'FAIL'}")
    if failed:
        print("failed:", ", ".join(failed))
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
