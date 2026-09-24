#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Certify the maximisers of C0/C1 in the finite box of parameter directions.

The box is the set of integer tuples (alpha0, alpha1, alpha2; beta) with every
entry between 1 and 30, gcd 1, alpha1 <= alpha2 and
alpha1 + alpha2 < beta <= alpha0 + alpha2 (Zudilin's parameter inequalities
with a bound imposed for enumeration).  For each tuple the long Erdos 1049
paper (Section 'Complements and further questions') defines

    c00 = a0+a1+a2-beta, c01 = a0, c11 = a1, c21 = a2, c12 = beta-a1,
    c22 = beta-a2, m = max(c..),
    omega(u) = max(0, [c21 u]+[c22 u]-[c11 u]-[c12 u], [c01 u]+[c21 u]-[c00 u]-[c12 u]),
    C1 = (a0+a1+a2) beta - (a1^2+a2^2+beta^2)/2,
    C0 = a1^2/2 + a0 a1 + (beta-a2)(a2-a1) - (3/pi^2)(m^2 - J),
    J  = integral over [0,1] of omega d(-psi_1),

where [x] is the floor.  Every coefficient c.. is at most 30, so omega is
constant on each of the 278 half-open cells cut out of [0,1) by the fractions
j/c with 1 <= c <= 30, and J is the sum over cells [u,v) with omega = w of
w (psi_1(u) - psi_1(v)).

Two implementations run on every tuple.

  A. 256 summands of (k+u)^-2 - (k+v)^-2 per cell summed exactly, the tail
     enclosed between (M+u)^-1 - (M+v)^-1 and that plus (M+u)^-2 - (M+v)^-2,
     cell bounds rounded outward to multiples of 10^-40, pi from Machin's
     formula, weights evaluated at left endpoints; enumeration by
     alpha1, alpha2, beta, alpha0 increasing.
  B. 512 summands per cell, each rounded down to a multiple of 10^-45 (so the
     partial sum lies between the rounded sum and that plus 512 * 10^-45), the
     same integral tail bounds rounded outward to that grid, weights evaluated
     at cell midpoints, the final products in exact fractions; enumeration by
     alpha0, beta, alpha2, alpha1 decreasing.

Each implementation encloses C0/C1 for every tuple and checks that exactly
two tuples, (14,12,14;27) and (15,12,13;26), have enclosures that are not
strictly below the largest lower endpoint, and that every other upper
endpoint is strictly below both of their lower endpoints.  The exact equality
of the two maximal values is the analytic argument printed in the paper; this
program checks its finite inputs (the floor identity on every cell, m = 15,
C1 = 1091/2, quadratic parts 266 and 265).

The result proves optimality only inside this finite box.  It gives no bound
for a direction outside the box, and the irrationality theorem does not use
it.  No floating-point arithmetic and no Lean kernel are involved.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from fractions import Fraction
from math import gcd
from pathlib import Path

SCHEMA = "erdos1049-public-computation/1"
PROGRAM = "parameter_box.py"
BOUND = 30
MAXIMISERS = [(14, 12, 14, 27), (15, 12, 13, 26)]
PRINTED_MAXIMISER_LOWER = "0.40568302137302"
PRINTED_MAXIMISER_UPPER = "0.40568302139506"
PRINTED_OTHERS_UPPER = "0.40563943278333"


def box_tuples_increasing() -> list[tuple[int, int, int, int]]:
    rows = []
    for a1 in range(1, BOUND + 1):
        for a2 in range(a1, BOUND + 1):
            for beta in range(a1 + a2 + 1, BOUND + 1):
                for a0 in range(beta - a2, BOUND + 1):
                    if gcd(gcd(a0, a1), gcd(a2, beta)) == 1:
                        rows.append((a0, a1, a2, beta))
    return rows


def box_tuples_decreasing() -> list[tuple[int, int, int, int]]:
    rows = []
    for a0 in range(BOUND, 0, -1):
        for beta in range(BOUND, 0, -1):
            for a2 in range(BOUND, 0, -1):
                for a1 in range(a2, 0, -1):
                    if not (a1 + a2 < beta <= a0 + a2):
                        continue
                    if gcd(gcd(a0, a1), gcd(a2, beta)) == 1:
                        rows.append((a0, a1, a2, beta))
    return rows


def coefficients(t: tuple[int, int, int, int]) -> tuple[int, int, int, int, int, int]:
    a0, a1, a2, beta = t
    return a0 + a1 + a2 - beta, a0, a1, a2, beta - a1, beta - a2


def omega_c(c: tuple[int, int, int, int, int, int], num: int, den: int) -> int:
    """omega at the point num/den, for the coefficients c = (c00, c01, c11, c21, c12, c22)."""

    c00, c01, c11, c21, c12, c22 = c
    f00, f01, f11 = c00 * num // den, c01 * num // den, c11 * num // den
    f21, f12, f22 = c21 * num // den, c12 * num // den, c22 * num // den
    return max(0, f21 + f22 - f11 - f12, f01 + f21 - f00 - f12)


def omega(t: tuple[int, int, int, int], x: Fraction) -> int:
    return omega_c(coefficients(t), x.numerator, x.denominator)


def c1_value(t: tuple[int, int, int, int]) -> Fraction:
    a0, a1, a2, beta = t
    return (a0 + a1 + a2) * beta - Fraction(a1 * a1 + a2 * a2 + beta * beta, 2)


def quadratic_part(t: tuple[int, int, int, int]) -> Fraction:
    a0, a1, a2, beta = t
    return Fraction(a1 * a1, 2) + a0 * a1 + (beta - a2) * (a2 - a1)


def partition_points() -> list[Fraction]:
    points = sorted({Fraction(j, c) for c in range(1, BOUND + 1) for j in range(c)})
    return points + [Fraction(1)]


def arctan_bounds(x: Fraction, terms: int) -> tuple[Fraction, Fraction]:
    s = sum(((-1) ** k * x ** (2 * k + 1) / (2 * k + 1) for k in range(terms)), Fraction(0))
    t = s + (-1) ** terms * x ** (2 * terms + 1) / (2 * terms + 1)
    return min(s, t), max(s, t)


def pi_bounds(terms_5: int, terms_239: int) -> tuple[Fraction, Fraction]:
    a = arctan_bounds(Fraction(1, 5), terms_5)
    b = arctan_bounds(Fraction(1, 239), terms_239)
    return 16 * a[0] - 4 * b[1], 16 * a[1] - 4 * b[0]


def scalar_times(s: tuple[Fraction, Fraction], x: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
    """Enclose s*x for a positive interval s and any interval x."""

    candidates = [s[0] * x[0], s[0] * x[1], s[1] * x[0], s[1] * x[1]]
    return min(candidates), max(candidates)


# ------------------------------------------------------------ implementation A
def implementation_a() -> dict:
    scale = 10**40
    m_terms = 256
    points = partition_points()
    cells = list(zip(points, points[1:]))
    low_int: list[int] = []
    high_int: list[int] = []
    for u, v in cells:
        if u == 0:
            # psi_1 is infinite at 0; omega vanishes on this cell (checked below).
            low_int.append(0)
            high_int.append(0)
            continue
        partial = Fraction(0)
        for k in range(m_terms):
            partial += 1 / (k + u) ** 2 - 1 / (k + v) ** 2
        integral = 1 / (m_terms + u) - 1 / (m_terms + v)
        low = partial + integral
        high = low + 1 / (m_terms + u) ** 2 - 1 / (m_terms + v) ** 2
        low_int.append((low.numerator * scale) // low.denominator)
        high_int.append(-((-high.numerator * scale) // high.denominator))
    pi = pi_bounds(40, 12)
    three_over_pi2 = (3 / pi[1] ** 2, 3 / pi[0] ** 2)
    s_low = (three_over_pi2[0].numerator * scale) // three_over_pi2[0].denominator
    s_high = -((-three_over_pi2[1].numerator * scale) // three_over_pi2[1].denominator)

    left_points = [(u.numerator, u.denominator) for u, _ in cells]
    enclosures = {}
    max_weight = 0
    first_cell_zero = True
    for t in box_tuples_increasing():
        c = coefficients(t)
        if max(c) > BOUND or min(c) < 1:
            raise ArithmeticError("a coefficient leaves the partition range")
        c1 = c1_value(t)
        if c1 <= 0:
            raise ArithmeticError("C1 is not positive")
        j_low = j_high = 0
        for index, (num, den) in enumerate(left_points):
            w = omega_c(c, num, den)
            if w:
                if index == 0:
                    first_cell_zero = False
                    raise ArithmeticError("omega is nonzero on the first cell")
                max_weight = max(max_weight, w)
                j_low += w * low_int[index]
                j_high += w * high_int[index]
        m2 = max(c) ** 2 * scale
        # (m^2 - J) in units of 10^-40; product with 3/pi^2 in units of 10^-80.
        diff = (m2 - j_high, m2 - j_low)
        products = [s_low * diff[0], s_low * diff[1], s_high * diff[0], s_high * diff[1]]
        q = quadratic_part(t) * scale * scale
        c0 = (q - max(products), q - min(products))
        denominator = c1 * scale * scale
        enclosures[t] = (c0[0] / denominator, c0[1] / denominator)
    return summarise(enclosures, "A", m_terms, "increasing (alpha1, alpha2, beta, alpha0)",
                     max_weight, first_cell_zero)


# ------------------------------------------------------------ implementation B
def implementation_b() -> dict:
    scale = 10**45
    m_terms = 512
    points = partition_points()
    cell_bounds = []
    for u, v in zip(points, points[1:]):
        if u == 0:
            # psi_1 is infinite at 0; omega vanishes on this cell (checked below).
            midpoint = (u + v) / 2
            cell_bounds.append((midpoint.numerator, midpoint.denominator, 0, 0))
            continue
        p1, q1, p2, q2 = u.numerator, u.denominator, v.numerator, v.denominator
        rounded = 0
        for k in range(m_terms):
            a, b = k * q1 + p1, k * q2 + p2
            rounded += (scale * (q1 * q1 * b * b - q2 * q2 * a * a)) // (a * a * b * b)
        tail_low = Fraction(1) / (m_terms + u) - Fraction(1) / (m_terms + v)
        tail_high = tail_low + Fraction(1) / (m_terms + u) ** 2 - Fraction(1) / (m_terms + v) ** 2
        # Round the tail enclosure outward to the same 10^-45 grid.
        low = rounded + (tail_low.numerator * scale) // tail_low.denominator
        high = rounded + m_terms - ((-tail_high.numerator * scale) // tail_high.denominator)
        midpoint = (u + v) / 2
        cell_bounds.append((midpoint.numerator, midpoint.denominator, low, high))
    pi = pi_bounds(45, 14)
    s = (3 / pi[1] ** 2, 3 / pi[0] ** 2)

    enclosures = {}
    max_weight = 0
    first_cell_zero = True
    for t in box_tuples_decreasing():
        c = coefficients(t)
        if max(c) > BOUND or min(c) < 1:
            raise ArithmeticError("a coefficient leaves the partition range")
        c1 = c1_value(t)
        if c1 <= 0:
            raise ArithmeticError("C1 is not positive")
        j_low = j_high = 0
        for index, (num, den, low, high) in enumerate(cell_bounds):
            w = omega_c(c, num, den)
            if w:
                if index == 0:
                    first_cell_zero = False
                    raise ArithmeticError("omega is nonzero on the first cell")
                max_weight = max(max_weight, w)
                j_low += w * low
                j_high += w * high
        m2 = max(c) ** 2
        product = scalar_times(s, (m2 - Fraction(j_high, scale), m2 - Fraction(j_low, scale)))
        q = quadratic_part(t)
        enclosures[t] = ((q - product[1]) / c1, (q - product[0]) / c1)
    return summarise(enclosures, "B", m_terms, "decreasing (alpha0, beta, alpha2, alpha1)",
                     max_weight, first_cell_zero)


def floor_decimal(x: Fraction, places: int) -> str:
    k = (x.numerator * 10**places) // x.denominator
    sign = "-" if k < 0 else ""
    k = abs(k)
    return f"{sign}{k // 10**places}.{k % 10**places:0{places}d}"


def ceil_decimal(x: Fraction, places: int) -> str:
    k = -((-x.numerator * 10**places) // x.denominator)
    sign = "-" if k < 0 else ""
    k = abs(k)
    return f"{sign}{k // 10**places}.{k % 10**places:0{places}d}"


def summarise(enclosures: dict, name: str, m_terms: int, order: str,
              max_weight: int, first_cell_zero: bool) -> dict:
    best_lower = max(low for low, _ in enclosures.values())
    candidates = sorted(t for t, (_, high) in enclosures.items() if high >= best_lower)
    others_upper = max(high for t, (_, high) in enclosures.items() if t not in candidates)
    candidates_lower = min(enclosures[t][0] for t in candidates)
    third = max((t for t in enclosures if t not in candidates), key=lambda t: enclosures[t][1])
    places = 17
    return {
        "implementation": name,
        "summands_per_cell": m_terms,
        "enumeration_order": order,
        "tuples": len(enclosures),
        "maximum_weight_on_any_cell": max_weight,
        "first_cell_contributes_zero": first_cell_zero,
        "maximiser_candidates": [list(t) for t in candidates],
        "maximiser_enclosures": {
            str(list(t)): [floor_decimal(enclosures[t][0], places), ceil_decimal(enclosures[t][1], places)]
            for t in candidates
        },
        "largest_other_tuple": list(third),
        "largest_other_upper_endpoint": ceil_decimal(others_upper, places),
        "separated": others_upper < candidates_lower,
        "_exact": (candidates, [enclosures[t] for t in candidates], others_upper),
    }


def exact_equality_inputs() -> dict:
    """Finite inputs of the paper's argument that the two maximisers tie exactly."""

    a, b = MAXIMISERS
    points = partition_points()
    floor_identity = all(
        omega(b, u) - omega(a, u)
        == (13 * u.numerator) // u.denominator + (15 * u.numerator) // u.denominator
        - 2 * ((14 * u.numerator) // u.denominator)
        for u in points[:-1]
    )
    return {
        "omega_B_minus_omega_A_equals_floor13_plus_floor15_minus_2floor14_on_every_cell": floor_identity,
        "m_values": [max(coefficients(a)), max(coefficients(b))],
        "C1_values": [str(c1_value(a)), str(c1_value(b))],
        "quadratic_parts": [str(quadratic_part(a)), str(quadratic_part(b))],
    }


def compute() -> dict:
    results = [implementation_a(), implementation_b()]
    equality = exact_equality_inputs()
    lower = Fraction(PRINTED_MAXIMISER_LOWER)
    upper = Fraction(PRINTED_MAXIMISER_UPPER)
    others = Fraction(PRINTED_OTHERS_UPPER)
    checks = {}
    for r in results:
        name = r["implementation"]
        candidates, bounds, others_upper = r.pop("_exact")
        checks[f"{name}: tuple count is 37533"] = r["tuples"] == 37533
        checks[f"{name}: every weight is 0 or 1"] = r["maximum_weight_on_any_cell"] <= 1
        checks[f"{name}: first cell contributes zero"] = r["first_cell_contributes_zero"]
        checks[f"{name}: exactly the two stated maximisers"] = candidates == sorted(MAXIMISERS)
        checks[f"{name}: maximisers separated from all other tuples"] = r["separated"]
        checks[f"{name}: both maximisers inside ({PRINTED_MAXIMISER_LOWER}, {PRINTED_MAXIMISER_UPPER})"] = all(
            lower < low and high < upper for low, high in bounds)
        checks[f"{name}: every other tuple below {PRINTED_OTHERS_UPPER}"] = others_upper < others
    checks["exact tie inputs: floor identity on every cell"] = equality[
        "omega_B_minus_omega_A_equals_floor13_plus_floor15_minus_2floor14_on_every_cell"]
    checks["exact tie inputs: m = 15 for both"] = equality["m_values"] == [15, 15]
    checks["exact tie inputs: C1 = 1091/2 for both"] = equality["C1_values"] == ["1091/2", "1091/2"]
    checks["exact tie inputs: quadratic parts 266 and 265"] = equality["quadratic_parts"] == ["266", "265"]
    return {
        "box": "1 <= alpha0, alpha1, alpha2, beta <= 30; gcd 1; alpha1 <= alpha2; alpha1 + alpha2 < beta <= alpha0 + alpha2",
        "partition_cells": len(partition_points()) - 1,
        "implementations": results,
        "exact_tie_inputs": equality,
        "printed_claims": {
            "maximiser_lower": PRINTED_MAXIMISER_LOWER,
            "maximiser_upper": PRINTED_MAXIMISER_UPPER,
            "others_upper": PRINTED_OTHERS_UPPER,
        },
        "checks": checks,
        "all_printed_claims_verified": all(checks.values()),
    }


def canonical(obj: object) -> str:
    return json.dumps(obj, indent=2, sort_keys=True) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--receipt", type=Path, help="write a receipt JSON to this path")
    args = parser.parse_args()
    result = compute()
    if args.receipt:
        receipt = {
            "schema": SCHEMA,
            "program": PROGRAM,
            "program_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "arguments": [],
            "verification_scope": "finite_computation_only",
            "claim_boundary": (
                "Interval-certified comparison of C0/C1 over the 37,533 primitive tuples with "
                "entries at most 30. No statement about directions outside the box. The "
                "irrationality theorem does not use this computation. No floating point and no "
                "Lean kernel."
            ),
            "paper_passage": "Subsection 'Proofs, earlier work and limitations', paragraph 'A certified finite parameter search'",
            "result": result,
        }
        args.receipt.write_text(canonical(receipt), encoding="utf-8")
    sys.stdout.write(canonical(result))
    return 0 if result["all_printed_claims_verified"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
