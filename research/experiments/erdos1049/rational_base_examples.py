#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Classify every small rational base against the cutoff theta*.

For coprime integers a > b >= 1 the region of the rational-base theorem is
log b / log a < theta*, with theta* = C0/C1 as defined in the long Erdos 1049
paper.  The region of Bundschuh and Vaananen is log b / log a < 1/2 - 1/pi^2,
the reciprocal of mu_BV = 2 pi^2 / (pi^2 - 2).  This program uses rational
bounds only:

  * logarithms: log x = k log 2 + 2 artanh((y-1)/(y+1)) with y = x / 2^k in
    [2/3, 4/3], and log 2 = 2 artanh(1/3); each artanh series is enclosed by
    its partial sum and a geometric bound on the positive tail;
  * pi: Machin's formula with alternating-series bounds;
  * theta*: the thirteen trigamma differences are enclosed as in
    threshold_digits.py (rounded partial sums plus integral tail bounds),
    with fewer summands, since only about ten correct digits are needed here.

It checks, for all 1101 reduced fractions a/b with 1 <= b < a <= 60, which
lie in the region of the theorem; the counts 137 and 78; the two largest
admitted logarithmic ratios (53/5 and 31/4) and their rounded margins below
theta*; the smallest excluded ratio (52/5) and its margin; the four
fixed-denominator strips s^mu < r <= s^mu_BV for s = 2, 3, 4, 5; and the
decimal values printed with the theorem on 31/4.  Every comparison is decided
by disjoint rational intervals; the program stops if one is not.

It proves only these finite comparisons.  It does not prove irrationality of
any value, and it says nothing about fractions outside the stated range.  No
floating-point arithmetic and no Lean kernel are involved.
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
PROGRAM = "rational_base_examples.py"
LIMIT = 60
THETA_SUMMANDS = 4096
THETA_DIGITS = 40
SERIES_TERMS = 60

INTERVALS = [
    (Fraction(1, 14), Fraction(1, 12)), (Fraction(1, 7), Fraction(1, 6)),
    (Fraction(3, 14), Fraction(1, 4)), (Fraction(2, 7), Fraction(1, 3)),
    (Fraction(5, 14), Fraction(2, 5)), (Fraction(3, 7), Fraction(7, 15)),
    (Fraction(1, 2), Fraction(8, 15)), (Fraction(4, 7), Fraction(3, 5)),
    (Fraction(9, 14), Fraction(2, 3)), (Fraction(5, 7), Fraction(11, 15)),
    (Fraction(11, 14), Fraction(4, 5)), (Fraction(6, 7), Fraction(13, 15)),
    (Fraction(13, 14), Fraction(14, 15)),
]

Interval = tuple[Fraction, Fraction]


# ---------------------------------------------------------------- enclosures
def artanh_bounds(t: Fraction) -> Interval:
    """Enclose artanh(t) for 0 <= t < 1 by partial sum and geometric tail."""

    if t == 0:
        return Fraction(0), Fraction(0)
    if not 0 < t < 1:
        raise ValueError("artanh needs 0 <= t < 1")
    low = sum((t ** (2 * k + 1) / (2 * k + 1) for k in range(SERIES_TERMS)), Fraction(0))
    n = SERIES_TERMS
    return low, low + t ** (2 * n + 1) / ((2 * n + 1) * (1 - t * t))


LOG2 = tuple(2 * x for x in artanh_bounds(Fraction(1, 3)))


def log_bounds(x: Fraction) -> Interval:
    if x <= 0:
        raise ValueError("log needs a positive argument")
    k = 0
    y = Fraction(x)
    while y > Fraction(4, 3):
        y /= 2
        k += 1
    while y < Fraction(2, 3):
        y *= 2
        k -= 1
    t = (y - 1) / (y + 1)
    a_low, a_high = artanh_bounds(abs(t))
    if t < 0:
        a_low, a_high = -a_high, -a_low
    base_low, base_high = (k * LOG2[0], k * LOG2[1]) if k >= 0 else (k * LOG2[1], k * LOG2[0])
    return base_low + 2 * a_low, base_high + 2 * a_high


def pi_bounds() -> Interval:
    def arctan(x: Fraction, terms: int) -> Interval:
        s = sum(((-1) ** k * x ** (2 * k + 1) / (2 * k + 1) for k in range(terms)), Fraction(0))
        t = s + (-1) ** terms * x ** (2 * terms + 1) / (2 * terms + 1)
        return min(s, t), max(s, t)

    a = arctan(Fraction(1, 5), 40)
    b = arctan(Fraction(1, 239), 12)
    return 16 * a[0] - 4 * b[1], 16 * a[1] - 4 * b[0]


def theta_star_bounds(pi: Interval) -> Interval:
    scale = 10**THETA_DIGITS
    m = THETA_SUMMANDS
    j_low = j_high = Fraction(0)
    for u, v in INTERVALS:
        p1, q1, p2, q2 = u.numerator, u.denominator, v.numerator, v.denominator
        rounded = 0
        for k in range(m):
            a, b = k * q1 + p1, k * q2 + p2
            rounded += (scale * (q1 * q1 * b * b - q2 * q2 * a * a)) // (a * a * b * b)
        integral = 1 / (m + u) - 1 / (m + v)
        j_low += Fraction(rounded, scale) + integral
        j_high += Fraction(rounded + m, scale) + integral + 1 / (m + u) ** 2 - 1 / (m + v) ** 2
    if not 0 < j_low < j_high < 225:
        raise ArithmeticError("unexpected enclosure of J")
    c1 = Fraction(1091, 2)
    return (266 - 3 * (225 - j_low) / pi[0] ** 2) / c1, (266 - 3 * (225 - j_high) / pi[1] ** 2) / c1


def ratio(num: Interval, den: Interval) -> Interval:
    """Enclose num/den for positive num and den intervals (num may be [0,0])."""

    if den[0] <= 0 or num[0] < 0:
        raise ArithmeticError("ratio needs a positive denominator and nonnegative numerator")
    return num[0] / den[1], num[1] / den[0]


def compare(x: Interval, y: Interval) -> int:
    """Return -1 if x < y, 1 if x > y; stop if the intervals overlap."""

    if x[1] < y[0]:
        return -1
    if x[0] > y[1]:
        return 1
    raise ArithmeticError("an interval comparison is undecided")


def rounds_to(x: Interval, printed: str) -> bool:
    """True if every point of x rounds to the printed decimal (half-up)."""

    places = len(printed.split(".")[1])
    target = Fraction(printed)
    half = Fraction(1, 2 * 10**places)
    return target - half <= x[0] and x[1] < target + half


def truncates_to(x: Interval, printed: str) -> bool:
    """True if every point of x has the printed decimal as its truncation."""

    places = len(printed.split(".")[1])
    target = Fraction(printed)
    return target <= x[0] and x[1] < target + Fraction(1, 10**places)


def sub(x: Interval, y: Interval) -> Interval:
    return x[0] - y[1], x[1] - y[0]


def show(x: Interval, places: int = 12) -> list[str]:
    def floor_str(v: Fraction) -> str:
        k = (v.numerator * 10**places) // v.denominator
        sign = "-" if k < 0 else ""
        k = abs(k)
        return f"{sign}{k // 10**places}.{k % 10**places:0{places}d}"

    def ceil_str(v: Fraction) -> str:
        k = -((-v.numerator * 10**places) // v.denominator)
        sign = "-" if k < 0 else ""
        k = abs(k)
        return f"{sign}{k // 10**places}.{k % 10**places:0{places}d}"

    return [floor_str(x[0]), ceil_str(x[1])]


# ---------------------------------------------------------------- computation
def compute() -> dict:
    pi = pi_bounds()
    theta = theta_star_bounds(pi)
    mu = (1 / theta[1], 1 / theta[0])
    theta_bv = (Fraction(1, 2) - 1 / pi[0] ** 2, Fraction(1, 2) - 1 / pi[1] ** 2)
    mu_bv = (1 / theta_bv[1], 1 / theta_bv[0])
    logs = {n: log_bounds(Fraction(n)) for n in range(1, LIMIT + 1)}
    logs[1] = (Fraction(0), Fraction(0))

    rows = []
    for a in range(2, LIMIT + 1):
        for b in range(1, a):
            if gcd(a, b) != 1:
                continue
            r = ratio(logs[b], logs[a])
            inside = compare(r, theta) < 0
            rows.append((a, b, r, inside))
    members = [row for row in rows if row[3]]
    excluded = [row for row in rows if not row[3]]
    noninteger_members = [row for row in members if row[1] > 1]

    # Order the members by ratio; certify the top two with disjoint intervals.
    members_sorted = sorted(members, key=lambda row: row[2][0], reverse=True)
    first, second = members_sorted[0], members_sorted[1]
    compare(first[2], second[2])
    for row in members_sorted[2:]:
        if compare(second[2], row[2]) <= 0:
            raise ArithmeticError("second member not separated")
    excluded_sorted = sorted(excluded, key=lambda row: row[2][0])
    least_excluded = excluded_sorted[0]
    for row in excluded_sorted[1:]:
        if compare(least_excluded[2], row[2]) >= 0:
            raise ArithmeticError("least excluded ratio not separated")

    margin_first = sub(theta, first[2])
    margin_second = sub(theta, second[2])
    excess_least = sub(least_excluded[2], theta)

    # Fixed-denominator strips s^mu < r <= s^mu_BV, i.e. theta_BV <= log s/log r < theta*.
    strips = {}
    for s in (2, 3, 4, 5):
        integers = []
        for r in range(s + 1, LIMIT + 1):
            q = ratio(logs[s], logs[r])
            if compare(q, theta) < 0 and compare(q, theta_bv) > 0:
                integers.append(r)
        # Every r in the strip is at most s^mu_BV < s^2.51 <= 5^2.51 < 60.
        if compare(ratio(logs[s], logs[LIMIT]), theta_bv) >= 0:
            raise ArithmeticError("strip search range is too short")
        strips[str(s)] = {
            "integers_in_strip": integers,
            "numerators_coprime_to_s": [r for r in integers if gcd(r, s) == 1],
        }
    # Least numerator: for s >= 5 every strip member exceeds s^mu >= 5^mu > 52 > 31.
    five_mu_above_52 = compare(logs[52], (mu[0] * logs[5][0], mu[1] * logs[5][1])) < 0

    r31 = ratio(logs[4], logs[31])
    r23 = ratio(logs[2], logs[3])
    four_mu = (mu[0] * logs[4][0], mu[1] * logs[4][1])
    four_mu_bv = (mu_bv[0] * logs[4][0], mu_bv[1] * logs[4][1])

    def exp_truncates_to(log_value: Interval, printed: str) -> bool:
        """True if exp(log_value) has the printed truncation (checked on logarithms)."""

        places = len(printed.split(".")[1])
        low = log_bounds(Fraction(printed))
        high = log_bounds(Fraction(printed) + Fraction(1, 10**places))
        return low[1] < log_value[0] and log_value[1] < high[0]

    printed_decimals = {
        "log4/log31 = 0.4036981731641997...": truncates_to(r31, "0.4036981731641997"),
        "4^mu = 30.483515...": exp_truncates_to(four_mu, "30.483515"),
        "4^mu_BV = 32.369642...": exp_truncates_to(four_mu_bv, "32.369642"),
        "mu_BV = 2.508284761994...": truncates_to(mu_bv, "2.508284761994"),
        "1/2 - 1/pi^2 = 0.3986788163576622...": truncates_to(theta_bv, "0.3986788163576622"),
        "log2/log3 = 0.6309297535714574...": truncates_to(r23, "0.6309297535714574"),
        "log2/log3 - theta* = 0.2252467...": truncates_to(sub(r23, theta), "0.2252467"),
        "log4/log31 < 81/200 < theta*": r31[1] < Fraction(81, 200) < theta[0],
        "1/2 - 1/pi^2 < 2/5 < log4/log31": theta_bv[1] < Fraction(2, 5) < r31[0],
    }

    checks = {
        "reduced_fraction_count_is_1101": len(rows) == 1101,
        "member_count_is_137": len(members) == 137,
        "noninteger_member_count_is_78": len(noninteger_members) == 78,
        "largest_admitted_ratio_is_53/5": (first[0], first[1]) == (53, 5),
        "second_largest_admitted_ratio_is_31/4": (second[0], second[1]) == (31, 4),
        "margin_53/5_rounds_to_0.000313": rounds_to(margin_first, "0.000313"),
        "margin_31/4_rounds_to_0.001985": rounds_to(margin_second, "0.001985"),
        "smallest_excluded_ratio_is_52/5": (least_excluded[0], least_excluded[1]) == (52, 5),
        "ratio_52/5_is_0.4073243836...": truncates_to(least_excluded[2], "0.4073243836"),
        "excess_52/5_rounds_to_0.001641": rounds_to(excess_least, "0.001641"),
        "strip_s2_empty": strips["2"]["numerators_coprime_to_s"] == [],
        "strip_s3_empty": strips["3"]["numerators_coprime_to_s"] == [],
        "strip_s4_is_{31}": strips["4"]["numerators_coprime_to_s"] == [31],
        "strip_s5_is_{53,54,56}": strips["5"]["numerators_coprime_to_s"] == [53, 54, 56],
        "5^mu_above_52_so_31/4_has_least_numerator": five_mu_above_52,
    }
    checks.update({f"printed: {k}": v for k, v in printed_decimals.items()})

    return {
        "range": "reduced a/b with 1 <= b < a <= 60",
        "theta_star_enclosure": show(theta, 14),
        "mu_bv_enclosure": show(mu_bv, 14),
        "reduced_fractions": len(rows),
        "members": len(members),
        "noninteger_members": len(noninteger_members),
        "noninteger_member_list": [f"{a}/{b}" for a, b, _, _ in sorted(noninteger_members)],
        "largest_admitted": [
            {"base": f"{row[0]}/{row[1]}", "log_ratio": show(row[2]),
             "margin_below_theta_star": show(margin)}
            for row, margin in ((first, margin_first), (second, margin_second))
        ],
        "smallest_excluded": {
            "base": f"{least_excluded[0]}/{least_excluded[1]}",
            "log_ratio": show(least_excluded[2]),
            "excess_over_theta_star": show(excess_least),
        },
        "strips_s_mu_lt_r_le_s_mu_bv": strips,
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
                "Finite rational-interval comparisons for reduced fractions with numerator at "
                "most 60 and for the four strips s = 2, 3, 4, 5. No irrationality statement is "
                "proved here. No floating point and no Lean kernel."
            ),
            "paper_passage": "Subsection 'Proofs, earlier work and limitations', paragraph 'Examples of rational bases'; decimal values in the theorem on the base 31/4",
            "result": result,
        }
        args.receipt.write_text(canonical(receipt), encoding="utf-8")
    sys.stdout.write(canonical(result))
    return 0 if result["all_printed_claims_verified"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
