#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Certify the printed decimal digits of the rational-base cutoff theta*.

The long Erdos 1049 paper defines

    C1 = 1091/2,   C0 = 266 - (3/pi^2) (225 - J),   theta* = C0/C1,   mu = 1/theta*,
    J  = sum over thirteen half-open intervals [u, v) of psi_1(u) - psi_1(v),

with psi_1(x) = sum_{k>=0} (k+x)^(-2).  For each interval put
f(k) = (k+u)^(-2) - (k+v)^(-2).  This program follows the error bound printed
in the paper, using integers and fractions only:

  * each of the first M = 65536 positive rational summands f(0), ..., f(M-1)
    is rounded down to a multiple of 10^-50, so the true partial sum lies
    between the rounded sum and the rounded sum plus M * 10^-50;
  * the tail sum_{k>=M} f(k) lies between the integral of f from M to infinity,
    (M+u)^(-1) - (M+v)^(-1), and that integral plus f(M), because f is
    positive and decreasing;
  * pi is enclosed by Machin's formula pi = 16 arctan(1/5) - 4 arctan(1/239)
    with alternating-series bounds;
  * because 225 - J > 0, the lower (upper) endpoint of C0 uses the lower
    (upper) endpoints of J and pi.

It proves the four strict inequalities

    0.4056830213840605403 < theta* < 0.4056830213840605417,
    2.4649786835749750334 < mu     < 2.4649786835749750415.

It does not prove anything about the irrationality theorem itself, which uses
the exact definitions of C0 and C1 and never these decimal values.  No
floating-point arithmetic and no Lean kernel are involved.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path

SCHEMA = "erdos1049-public-computation/1"
PROGRAM = "threshold_digits.py"
DEFAULT_SUMMANDS = 65536
DEFAULT_ROUNDING_DIGITS = 50

# The thirteen half-open intervals on which Zudilin's weight omega equals 1
# for the direction (14,12,14;27), as printed in Section 2 of the paper.
INTERVALS = [
    (Fraction(1, 14), Fraction(1, 12)),
    (Fraction(1, 7), Fraction(1, 6)),
    (Fraction(3, 14), Fraction(1, 4)),
    (Fraction(2, 7), Fraction(1, 3)),
    (Fraction(5, 14), Fraction(2, 5)),
    (Fraction(3, 7), Fraction(7, 15)),
    (Fraction(1, 2), Fraction(8, 15)),
    (Fraction(4, 7), Fraction(3, 5)),
    (Fraction(9, 14), Fraction(2, 3)),
    (Fraction(5, 7), Fraction(11, 15)),
    (Fraction(11, 14), Fraction(4, 5)),
    (Fraction(6, 7), Fraction(13, 15)),
    (Fraction(13, 14), Fraction(14, 15)),
]

C1 = Fraction(1091, 2)

# The decimal claims printed in the paper.
PRINTED = {
    "theta_star_lower": "0.4056830213840605403",
    "theta_star_upper": "0.4056830213840605417",
    "mu_lower": "2.4649786835749750334",
    "mu_upper": "2.4649786835749750415",
}


def omega(x: Fraction) -> int:
    """Zudilin's weight for the direction (14,12,14;27), as printed in the paper."""

    def fl(c: int) -> int:
        return (c * x.numerator) // x.denominator

    return max(0, fl(14) + fl(13) - fl(12) - fl(15), 2 * fl(14) - fl(13) - fl(15))


def check_intervals() -> None:
    """Recover the support of omega on [0, 1) and compare with INTERVALS."""

    points = sorted({Fraction(k, c) for c in (12, 13, 14, 15) for k in range(c + 1)})
    found: list[list[Fraction]] = []
    for left, right in zip(points, points[1:]):
        value = omega((left + right) / 2)
        if value != omega(left):
            raise ArithmeticError("omega is not constant on a cell")
        if value not in (0, 1):
            raise ArithmeticError("omega takes a value other than 0 or 1")
        if value == 1:
            if found and found[-1][1] == left:
                found[-1][1] = right
            else:
                found.append([left, right])
    if [tuple(pair) for pair in found] != INTERVALS:
        raise ArithmeticError("the support of omega differs from the printed intervals")


def arctan_bounds(x: Fraction, terms: int) -> tuple[Fraction, Fraction]:
    """Alternating-series enclosure of arctan(x) for 0 < x < 1."""

    partial = Fraction(0)
    for k in range(terms):
        partial += (-1) ** k * x ** (2 * k + 1) / (2 * k + 1)
    following = partial + (-1) ** terms * x ** (2 * terms + 1) / (2 * terms + 1)
    return min(partial, following), max(partial, following)


def pi_bounds() -> tuple[Fraction, Fraction]:
    a_low, a_high = arctan_bounds(Fraction(1, 5), 40)
    b_low, b_high = arctan_bounds(Fraction(1, 239), 12)
    return 16 * a_low - 4 * b_high, 16 * a_high - 4 * b_low


def interval_sum_bounds(
    u: Fraction, v: Fraction, summands: int, digits: int
) -> tuple[Fraction, Fraction, int]:
    """Enclose psi_1(u) - psi_1(v) = sum_{k>=0} f(k)."""

    scale = 10**digits
    p1, q1 = u.numerator, u.denominator
    p2, q2 = v.numerator, v.denominator
    rounded = 0
    for k in range(summands):
        a = k * q1 + p1
        b = k * q2 + p2
        numerator = q1 * q1 * b * b - q2 * q2 * a * a
        denominator = a * a * b * b
        if numerator <= 0:
            raise ArithmeticError("a summand is not positive")
        rounded += (scale * numerator) // denominator
    partial_low = Fraction(rounded, scale)
    partial_high = Fraction(rounded + summands, scale)
    m = summands
    integral = 1 / (m + u) - 1 / (m + v)
    first_tail_term = 1 / (m + u) ** 2 - 1 / (m + v) ** 2
    return partial_low + integral, partial_high + integral + first_tail_term, rounded


def decimal_floor(x: Fraction, places: int) -> str:
    k = (x.numerator * 10**places) // x.denominator
    return f"{k // 10**places}.{k % 10**places:0{places}d}"


def decimal_ceil(x: Fraction, places: int) -> str:
    k = -((-x.numerator * 10**places) // x.denominator)
    return f"{k // 10**places}.{k % 10**places:0{places}d}"


def compute(summands: int, digits: int) -> dict:
    check_intervals()
    j_low = Fraction(0)
    j_high = Fraction(0)
    rounded_sums = []
    for u, v in INTERVALS:
        low, high, rounded = interval_sum_bounds(u, v, summands, digits)
        j_low += low
        j_high += high
        rounded_sums.append(str(rounded))
    pi_low, pi_high = pi_bounds()
    if not (0 < j_low < j_high < 225):
        raise ArithmeticError("unexpected enclosure of J")
    # 225 - J > 0, so C0 increases with J and with pi.
    c0_low = 266 - 3 * (225 - j_low) / pi_low**2
    c0_high = 266 - 3 * (225 - j_high) / pi_high**2
    theta_low, theta_high = c0_low / C1, c0_high / C1
    mu_low, mu_high = C1 / c0_high, C1 / c0_low
    printed = {key: Fraction(value) for key, value in PRINTED.items()}
    checks = {
        "theta_star_above_printed_lower": theta_low > printed["theta_star_lower"],
        "theta_star_below_printed_upper": theta_high < printed["theta_star_upper"],
        "mu_above_printed_lower": mu_low > printed["mu_lower"],
        "mu_below_printed_upper": mu_high < printed["mu_upper"],
    }
    places = 24
    return {
        "summands_per_interval": summands,
        "rounding_unit": f"10^-{digits}",
        "intervals": [[str(u), str(v)] for u, v in INTERVALS],
        "omega_support_matches_printed_intervals": True,
        "rounded_partial_sums_in_rounding_units": rounded_sums,
        "enclosures_outward_decimal": {
            "J": [decimal_floor(j_low, places), decimal_ceil(j_high, places)],
            "pi": [decimal_floor(pi_low, places), decimal_ceil(pi_high, places)],
            "C0": [decimal_floor(c0_low, places), decimal_ceil(c0_high, places)],
            "theta_star": [decimal_floor(theta_low, places), decimal_ceil(theta_high, places)],
            "mu": [decimal_floor(mu_low, places), decimal_ceil(mu_high, places)],
        },
        "theta_star_enclosure_width_upper_bound": decimal_ceil(theta_high - theta_low, 25),
        "printed_claims": PRINTED,
        "checks": checks,
        "all_printed_claims_verified": all(checks.values()),
    }


def canonical(obj: object) -> str:
    return json.dumps(obj, indent=2, sort_keys=True) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--summands", type=int, default=DEFAULT_SUMMANDS,
                        help="summands per interval before the integral tail (paper: 65536)")
    parser.add_argument("--digits", type=int, default=DEFAULT_ROUNDING_DIGITS,
                        help="each summand is rounded down to a multiple of 10^-DIGITS (paper: 50)")
    parser.add_argument("--receipt", type=Path, help="write a receipt JSON to this path")
    args = parser.parse_args()
    if args.summands < 1 or args.digits < 1:
        parser.error("--summands and --digits must be positive")
    result = compute(args.summands, args.digits)
    if args.receipt:
        arguments = []
        if args.summands != DEFAULT_SUMMANDS:
            arguments += ["--summands", str(args.summands)]
        if args.digits != DEFAULT_ROUNDING_DIGITS:
            arguments += ["--digits", str(args.digits)]
        receipt = {
            "schema": SCHEMA,
            "program": PROGRAM,
            "program_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "arguments": arguments,
            "verification_scope": "finite_computation_only",
            "claim_boundary": (
                "Rational enclosures of theta* and mu that certify the printed decimal "
                "truncations. The irrationality proofs use the exact definitions, not these "
                "digits. No floating point and no Lean kernel."
            ),
            "paper_passage": "Subsection 'The rational bracket around theta*', paragraph beginning 'Here is the complete error bound used in that calculation'",
            "result": result,
        }
        args.receipt.write_text(canonical(receipt), encoding="utf-8")
    sys.stdout.write(canonical(result))
    return 0 if result["all_printed_claims_verified"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
