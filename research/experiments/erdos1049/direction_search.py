#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Replay the bounded numerical direction search used in the #1049 paper.

For a direction ``(alpha0, alpha1, alpha2; beta)`` in Zudilin's cone,
equations (25) and (26) of his 2004 paper give constants ``C0`` and ``C1``.
The rational-base threshold is ``theta_star = C0 / C1``.  This program
enumerates the primitive integer directions with every entry at most 30 and
records the largest numerical values of that quotient.

The combinatorial enumeration and the value of C1 are exact.  Evaluating C0
uses mpmath trigamma values at 30 decimal digits.  Consequently the output is
a reproducible numerical receipt, not an interval-certified proof that the
reported ordering is exact.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from typing import Any

import mpmath
from mpmath import mp


SUPPORTED_BOUND = 30
DECIMAL_PRECISION = 30
TOP_COUNT = 25
SUPPORTED_MPMATH_VERSION = "1.3.0"
PREPUBLICATION_PROBE_SHA256 = (
    "d0cd58b0a72dc5bcc98fb237b2033962fb66cf18157d281bb7758852f416fef2"
)

mp.dps = DECIMAL_PRECISION
THREE_OVER_PI_SQUARED = 3 / mp.pi**2


@lru_cache(maxsize=None)
def trigamma(num: int, den: int):
    """Return psi'(num/den) at the configured mpmath precision."""

    return mp.polygamma(1, mp.mpf(num) / den)


def threshold(
    alpha0: int, alpha1: int, alpha2: int, beta: int
) -> tuple[Any, Fraction] | None:
    """Evaluate C0/C1 for one admissible direction.

    Breakpoints and the step-function weight are computed with rational and
    integer arithmetic.  Only the trigamma evaluations and the final quotient
    use mpmath floating-point arithmetic.
    """

    c00 = alpha0 + alpha1 + alpha2 - beta
    c01 = alpha0
    c11 = alpha1
    c21 = alpha2
    c12 = beta - alpha1
    c22 = beta - alpha2
    if c00 <= 0:
        return None

    coefficients = (c00, c01, c11, c21, c12, c22)
    maximum = max(coefficients)
    c1 = Fraction((alpha0 + alpha1 + alpha2) * beta) - Fraction(
        alpha1**2 + alpha2**2 + beta**2, 2
    )
    c0_rational = (
        Fraction(alpha1**2, 2)
        + alpha0 * alpha1
        + (beta - alpha2) * (alpha2 - alpha1)
    )
    breakpoints = sorted({
        Fraction(k, coefficient)
        for coefficient in coefficients
        for k in range(coefficient + 1)
    })

    def floor_product(coefficient: int, x: Fraction) -> int:
        product = coefficient * x
        return product.numerator // product.denominator

    def omega(x: Fraction) -> int:
        return max(
            0,
            floor_product(c21, x)
            + floor_product(c22, x)
            - floor_product(c11, x)
            - floor_product(c12, x),
            floor_product(c01, x)
            + floor_product(c21, x)
            - floor_product(c00, x)
            - floor_product(c12, x),
        )

    integral = mp.mpf(0)
    for left, right in zip(breakpoints, breakpoints[1:]):
        weight = omega((left + right) / 2)
        if weight:
            integral += weight * (
                trigamma(left.numerator, left.denominator)
                - trigamma(right.numerator, right.denominator)
            )

    c0 = (
        mp.mpf(c0_rational.numerator) / c0_rational.denominator
        - THREE_OVER_PI_SQUARED * (maximum**2 - integral)
    )
    if c0 <= 0:
        return None
    return c0 / (mp.mpf(c1.numerator) / c1.denominator), c1


def enumerate_directions(
    bound: int,
) -> tuple[list[tuple[float, tuple[int, int, int, int]]], int, int]:
    """Enumerate the primitive directions in the published finite box."""

    ranked: list[tuple[float, tuple[int, int, int, int]]] = []
    directions_scanned = 0
    positive_c0_directions = 0
    for alpha1 in range(1, bound + 1):
        for alpha2 in range(alpha1, bound + 1):
            for beta in range(alpha1 + alpha2 + 1, bound + 1):
                for alpha0 in range(beta - alpha2, bound + 1):
                    if math.gcd(math.gcd(alpha0, alpha1), math.gcd(alpha2, beta)) != 1:
                        continue
                    directions_scanned += 1
                    result = threshold(alpha0, alpha1, alpha2, beta)
                    if result is None:
                        continue
                    theta_star, _ = result
                    positive_c0_directions += 1
                    # Preserve the original receipt's binary64 ranking boundary.
                    ranked.append((float(theta_star), (alpha0, alpha1, alpha2, beta)))
    ranked.sort(reverse=True)
    return ranked, directions_scanned, positive_c0_directions


def make_receipt(bound: int) -> dict[str, Any]:
    ranked, scanned, positive = enumerate_directions(bound)
    reference_result = threshold(14, 12, 14, 27)
    if reference_result is None:
        raise RuntimeError("the reference direction unexpectedly has nonpositive C0")
    reference, _ = reference_result
    return {
        "schema": "erdos1049-direction-search/1",
        "evidence_class": "bounded numerical search",
        "source_formula": "Zudilin (2004), equations (25) and (26)",
        "prepublication_probe_sha256": PREPUBLICATION_PROBE_SHA256,
        "bound": bound,
        "decimal_precision": DECIMAL_PRECISION,
        "mpmath_version": mpmath.__version__,
        "directions_scanned": scanned,
        "positive_c0_directions": positive,
        "best": [
            {
                "direction": list(direction),
                "theta_star": theta_star,
                "mu": 1 / theta_star,
            }
            for theta_star, direction in ranked[:TOP_COUNT]
        ],
        "reference_14_12_14_27": float(reference),
        "claim_boundary": (
            "The enumeration and rational breakpoints are exact, but trigamma and pi are "
            "evaluated by mpmath at 30 decimal digits. This receipt is not an interval-certified "
            "proof of the ordering, and it says nothing about directions outside the bound-30 box."
        ),
    }


def canonical_json(receipt: dict[str, Any]) -> str:
    return json.dumps(receipt, ensure_ascii=False, indent=2, sort_keys=True) + "\n"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--bound",
        type=int,
        required=True,
        help="box bound; this published replay supports exactly 30",
    )
    parser.add_argument("--output", type=Path, required=True, help="receipt JSON path")
    parser.add_argument(
        "--check",
        action="store_true",
        help="compare the computed receipt with --output instead of writing it",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if mpmath.__version__ != SUPPORTED_MPMATH_VERSION:
        raise SystemExit(
            "this receipt requires mpmath "
            f"{SUPPORTED_MPMATH_VERSION}; got {mpmath.__version__}"
        )
    if args.bound != SUPPORTED_BOUND:
        raise SystemExit(
            f"this published replay requires --bound {SUPPORTED_BOUND}; got {args.bound}"
        )

    rendered = canonical_json(make_receipt(args.bound))
    if args.check:
        try:
            existing = args.output.read_text(encoding="utf-8")
        except FileNotFoundError:
            print(f"missing receipt: {args.output}", file=sys.stderr)
            return 1
        if existing != rendered:
            print(f"receipt differs: {args.output}", file=sys.stderr)
            return 1
        print(f"receipt matches: {args.output}")
        return 0

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(rendered, encoding="utf-8")
    print(
        f"wrote {args.output}: {SUPPORTED_BOUND=}, "
        f"directions_scanned={json.loads(rendered)['directions_scanned']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
