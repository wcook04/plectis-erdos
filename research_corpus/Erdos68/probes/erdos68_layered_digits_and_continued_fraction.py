#!/usr/bin/env python3
"""Erdos #68: exact finite second-layer digits and two finite genericity probes.

Upstream analytic state
-----------------------
`FactorialDigitLawLab.md` collapsed four producer families into level sets of the
single rounding digit `D_m`, and measured `(D_m+1)/m` against `Uniform[0,1)` over
49998 indices with no detectable bias.  The canonical convention is important:
a rational `S = sum_(n>=2) 1/(n!-1)` would have `d_m(S) = 0` for all large `m`,
not an eventually maximal digit tail.

Two things had never been computed.

Part 1: the layer decomposition
-------------------------------
From `1/(n!-1) = 1/n! + 1/(n!(n!-1))`,

    S = (e-2) + S2,      S2 = sum_(n>=2) 1/(n!(n!-1)).

In factorial base `e-2 = sum_(n>=2) 1/n!` has digit exactly 1 at every position.
Factorial-base addition with carries gives the exact law

    d_m(S) = (1 + d_m(S2) + c_(m+1))  mod  m .

That law is retained here as a finite consistency check.  It does not turn an
eventually maximal tail into the rationality boundary.

The exact finite-prefix coordinate is cleaner.  If `P_m` and `P2_m` are the
prefixes of `S` and `S2`, and `b_m` is the strict-successor carry, then

    floor(m! P2_m) - m floor((m-1)! P2_(m-1)) = m - 1 - b_m.

`SecondLayerDigit.lean` proves this identity.  Replacing the finite floors by
the floors of the infinite `S2` requires showing that the positive second-layer
tail does not cross the next integer.  The weak estimate "scaled tail < 1" is
not enough.  This probe checks the exact distance to that integer against the
strong elementary bound `m! * tail2_m < 1/m!`.

Part 2: the continued fraction
------------------------------
The packet computed 23449 partial quotients of `S` and used them for one thing --
a denominator bound `q > 10^12039`.  Their *distribution* was never examined.
A continued fraction is the classical measure of how close a number comes to
rational, and it is statistically independent of the factorial-digit statistic:
different algorithm, different invariant measure.  If `S` had arithmetic
structure pushing it toward rationality, the partial quotients would show it as
excess mass at large values or as records clustering at the unit-carry indices.

Probe
-----
Part 1 proves the finite-prefix identity by exact `Fraction` arithmetic, checks
the no-crossing inequality against a rigorous tail bound, and independently
computes `d_m` for `S`, `e-2`, and `S2` at 3400-digit scale.

Part 2 computes the continued fraction of `S` inside a validated horizon
(convergent denominators kept below the precision half-life), and compares it to
Gauss-Kuzmin and to Khinchin's constant.

Predeclared falsifiers
----------------------
Part 1: any failure of the exact finite-prefix identity, any negative strict-
successor carry, any failure of the no-crossing certificate, any digit outside
`[0,m-1]`, or any failure of the digitwise addition.
Part 2: a Gauss-Kuzmin chi-square that would be exceeded by chance less than 1%
of the time, or a Khinchin geometric mean off by more than 5%.  Either would be
evidence of arithmetic structure and would be the interesting outcome.

Claim boundary
--------------
Finite exact computation.  The layer identity is exact algebra; the genericity
measurements are finite evidence for a cofinal statement and are not a proof.
Erdos #68 remains open.
"""

from __future__ import annotations

import argparse
import json
import math
from collections import Counter
from fractions import Fraction
from math import factorial
from pathlib import Path

MAX_POSITION = 500
SERIES_TERMS = 1100
DIGIT_SCALE_DIGITS = 3400
CF_PRECISION_DIGITS = 3000


def _floor_k_factorial_times_sum(denominators, k_factorial, scale) -> int:
    total = k_factorial * scale
    return sum(total // d for d in denominators) // scale


def _digits(denominators, max_position, scale, factorials) -> dict[int, int]:
    out: dict[int, int] = {}
    previous = _floor_k_factorial_times_sum(denominators, factorials[1], scale)
    for k in range(2, max_position + 1):
        current = _floor_k_factorial_times_sum(denominators, factorials[k], scale)
        out[k] = current - k * previous
        previous = current
    return out


def exact_second_layer_coordinate(max_position: int) -> dict:
    """Check the Lean finite-prefix law and a sufficient no-crossing inequality.

    For `m >= 2`, positivity and factorial growth give the strict bound

        m! * sum_(n>m) 1/(n! (n!-1)) < 1/m!.

    Thus the finite and infinite second-layer floors agree whenever the exact
    finite scaled prefix lies at distance greater than `1/m!` below the next
    integer.  This compares the tail to the actual gap; merely checking that the
    tail is below one would not certify the floor.
    """
    factorials = [factorial(k) for k in range(max_position + 1)]
    gap_prefix = Fraction(0)
    second_prefix = Fraction(0)
    previous_top = 1  # strictFacTopRat(0, 1)
    previous_second_floor = 0
    formula_failures: list[int] = []
    floor_stability_failures: list[int] = []
    negative_carries: list[dict[str, int]] = []
    unit_carries: list[int] = []
    minimum_margin_ratio: Fraction | None = None
    minimum_margin_index: int | None = None
    carry_min: int | None = None
    carry_max: int | None = None

    for m in range(2, max_position + 1):
        fm = factorials[m]
        gap_prefix += Fraction(1, fm - 1)
        second_prefix += Fraction(1, fm * (fm - 1))

        scaled_gap = fm * gap_prefix
        top = scaled_gap.numerator // scaled_gap.denominator + 1
        carry = m * previous_top + 1 - top

        scaled_second = fm * second_prefix
        second_floor = scaled_second.numerator // scaled_second.denominator
        finite_digit = second_floor - m * previous_second_floor
        if finite_digit != m - 1 - carry:
            formula_failures.append(m)

        fractional_part = scaled_second - second_floor
        distance_to_next = 1 - fractional_part
        tail_upper = Fraction(1, fm)
        margin_ratio = distance_to_next / tail_upper
        if minimum_margin_ratio is None or margin_ratio < minimum_margin_ratio:
            minimum_margin_ratio = margin_ratio
            minimum_margin_index = m
        if not tail_upper < distance_to_next:
            floor_stability_failures.append(m)

        if carry < 0:
            negative_carries.append({"m": m, "carry": carry})
        if carry == 1:
            unit_carries.append(m)
        carry_min = carry if carry_min is None else min(carry_min, carry)
        carry_max = carry if carry_max is None else max(carry_max, carry)
        previous_top = top
        previous_second_floor = second_floor

    assert minimum_margin_ratio is not None
    ratio_log10 = math.log10(minimum_margin_ratio.numerator) - math.log10(
        minimum_margin_ratio.denominator
    )
    return {
        "range": [2, max_position],
        "finite digit law d_m(P2_m) = m-1-b_m": not formula_failures,
        "finite digit law failures": formula_failures,
        "negative strict-successor carries": negative_carries,
        "carry range": [carry_min, carry_max],
        "unit carry positions": unit_carries,
        "floor stability certified by m!*tail2 < 1/m!": not floor_stability_failures,
        "floor stability failures": floor_stability_failures,
        "smallest gap/tail-bound ratio index": minimum_margin_index,
        "log10(smallest gap/tail-bound ratio)": round(ratio_log10, 6),
        "interpretation": (
            "A ratio above 1 certifies that the infinite second-layer tail cannot "
            "cross the next integer at that factorial scale."
        ),
    }


def layer_decomposition(max_position: int, terms: int) -> dict:
    scale = 10 ** DIGIT_SCALE_DIGITS
    factorials = [factorial(k) for k in range(max_position + 2)]
    fn = [factorial(n) for n in range(terms + 2)]

    d_series = _digits([fn[n] - 1 for n in range(2, terms + 1)], max_position, scale, factorials)
    d_exp = _digits([fn[n] for n in range(2, terms + 1)], max_position, scale, factorials)
    d_second = _digits(
        [fn[n] * (fn[n] - 1) for n in range(2, terms + 1)], max_position, scale, factorials
    )

    positions = range(2, max_position + 1)
    exp_all_one = all(d_exp[k] == 1 for k in positions)
    ranges_ok = all(0 <= d_series[k] <= k - 1 for k in positions) and all(
        0 <= d_second[k] <= k - 1 for k in positions
    )

    carries: dict[int, int] = {}
    carry = 0
    addition_ok = True
    for k in range(max_position, 1, -1):
        carries[k] = carry
        total = d_exp[k] + d_second[k] + carry
        if total % k != d_series[k]:
            addition_ok = False
            break
        carry = total // k

    zeros = [k for k in range(3, max_position + 1) if d_series[k] == 0]
    maximal = [k for k in range(3, max_position + 1) if d_series[k] == k - 1]
    zero_pred = all(d_second[k] == k - 1 - carries[k] for k in zeros)
    maximal_pred = all(d_second[k] == k - 2 - carries[k] for k in maximal)

    return {
        "d_m(e-2) == 1 at every position": exp_all_one,
        "digit ranges respected": ranges_ok,
        "S = (e-2) + S2 reproduced digitwise with carries": addition_ok,
        "positions with d_m(S) = 0 (non-unit carry, D_m = -1)": zeros,
        "positions with d_m(S) = m-1 (UNIT carry, D_m = 0)": maximal,
        "prediction d_m(S)=0 => d_m(S2)=m-1-carry": zero_pred,
        "prediction d_m(S)=m-1 => d_m(S2)=m-2-carry": maximal_pred,
        "max_position": max_position,
    }


def continued_fraction(precision_digits: int, terms: int) -> dict:
    scale = 10 ** precision_digits
    fn = [factorial(n) for n in range(terms + 2)]
    numerator = sum(scale // (fn[n] - 1) for n in range(2, terms + 1))

    quotients: list[int] = []
    p, q = numerator, scale
    while q and len(quotients) < 3000:
        quotients.append(p // q)
        p, q = q, p - (p // q) * q

    # Keep only the horizon where the convergent denominator is safely inside
    # the working precision: q_k^2 must stay below 10^(precision-20).
    k0, k1 = 0, 1
    valid = 0
    records: list[tuple[int, int]] = []
    best = 0
    for index, a in enumerate(quotients[1:], 1):
        k0, k1 = k1, a * k1 + k0
        if math.log10(k1) * 2 < precision_digits - 20:
            valid = index
            if a > best:
                best = a
                records.append((index, a))
    quotients = quotients[: valid + 1]
    tail = quotients[1:]
    n = len(tail)

    counts = Counter(min(a, 10) for a in tail)
    chi_square = 0.0
    rows = []
    for value in range(1, 10):
        expected = n * math.log2(1 + 1 / (value * (value + 2)))
        chi_square += (counts[value] - expected) ** 2 / expected
        rows.append({"a": value, "observed": counts[value], "gauss_kuzmin": round(expected, 1)})
    expected_tail = n * (1 - sum(math.log2(1 + 1 / (v * (v + 2))) for v in range(1, 10)))
    chi_square += (counts[10] - expected_tail) ** 2 / expected_tail
    rows.append({"a": ">=10", "observed": counts[10], "gauss_kuzmin": round(expected_tail, 1)})

    khinchin_observed = math.exp(sum(math.log(a) for a in tail) / n)

    return {
        "partial_quotients_inside_validated_horizon": n,
        "first_25": quotients[:25],
        "gauss_kuzmin_table": rows,
        "gauss_kuzmin_chi_square_9df": round(chi_square, 2),
        "gauss_kuzmin_chi_square_1pc_critical_9df": 21.67,
        "gauss_kuzmin_consistent": chi_square < 21.67,
        "khinchin_geometric_mean_observed": round(khinchin_observed, 4),
        "khinchin_constant": 2.6854520010,
        "khinchin_relative_error": round(abs(khinchin_observed - 2.6854520010) / 2.6854520010, 4),
        "khinchin_consistent": abs(khinchin_observed - 2.6854520010) / 2.6854520010 < 0.05,
        "record_partial_quotients": [{"k": k, "a_k": a} for k, a in records],
        "largest_partial_quotient": max(tail),
    }


def run(max_position: int = MAX_POSITION) -> dict:
    exact_coordinate = exact_second_layer_coordinate(max_position)
    layers = layer_decomposition(max_position, SERIES_TERMS)
    cf = continued_fraction(CF_PRECISION_DIGITS, SERIES_TERMS)
    return {
        "probe": "erdos68_layered_digits_and_continued_fraction",
        "part_0_exact_second_layer_coordinate": exact_coordinate,
        "part_1_layer_decomposition": layers,
        "part_2_continued_fraction": cf,
        "reading": (
            "The exact finite second-layer digit is m-1-b_m. The separate "
            "no-crossing check is what permits comparison with the infinite S2; "
            "tail<1 alone does not. Canonical rational factorial digits are "
            "eventually zero, so the old eventually-maximal rationality boundary "
            "is rejected. The finite factorial-digit and continued-fraction "
            "statistics remain independent genericity evidence, not proofs."
        ),
        "claim_boundary": (
            "The layer identity is exact algebra. The genericity measurements are "
            "finite evidence for a cofinal statement, never a proof. Erdos #68 "
            "remains open."
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--max-position", type=int, default=MAX_POSITION)
    parser.add_argument("--json-out", type=Path, default=None)
    args = parser.parse_args()

    result = run(args.max_position)
    text = json.dumps(result, indent=2)
    print(text)
    if args.json_out:
        args.json_out.write_text(text + "\n", encoding="utf-8")

    exact_coordinate = result["part_0_exact_second_layer_coordinate"]
    layers = result["part_1_layer_decomposition"]
    cf = result["part_2_continued_fraction"]
    checks = [
        exact_coordinate["finite digit law d_m(P2_m) = m-1-b_m"],
        not exact_coordinate["negative strict-successor carries"],
        exact_coordinate["floor stability certified by m!*tail2 < 1/m!"],
        layers["d_m(e-2) == 1 at every position"],
        layers["digit ranges respected"],
        layers["S = (e-2) + S2 reproduced digitwise with carries"],
        layers["prediction d_m(S)=0 => d_m(S2)=m-1-carry"],
        layers["prediction d_m(S)=m-1 => d_m(S2)=m-2-carry"],
        cf["gauss_kuzmin_consistent"],
        cf["khinchin_consistent"],
    ]
    return 0 if all(checks) else 1


if __name__ == "__main__":
    raise SystemExit(main())
