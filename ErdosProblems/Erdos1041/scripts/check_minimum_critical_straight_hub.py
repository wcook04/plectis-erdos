#!/usr/bin/env python3
"""Exact counterexample to the minimum-critical straight-hub mechanism.

The five roots are Gaussian rationals obtained from rational half-angle
parameters and a common rational radius.  Floating-point root finding proposes
small rational rectangles for the four derivative roots, but every decisive
claim is subsequently checked by exact complex root counts and rational
interval arithmetic:

* one rectangle contains each critical point;
* one critical-value modulus is strictly smaller than the other three and is
  itself below one; and
* four of the five root spokes from that critical point contain a rational-
  parameter waypoint where ``|f|^2>1``.

Thus at most one spoke is contained in the strict unit lemniscate.  The result
eliminates the straight-spoke completion of the first-merge reduction, not
Erdős #1041 and not the two curved descending inverse-ray branches.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Any

import sympy as sp

from system.lib.formal_math_experiment_contract import source_record


REPO_ROOT = Path(__file__).resolve().parents[5]
SCRIPT_PATH = Path(__file__).resolve()
SOURCE_REF = str(SCRIPT_PATH.relative_to(REPO_ROOT))
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "MinimumCriticalNewtonHubLab.md"
)
SEARCH_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "scripts/search_counterexample.py"
)
RESEARCH_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "research_packet.json"
)
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "erdos1041_minimum_critical_straight_hub_counterexample_receipt.json"
)


Interval = tuple[Fraction, Fraction]
CInterval = tuple[Interval, Interval]


def canonical_hash(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def as_fraction(value: sp.Rational) -> Fraction:
    return Fraction(int(value.p), int(value.q))


def interval_add(left: Interval, right: Interval) -> Interval:
    return left[0] + right[0], left[1] + right[1]


def interval_neg(value: Interval) -> Interval:
    return -value[1], -value[0]


def interval_sub(left: Interval, right: Interval) -> Interval:
    return interval_add(left, interval_neg(right))


def interval_mul(left: Interval, right: Interval) -> Interval:
    products = (
        left[0] * right[0],
        left[0] * right[1],
        left[1] * right[0],
        left[1] * right[1],
    )
    return min(products), max(products)


def interval_scale(value: Interval, scalar: Fraction) -> Interval:
    return interval_mul(value, (scalar, scalar))


def interval_square(value: Interval) -> Interval:
    squares = value[0] ** 2, value[1] ** 2
    lower = Fraction(0) if value[0] <= 0 <= value[1] else min(squares)
    return lower, max(squares)


def complex_add(left: CInterval, right: CInterval) -> CInterval:
    return interval_add(left[0], right[0]), interval_add(left[1], right[1])


def complex_mul(left: CInterval, right: CInterval) -> CInterval:
    ac = interval_mul(left[0], right[0])
    bd = interval_mul(left[1], right[1])
    ad = interval_mul(left[0], right[1])
    bc = interval_mul(left[1], right[0])
    return interval_sub(ac, bd), interval_add(ad, bc)


def complex_scale(value: CInterval, scalar: Fraction) -> CInterval:
    return interval_scale(value[0], scalar), interval_scale(value[1], scalar)


def complex_point(value: sp.Expr) -> CInterval:
    real = as_fraction(sp.re(value))
    imag = as_fraction(sp.im(value))
    return (real, real), (imag, imag)


def complex_coefficient(value: sp.Expr) -> CInterval:
    return complex_point(sp.expand(value))


def polynomial_interval(poly: sp.Poly, box: CInterval) -> CInterval:
    result: CInterval = ((Fraction(0), Fraction(0)), (Fraction(0), Fraction(0)))
    for coefficient in poly.all_coeffs():
        result = complex_add(complex_mul(result, box), complex_coefficient(coefficient))
    return result


def norm_sq_interval(value: CInterval) -> Interval:
    return interval_add(interval_square(value[0]), interval_square(value[1]))


def interval_json(value: Interval) -> list[str]:
    return [str(value[0]), str(value[1])]


def complex_interval_json(value: CInterval) -> dict[str, list[str]]:
    return {"real": interval_json(value[0]), "imaginary": interval_json(value[1])}


def rational_unit_direction(parameter: Fraction) -> sp.Expr:
    s = sp.Rational(parameter.numerator, parameter.denominator)
    return sp.cancel((1 - s**2) / (1 + s**2)) + sp.I * sp.cancel(
        2 * s / (1 + s**2)
    )


def proposed_critical_boxes(derivative: sp.Poly) -> list[CInterval]:
    """Use numerical roots only to propose exact rational isolation boxes."""

    roots = sp.nroots(derivative, n=80, maxsteps=300)
    radius = Fraction(1, 10**10)
    boxes: list[CInterval] = []
    for root in roots:
        real_text, imag_text = str(sp.re(root)), str(sp.im(root))
        real = Fraction(real_text).limit_denominator(10**24)
        imag = Fraction(imag_text).limit_denominator(10**24)
        boxes.append(((real - radius, real + radius), (imag - radius, imag + radius)))
    return boxes


def rouche_root_certificate(poly: sp.Poly, box: CInterval) -> dict[str, str | bool | int]:
    """Prove that the centered disk inscribed in ``box`` has one root."""

    z = poly.gens[0]
    real_center = (box[0][0] + box[0][1]) / 2
    imag_center = (box[1][0] + box[1][1]) / 2
    radius = (box[0][1] - box[0][0]) / 2
    if radius != (box[1][1] - box[1][0]) / 2:
        raise AssertionError("critical isolation box is not square")
    center = (
        sp.Rational(real_center.numerator, real_center.denominator)
        + sp.I * sp.Rational(imag_center.numerator, imag_center.denominator)
    )
    coefficients = [
        sp.expand(sp.diff(poly.as_expr(), z, order).subs(z, center))
        / sp.factorial(order)
        for order in range(poly.degree() + 1)
    ]

    def l1(value: sp.Expr) -> Fraction:
        return abs(as_fraction(sp.re(value))) + abs(as_fraction(sp.im(value)))

    derivative = coefficients[1]
    derivative_lower = max(
        abs(as_fraction(sp.re(derivative))), abs(as_fraction(sp.im(derivative)))
    )
    linear_lower = derivative_lower * radius
    remainder_upper = l1(coefficients[0])
    for order, coefficient in enumerate(coefficients[2:], start=2):
        remainder_upper += l1(coefficient) * radius**order
    if not remainder_upper < linear_lower:
        raise AssertionError((remainder_upper, linear_lower))
    return {
        "disk_center_real": str(real_center),
        "disk_center_imaginary": str(imag_center),
        "disk_radius": str(radius),
        "constant_and_higher_boundary_upper": str(remainder_upper),
        "linear_boundary_lower": str(linear_lower),
        "strict_rouche_inequality": True,
        "root_count_in_open_disk": 1,
    }


def build_result() -> dict[str, Any]:
    z = sp.symbols("z")
    radius = Fraction(999_999, 1_000_000)
    parameters = (
        Fraction(3_705_471, 251_106_715),
        Fraction(440_437_799, 579_901_420),
        Fraction(3_032_911_868, 924_490_473),
        Fraction(-2_623_783_291, 898_185_297),
        Fraction(-540_347_338, 778_985_653),
    )
    scale = sp.Rational(radius.numerator, radius.denominator)
    roots = tuple(scale * rational_unit_direction(parameter) for parameter in parameters)
    polynomial = sp.Poly(sp.expand(sp.prod(z - root for root in roots)), z)
    derivative = sp.Poly(sp.diff(polynomial.as_expr(), z), z)

    root_rows: list[dict[str, Any]] = []
    for index, (parameter, root) in enumerate(zip(parameters, roots, strict=True)):
        norm_sq = sp.cancel(sp.re(root) ** 2 + sp.im(root) ** 2)
        if norm_sq != scale**2 or not norm_sq < 1:
            raise AssertionError((index, norm_sq))
        root_rows.append(
            {
                "root_index": index,
                "half_angle_parameter": str(parameter),
                "real": str(as_fraction(sp.re(root))),
                "imaginary": str(as_fraction(sp.im(root))),
                "squared_modulus": str(as_fraction(norm_sq)),
            }
        )

    boxes = proposed_critical_boxes(derivative)
    if len(boxes) != 4:
        raise AssertionError("quintic derivative did not have four proposed roots")
    for left in range(len(boxes)):
        for right in range(left + 1, len(boxes)):
            left_box, right_box = boxes[left], boxes[right]
            separated = bool(
                left_box[0][1] < right_box[0][0]
                or right_box[0][1] < left_box[0][0]
                or left_box[1][1] < right_box[1][0]
                or right_box[1][1] < left_box[1][0]
            )
            if not separated:
                raise AssertionError(("overlapping critical boxes", left, right))
    critical_rows: list[dict[str, Any]] = []
    for index, box in enumerate(boxes):
        root_certificate = rouche_root_certificate(derivative, box)
        value_box = polynomial_interval(polynomial, box)
        value_norm_sq = norm_sq_interval(value_box)
        critical_rows.append(
            {
                "critical_index": index,
                "critical_point_box": complex_interval_json(box),
                "critical_point_rouche_certificate": root_certificate,
                "exact_derivative_root_count": 1,
                "critical_value_box": complex_interval_json(value_box),
                "critical_value_squared_modulus_interval": interval_json(value_norm_sq),
                "_box": box,
                "_norm": value_norm_sq,
            }
        )

    selected_index = min(range(4), key=lambda index: critical_rows[index]["_norm"][1])
    selected = critical_rows[selected_index]
    selected_norm: Interval = selected["_norm"]
    other_lower = min(
        row["_norm"][0]
        for index, row in enumerate(critical_rows)
        if index != selected_index
    )
    if not selected_norm[1] < other_lower:
        raise AssertionError((selected_norm, other_lower))
    if not selected_norm[1] < 1:
        raise AssertionError("minimum critical value is not inside the unit lemniscate")

    # Dyadic parameters selected from the 16385-point numerical spoke scan.
    waypoint_parameters = {
        0: Fraction(1302, 4096),
        2: Fraction(552, 4096),
        3: Fraction(1386, 4096),
        4: Fraction(648, 4096),
    }
    selected_box: CInterval = selected["_box"]
    waypoint_rows: list[dict[str, Any]] = []
    for root_index, parameter in waypoint_parameters.items():
        root_box = complex_point(roots[root_index])
        waypoint_box = complex_add(
            complex_scale(selected_box, 1 - parameter),
            complex_scale(root_box, parameter),
        )
        value_box = polynomial_interval(polynomial, waypoint_box)
        value_norm_sq = norm_sq_interval(value_box)
        if not 1 < value_norm_sq[0]:
            raise AssertionError((root_index, parameter, value_norm_sq))
        waypoint_rows.append(
            {
                "root_index": root_index,
                "spoke_parameter": str(parameter),
                "waypoint_box": complex_interval_json(waypoint_box),
                "value_squared_modulus_interval": interval_json(value_norm_sq),
                "strict_escape": True,
            }
        )

    public_critical_rows = []
    for row in critical_rows:
        public_critical_rows.append(
            {key: value for key, value in row.items() if not key.startswith("_")}
        )

    result: dict[str, Any] = {
        "schema": "erdos1041-minimum-critical-straight-hub-counterexample/1",
        "status": "exact_counterexample_to_proof_mechanism",
        "claim_ceiling": (
            "Exact counterexample to the assertion that a minimum-modulus "
            "critical point always has two contained straight root spokes. It "
            "is not a counterexample to Erdős #1041 or to curved inverse rays."
        ),
        "witness": {
            "common_radius": str(radius),
            "roots": root_rows,
            "critical_points": public_critical_rows,
            "critical_point_isolation_complete": {
                "derivative_degree": derivative.degree(),
                "pairwise_disjoint_rouche_disks": True,
                "certified_root_count_sum": len(critical_rows),
                "all_derivative_roots_accounted_for": True,
            },
            "selected_minimum_critical_index": selected_index,
            "selected_critical_value_squared_modulus_upper": str(selected_norm[1]),
            "other_critical_value_squared_modulus_lower": str(other_lower),
            "strict_critical_value_ordering": True,
            "unsafe_spoke_waypoints": waypoint_rows,
            "safe_spoke_count_upper_bound": 1,
        },
        "consequence": {
            "eliminated": (
                "Select a critical point of minimum critical-value modulus and "
                "join it to two roots by straight segments."
            ),
            "survives": (
                "The two descending inverse-ray branches at the same first merge, "
                "and selection of a later critical point or another curve."
            ),
        },
        "links": {
            "source_ref": SOURCE_REF,
            "analysis_ref": ANALYSIS_REF,
            "search_ref": SEARCH_REF,
            "research_ref": RESEARCH_REF,
        },
        "sources": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, ANALYSIS_REF),
            source_record(REPO_ROOT, SEARCH_REF),
        ],
    }
    result["receipt_sha256"] = canonical_hash(result)
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = build_result()
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.exists() or args.output.read_text(encoding="utf-8") != rendered:
            raise SystemExit(f"stale or missing receipt: {args.output}")
        print(json.dumps({"status": "ok", "receipt": str(args.output)}))
        return 0
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": result["status"], "receipt": str(args.output)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
