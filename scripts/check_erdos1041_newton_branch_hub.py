#!/usr/bin/env python3
"""Exact certificate killing the metric-selected Newton hub in Erdős #1041.

The balanced quintic already used to refute straight nearest-root spokes has a
simple critical point at zero.  This checker proves that the two inverse-ray
branches descending from that point have combined length greater than two.

All decisive comparisons use rational arithmetic.  SymPy's exact root-count
and real-root isolation algorithms are used only on polynomials over ``QQ``;
floating point is not part of the certificate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Any

import sympy as sp

from system.lib.formal_math_experiment_contract import (
    build_experiment_contract,
    source_record,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
SCRIPT_PATH = Path(__file__).resolve()
SOURCE_REF = str(SCRIPT_PATH.relative_to(REPO_ROOT))
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "NewtonBranchHubCounterexampleComputationalLab.md"
)
SEARCH_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "scripts/search_counterexample.py"
)
RESEARCH_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "research_packet.json"
)
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "CriticalTwoRootProximity.lean"
)
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "erdos1041_newton_branch_hub_counterexample_receipt.json"
)


Interval = tuple[Fraction, Fraction]


def canonical_hash(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def as_fraction(value: sp.Rational) -> Fraction:
    return Fraction(int(value.p), int(value.q))


def interval_mul(left: Interval, right: Interval) -> Interval:
    products = (
        left[0] * right[0],
        left[0] * right[1],
        left[1] * right[0],
        left[1] * right[1],
    )
    return min(products), max(products)


def polynomial_interval(poly: sp.Poly, interval: Interval) -> Interval:
    """Horner evaluation of a rational polynomial on a rational interval."""

    result: Interval = (Fraction(0), Fraction(0))
    for coefficient in poly.all_coeffs():
        result = interval_mul(result, interval)
        value = as_fraction(coefficient)
        result = result[0] + value, result[1] + value
    return result


def ratio_interval(interval: Interval, denominator: Fraction) -> Interval:
    if denominator == 0:
        raise ZeroDivisionError
    values = interval[0] / denominator, interval[1] / denominator
    return min(values), max(values)


def interval_json(interval: Interval) -> list[str]:
    return [str(interval[0]), str(interval[1])]


def complex_norm_sq(value: sp.Expr) -> sp.Rational:
    real = sp.re(value)
    imag = sp.im(value)
    return sp.cancel(real * real + imag * imag)


def boundary_edge_certificates(
    polynomial: sp.Poly, critical_value: sp.Rational
) -> list[dict[str, Any]]:
    """Prove a rectangle avoids every level ``s*v``, ``1/2 <= s <= 1``."""

    x, y = sp.symbols("x y", real=True)
    z = polynomial.gens[0]
    value = sp.expand(polynomial.as_expr().subs(z, x + sp.I * y))
    real_part = sp.expand(sp.re(value))
    imaginary_part = sp.expand(sp.im(value))
    x_bounds = (sp.Rational(-4, 5), sp.Rational(1, 5))
    y_bounds = (sp.Rational(-4, 5), sp.Rational(4, 5))
    edges = (
        ("left", x, x_bounds[0], y, y_bounds),
        ("right", x, x_bounds[1], y, y_bounds),
        ("bottom", y, y_bounds[0], x, x_bounds),
        ("top", y, y_bounds[1], x, x_bounds),
    )
    rows: list[dict[str, Any]] = []
    denominator = as_fraction(critical_value)
    for name, fixed_variable, fixed_value, parameter, bounds in edges:
        substitution = {fixed_variable: fixed_value}
        imaginary_poly = sp.Poly(imaginary_part.subs(substitution), parameter)
        real_poly = sp.Poly(real_part.subs(substitution), parameter)
        root_rows: list[dict[str, Any]] = []
        for sympy_interval, multiplicity in sp.intervals(
            imaginary_poly, eps=sp.Rational(1, 10**24)
        ):
            lower, upper = sympy_interval
            if upper < bounds[0] or bounds[1] < lower:
                continue
            clipped = max(lower, bounds[0]), min(upper, bounds[1])
            rational_interval = as_fraction(clipped[0]), as_fraction(clipped[1])
            value_interval = polynomial_interval(real_poly, rational_interval)
            level_ratio_interval = ratio_interval(value_interval, denominator)
            avoids = bool(
                level_ratio_interval[1] < Fraction(1, 2)
                or Fraction(1) < level_ratio_interval[0]
            )
            if not avoids:
                raise AssertionError((name, rational_interval, level_ratio_interval))
            root_rows.append(
                {
                    "parameter_interval": interval_json(rational_interval),
                    "multiplicity": int(multiplicity),
                    "level_ratio_interval": interval_json(level_ratio_interval),
                    "avoids_closed_half_to_one_segment": True,
                }
            )
        rows.append(
            {
                "edge": name,
                "fixed_coordinate": str(as_fraction(fixed_value)),
                "imaginary_part_real_root_count_on_edge": sum(
                    row["multiplicity"] for row in root_rows
                ),
                "real_value_intersections": root_rows,
            }
        )
    return rows


def rouche_waypoint_certificate(
    level_polynomial: sp.Poly, center: sp.Expr, radius: Fraction
) -> dict[str, Any]:
    """Certify one level root in a rational disk by a linear Rouché bound."""

    z = level_polynomial.gens[0]
    coefficients = [
        sp.expand(sp.diff(level_polynomial.as_expr(), z, order).subs(z, center))
        / sp.factorial(order)
        for order in range(level_polynomial.degree() + 1)
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
        "center": {
            "real": str(as_fraction(sp.re(center))),
            "imaginary": str(as_fraction(sp.im(center))),
        },
        "radius": str(radius),
        "linear_term_boundary_lower_bound": str(linear_lower),
        "constant_and_higher_terms_boundary_upper_bound": str(remainder_upper),
        "strict_rouche_inequality": True,
        "root_count_in_open_disk": 1,
    }


def build_result() -> dict[str, Any]:
    z, s = sp.symbols("z s")
    p = sp.Rational(999, 1000)
    a = sp.Rational(901, 902) * p
    roots = (
        a,
        sp.I * p,
        -sp.I * p,
        p * (-451 + 780 * sp.I) / 901,
        p * (-451 - 780 * sp.I) / 901,
    )
    polynomial = sp.Poly(sp.expand(sp.prod(z - root for root in roots)), z)
    critical_value = polynomial.eval(0)
    derivative = sp.Poly(sp.diff(polynomial.as_expr(), z), z)
    if derivative.eval(0) != 0 or sp.diff(polynomial.as_expr(), z, 2).subs(z, 0) == 0:
        raise AssertionError("zero is not a simple critical point")
    if not abs(critical_value) < 1:
        raise AssertionError("critical point is outside the strict lemniscate")
    if any(not complex_norm_sq(root) < 1 for root in roots):
        raise AssertionError("a root is outside the open unit disk")

    # The only critical level on the oriented segment 0 < s <= 1 is s=1.
    discriminant = sp.Poly(
        sp.resultant(
            derivative.as_expr(), polynomial.as_expr() - s * critical_value, z
        ),
        s,
    )
    quotient = sp.Poly(sp.cancel(discriminant.as_expr() / (s - 1)), s)
    if discriminant.eval(1) != 0 or quotient.eval(1) == 0:
        raise AssertionError("the critical-level factor at one is not simple")
    if quotient.count_roots(0, 1) != 0:
        raise AssertionError("another critical value lies on the descending ray")

    rectangle_lower = sp.Rational(-4, 5) - sp.I * sp.Rational(4, 5)
    rectangle_upper = sp.Rational(1, 5) + sp.I * sp.Rational(4, 5)
    hub_level = sp.Poly(polynomial.as_expr() - critical_value, z)
    half_level = sp.Poly(polynomial.as_expr() - critical_value / 2, z)
    hub_count = int(hub_level.count_roots(rectangle_lower, rectangle_upper))
    half_count = int(half_level.count_roots(rectangle_lower, rectangle_upper))
    if hub_count != 2 or half_count != 2:
        raise AssertionError((hub_count, half_count))
    edge_rows = boundary_edge_certificates(polynomial, critical_value)

    waypoint = -sp.Rational(1398549, 10_000_000) + sp.I * sp.Rational(
        6823938, 10_000_000
    )
    waypoint_radius = Fraction(1, 1_000_000)
    waypoint_certificate = rouche_waypoint_certificate(
        half_level, waypoint, waypoint_radius
    )
    conjugate_certificate = rouche_waypoint_certificate(
        half_level, sp.conjugate(waypoint), waypoint_radius
    )

    radial_lower = Fraction(696, 1000)
    root_distance_lower = Fraction(346, 1000)
    if not complex_norm_sq(waypoint) > sp.Rational(
        radial_lower.numerator**2, radial_lower.denominator**2
    ):
        raise AssertionError("waypoint radial lower bound failed")
    root_distance_rows = []
    for index, root in enumerate(roots):
        squared_distance = complex_norm_sq(waypoint - root)
        if not squared_distance > sp.Rational(
            root_distance_lower.numerator**2, root_distance_lower.denominator**2
        ):
            raise AssertionError((index, squared_distance))
        root_distance_rows.append(
            {
                "root_index": index,
                "squared_distance": str(squared_distance),
                "strictly_greater_than": str(root_distance_lower**2),
            }
        )
    one_branch_lower = radial_lower + root_distance_lower - 2 * waypoint_radius
    combined_lower = 2 * one_branch_lower
    if not combined_lower > 2:
        raise AssertionError("combined branch lower bound does not exceed two")

    result_summary = (
        "For the exact balanced quintic, the two descending inverse-ray branches "
        "from the metric critical point zero each pass through a certified half-level "
        "waypoint disk. Triangle inequalities force each branch length above "
        f"{one_branch_lower}, hence their combined length above {combined_lower}>2. "
        "This eliminates the metric-selected Newton-branch hub mechanism, not "
        "Erdős #1041 or hubs based at a different critical point."
    )
    payload = {
        "schema": "erdos1041-newton-branch-hub-counterexample/1",
        "problem_id": "erdos_1041",
        "result_status": "exact_metric_selected_newton_hub_mechanism_elimination",
        "result_summary": result_summary,
        "claim_ceiling": (
            "This proves that replacing the two metric-selected straight spokes by "
            "the canonical descending inverse-ray branches at that same critical "
            "point can exceed length two. It does not exclude another critical hub, "
            "another curved path, or the full Erdős #1041 statement."
        ),
        "exact_configuration": {
            "p": str(as_fraction(p)),
            "a": str(as_fraction(a)),
            "roots": [str(root) for root in roots],
            "polynomial_coefficients_descending": [
                str(coefficient) for coefficient in polynomial.all_coeffs()
            ],
            "critical_point": "0",
            "critical_value": str(critical_value),
            "critical_value_modulus_lt_one": True,
            "all_roots_in_open_unit_disk": True,
        },
        "descending_ray_regular_value_certificate": {
            "resultant_factorization": str(sp.factor(discriminant.as_expr())),
            "distinguished_critical_level": "s=1",
            "other_real_critical_level_count_in_open_zero_one": 0,
            "meaning": (
                "The two local branches issuing from zero continue along the "
                "oriented value ray to polynomial roots without another critical level."
            ),
        },
        "half_level_branch_identification": {
            "parameter_interval": ["1/2", "1"],
            "rectangle": {
                "real": ["-4/5", "1/5"],
                "imaginary": ["-4/5", "4/5"],
            },
            "root_count_at_hub_level": hub_count,
            "root_count_at_half_level": half_count,
            "boundary_real_value_intersections": edge_rows,
            "boundary_avoids_all_levels_in_closed_half_to_one": True,
            "meaning": (
                "The rectangle contains only the double root zero at s=1 and "
                "exactly the conjugate waypoint pair at s=1/2; no root crosses "
                "its boundary during the homotopy."
            ),
        },
        "waypoint_root_certificates": [
            waypoint_certificate,
            conjugate_certificate,
        ],
        "length_lower_bound": {
            "waypoint_modulus_strict_lower_bound": str(radial_lower),
            "waypoint_to_every_root_strict_lower_bound": str(root_distance_lower),
            "waypoint_disk_radius": str(waypoint_radius),
            "root_distance_squared_certificates": root_distance_rows,
            "one_branch_strict_lower_bound": str(one_branch_lower),
            "combined_two_branch_strict_lower_bound": str(combined_lower),
            "combined_two_branch_length_gt_two": True,
        },
        "lemniscate_containment": {
            "identity": "f(z(s))=s*f(0), 0<=s<=1",
            "strict_bound": "|f(z(s))|<=|f(0)|<1",
            "holds_for_both_branches": True,
        },
        "consequence_reconciliation": {
            "delta_class": "counterexample_or_no_go",
            "authority": "exact_algebraic_topological_checker",
            "claim_ceiling": (
                "The same-critical-point Newton repair is eliminated; another "
                "critical hub and the original Erdős problem remain open."
            ),
            "candidate_count": 10,
            "decision_count": 10,
            "decisions": [
                {
                    "file": "state/formal_math_research_operations/pilots/ramanujan_challenge/certificate_search_receipts/ramanujan_2_1_proof_review_v1.json",
                    "decision": "outside_scope",
                    "reason": "Only the generic proof_location schema key matched; there is no shared mathematical object or claim.",
                },
                {
                    "file": "state/formal_math_research_operations/pilots/ramanujan_challenge/certificate_search_receipts/ramanujan_3_1_toric_tame_symbol_table_candidate_v1.json",
                    "decision": "outside_scope",
                    "reason": "Only the generic root_rows validator key matched; the Ramanujan certificate has no Newton-hub consequence.",
                },
                *[
                    {
                        "file": (
                            "state/formal_math_research_operations/type_b_handoffs/"
                            "erdos249_digit_reduction_six_wave13_2026_07_24/"
                            f"{prefix}_{slug}_manifest.json"
                        ),
                        "decision": "outside_scope",
                        "reason": (
                            "Only generic negative_results/open_producers container "
                            "keys matched; Erdős 249 has no lemniscate or Newton-flow edge."
                        ),
                    }
                    for prefix, slug in (
                        ("01", "digital_weyl_transport"),
                        ("02", "cototient_renormalization"),
                        ("03", "probabilistic_totient_digits"),
                        ("04", "signed_hermite_pade"),
                        ("05", "prime_support_positivity"),
                        ("06", "subword_complexity"),
                    )
                ],
                {
                    "file": "state/formal_math_research_operations/type_b_handoffs/paper_expert_questions_2026_08_01/09_erdos1041_manifest.json",
                    "decision": "verified_no_change",
                    "reason": (
                        "The manifest already delegates the live proof map to the exact "
                        "research_packet.json source reference; it contains no duplicated "
                        "claim text to stale."
                    ),
                },
                {
                    "file": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/research_packet.json",
                    "decision": "outside_scope",
                    "reason": (
                        "Only generic research-packet container keys matched; the q-order "
                        "problem has no inverse-ray or lemniscate implication."
                    ),
                },
            ],
            "updated_authority_surfaces": [
                ANALYSIS_REF,
                RESEARCH_REF,
            ],
            "surviving_residual": (
                "Prove a selection theorem over critical points that controls the "
                "minimum total length of two descending inverse-ray branches, or "
                "replace local hubs by global Reeb/component geometry."
            ),
        },
        "experiment_contract": build_experiment_contract(
            problem_id="erdos_1041",
            target_statement=(
                "Find two roots joined by a curve of length less than two inside "
                "the strict unit lemniscate."
            ),
            claim_ceiling=(
                "The exact quintic eliminates only the two canonical descending "
                "branches at the metric-selected critical point; other hubs and "
                "the original problem remain open."
            ),
            hypothesis_id="metric_selected_critical_point_newton_hub",
            hypothesis_statement=(
                "At the critical point supplied by the critical-pair metric theorem, "
                "the two descending inverse-ray branches reach roots with combined "
                "length less than two."
            ),
            probe_id="exact_half_level_waypoint_branch_lower_bound",
            probe_question=(
                "Can a certified intermediate point on each canonical descending "
                "branch force the total arc length above two?"
            ),
            computation=(
                "Use an exact resultant to exclude intervening critical levels, "
                "exact rectangle root counts plus boundary isolation to identify "
                "the branches, a rational Rouché disk at level f(0)/2, and exact "
                "triangle-inequality lower bounds to every root."
            ),
            falsifier=(
                "A boundary crossing for a level s*f(0), an additional critical "
                "level on 0<s<1, failure of the waypoint Rouché inequality, or a "
                "combined exact length lower bound at most two."
            ),
            stop_condition=(
                "Once the two hub branches are exactly identified and their combined "
                "lower bound is strictly above two, retire this same-critical-point "
                "Newton repair and test selection among other critical hubs."
            ),
            survival_consequence=(
                "If the lower bound did not cross two, seek an upper bound comparing "
                "inverse-ray length with the critical-pair metric distances."
            ),
            falsification_consequence=(
                "The metric theorem and Newton containment cannot be coupled at an "
                "arbitrary supplied critical point; any hub proof needs a new "
                "critical-point selection theorem or global Reeb geometry."
            ),
            consumer_ref=RESEARCH_REF,
            analysis_refs=[ANALYSIS_REF],
            source_refs=[SOURCE_REF, SEARCH_REF, LEAN_REF],
            result_status="exact_one_way_result",
            result_summary=result_summary,
            progress_class="mechanism_eliminated",
            decision_basis=(
                "The exact combined branch-length lower bound 520999/250000 "
                "is strictly greater than two."
            ),
            next_analytic_target=(
                "Select a different critical point by controlling the sum of its "
                "two descending inverse-ray lengths across the critical-point tree."
            ),
        ),
        "sources": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, SEARCH_REF),
            source_record(REPO_ROOT, LEAN_REF),
            source_record(REPO_ROOT, ANALYSIS_REF),
            source_record(REPO_ROOT, RESEARCH_REF),
        ],
    }
    return {**payload, "receipt_payload_sha256": canonical_hash(payload)}


def emit(result: dict[str, Any], output: Path, check: bool) -> int:
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    output = output.resolve()
    if check:
        if not output.exists() or output.read_text(encoding="utf-8") != rendered:
            print(f"stale receipt: {output}")
            return 1
        print(json.dumps({"status": "current", "output": str(output)}))
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(output)}))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    return emit(build_result(), args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
