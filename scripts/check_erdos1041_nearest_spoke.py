#!/usr/bin/env python3
"""Exact certificate for the Erdős #1041 unique-nearest spoke no-go."""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
)


SOURCE_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "NearestSpokeCounterexampleComputationalLab.md"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "CriticalTwoRootProximity.lean"
)
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "erdos1041_nearest_spoke_counterexample_receipt.json"
)

RationalComplex = tuple[Fraction, Fraction]


def rc_add(left: RationalComplex, right: RationalComplex) -> RationalComplex:
    return left[0] + right[0], left[1] + right[1]


def rc_mul(left: RationalComplex, right: RationalComplex) -> RationalComplex:
    return (
        left[0] * right[0] - left[1] * right[1],
        left[0] * right[1] + left[1] * right[0],
    )


def rc_neg(value: RationalComplex) -> RationalComplex:
    return -value[0], -value[1]


def rc_sub(left: RationalComplex, right: RationalComplex) -> RationalComplex:
    return rc_add(left, rc_neg(right))


def rc_norm_sq(value: RationalComplex) -> Fraction:
    return value[0] * value[0] + value[1] * value[1]


def rc_inv(value: RationalComplex) -> RationalComplex:
    denominator = rc_norm_sq(value)
    if denominator == 0:
        raise ZeroDivisionError("zero rational-complex inverse")
    return value[0] / denominator, -value[1] / denominator


def encode_fraction(value: Fraction) -> dict[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


def encode_complex(value: RationalComplex) -> dict[str, dict[str, int]]:
    return {"real": encode_fraction(value[0]), "imaginary": encode_fraction(value[1])}


def build_result() -> dict[str, object]:
    p = Fraction(999, 1000)
    a = Fraction(901, 902) * p
    u_plus = (Fraction(-451, 901), Fraction(780, 901))
    u_minus = (Fraction(-451, 901), Fraction(-780, 901))
    roots: list[RationalComplex] = [
        (a, Fraction(0)),
        (Fraction(0), p),
        (Fraction(0), -p),
        (p * u_plus[0], p * u_plus[1]),
        (p * u_minus[0], p * u_minus[1]),
    ]

    reciprocal_sum = (Fraction(0), Fraction(0))
    for root in roots:
        reciprocal_sum = rc_add(reciprocal_sum, rc_inv(root))
    if reciprocal_sum != (0, 0):
        raise AssertionError(("critical balance failed", reciprocal_sum))

    norm_squares = [rc_norm_sq(root) for root in roots]
    if not all(norm_squares[0] < value for value in norm_squares[1:]):
        raise AssertionError(("nearest root is not unique", norm_squares))
    if not all(value < 1 for value in norm_squares):
        raise AssertionError(("root outside open unit disk", norm_squares))

    spoke_point = (a / 10, Fraction(0))
    polynomial_value = (Fraction(1), Fraction(0))
    for root in roots:
        polynomial_value = rc_mul(polynomial_value, rc_sub(spoke_point, root))
    if polynomial_value[1] != 0:
        raise AssertionError(("conjugate product not real", polynomial_value))
    spoke_abs = abs(polynomial_value[0])
    if not 1 < spoke_abs:
        raise AssertionError(("spoke does not escape", spoke_abs))

    result_summary = (
        "An exact balanced five-root polynomial has a unique nearest root to "
        "the critical point 0, yet its straight spoke leaves |f|<1 at one "
        "tenth of the root radius. This falsifies the two-nearest straight-"
        "spoke completion of the checked metric theorem."
    )
    return {
        "schema": "erdos1041-nearest-spoke-exact-counterexample/1",
        "claim_ceiling": (
            "This is a counterexample to one straight-spoke completion, not to "
            "Erdős #1041 and not to curved descending paths."
        ),
        "parameters": {
            "p": encode_fraction(p),
            "a": encode_fraction(a),
            "u_plus": encode_complex(u_plus),
            "u_minus": encode_complex(u_minus),
        },
        "roots": [encode_complex(root) for root in roots],
        "exact_checks": {
            "pythagorean_identity": {
                "left": 451**2 + 780**2,
                "right": 901**2,
                "holds": 451**2 + 780**2 == 901**2,
            },
            "reciprocal_sum": encode_complex(reciprocal_sum),
            "critical_at_origin": True,
            "root_norm_squares": [encode_fraction(value) for value in norm_squares],
            "unique_nearest_root_index": 0,
            "all_roots_strictly_inside_unit_disk": True,
            "spoke_parameter": encode_fraction(Fraction(1, 10)),
            "spoke_point": encode_complex(spoke_point),
            "polynomial_value": encode_complex(polynomial_value),
            "polynomial_abs": encode_fraction(spoke_abs),
            "polynomial_abs_exceeds_one": True,
            "excess_numerator_at_common_denominator": (
                spoke_abs.numerator - spoke_abs.denominator
            ),
        },
        "mechanism_effect": (
            "The proof of exists_two_roots_dist_sum_le_two_mul_geomMean selects "
            "a nearest root and a second-nearest root. Here the nearest root is "
            "unique and its spoke is unsafe, so the selected broken straight "
            "line through the critical point cannot stay in the lemniscate."
        ),
        "experiment_contract": build_experiment_contract(
            problem_id="erdos_1041",
            target_statement=(
                "Find two roots joined by a curve of length less than 2 inside "
                "the strict unit lemniscate of a monic polynomial with roots "
                "in the open unit disk."
            ),
            claim_ceiling=(
                "An exact counterexample to the nearest-root straight-spoke "
                "completion does not disprove the Erdős problem."
            ),
            hypothesis_id="two_nearest_straight_spokes_are_safe",
            hypothesis_statement=(
                "At the critical point used by the geometric-mean metric theorem, "
                "the nearest and second-nearest roots can be joined to the "
                "critical point by straight segments contained in |f|<1."
            ),
            probe_id="balanced_rational_unique_nearest_spoke",
            probe_question=(
                "Can reciprocal balance, unique nearest-root selection, and an "
                "unsafe straight spoke occur simultaneously?"
            ),
            computation=(
                "Construct five rational-complex roots with exact reciprocal "
                "sum zero, compare their rational squared norms, and evaluate "
                "the factored polynomial exactly at one tenth of the unique "
                "nearest root."
            ),
            falsifier=(
                "A balanced configuration with a unique nearest root whose "
                "straight spoke contains a point where |f|>1."
            ),
            stop_condition=(
                "At the first exact unique-nearest unsafe-spoke witness, retire "
                "the two-nearest straight-spoke completion and return to curved "
                "branch selection, collar stability, or the Reeb decomposition."
            ),
            survival_consequence=(
                "If unique-nearest spokes were always safe, the checked metric "
                "pair theorem would have a direct containment route."
            ),
            falsification_consequence=(
                "The metric pair cannot be converted into the required path by "
                "using its two straight spokes; a curved/topological producer is "
                "essential."
            ),
            consumer_ref=CONSUMER_REF,
            analysis_refs=[ANALYSIS_REF],
            source_refs=[SOURCE_REF],
            result_status="exact_one_way_result",
            result_summary=result_summary,
        ),
        "source": source_record(REPO_ROOT, SOURCE_REF),
    }


def emit(result: dict[str, object], output: Path, check: bool) -> int:
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    output = output.resolve()
    if check:
        if not output.exists() or output.read_text(encoding="utf-8") != rendered:
            print(f"stale receipt: {output}", file=sys.stderr)
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
