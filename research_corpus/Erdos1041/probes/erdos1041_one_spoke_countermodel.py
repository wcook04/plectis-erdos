#!/usr/bin/env python3
"""Exact unit-circle counterexample to the Erdős #1041 ONE-SPOKE stress test.

For unit complex numbers w_1,...,w_n, ONE-SPOKE asks for an index j such that

    prod_k |t w_j - w_k| <= 1   for every t in [0,1].

The five Gaussian-rational unit points below refute the statement: every
radial spoke has an explicit rational parameter where the squared product is
strictly greater than one.  The points are the unit-circle normalization of
the common-radius E16 origin-spoke witness already checked in the #1041
visibility-overlap source.  This refutes ONE-SPOKE, not the first-merge COVER
hypothesis and not Erdős #1041.
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


SOURCE_REF = "formal_math/probes/erdos1041_one_spoke_countermodel.py"
ORIGIN_CHECKER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/"
    "check_erdos1041_visibility_overlap.py"
)
ORIGIN_NOTE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "VisibilityOverlapReduction.md"
)
ORIGIN_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1041_visibility_overlap_receipt.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/probes/erdos1041_one_spoke_countermodel_receipt.json"
)

GaussianRational = tuple[Fraction, Fraction]

UNIT_ROOTS: tuple[GaussianRational, ...] = (
    (Fraction(1), Fraction(0)),
    (Fraction(-20, 101), Fraction(99, 101)),
    (Fraction(-20, 101), Fraction(-99, 101)),
    (Fraction(-28, 197), Fraction(195, 197)),
    (Fraction(-28, 197), Fraction(-195, 197)),
)

WITNESS_PARAMETERS: tuple[Fraction, ...] = (
    Fraction(339, 1000),
    Fraction(1, 1000),
    Fraction(1, 1000),
    Fraction(1, 500),
    Fraction(1, 500),
)

E16_RADIUS = Fraction(99999, 100000)


def complex_sub(left: GaussianRational, right: GaussianRational) -> GaussianRational:
    return left[0] - right[0], left[1] - right[1]


def complex_mul(left: GaussianRational, right: GaussianRational) -> GaussianRational:
    return (
        left[0] * right[0] - left[1] * right[1],
        left[0] * right[1] + left[1] * right[0],
    )


def complex_scale(scale: Fraction, value: GaussianRational) -> GaussianRational:
    return scale * value[0], scale * value[1]


def norm_sq(value: GaussianRational) -> Fraction:
    return value[0] * value[0] + value[1] * value[1]


def polynomial_value(
    point: GaussianRational, roots: tuple[GaussianRational, ...]
) -> GaussianRational:
    value: GaussianRational = Fraction(1), Fraction(0)
    for root in roots:
        value = complex_mul(value, complex_sub(point, root))
    return value


def polynomial_abs_sq(
    point: GaussianRational, roots: tuple[GaussianRational, ...]
) -> Fraction:
    return norm_sq(polynomial_value(point, roots))


def fraction_record(value: Fraction) -> dict[str, str | float]:
    return {
        "exact": str(value),
        "decimal": float(value),
    }


def exact_countermodel() -> dict[str, Any]:
    if len(set(UNIT_ROOTS)) != 5:
        raise AssertionError("unit-circle roots are not distinct")
    moduli = [norm_sq(root) for root in UNIT_ROOTS]
    if moduli != [Fraction(1)] * 5:
        raise AssertionError(f"non-unit root detected: {moduli}")

    rows: list[dict[str, Any]] = []
    e16_roots = tuple(complex_scale(E16_RADIUS, root) for root in UNIT_ROOTS)
    for index, (root, parameter) in enumerate(
        zip(UNIT_ROOTS, WITNESS_PARAMETERS, strict=True)
    ):
        point = complex_scale(parameter, root)
        value = polynomial_abs_sq(point, UNIT_ROOTS)
        margin = value - 1
        if margin <= 0:
            raise AssertionError(
                f"spoke {index} failed to violate ONE-SPOKE at t={parameter}: {value}"
            )

        scaled_point = complex_scale(parameter, e16_roots[index])
        e16_value = polynomial_abs_sq(scaled_point, e16_roots)
        expected_scaled = E16_RADIUS ** 10 * value
        if e16_value != expected_scaled or e16_value <= 1:
            raise AssertionError(
                f"E16 scaling parity failed on spoke {index}: "
                f"{e16_value} != {expected_scaled}"
            )
        rows.append(
            {
                "spoke_index": index,
                "root": {
                    "real": str(root[0]),
                    "imaginary": str(root[1]),
                },
                "parameter_t": str(parameter),
                "unit_circle_product_abs_sq": fraction_record(value),
                "strict_margin_over_one": fraction_record(margin),
                "e16_open_disk_product_abs_sq": fraction_record(e16_value),
            }
        )

    minimum_value = min(
        Fraction(row["unit_circle_product_abs_sq"]["exact"]) for row in rows
    )
    minimum_e16_value = min(
        Fraction(row["e16_open_disk_product_abs_sq"]["exact"]) for row in rows
    )
    if minimum_value <= 1 or minimum_e16_value <= 1:
        raise AssertionError("strict family margin was lost")

    return {
        "unit_circle_roots": [
            {"real": str(root[0]), "imaginary": str(root[1])}
            for root in UNIT_ROOTS
        ],
        "all_roots_have_exact_squared_modulus_one": True,
        "all_roots_distinct": True,
        "spoke_count": len(rows),
        "unsafe_spoke_count": sum(
            Fraction(row["unit_circle_product_abs_sq"]["exact"]) > 1 for row in rows
        ),
        "witnesses": rows,
        "minimum_unit_circle_witness_value_abs_sq": fraction_record(minimum_value),
        "e16_radius": str(E16_RADIUS),
        "minimum_e16_witness_value_abs_sq": fraction_record(minimum_e16_value),
        "explicit_radial_family": {
            "radius_interval": f"[{E16_RADIUS}, 1)",
            "statement": (
                "For every rational or real radius rho in this interval, the "
                "five roots rho*w_j lie in the open unit disk and every radial "
                "root-to-origin spoke has the same listed parameter t_j with "
                "|prod_k(t_j rho w_j-rho w_k)|^2 = "
                "rho^10 |prod_k(t_j w_j-w_k)|^2 > 1."
            ),
            "endpoint_check": "E16_RADIUS^10 * every unit witness value > 1",
        },
        "open_perturbation_family": (
            "All five inequalities are strict at finitely many fixed parameters. "
            "Continuity in the five unit-circle angles therefore gives an open "
            "neighborhood of unit-circle configurations with no safe radial spoke."
        ),
        "claim_effect": (
            "ONE-SPOKE is false for n=5. This removes the proposed unit-circle "
            "equality-stratum stress statement. It does not refute first-merge "
            "COVER, because the countermodel concerns the origin/level-one radial "
            "spokes rather than intrinsic distance in the first-merge component."
        ),
    }


def build_receipt() -> dict[str, Any]:
    countermodel = exact_countermodel()
    contract = build_experiment_contract(
        problem_id="erdos_1041",
        target_statement=(
            "For roots in the open unit disk, join two roots by a curve of "
            "length less than two inside the open lemniscate."
        ),
        claim_ceiling=(
            "Exact counterexample to the auxiliary unit-circle ONE-SPOKE "
            "statement and an explicit open family; no counterexample to COVER "
            "or Erdős #1041."
        ),
        hypothesis_id="unit_circle_one_spoke",
        hypothesis_statement=(
            "For any finite unit-circle configuration there is one root direction "
            "whose full radial product stays at most one for every t in [0,1]."
        ),
        probe_id="exact_gaussian_rational_one_spoke_countermodel",
        probe_question=(
            "Does the normalized E16 common-radius witness leave even one safe "
            "unit-circle radial spoke?"
        ),
        computation=(
            "Evaluate the squared product exactly in Fraction arithmetic at one "
            "rational parameter on each of five Gaussian-rational unit directions, "
            "then verify exact scaling parity with the original open-disk E16 witness."
        ),
        falsifier=(
            "A unit-circle configuration with one exact product value greater than "
            "one on every root direction."
        ),
        stop_condition=(
            "Stop after all five exact strict inequalities and the common-radius "
            "family endpoint are verified."
        ),
        survival_consequence=(
            "If one spoke remained safe, ONE-SPOKE would survive this strongest "
            "stored common-radius witness."
        ),
        falsification_consequence=(
            "Retire ONE-SPOKE as an open producer; preserve COVER at the first-merge "
            "level as a distinct, strictly more flexible hypothesis."
        ),
        consumer_ref=ORIGIN_NOTE_REF,
        analysis_refs=[ORIGIN_NOTE_REF, ORIGIN_CHECKER_REF, ORIGIN_RECEIPT_REF],
        source_refs=[SOURCE_REF, ORIGIN_NOTE_REF, ORIGIN_CHECKER_REF, ORIGIN_RECEIPT_REF],
        result_status="finite_counterexample",
        result_summary=countermodel["claim_effect"],
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos1041-one-spoke-countermodel/1",
        "status": "verified_exact_unit_circle_countermodel",
        "experiment_contract": contract,
        "countermodel": countermodel,
        "landed_origin_snapshot": {
            "commit": "c77898fbb9f329f9f86d4801102e9c6d710ccfd2",
            "note_sha256": "b373871efacea2492d96189b0f390240ba636bc2f3354fa74de31627af044edc",
            "checker_sha256": "95dbf7f8154c3b50fba3265b1308ef34f578e8a9d13cf4326acfe79bc1ac65b2",
            "receipt_sha256": "7d40c539fd3ed5f03eabbcde4754fa00803631fde9c2931275bb038f02ff7712",
            "boundary": (
                "The source note is concurrently owned and may carry later "
                "worktree edits. These hashes bind the exact landed evidence "
                "snapshot from which the normalized countermodel is derived."
            ),
        },
        "source_records": [
            source_record(REPO_ROOT, SOURCE_REF),
        ],
    }


def emit(payload: dict[str, Any], output: Path, check: bool) -> int:
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
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
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    return emit(build_receipt(), args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
