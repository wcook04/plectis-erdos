#!/usr/bin/env python3
"""Reduce Zudilin first-appearance residues to a bordered null-vector form."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any

import sympy as sp


REPO_ROOT = Path(__file__).resolve().parents[5]
SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(REPO_ROOT))
sys.path.insert(0, str(SCRIPT_DIR))

from check_zudilin_residual_border_charge import residual_exponent  # noqa: E402
from check_zudilin_scalar_content import mu, p  # noqa: E402
from system.lib.formal_math_bordered_determinant import (  # noqa: E402
    bordered_first_order_coefficient,
)
from system.lib.formal_math_cyclotomic_local import CyclotomicLocalRing  # noqa: E402
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)
from zudilin_cyclotomic_local import associated_graded_first_appearance  # noqa: E402


SOURCE_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
BORDER_ENGINE_REF = "system/lib/formal_math_bordered_determinant.py"
LOCAL_ENGINE_REF = "system/lib/formal_math_cyclotomic_local.py"
LOCAL_ADAPTER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/"
    "zudilin_cyclotomic_local.py"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "ZudilinFirstAppearanceBorderFormLab.md"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "AdelicHeightBridge.lean"
)
PHI5_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_phi5_associated_graded_receipt.json"
)
INPUT_RECEIPTS = [
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_phi3_associated_graded_receipt.json",
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_phi4_associated_graded_receipt.json",
    PHI5_RECEIPT_REF,
]
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_first_appearance_border_form_receipt.json"
)
RAW_SCHEMA = "erdos1049-zudilin-first-appearance-border-form/1"


def _parse_polynomial(text: str) -> sp.Poly:
    return sp.Poly(sp.sympify(text, locals={"p": p}), p, domain=sp.QQ)


def _border_record(result: dict[str, Any]) -> dict[str, Any]:
    cyclotomic_index = int(result["cyclotomic_index"])
    rank = int(result["rank"])
    if rank != 2 * cyclotomic_index + 1:
        raise ValueError("result is not at first appearance")
    ring = CyclotomicLocalRing(p, cyclotomic_index, precision=1)
    coefficient_domain = sp.QQ.poly_ring(mu)
    cyclotomic = sp.Poly(
        ring.cyclotomic.as_expr(),
        p,
        domain=coefficient_domain,
    )
    primitive_records = result["primitive_row_residues"]
    units = [_parse_polynomial(row["scalar_unit_residue"]) for row in primitive_records]
    inverse_units = [
        ring.invert_unit_mod_cyclotomic(unit)
        for unit in units[:rank]
    ]

    def reduce_residue(expression: sp.Expr) -> sp.Expr:
        return sp.Poly(
            sp.expand(expression),
            p,
            domain=coefficient_domain,
        ).rem(cyclotomic).as_expr()

    coefficients = []
    weights = []
    for row in range(rank):
        coefficient_row = []
        weight_row = []
        for column in range(rank):
            moment_index = row + column
            source = primitive_records[moment_index]
            a_residue = _parse_polynomial(source["a_residue"])
            if moment_index >= cyclotomic_index and not a_residue.is_zero:
                raise AssertionError("minimum-support moment retains a mu coefficient")
            primitive_moment = (
                a_residue.as_expr() * mu
                - _parse_polynomial(source["b_residue"]).as_expr()
                - _parse_polynomial(source["c_residue"]).as_expr()
            )
            coefficient = reduce_residue(
                primitive_moment
                * units[moment_index].as_expr()
                * inverse_units[row].as_expr()
                * inverse_units[column].as_expr()
            )
            coefficient_row.append(coefficient)
            weight_row.append(residual_exponent(cyclotomic_index, row, column))
        coefficients.append(coefficient_row)
        weights.append(weight_row)

    low = list(range(cyclotomic_index))
    positive = list(range(cyclotomic_index, rank))
    cross_forward = [
        [
            coefficients[row][column] if weights[row][column] == 0 else sp.Integer(0)
            for column in positive
        ]
        for row in low
    ]
    cross_backward = [
        [
            coefficients[row][column] if weights[row][column] == 0 else sp.Integer(0)
            for column in low
        ]
        for row in positive
    ]
    border = [
        [
            coefficients[row][column] if weights[row][column] == 1 else sp.Integer(0)
            for column in positive
        ]
        for row in positive
    ]
    bordered = bordered_first_order_coefficient(
        cross_forward,
        cross_backward,
        border,
        one=sp.Integer(1),
        zero=sp.Integer(0),
        normalize=reduce_residue,
        is_zero=lambda value: value == 0,
    )
    expected = reduce_residue(sp.sympify(result["signed_leading_residue"], locals={"p": p}))

    left_null = [
        reduce_residue(
            sum(
                bordered.left_cofactor_vector[row] * cross_backward[row][column]
                for row in range(cyclotomic_index + 1)
            )
        )
        for column in range(cyclotomic_index)
    ]
    right_null = [
        reduce_residue(
            sum(
                cross_forward[row][column] * bordered.right_cofactor_vector[column]
                for column in range(cyclotomic_index + 1)
            )
        )
        for row in range(cyclotomic_index)
    ]
    symmetric_cross_blocks = all(
        reduce_residue(cross_forward[row][column] - cross_backward[column][row]) == 0
        for row in range(cyclotomic_index)
        for column in range(cyclotomic_index + 1)
    )
    symmetric_border = all(
        reduce_residue(border[row][column] - border[column][row]) == 0
        for row in range(cyclotomic_index + 1)
        for column in range(cyclotomic_index + 1)
    )
    cofactor_vectors_equal = all(
        reduce_residue(left - right) == 0
        for left, right in zip(
            bordered.left_cofactor_vector,
            bordered.right_cofactor_vector,
        )
    )
    endpoint_support_only = (
        bordered.right_cofactor_vector[0] != 0
        and bordered.right_cofactor_vector[-1] != 0
        and all(value == 0 for value in bordered.right_cofactor_vector[1:-1])
    )
    endpoint_quadratic_residue = reduce_residue(
        (-1) ** cyclotomic_index
        * (
            bordered.right_cofactor_vector[0] ** 2 * border[0][0]
            + bordered.right_cofactor_vector[0]
            * bordered.right_cofactor_vector[-1]
            * border[0][-1]
            + bordered.right_cofactor_vector[-1]
            * bordered.right_cofactor_vector[0]
            * border[-1][0]
            + bordered.right_cofactor_vector[-1] ** 2 * border[-1][-1]
        )
    )
    top_left_contribution = reduce_residue(
        bordered.right_cofactor_vector[0] ** 2 * border[0][0]
    )
    cross_contribution = reduce_residue(
        bordered.right_cofactor_vector[0]
        * bordered.right_cofactor_vector[-1]
        * (border[0][-1] + border[-1][0])
    )
    bottom_right_contribution = reduce_residue(
        bordered.right_cofactor_vector[-1] ** 2 * border[-1][-1]
    )
    cross_ratio_relation = reduce_residue(
        2 * cross_contribution + 11 * top_left_contribution
    ) == 0
    bottom_ratio_relation = reduce_residue(
        3 * bottom_right_contribution - 50 * top_left_contribution
    ) == 0
    seventy_three_identity = reduce_residue(
        6 * ((-1) ** cyclotomic_index) * expected
        - 73 * top_left_contribution
    ) == 0
    return {
        "cyclotomic_index": cyclotomic_index,
        "rank": rank,
        "cyclotomic_polynomial": str(sp.cyclotomic_poly(cyclotomic_index, p)),
        "subset_dp_residue": str(sp.factor(expected)),
        "bordered_residue": str(sp.factor(bordered.signed_coefficient)),
        "bordered_residue_matches_subset_dp": reduce_residue(
            bordered.signed_coefficient - expected
        ) == 0,
        "left_cofactor_vector": [str(sp.factor(value)) for value in bordered.left_cofactor_vector],
        "right_cofactor_vector": [str(sp.factor(value)) for value in bordered.right_cofactor_vector],
        "left_null_vector_check": all(value == 0 for value in left_null),
        "right_null_vector_check": all(value == 0 for value in right_null),
        "symmetric_cross_blocks": symmetric_cross_blocks,
        "symmetric_border": symmetric_border,
        "cofactor_vectors_equal": cofactor_vectors_equal,
        "quadratic_form_reduction": (
            symmetric_cross_blocks and symmetric_border and cofactor_vectors_equal
        ),
        "cofactor_vector_supported_only_at_endpoints": endpoint_support_only,
        "border_corner_entries": {
            "top_left": str(sp.factor(border[0][0])),
            "top_right": str(sp.factor(border[0][-1])),
            "bottom_left": str(sp.factor(border[-1][0])),
            "bottom_right": str(sp.factor(border[-1][-1])),
        },
        "endpoint_quadratic_residue": str(sp.factor(endpoint_quadratic_residue)),
        "endpoint_quadratic_residue_matches_full_layer": reduce_residue(
            endpoint_quadratic_residue - expected
        ) == 0,
        "endpoint_contributions": {
            "top_left": str(sp.factor(top_left_contribution)),
            "cross": str(sp.factor(cross_contribution)),
            "bottom_right": str(sp.factor(bottom_right_contribution)),
        },
        "twice_cross_plus_eleven_top_left_is_zero": cross_ratio_relation,
        "three_bottom_right_minus_fifty_top_left_is_zero": bottom_ratio_relation,
        "six_signed_residue_equals_seventy_three_top_left": seventy_three_identity,
        "top_left_contribution_nonzero": top_left_contribution != 0,
        "cofactor_vector_has_no_zero_entries": all(
            value != 0 for value in bordered.right_cofactor_vector
        ),
        "minor_determinant_count": bordered.minor_determinant_count,
        "border_entry_count": (cyclotomic_index + 1) ** 2,
        "minimum_assignment_count": result["minimum_permutation_count"],
    }


def compute() -> dict[str, Any]:
    source_results = [associated_graded_first_appearance(index) for index in range(1, 5)]
    phi5_receipt = json.loads((REPO_ROOT / PHI5_RECEIPT_REF).read_text(encoding="utf-8"))
    source_results.append(phi5_receipt["result"])
    records = [_border_record(result) for result in source_results]
    return {
        "schema": RAW_SCHEMA,
        "records": records,
        "all_bordered_residues_match_subset_dp": all(
            record["bordered_residue_matches_subset_dp"] for record in records
        ),
        "all_cross_blocks_and_borders_symmetric": all(
            record["symmetric_cross_blocks"] and record["symmetric_border"]
            for record in records
        ),
        "all_cofactor_vectors_are_equal_null_vectors": all(
            record["cofactor_vectors_equal"]
            and record["left_null_vector_check"]
            and record["right_null_vector_check"]
            for record in records
        ),
        "all_layers_reduce_to_one_quadratic_form": all(
            record["quadratic_form_reduction"] for record in records
        ),
        "all_cofactor_vectors_are_endpoint_supported": all(
            record["cofactor_vector_supported_only_at_endpoints"]
            and record["endpoint_quadratic_residue_matches_full_layer"]
            for record in records
        ),
        "all_endpoint_contributions_obey_fixed_73_identity": all(
            record["twice_cross_plus_eleven_top_left_is_zero"]
            and record["three_bottom_right_minus_fifty_top_left_is_zero"]
            and record["six_signed_residue_equals_seventy_three_top_left"]
            and record["top_left_contribution_nonzero"]
            for record in records
        ),
        "authority_boundary": (
            "The block identity is exact for every compatible matrix. The source "
            "records instantiate it only for d=1,...,5 and do not prove uniform "
            "nonvanishing of the resulting quadratic form."
        ),
    }


def build_payload(result: dict[str, Any]) -> dict[str, Any]:
    required = (
        "all_bordered_residues_match_subset_dp",
        "all_cross_blocks_and_borders_symmetric",
        "all_cofactor_vectors_are_equal_null_vectors",
        "all_layers_reduce_to_one_quadratic_form",
        "all_cofactor_vectors_are_endpoint_supported",
        "all_endpoint_contributions_obey_fixed_73_identity",
    )
    if not all(result[field] for field in required):
        raise AssertionError("bordered quadratic-form reduction failed")
    contract = build_experiment_contract(
        problem_id="erdos_1049",
        target_statement="Prove irrationality of the Lambert value at p=3/2.",
        claim_ceiling=(
            "Exact all-matrix bordered coefficient identity and exact d=1,...,5 "
            "Zudilin instantiations; not uniform noncancellation or irrationality."
        ),
        hypothesis_id="first_appearance_layer_is_boundary_quadratic_form",
        hypothesis_statement=(
            "The exponentially described minimum determinant layer is the "
            "quadratic form of the positive-border block on the one-dimensional "
            "null vector of the rectangular cross block."
        ),
        probe_id="bordered_cofactor_null_vector_reduction",
        probe_question=(
            "Do the exact d=1,...,5 residues equal (-1)^d v^T Z v, with v the "
            "common cofactor/null vector forced by Hankel symmetry?"
        ),
        computation=(
            "Extract zero-weight rectangular cross blocks and the weight-one "
            "positive block from the local residue matrix; compute all maximal "
            "minors by exact subset DP and contract the resulting null vectors."
        ),
        falsifier=(
            "Any mismatch with the full subset-DP residue, failed null relation, "
            "or asymmetric source block falsifies the proposed reduction."
        ),
        stop_condition=(
            "Stop after the exact structural reduction and d=1,...,5 validation; "
            "do not count more cyclotomic indices without a quadratic-form invariant."
        ),
        survival_consequence=(
            "The first-appearance problem becomes uniform nonvanishing of one "
            "explicit boundary quadratic form, opening recurrence, norm, and "
            "resultant probes on its cofactor vector."
        ),
        falsification_consequence=(
            "Failure would eliminate the bordered-null-vector route and force a "
            "different organization of the minimum layer."
        ),
        consumer_ref=CONSUMER_REF,
        consumer_declarations=["zudilinScalarPlusBorder_cannot_meet_required_charge"],
        analysis_refs=[ANALYSIS_REF],
        source_refs=[SOURCE_REF, BORDER_ENGINE_REF, LOCAL_ENGINE_REF, LOCAL_ADAPTER_REF],
        input_receipt_refs=INPUT_RECEIPTS,
        result_status="exact_one_way_result",
        result_summary=(
            "The first-appearance layer is exactly (-1)^d v^T Z v: v is the "
            "common cofactor/null vector of the symmetric rectangular cross "
            "blocks. For d=1,...,5, v is supported only at its endpoints, so a "
            "two-by-two corner quadratic form reproduces every committed residue. "
            "Its three contributions have fixed ratios -11/2 and 50/3, giving "
            "the exact identity 6*(-1)^d*Res_d=73*T_00 throughout d=1,...,5."
        ),
        progress_class="mechanism_opened",
        decision_basis=(
            "This replaces an exponentially described determinant layer by a "
            "one-dimensional boundary mode and an explicit quadratic form, a new "
            "analytic mechanism rather than a longer finite horizon."
        ),
        next_analytic_target=(
            "Prove the cross-block column recurrence forcing all interior "
            "cofactors to vanish and the two fixed corner ratios. Then uniform "
            "noncancellation reduces to the nonzero triangular minor and top-left "
            "border residue, because 73 is nonzero in characteristic zero."
        ),
        resource_bounds={
            "minimum_cyclotomic_index": 1,
            "maximum_cyclotomic_index": 5,
            "cyclotomic_index_count": 5,
            "maximum_cross_block_size": 5,
            "maximum_minor_count": 12,
            "maximum_border_entry_count": 36,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    refs = (SOURCE_REF, BORDER_ENGINE_REF, LOCAL_ENGINE_REF, LOCAL_ADAPTER_REF, ANALYSIS_REF, CONSUMER_REF)
    return {
        "schema": "erdos1049-zudilin-first-appearance-border-form-receipt/1",
        "status": "exact_mechanism_opened",
        "result": result,
        "experiment_contract": contract,
        "source_records": [source_record(REPO_ROOT, ref) for ref in refs],
    }


def _read_result(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("schema") != RAW_SCHEMA:
        raise ValueError(f"unexpected raw result schema in {path}")
    return payload


def _render(payload: dict[str, Any]) -> str:
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--result-output", type=Path)
    parser.add_argument("--from-result", type=Path)
    parser.add_argument("--result-only", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.result_only and args.result_output is None:
        parser.error("--result-only requires --result-output")
    if args.check and args.result_only:
        parser.error("--check and --result-only are incompatible")
    if args.check:
        if not args.output.exists():
            print(f"missing receipt: {args.output}", file=sys.stderr)
            return 1
        existing = json.loads(args.output.read_text(encoding="utf-8"))
        expected = _render(build_payload(existing["result"]))
        if args.output.read_text(encoding="utf-8") != expected:
            print(f"stale receipt: {args.output}", file=sys.stderr)
            return 1
        print(json.dumps({"status": "current", "output": str(args.output)}))
        return 0
    result = _read_result(args.from_result) if args.from_result else compute()
    if args.result_output is not None:
        args.result_output.parent.mkdir(parents=True, exist_ok=True)
        args.result_output.write_text(_render(result), encoding="utf-8")
    if args.result_only:
        print(json.dumps({"status": "result_written", "output": str(args.result_output)}))
        return 0
    payload = build_payload(result)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(_render(payload), encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(args.output)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
