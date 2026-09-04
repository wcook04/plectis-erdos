#!/usr/bin/env python3
"""Test the endpoint-column and fixed-corner recurrence at Phi_6 and Phi_7."""

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

from check_zudilin_scalar_content import p  # noqa: E402
from system.lib.formal_math_bordered_determinant import (  # noqa: E402
    bordered_first_order_coefficient,
)
from system.lib.formal_math_cyclotomic_local import CyclotomicLocalRing  # noqa: E402
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)
from zudilin_cyclotomic_local import (  # noqa: E402
    local_cleared_row,
    primitive_row_residue,
    scalar_unit_residue,
)


TARGET_INDICES = (6, 7)
SOURCE_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
LOCAL_ADAPTER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/"
    "zudilin_cyclotomic_local.py"
)
LOCAL_ENGINE_REF = "system/lib/formal_math_cyclotomic_local.py"
BORDER_ENGINE_REF = "system/lib/formal_math_bordered_determinant.py"
PREVIOUS_ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "ZudilinFirstAppearanceBorderFormLab.md"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "ZudilinEndpointRecurrenceLab.md"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "AdelicHeightBridge.lean"
)
INPUT_RECEIPTS = [
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_phi1_kernel_receipt.json",
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_first_appearance_border_form_receipt.json"
]
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_endpoint_recurrence_receipt.json"
)
RAW_SCHEMA = "erdos1049-zudilin-endpoint-recurrence/1"


def _q_lucas_regression(cyclotomic_index: int) -> dict[str, Any]:
    """Replay q-Lucas through every quotient block used by the recurrence."""

    d = cyclotomic_index
    ring = CyclotomicLocalRing(p, d, precision=1)
    maximum_top = 5 * d - 1
    gaussian = ring.gaussian_table(maximum_top)
    checked = 0
    mismatches = []
    for top_quotient in range(5):
        for bottom_quotient in range(top_quotient + 1):
            for top_residue in range(d):
                top = top_quotient * d + top_residue
                for bottom_residue in range(d):
                    bottom = bottom_quotient * d + bottom_residue
                    if bottom > top:
                        continue
                    expected = (
                        ring.reduce(
                            sp.binomial(top_quotient, bottom_quotient)
                            * gaussian[(top_residue, bottom_residue)]
                        )
                        if bottom_residue <= top_residue
                        else ring.poly(0)
                    )
                    observed = gaussian[(top, bottom)]
                    checked += 1
                    if observed != expected:
                        mismatches.append(
                            {
                                "top": top,
                                "bottom": bottom,
                                "observed": str(observed.as_expr()),
                                "expected": str(expected.as_expr()),
                            }
                        )
    return {
        "maximum_quotient_block": 4,
        "case_count": checked,
        "mismatch_count": len(mismatches),
        "matches": not mismatches,
        "mismatches": mismatches,
    }


def _phi1_kernel_microcosm() -> dict[str, Any]:
    moments = {
        index: sp.factorial(index) ** 3
        * sum(sp.Rational(1, denominator) for denominator in range(1, index + 1))
        for index in (2, 3, 4)
    }
    corners = {
        2: -3 * moments[2],
        3: sp.Rational(3, 4) * moments[3],
        4: -sp.Rational(3, 16) * moments[4],
    }
    contraction = 9 * corners[2] + 6 * corners[3] + corners[4]
    return {
        "moment_formula": "m_q=(q!)^3 H_q",
        "moments": {str(index): int(value) for index, value in moments.items()},
        "scaled_corner_triple": [int(corners[index]) for index in (2, 3, 4)],
        "endpoint_vector": [3, 1],
        "binary_contraction": int(contraction),
        "binary_contraction_equals_minus_54_times_73": contraction == -54 * 73,
        "corner_ratios_match_eleven_fourths_and_fifty_thirds": (
            corners[3] / corners[2] == -sp.Rational(33, 4)
            and corners[4] / corners[2] == 150
        ),
    }


def _enrich_record(record: dict[str, Any]) -> dict[str, Any]:
    enriched = dict(record)
    d = int(enriched["cyclotomic_index"])
    if "q_lucas_regression" not in enriched:
        enriched["q_lucas_regression"] = _q_lucas_regression(d)
    if "source_block_multiplier_K" not in enriched:
        ring = CyclotomicLocalRing(p, d, precision=1)
        cyclotomic = sp.Poly(ring.cyclotomic.as_expr(), p, domain=sp.QQ)

        def reduce_residue(expression: sp.Expr) -> sp.Expr:
            return sp.Poly(sp.expand(expression), p, domain=sp.QQ).rem(
                cyclotomic
            ).as_expr()

        unit_d = scalar_unit_residue(d, d).as_expr()
        unit_2d = scalar_unit_residue(2 * d, d).as_expr()
        inverse_unit_d = sp.Poly(
            sp.invert(sp.Poly(unit_d, p, domain=sp.QQ), cyclotomic),
            p,
            domain=sp.QQ,
        ).as_expr()
        rho = sp.sympify(enriched["endpoint_column_multiplier_rho"], locals={"p": p})
        multiplier = reduce_residue(rho * unit_2d * inverse_unit_d)
        prime_formula = reduce_residue(
            multiplier - 12 * d**3 * (p - 1) ** 3
        ) == 0
        enriched["source_block_multiplier_K"] = str(sp.factor(multiplier))
        enriched["prime_index_multiplier_formula_applicable"] = bool(sp.isprime(d))
        enriched["prime_index_multiplier_formula_matches"] = (
            prime_formula if sp.isprime(d) else None
        )
    return enriched


def _record(cyclotomic_index: int) -> dict[str, Any]:
    d = cyclotomic_index
    ring = CyclotomicLocalRing(p, d, precision=1)
    cyclotomic = sp.Poly(ring.cyclotomic.as_expr(), p, domain=sp.QQ)

    def reduce_residue(expression: sp.Expr) -> sp.Expr:
        return sp.Poly(sp.expand(expression), p, domain=sp.QQ).rem(cyclotomic).as_expr()

    def inverse(expression: sp.Expr) -> sp.Expr:
        polynomial = sp.Poly(expression, p, domain=sp.QQ).rem(cyclotomic)
        if polynomial.is_zero:
            raise AssertionError("attempted to invert a zero residue")
        return sp.Poly(sp.invert(polynomial, cyclotomic), p, domain=sp.QQ).as_expr()

    unit_cache: dict[int, sp.Expr] = {}
    inverse_unit_cache: dict[int, sp.Expr] = {}

    def unit(index: int) -> sp.Expr:
        if index not in unit_cache:
            unit_cache[index] = scalar_unit_residue(index, d).as_expr()
        return unit_cache[index]

    def inverse_unit(index: int) -> sp.Expr:
        if index not in inverse_unit_cache:
            inverse_unit_cache[index] = inverse(unit(index))
        return inverse_unit_cache[index]

    moment_cache: dict[int, sp.Expr] = {}

    def moment(index: int) -> sp.Expr:
        if index not in moment_cache:
            a_residue, b_residue, c_residue = primitive_row_residue(index, d)
            if index >= d and not a_residue.is_zero:
                raise AssertionError("primitive moment contradicts mu-vanishing theorem")
            moment_cache[index] = reduce_residue(
                -b_residue.as_expr() - c_residue.as_expr()
            )
        return moment_cache[index]

    def entry(row: int, column: int) -> sp.Expr:
        index = row + column
        return reduce_residue(
            moment(index) * unit(index) * inverse_unit(row) * inverse_unit(column)
        )

    low = list(range(d))
    positive = list(range(d, 2 * d + 1))
    cross = [[entry(row, column) for column in positive] for row in low]
    transpose = [
        [cross[column][row] for column in range(d)]
        for row in range(d + 1)
    ]
    zero_border = [[sp.Integer(0) for _ in range(d + 1)] for _ in range(d + 1)]
    cofactors = bordered_first_order_coefficient(
        cross,
        transpose,
        zero_border,
        one=sp.Integer(1),
        zero=sp.Integer(0),
        normalize=reduce_residue,
        is_zero=lambda value: value == 0,
    ).right_cofactor_vector
    endpoints_nonzero = cofactors[0] != 0 and cofactors[-1] != 0
    endpoint_support = endpoints_nonzero and all(
        value == 0 for value in cofactors[1:-1]
    )
    rho = (
        reduce_residue(-cofactors[0] * inverse(cofactors[-1]))
        if endpoints_nonzero
        else sp.Integer(0)
    )
    endpoint_column_recurrence = endpoints_nonzero and all(
        reduce_residue(cross[row][-1] - rho * cross[row][0]) == 0
        for row in range(d)
    )

    z00 = entry(d, d)
    z0d = entry(d, 2 * d)
    zdd = entry(2 * d, 2 * d)
    first_corner_ratio = endpoints_nonzero and reduce_residue(
        z0d - sp.Rational(11, 4) * rho * z00
    ) == 0
    last_corner_ratio = endpoints_nonzero and reduce_residue(
        zdd - sp.Rational(50, 3) * rho**2 * z00
    ) == 0
    v0 = cofactors[0]
    vd = cofactors[-1]
    top_left_contribution = reduce_residue(v0**2 * z00)
    cross_contribution = reduce_residue(2 * v0 * vd * z0d)
    bottom_right_contribution = reduce_residue(vd**2 * zdd)
    predicted_residue = reduce_residue(
        (-1) ** d
        * (top_left_contribution + cross_contribution + bottom_right_contribution)
    )
    seventy_three_identity = endpoints_nonzero and reduce_residue(
        6 * ((-1) ** d) * predicted_residue - 73 * top_left_contribution
    ) == 0
    required_moment_indices = sorted(set(range(d, 3 * d)) | {3 * d, 4 * d})
    maximum_local_modulus_degree = max(
        local_cleared_row(index, d)[1].modulus.degree()
        for index in required_moment_indices
    )
    return _enrich_record({
        "cyclotomic_index": d,
        "cyclotomic_polynomial": str(sp.cyclotomic_poly(d, p)),
        "cyclotomic_degree": int(sp.totient(d)),
        "rank": 2 * d + 1,
        "cofactor_vector": [str(sp.factor(value)) for value in cofactors],
        "cofactor_vector_supported_only_at_endpoints": endpoint_support,
        "endpoint_column_multiplier_rho": str(sp.factor(rho)),
        "last_cross_column_equals_rho_times_first": endpoint_column_recurrence,
        "corner_entries": {
            "z00": str(sp.factor(z00)),
            "z0d": str(sp.factor(z0d)),
            "zdd": str(sp.factor(zdd)),
        },
        "z0d_equals_eleven_fourths_rho_z00": first_corner_ratio,
        "zdd_equals_fifty_thirds_rho_squared_z00": last_corner_ratio,
        "top_left_contribution": str(sp.factor(top_left_contribution)),
        "predicted_first_appearance_residue": str(sp.factor(predicted_residue)),
        "predicted_residue_nonzero": predicted_residue != 0,
        "six_signed_residue_equals_seventy_three_top_left": seventy_three_identity,
        "required_moment_indices": required_moment_indices,
        "required_moment_count": len(required_moment_indices),
        "maximum_local_modulus_degree": int(maximum_local_modulus_degree),
        "minimum_assignment_count_avoided": (d + 1) * 2**d,
    })


def compute(indices: list[int]) -> dict[str, Any]:
    records = [_record(index) for index in sorted(set(indices))]
    return {
        "schema": RAW_SCHEMA,
        "records": records,
        "all_endpoint_recurrences_hold": all(
            record["cofactor_vector_supported_only_at_endpoints"]
            and record["last_cross_column_equals_rho_times_first"]
            for record in records
        ),
        "all_fixed_corner_ratios_hold": all(
            record["z0d_equals_eleven_fourths_rho_z00"]
            and record["zdd_equals_fifty_thirds_rho_squared_z00"]
            for record in records
        ),
        "all_73_identities_hold": all(
            record["six_signed_residue_equals_seventy_three_top_left"]
            and record["predicted_residue_nonzero"]
            for record in records
        ),
        "all_q_lucas_regressions_hold": all(
            record["q_lucas_regression"]["matches"] for record in records
        ),
        "all_applicable_prime_multiplier_formulas_hold": all(
            not record["prime_index_multiplier_formula_applicable"]
            or record["prime_index_multiplier_formula_matches"]
            for record in records
        ),
        "phi1_kernel_microcosm": _phi1_kernel_microcosm(),
        "authority_boundary": (
            "The targeted computation exactly decides the endpoint recurrence "
            "and implied first-appearance residue at the listed indices. It does "
            "not by itself prove the identities for all d."
        ),
    }


def _combine_results(results: list[dict[str, Any]]) -> dict[str, Any]:
    records_by_index: dict[int, dict[str, Any]] = {}
    for result in results:
        if result.get("schema") != RAW_SCHEMA:
            raise ValueError("unexpected raw result schema")
        for record in result["records"]:
            records_by_index[int(record["cyclotomic_index"])] = _enrich_record(record)
    combined_records = [records_by_index[index] for index in sorted(records_by_index)]
    combined = {
        "schema": RAW_SCHEMA,
        "records": combined_records,
        "all_endpoint_recurrences_hold": all(
            record["cofactor_vector_supported_only_at_endpoints"]
            and record["last_cross_column_equals_rho_times_first"]
            for record in combined_records
        ),
        "all_fixed_corner_ratios_hold": all(
            record["z0d_equals_eleven_fourths_rho_z00"]
            and record["zdd_equals_fifty_thirds_rho_squared_z00"]
            for record in combined_records
        ),
        "all_73_identities_hold": all(
            record["six_signed_residue_equals_seventy_three_top_left"]
            and record["predicted_residue_nonzero"]
            for record in combined_records
        ),
        "all_q_lucas_regressions_hold": all(
            record["q_lucas_regression"]["matches"] for record in combined_records
        ),
        "all_applicable_prime_multiplier_formulas_hold": all(
            not record["prime_index_multiplier_formula_applicable"]
            or record["prime_index_multiplier_formula_matches"]
            for record in combined_records
        ),
        "phi1_kernel_microcosm": _phi1_kernel_microcosm(),
        "authority_boundary": (
            "The targeted computation exactly decides the endpoint recurrence "
            "and implied first-appearance residue at the listed indices. It does "
            "not by itself prove the identities for all d."
        ),
    }
    return combined


def build_payload(result: dict[str, Any]) -> dict[str, Any]:
    indices = [int(record["cyclotomic_index"]) for record in result["records"]]
    if indices != list(TARGET_INDICES):
        raise ValueError(f"canonical receipt requires indices {TARGET_INDICES}")
    survives = (
        result["all_endpoint_recurrences_hold"]
        and result["all_fixed_corner_ratios_hold"]
        and result["all_73_identities_hold"]
        and result["all_q_lucas_regressions_hold"]
        and result["all_applicable_prime_multiplier_formulas_hold"]
        and result["phi1_kernel_microcosm"][
            "binary_contraction_equals_minus_54_times_73"
        ]
        and result["phi1_kernel_microcosm"][
            "corner_ratios_match_eleven_fourths_and_fifty_thirds"
        ]
    )
    if survives:
        progress_class = "mechanism_opened"
        status = "exact_mechanism_opened"
        result_summary = (
            "The endpoint recurrence and fixed 11/4, 50/3 corner ratios survive "
            "exactly at composite d=6 and degree-six d=7, imply nonzero first-"
            "appearance residues, and preserve the universal factor-73 identity. "
            "The q-Lucas identity is also replayed exactly through every quotient "
            "block used by the proposed proof, and the prime-index source "
            "multiplier is exactly 12*d^3*(p-1)^3 at d=7. The universal corner "
            "constants are the q=2,3,4 moments of the committed Phi_1 harmonic "
            "kernel and their endpoint contraction is -54*73."
        )
        next_target = (
            "Prove the root-of-unity source-row recurrence uniformly using the "
            "q-Lucas decomposition of indices n=qd+s."
        )
    else:
        progress_class = "mechanism_eliminated"
        status = "exact_mechanism_eliminated"
        result_summary = (
            "At least one of the endpoint or fixed-corner identities fails at "
            "d=6 or d=7, eliminating the proposed uniform recurrence."
        )
        next_target = "Isolate the first failed identity and derive the missing index dependence."
    contract = build_experiment_contract(
        problem_id="erdos_1049",
        target_statement="Prove irrationality of the Lambert value at p=3/2.",
        claim_ceiling=(
            "Exact endpoint/corner decisions and implied first-appearance residues "
            "at d=6,7; not an all-d theorem or irrationality proof."
        ),
        hypothesis_id="uniform_endpoint_and_corner_recurrence",
        hypothesis_statement=(
            "The cross-block kernel is endpoint-supported and its corner ratios "
            "are universally 11/4 and 50/3 after scaling by rho_d."
        ),
        probe_id="targeted_phi6_phi7_endpoint_recurrence",
        probe_question=(
            "Do the exact recurrence and factor-73 identities survive a composite "
            "index and the first degree-six cyclotomic field?"
        ),
        computation=(
            "Construct only moments d,...,3d and 4d in the local cyclotomic ring, "
            "compute the rectangular cross-block cofactors, and test the last-"
            "column multiplier and three corner contributions exactly."
        ),
        falsifier=(
            "An interior nonzero cofactor, failed endpoint column proportionality, "
            "or failed 11/4, 50/3 corner ratio kills the uniform recurrence."
        ),
        stop_condition=(
            "Stop after d=6,7 decide the named invariant; do not extend indices "
            "without beginning the q-Lucas proof."
        ),
        survival_consequence=(
            "Survival across composite d=6 and degree-six d=7 opens an all-d "
            "q-Lucas proof of first-appearance noncancellation."
        ),
        falsification_consequence=(
            "Failure identifies the exact first index where the fixed recurrence "
            "must acquire additional residue-class dependence."
        ),
        consumer_ref=CONSUMER_REF,
        consumer_declarations=["zudilinScalarPlusBorder_cannot_meet_required_charge"],
        analysis_refs=[ANALYSIS_REF, PREVIOUS_ANALYSIS_REF],
        source_refs=[SOURCE_REF, LOCAL_ADAPTER_REF, LOCAL_ENGINE_REF, BORDER_ENGINE_REF],
        input_receipt_refs=INPUT_RECEIPTS,
        result_status="exact_one_way_result",
        result_summary=result_summary,
        progress_class=progress_class,
        decision_basis=(
            "The probe targets the exact all-d recurrence predicted by d<=5, "
            "rather than auditing another unrestricted determinant horizon."
        ),
        next_analytic_target=next_target,
        resource_bounds={
            "minimum_cyclotomic_index": 6,
            "maximum_cyclotomic_index": 7,
            "cyclotomic_index_count": 2,
            "maximum_required_moment_count": max(
                record["required_moment_count"] for record in result["records"]
            ),
            "maximum_local_modulus_degree": max(
                record["maximum_local_modulus_degree"] for record in result["records"]
            ),
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    refs = (SOURCE_REF, LOCAL_ADAPTER_REF, LOCAL_ENGINE_REF, BORDER_ENGINE_REF, ANALYSIS_REF, PREVIOUS_ANALYSIS_REF, CONSUMER_REF)
    return {
        "schema": "erdos1049-zudilin-endpoint-recurrence-receipt/1",
        "status": status,
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
    parser.add_argument("--cyclotomic-index", type=int, action="append")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--result-output", type=Path)
    parser.add_argument("--from-result", type=Path, action="append")
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
    if args.from_result:
        result = _combine_results([_read_result(path) for path in args.from_result])
    else:
        result = compute(args.cyclotomic_index or list(TARGET_INDICES))
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
