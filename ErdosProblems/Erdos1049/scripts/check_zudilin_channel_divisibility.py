#!/usr/bin/env python3
"""Probe the global polynomial identity behind the local Zudilin B=2C law."""

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

from check_zudilin_phi3_associated_graded import (  # noqa: E402
    fast_cleared_row,
    positive_pochhammer,
)
from check_zudilin_scalar_content import p  # noqa: E402
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


TARGET_INDICES = tuple(range(1, 8))
SOURCE_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
ROW_CONSTRUCTOR_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/"
    "check_zudilin_phi3_associated_graded.py"
)
SCALAR_SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/"
    "check_zudilin_scalar_content.py"
)
PRIMARY_SOURCE_REF = "annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/extracted.md"
PREVIOUS_ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "ZudilinPhi1BlockCollapseLab.md"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "ZudilinChannelDivisibilityLab.md"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "AdelicHeightBridge.lean"
)
INPUT_RECEIPTS = [
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_scalar_content_receipt.json",
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_phi1_block_collapse_receipt.json",
]
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_channel_divisibility_receipt.json"
)
RAW_SCHEMA = "erdos1049-zudilin-channel-divisibility-result/1"


def _p_order(polynomial: sp.Poly) -> int:
    if polynomial.is_zero:
        raise ValueError("zero polynomial has no finite p-order")
    return min(monomial[0] for monomial, _ in polynomial.terms())


def _record(index: int) -> dict[str, Any]:
    if index < 1:
        raise ValueError("row index must be positive")
    _, b_polynomial, c_polynomial = fast_cleared_row(index)
    pochhammer = positive_pochhammer(index)
    pochhammer_cube = pochhammer**3
    scale = sp.Poly(p ** (index + 1), p, domain=sp.ZZ)
    difference = b_polynomial - 2 * c_polynomial
    quotient, remainder = sp.div(difference, pochhammer_cube, domain=sp.ZZ)
    divides = remainder.is_zero
    normalized_quotient = (
        quotient.exquo(scale) if divides and quotient.rem(scale).is_zero else None
    )
    scale_also_divides = normalized_quotient is not None
    if normalized_quotient is None:
        normalized_expression = None
        normalized_degree = None
        normalized_p_order = None
        normalized_at_one = None
        normalized_matches_n_cubed = False
        coprime_to_pochhammer = False
        cyclotomic_orders_are_exact = False
    else:
        normalized_expression = str(sp.factor(normalized_quotient.as_expr()))
        normalized_degree = normalized_quotient.degree()
        normalized_p_order = _p_order(normalized_quotient)
        normalized_at_one = int(normalized_quotient.eval(1))
        normalized_matches_n_cubed = normalized_at_one == index**3
        coprime_to_pochhammer = sp.gcd(normalized_quotient, pochhammer).degree() == 0
        cyclotomic_orders_are_exact = coprime_to_pochhammer
    expected_degree = (index + 1) * (3 * index - 2) // 2
    return {
        "row_index": index,
        "difference": "B_n-2*C_n",
        "divisor": "P_n^3, P_n=product_(1<=j<=n)(p^j-1)",
        "pochhammer_cube_divides": divides,
        "remainder": str(sp.factor(remainder.as_expr())),
        "p_to_n_plus_one_also_divides_quotient": scale_also_divides,
        "normalized_difference_polynomial_D_n": normalized_expression,
        "normalized_difference_degree": normalized_degree,
        "expected_normalized_degree": expected_degree,
        "normalized_degree_matches": normalized_degree == expected_degree,
        "normalized_p_order": normalized_p_order,
        "normalized_p_order_is_one": normalized_p_order == 1,
        "normalized_value_at_p_equals_one": normalized_at_one,
        "normalized_value_at_one_equals_n_cubed": normalized_matches_n_cubed,
        "normalized_difference_coprime_to_P_n": coprime_to_pochhammer,
        "all_cyclotomic_orders_in_P_n_are_exactly_gained_by_one": (
            cyclotomic_orders_are_exact
        ),
        "difference_degree": difference.degree(),
        "pochhammer_cube_degree": pochhammer_cube.degree(),
    }


def _summarize(records: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "schema": RAW_SCHEMA,
        "records": records,
        "all_pochhammer_cube_divisibilities_hold": all(
            record["pochhammer_cube_divides"] for record in records
        ),
        "all_scale_divisibilities_hold": all(
            record["p_to_n_plus_one_also_divides_quotient"]
            for record in records
        ),
        "all_cyclotomic_orders_are_exactly_gained_by_one": all(
            record["all_cyclotomic_orders_in_P_n_are_exactly_gained_by_one"]
            for record in records
        ),
        "all_normalized_degrees_match": all(
            record["normalized_degree_matches"] for record in records
        ),
        "all_normalized_p_orders_are_one": all(
            record["normalized_p_order_is_one"] for record in records
        ),
        "all_normalized_values_at_one_equal_n_cubed": all(
            record["normalized_value_at_one_equals_n_cubed"]
            for record in records
        ),
        "authority_boundary": (
            "The exact polynomial divisions decide the displayed rows. They "
            "identify a global all-n identity to prove, but do not establish "
            "that identity outside the listed indices."
        ),
    }


def compute(indices: list[int]) -> dict[str, Any]:
    return _summarize([_record(index) for index in sorted(set(indices))])


def _combine_results(results: list[dict[str, Any]]) -> dict[str, Any]:
    records_by_index: dict[int, dict[str, Any]] = {}
    for result in results:
        if result.get("schema") != RAW_SCHEMA:
            raise ValueError("unexpected raw result schema")
        for record in result["records"]:
            records_by_index[int(record["row_index"])] = record
    return _summarize([records_by_index[index] for index in sorted(records_by_index)])


def build_payload(result: dict[str, Any]) -> dict[str, Any]:
    indices = [int(record["row_index"]) for record in result["records"]]
    if indices != list(TARGET_INDICES):
        raise ValueError(f"canonical receipt requires indices {TARGET_INDICES}")
    survives = (
        result["all_pochhammer_cube_divisibilities_hold"]
        and result["all_scale_divisibilities_hold"]
        and result["all_cyclotomic_orders_are_exactly_gained_by_one"]
        and result["all_normalized_degrees_match"]
        and result["all_normalized_p_orders_are_one"]
        and result["all_normalized_values_at_one_equal_n_cubed"]
    )
    if survives:
        progress_class = "mechanism_opened"
        status = "exact_mechanism_opened"
        result_summary = (
            "For every n=1,...,7, the exact cleared source difference B_n-2C_n "
            "is divisible by p^(n+1)P_n^3. The normalized quotient D_n is a "
            "polynomial of degree (n+1)(3n-2)/2, has p-order one, satisfies "
            "D_n(1)=n^3, and is coprime to P_n. Hence every Phi_d in P_n gains "
            "exactly one order over the scalar layer in the tested rows. This "
            "opens a single global polynomiality identity as the explanation of "
            "the committed local B=2C law."
        )
        next_target = (
            "Prove that the rational source sum B_n-2C_n is polynomial by "
            "constructing a q-binomial telescoping or Heine-symmetry certificate; "
            "then P_n^3 divisibility, and therefore leading B=2C for every d<=n, "
            "follows for all n."
        )
    else:
        progress_class = "mechanism_eliminated"
        status = "exact_mechanism_eliminated"
        result_summary = (
            "The exact P_n^3 divisibility or its predicted sharp signature fails "
            "for at least one row n<=7, eliminating the proposed global "
            "explanation of local B=2C."
        )
        next_target = (
            "Inspect the first failed row and retain only the cyclotomic factors "
            "whose exact remainders vanish."
        )
    contract = build_experiment_contract(
        problem_id="erdos_1049",
        target_statement="Prove irrationality of the Lambert value at p=3/2.",
        claim_ceiling=(
            "Exact global polynomial-divisibility decisions for source rows "
            "n=1,...,7; not an all-n theorem or irrationality proof."
        ),
        hypothesis_id="zudilin_B_minus_2C_has_full_pochhammer_cube",
        hypothesis_statement=(
            "For every n>=1, the cleared source difference B_n-2C_n is "
            "divisible by p^(n+1)P_n^3, so each Phi_d leading layer has B=2C."
        ),
        probe_id="exact_global_channel_divisibility_n1_n7",
        probe_question=(
            "Does one global P_n^3 divisor explain the complete local B=2C "
            "strips, and is the gained cyclotomic order sharp?"
        ),
        computation=(
            "Construct the exact cleared Zudilin rows in Z[p], divide B_n-2C_n "
            "by P_n^3 and p^(n+1), and test the quotient degree, p-order, value "
            "at one, and coprimality with P_n."
        ),
        falsifier=(
            "A nonzero exact division remainder kills the global mechanism; a "
            "nontrivial gcd of the normalized quotient with P_n kills sharpness."
        ),
        stop_condition=(
            "Stop at n=7 after the divisor survives a degree-168 source difference; "
            "replace further row extension with an all-n summand certificate."
        ),
        survival_consequence=(
            "Survival opens one q-binomial polynomiality theorem that implies "
            "leading B=2C simultaneously at every cyclotomic index."
        ),
        falsification_consequence=(
            "Failure returns the proof target to separate local channel residues "
            "and identifies the first missing cyclotomic factor."
        ),
        consumer_ref=CONSUMER_REF,
        consumer_declarations=["zudilinScalarPlusBorder_cannot_meet_required_charge"],
        analysis_refs=[ANALYSIS_REF, PREVIOUS_ANALYSIS_REF],
        source_refs=[
            SOURCE_REF,
            ROW_CONSTRUCTOR_REF,
            SCALAR_SOURCE_REF,
            PRIMARY_SOURCE_REF,
        ],
        input_receipt_refs=INPUT_RECEIPTS,
        result_status="exact_one_way_result",
        result_summary=result_summary,
        progress_class=progress_class,
        decision_basis=(
            "The probe replaces an expanding family of local equalities with one "
            "global polynomial divisor and tests its exact cyclotomic content."
        ),
        next_analytic_target=next_target,
        resource_bounds={
            "minimum_row_index": min(indices),
            "maximum_row_index": max(indices),
            "row_count": len(indices),
            "maximum_difference_degree": max(
                int(record["difference_degree"]) for record in result["records"]
            ),
            "maximum_normalized_difference_degree": max(
                int(record["normalized_difference_degree"])
                for record in result["records"]
            ),
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    refs = (
        SOURCE_REF,
        ROW_CONSTRUCTOR_REF,
        SCALAR_SOURCE_REF,
        PRIMARY_SOURCE_REF,
        ANALYSIS_REF,
        PREVIOUS_ANALYSIS_REF,
        CONSUMER_REF,
    )
    return {
        "schema": "erdos1049-zudilin-channel-divisibility-receipt/1",
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
    parser.add_argument("--row-index", type=int, action="append")
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
        result = compute(args.row_index or list(TARGET_INDICES))
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
