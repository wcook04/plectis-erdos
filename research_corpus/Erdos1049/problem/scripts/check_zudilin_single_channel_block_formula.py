#!/usr/bin/env python3
"""Regress the all-d single-channel Zudilin block formula."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import sys
from typing import Any

import sympy as sp


REPO_ROOT = Path(__file__).resolve().parents[5]
SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(REPO_ROOT))
sys.path.insert(0, str(SCRIPT_DIR))

from check_zudilin_scalar_content import p  # noqa: E402
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


SOURCE_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
PREVIOUS_PROOF_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "ZudilinChannelDivisibilityProof.md"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "ZudilinSingleChannelBlockFormulaProof.md"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "AdelicHeightBridge.lean"
)
BLOCK_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_phi1_block_collapse_receipt.json"
)
ENDPOINT_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_endpoint_recurrence_receipt.json"
)
POLE_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_pole_separation_receipt.json"
)
INPUT_RECEIPTS = [BLOCK_RECEIPT_REF, ENDPOINT_RECEIPT_REF, POLE_RECEIPT_REF]
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_single_channel_block_formula_receipt.json"
)
RAW_SCHEMA = "erdos1049-zudilin-single-channel-block-formula-result/1"


def harmonic(index: int) -> sp.Rational:
    return sum(
        (sp.Rational(1, denominator) for denominator in range(1, index + 1)),
        start=sp.Rational(0),
    )


def normalized_phi1_constant(quotient: int) -> sp.Rational:
    return sp.Rational(math.factorial(quotient) ** 3, 12 ** (quotient - 1)) * harmonic(
        quotient
    )


def _load_input_receipts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    return tuple(
        json.loads((REPO_ROOT / ref).read_text(encoding="utf-8"))
        for ref in INPUT_RECEIPTS
    )  # type: ignore[return-value]


def _observed_multipliers(
    block_receipt: dict[str, Any], endpoint_receipt: dict[str, Any]
) -> dict[int, str]:
    records = (
        block_receipt["result"]["records"]
        + endpoint_receipt["result"]["records"]
    )
    return {
        int(record["cyclotomic_index"]): record["source_block_multiplier_K"]
        for record in records
    }


def _multiplier_record(d: int, observed: str | None) -> dict[str, Any]:
    cyclotomic = sp.Poly(sp.cyclotomic_poly(d, p), p, domain=sp.QQ)

    def reduce_residue(expression: sp.Expr) -> sp.Expr:
        return sp.Poly(sp.expand(expression), p, domain=sp.QQ).rem(
            cyclotomic
        ).as_expr()

    root_product = reduce_residue(
        sp.prod(p**residue - 1 for residue in range(1, d))
    )
    expected_root_product = sp.Integer((-1) ** (d - 1) * d)
    proper_factor = sp.div(
        sp.Poly(p**d - 1, p, domain=sp.QQ), cyclotomic, domain=sp.QQ
    )[0].as_expr()
    multiplier = reduce_residue(12 * d**3 * proper_factor**3)
    if observed is None:
        observed_matches = None
    else:
        observed_expression = sp.sympify(observed, locals={"p": p})
        observed_matches = reduce_residue(multiplier - observed_expression) == 0
    return {
        "cyclotomic_index": d,
        "cyclotomic_polynomial": str(sp.cyclotomic_poly(d, p)),
        "root_product_A_d": str(sp.factor(root_product)),
        "root_product_equals_minus_one_to_d_minus_one_times_d": (
            reduce_residue(root_product - expected_root_product) == 0
        ),
        "proper_cyclotomic_factor_M_d": str(sp.factor(proper_factor)),
        "multiplier_formula": "K_d=12*d^3*M_d(zeta)^3",
        "predicted_multiplier_K_d": str(sp.factor(multiplier)),
        "observed_multiplier_K_d": observed,
        "observed_multiplier_matches": observed_matches,
        "predicted_multiplier_nonzero": multiplier != 0,
    }


def compute() -> dict[str, Any]:
    block_receipt, endpoint_receipt, pole_receipt = _load_input_receipts()
    observed = _observed_multipliers(block_receipt, endpoint_receipt)
    multiplier_records = [
        _multiplier_record(d, observed.get(d)) for d in range(1, 11)
    ]
    constant_records = []
    for quotient in range(1, 13):
        moment = sp.factorial(quotient) ** 3 * harmonic(quotient)
        constant = normalized_phi1_constant(quotient)
        constant_records.append(
            {
                "quotient_block": quotient,
                "phi1_harmonic_moment": str(moment),
                "normalized_block_constant": str(constant),
                "identity": (
                    "c_q=(q!)^3*H_q/12^(q-1)"
                ),
                "identity_holds": constant
                * 12 ** (quotient - 1)
                == moment,
            }
        )
    observed_constants = block_receipt["result"]["phi1_block_constants"]
    observed_constant_matches = all(
        sp.Rational(observed_constants[str(quotient)])
        == normalized_phi1_constant(quotient)
        for quotient in (2, 3, 4)
    )
    pole_theorem = pole_receipt["analytic_theorem"]
    return {
        "schema": RAW_SCHEMA,
        "multiplier_records": multiplier_records,
        "constant_records": constant_records,
        "all_root_product_identities_hold": all(
            record["root_product_equals_minus_one_to_d_minus_one_times_d"]
            for record in multiplier_records
        ),
        "all_predicted_multipliers_nonzero": all(
            record["predicted_multiplier_nonzero"]
            for record in multiplier_records
        ),
        "all_observed_multiplier_comparisons_hold": all(
            record["observed_multiplier_matches"] is not False
            for record in multiplier_records
        ),
        "observed_multiplier_comparison_count": sum(
            record["observed_multiplier_matches"] is not None
            for record in multiplier_records
        ),
        "all_phi1_constant_identities_hold": all(
            record["identity_holds"] for record in constant_records
        ),
        "observed_q2_q4_constants_match_formula": observed_constant_matches,
        "input_block_receipt_status": block_receipt["status"],
        "input_endpoint_receipt_status": endpoint_receipt["status"],
        "input_pole_theorem_statement": pole_theorem["statement"],
        "input_pole_theorem_is_all_index": (
            pole_receipt["status"] == "authored_all_n_mechanism_eliminated"
        ),
        "authority_boundary": (
            "The multiplier and constant computations regress the authored "
            "all-d block proof. Universal d,q,s quantifiers come from the "
            "root-product and pole-factorization algebra in the proof note."
        ),
    }


def build_payload(result: dict[str, Any]) -> dict[str, Any]:
    survives = (
        result["all_root_product_identities_hold"]
        and result["all_predicted_multipliers_nonzero"]
        and result["all_observed_multiplier_comparisons_hold"]
        and result["observed_multiplier_comparison_count"] == 7
        and result["all_phi1_constant_identities_hold"]
        and result["observed_q2_q4_constants_match_formula"]
        and result["input_pole_theorem_is_all_index"]
    )
    if not survives:
        raise AssertionError("canonical single-channel block regression failed")
    result_summary = (
        "The authored source calculation proves for every d>=1, q>=1, and "
        "0<=s<d that the leading C-channel row satisfies C_(qd+s)=K_d^(q-1) "
        "(q!)^3 H_q/12^(q-1) C_(d+s), where K_d=12 d^3 M_d(zeta)^3 and "
        "M_d=(p^d-1)/Phi_d at a primitive d-th root. The all-index B=2C "
        "theorem transfers the same law to the full inhomogeneous source. Exact "
        "multiplier comparisons reproduce d=1,...,7, including composite d=4,6; "
        "root-product identities are replayed through d=10 and harmonic constants "
        "through quotient 12. This eliminates nonuniform quotient-block growth "
        "as a first-appearance boundary mechanism."
    )
    next_target = (
        "Prove the all-d nonsingularity of the first-block d-by-d cross matrix, "
        "or find its first exact singular cyclotomic index. The block law then "
        "turns that decision directly into endpoint support and factor-73 "
        "first-appearance noncancellation."
    )
    contract = build_experiment_contract(
        problem_id="erdos_1049",
        target_statement="Prove irrationality of the Lambert value at p=3/2.",
        claim_ceiling=(
            "Authored all-d, all-block leading source identity with exact prior-"
            "receipt comparisons; not cross-block rank, full determinant charge, "
            "or irrationality."
        ),
        hypothesis_id="zudilin_single_C_channel_has_universal_phi1_block_law",
        hypothesis_statement=(
            "The leading C source at n=qd+s is its first-block residue times "
            "K_d^(q-1)(q!)^3H_q/12^(q-1), uniformly in d and s."
        ),
        probe_id="root_product_multiplier_and_harmonic_block_formula",
        probe_question=(
            "Does the pole-separated C channel yield the exact observed prime "
            "and composite multipliers and all Phi_1 harmonic block constants?"
        ),
        computation=(
            "Compute A_d, M_d, and K_d in QQ[p]/(Phi_d), compare K_d against "
            "the committed d=1,...,7 source multipliers, and replay normalized "
            "factorial-harmonic constants."
        ),
        falsifier=(
            "A failed observed multiplier, root-product identity, nonzero claim, "
            "or harmonic normalization invalidates a step of the all-d formula."
        ),
        stop_condition=(
            "Stop multiplier sampling after all committed d<=7 source values, "
            "including both composite cases, match; the universal result must "
            "come from the displayed block-product proof."
        ),
        survival_consequence=(
            "The all-d block theorem eliminates nonuniform quotient growth and "
            "reduces first-appearance cancellation to first-block cross rank."
        ),
        falsification_consequence=(
            "Failure would invalidate the claimed source block proof and return "
            "the boundary analysis to residue-dependent recurrences."
        ),
        consumer_ref=CONSUMER_REF,
        consumer_declarations=["zudilinScalarPlusBorder_cannot_meet_required_charge"],
        analysis_refs=[ANALYSIS_REF, PREVIOUS_PROOF_REF],
        source_refs=[SOURCE_REF],
        input_receipt_refs=INPUT_RECEIPTS,
        result_status="exact_one_way_result",
        result_summary=result_summary,
        progress_class="mechanism_eliminated",
        decision_basis=(
            "The proof removes every quotient-block and residue-dependent degree "
            "of freedom above the first cyclotomic block."
        ),
        next_analytic_target=next_target,
        resource_bounds={
            "maximum_cyclotomic_index": 10,
            "observed_multiplier_comparison_count": result[
                "observed_multiplier_comparison_count"
            ],
            "maximum_observed_cyclotomic_index": 7,
            "maximum_quotient_block": 12,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    refs = (
        SOURCE_REF,
        ANALYSIS_REF,
        PREVIOUS_PROOF_REF,
        CONSUMER_REF,
        *INPUT_RECEIPTS,
    )
    return {
        "schema": "erdos1049-zudilin-single-channel-block-formula-receipt/1",
        "status": "authored_all_d_block_mechanism_eliminated",
        "analytic_theorem": {
            "statement": (
                "For d>=1, q>=1, 0<=s<d, the leading inhomogeneous Zudilin "
                "source obeys S_(qd+s)=K_d^(q-1)(q!)^3H_q/12^(q-1)S_(d+s), "
                "with K_d=12d^3M_d(zeta)^3 nonzero."
            ),
            "proof_ref": ANALYSIS_REF,
            "authority": "authored_mathematical_argument",
            "lean_formalized": False,
        },
        "result": result,
        "experiment_contract": contract,
        "source_records": [source_record(REPO_ROOT, ref) for ref in refs],
    }


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
    if args.from_result is not None:
        result = json.loads(args.from_result.read_text(encoding="utf-8"))
        if result.get("schema") != RAW_SCHEMA:
            raise ValueError("unexpected raw result schema")
    else:
        result = compute()
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
