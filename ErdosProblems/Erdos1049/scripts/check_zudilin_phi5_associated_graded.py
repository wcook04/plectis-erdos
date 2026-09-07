#!/usr/bin/env python3
"""Decide first-appearance Phi_5 cancellation using bounded local arithmetic."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[5]
SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(REPO_ROOT))
sys.path.insert(0, str(SCRIPT_DIR))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)
from zudilin_cyclotomic_local import associated_graded_first_appearance  # noqa: E402


CYCLOTOMIC_INDEX = 5
RANK = 2 * CYCLOTOMIC_INDEX + 1
SOURCE_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
LOCAL_ADAPTER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/"
    "zudilin_cyclotomic_local.py"
)
LOCAL_ENGINE_REF = "system/lib/formal_math_cyclotomic_local.py"
TROPICAL_ENGINE_REF = "system/lib/formal_math_tropical_determinant.py"
BORDER_SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/"
    "check_zudilin_residual_border_charge.py"
)
SCALAR_SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/"
    "check_zudilin_scalar_content.py"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "ZudilinPhi5AssociatedGradedLab.md"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "AdelicHeightBridge.lean"
)
BLOCK_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "SoutheastBlockDeterminant.lean"
)
INPUT_RECEIPTS = [
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_residual_border_charge_receipt.json",
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_phi4_associated_graded_receipt.json",
]
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_phi5_associated_graded_receipt.json"
)
RAW_SCHEMA = "erdos1049-zudilin-local-cyclotomic-associated-graded/1"


def compute() -> dict[str, Any]:
    return associated_graded_first_appearance(CYCLOTOMIC_INDEX)


def build_payload(result: dict[str, Any]) -> dict[str, Any]:
    if result.get("rank") != RANK or result.get("cyclotomic_index") != CYCLOTOMIC_INDEX:
        raise ValueError("raw result does not describe the rank-eleven Phi_5 probe")
    if not result["minimum_assignment_count_matches_formula"]:
        raise AssertionError("Phi_5 assignment graph violates the support theorem")
    if not result["local_constructor_matches_global_source"]:
        raise AssertionError("local constructor failed its global-source regression")
    if not result["primitive_mu_coefficient_zero_from_index_d_through_4d"]:
        raise AssertionError("Phi_5 rows contradict the all-index mu-vanishing identity")
    if not result["signed_leading_residue_is_mu_independent"]:
        raise AssertionError("Phi_5 minimum layer contradicts parameter independence")

    cancellation = result["genuine_minimum_layer_cancellation"]
    if cancellation:
        progress_class = "mechanism_opened"
        status = "exact_mechanism_opened"
        result_summary = (
            "At first appearance, the 192 minimum Phi_5 assignments cancel "
            "coefficientwise in Q[p]/(Phi_5), opening an extra local factor; "
            "the all-index source identity rules out mu-dependent tuning."
        )
        next_target = (
            "Extract the next Phi_5 layer locally and identify the residue-class "
            "identity responsible for the extra order."
        )
    else:
        progress_class = "mechanism_eliminated"
        status = "exact_mechanism_eliminated"
        result_summary = (
            "At first appearance, the exact coefficientwise sum of all 192 "
            "minimum Phi_5 assignments is a nonzero element of Q[p]/(Phi_5), "
            "so no extra Phi_5 copy occurs and mu-dependent tuning is impossible."
        )
        next_target = (
            "Do not extend the Phi_5 rank horizon blindly; use the local engine "
            "to seek an all-index identity or rotate to a distinct mechanism."
        )

    contract = build_experiment_contract(
        problem_id="erdos_1049",
        target_statement="Prove irrationality of the Lambert value at p=3/2.",
        claim_ceiling=(
            "Exact rank-eleven first-appearance Phi_5 minimum-layer decision; "
            "not an all-rank theorem or an irrationality proof."
        ),
        hypothesis_id="rank_eleven_minimum_phi5_terms_cancel",
        hypothesis_statement=(
            "At the first rank where Phi_5 has positive forced border order, "
            "the signed minimum determinant layer vanishes coefficientwise."
        ),
        probe_id="local_phi_adic_subset_dp_phi5_minimum_determinant",
        probe_question=(
            "Does the exact rank-eleven minimum determinant coefficient vanish "
            "in Q[mu,p]/(p^4+p^3+p^2+p+1)?"
        ),
        computation=(
            "Construct every source row only modulo Phi_5^(e_5(n)+1), divide "
            "the known scalar order locally, assemble primitive entry residues "
            "from scalar units, and sum the minimum layer by subset DP."
        ),
        falsifier=(
            "A nonzero local coefficientwise residue proves exact forced Phi_5 "
            "order one at rank eleven."
        ),
        stop_condition=(
            "Stop after the exact first-appearance decision; a higher Phi_5 rank "
            "requires a new all-index residue mechanism."
        ),
        survival_consequence=(
            "Vanishing opens a second Phi_5 content layer and licenses local "
            "extraction of its next associated-graded coefficient."
        ),
        falsification_consequence=(
            "Nonvanishing eliminates first-appearance minimum-layer Phi_5 "
            "cancellation as the missing height mechanism; the source identity "
            "independently eliminates parameter tuning in this layer for all d."
        ),
        consumer_ref=CONSUMER_REF,
        consumer_declarations=["zudilinScalarPlusBorder_cannot_meet_required_charge"],
        analysis_refs=[ANALYSIS_REF],
        source_refs=[
            SOURCE_REF,
            LOCAL_ADAPTER_REF,
            LOCAL_ENGINE_REF,
            TROPICAL_ENGINE_REF,
            BORDER_SOURCE_REF,
            SCALAR_SOURCE_REF,
            BLOCK_REF,
        ],
        input_receipt_refs=INPUT_RECEIPTS,
        result_status="exact_one_way_result",
        result_summary=result_summary,
        progress_class=progress_class,
        decision_basis=(
            "Phi_5 is the first cyclotomic field of degree four in this sequence, "
            "and rank eleven is its first positive-border rank. The local engine "
            "changes both the quotient field and computational mechanism."
        ),
        next_analytic_target=next_target,
        resource_bounds={
            "rank": RANK,
            "maximum_subset_count": 2**RANK,
            "cyclotomic_index": CYCLOTOMIC_INDEX,
            "maximum_local_modulus_degree": result["maximum_local_modulus_degree"],
            "global_source_regression_row_count": len(
                result["local_constructor_regressions"]
            ),
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    refs = (
        SOURCE_REF,
        LOCAL_ADAPTER_REF,
        LOCAL_ENGINE_REF,
        TROPICAL_ENGINE_REF,
        BORDER_SOURCE_REF,
        SCALAR_SOURCE_REF,
        BLOCK_REF,
        ANALYSIS_REF,
        CONSUMER_REF,
    )
    return {
        "schema": "erdos1049-zudilin-phi5-associated-graded-receipt/1",
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
