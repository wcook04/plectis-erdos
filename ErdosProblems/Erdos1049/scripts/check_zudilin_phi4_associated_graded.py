#!/usr/bin/env python3
"""Decide first-appearance Phi_4 cancellation in Zudilin's residual Hankel form."""

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

from check_zudilin_phi3_associated_graded import (  # noqa: E402
    compute as generic_compute,
    enrich_first_appearance_support_theory,
)
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


RANK = 9
CYCLOTOMIC_INDEX = 4
SOURCE_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
GENERIC_SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/"
    "check_zudilin_phi3_associated_graded.py"
)
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
    "ZudilinPhi4AssociatedGradedLab.md"
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
    "erdos1049_zudilin_phi3_associated_graded_receipt.json",
]
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_phi4_associated_graded_receipt.json"
)
RAW_SCHEMA = "erdos1049-zudilin-cyclotomic-associated-graded/2"


def compute() -> dict[str, Any]:
    return generic_compute(rank=RANK, cyclotomic_index=CYCLOTOMIC_INDEX)


def build_payload(result: dict[str, Any]) -> dict[str, Any]:
    if result.get("rank") != RANK or result.get("cyclotomic_index") != CYCLOTOMIC_INDEX:
        raise ValueError("raw result does not describe the rank-nine Phi_4 probe")
    support_theory = result["first_appearance_support_theory"]
    if not support_theory["applicable"] or not support_theory["matches"]:
        raise AssertionError("rank-nine assignment graph violates support theorem")
    cancellation = result["minimum_layer_cancels_coefficientwise"]
    if cancellation:
        progress_class = "mechanism_opened"
        status = "exact_mechanism_opened"
        result_summary = (
            "At its first positive border rank, the complete minimum-Phi_4 "
            "determinant layer cancels coefficientwise modulo Phi_4, opening a "
            "genuinely deeper cyclotomic-content mechanism."
        )
        next_target = (
            "Extract the next Phi_4 layer and seek an all-rank residue-class "
            "identity explaining the extra order."
        )
    else:
        progress_class = "mechanism_eliminated"
        status = "exact_mechanism_eliminated"
        result_summary = (
            "At the first rank with positive forced Phi_4 border order, the "
            "coefficientwise associated-graded determinant is nonzero modulo "
            "Phi_4, so minimum-term cancellation supplies no extra Phi_4 copy."
        )
        next_target = (
            "Seek an all-rank residue-class theorem or rotate to a genuinely new "
            "cyclotomic/integral mechanism; do not extend rank at Phi_4 blindly."
        )

    contract = build_experiment_contract(
        problem_id="erdos_1049",
        target_statement="Prove irrationality of the Lambert value at p=3/2.",
        claim_ceiling=(
            "Exact rank-nine decision for minimum-term Phi_4 cancellation in the "
            "primitive residual Hankel determinant; not an all-rank theorem or "
            "an irrationality proof."
        ),
        hypothesis_id="rank_nine_minimum_phi4_terms_cancel",
        hypothesis_statement=(
            "At the first rank where Phi_4 has positive forced border order, the "
            "signed minimum-order determinant terms cancel coefficientwise and "
            "create a second Phi_4 factor."
        ),
        probe_id="quotient_ring_subset_dp_phi4_minimum_determinant",
        probe_question=(
            "Does the exact rank-nine minimum-weight determinant coefficient "
            "vanish in Q[mu,p]/(p^2+1)?"
        ),
        computation=(
            "Use the termwise-cancelled Z[p] source constructor, extract exact "
            "Phi_4 valuations and leading residues, and sum all minimum-weight "
            "determinant terms by subset DP in Q[mu,p]/(Phi_4)."
        ),
        falsifier=(
            "A nonzero coefficientwise minimum-layer residue proves the rank-nine "
            "Phi_4 order equals the forced border order one."
        ),
        stop_condition=(
            "Stop after the exact first-appearance Phi_4 decision; a higher rank "
            "requires a new residue-class identity."
        ),
        survival_consequence=(
            "Coefficientwise vanishing opens a second Phi_4 content layer not "
            "visible in the entry valuations."
        ),
        falsification_consequence=(
            "Nonvanishing eliminates minimum-layer Phi_4 cancellation at its "
            "first possible rank."
        ),
        consumer_ref=CONSUMER_REF,
        consumer_declarations=["zudilinScalarPlusBorder_cannot_meet_required_charge"],
        analysis_refs=[ANALYSIS_REF],
        source_refs=[
            SOURCE_REF,
            GENERIC_SOURCE_REF,
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
            "Phi_4 is a new cyclotomic quotient and rank nine is its first positive "
            "border rank, so this is a mechanism change rather than a longer Phi_3 "
            "horizon."
        ),
        next_analytic_target=next_target,
        resource_bounds={
            "rank": RANK,
            "maximum_subset_count": 2**RANK,
            "cyclotomic_index": CYCLOTOMIC_INDEX,
            "specialization_regression_count": 2,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    refs = (
        SOURCE_REF,
        GENERIC_SOURCE_REF,
        TROPICAL_ENGINE_REF,
        BORDER_SOURCE_REF,
        SCALAR_SOURCE_REF,
        BLOCK_REF,
        ANALYSIS_REF,
        CONSUMER_REF,
    )
    return {
        "schema": "erdos1049-zudilin-phi4-associated-graded-receipt/1",
        "status": status,
        "result": result,
        "experiment_contract": contract,
        "source_records": [source_record(REPO_ROOT, ref) for ref in refs],
    }


def _read_result(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("schema") != RAW_SCHEMA:
        raise ValueError(f"unexpected raw result schema in {path}")
    return enrich_first_appearance_support_theory(payload)


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
