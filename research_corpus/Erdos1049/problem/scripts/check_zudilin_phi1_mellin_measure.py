#!/usr/bin/env python3
"""Check the canonical signed Mellin measure for the Phi_1 Hankel kernel."""

from __future__ import annotations

import argparse
import json
from math import factorial
from pathlib import Path
import sys
from typing import Any

import sympy as sp


REPO_ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


SOURCE_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "ZudilinPhi1MellinMeasureNoGo.md"
)
KERNEL_ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "ZudilinPhi1AssociatedGradedKernel.md"
)
KERNEL_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_phi1_kernel_receipt.json"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "ZudilinPhi1AssociatedGradedKernel.md"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_phi1_mellin_measure_receipt.json"
)


def compute(max_index: int) -> dict[str, Any]:
    records = []
    for index in range(max_index + 1):
        gamma_value = sp.Integer(factorial(index))
        differentiated_mellin_moment = sp.simplify(
            gamma_value**3
            * (sp.polygamma(0, index + 1) + sp.EulerGamma)
        )
        factorial_harmonic_moment = gamma_value**3 * sp.harmonic(index)
        records.append(
            {
                "index": index,
                "differentiated_mellin_moment": str(differentiated_mellin_moment),
                "factorial_harmonic_moment": str(factorial_harmonic_moment),
                "identity_holds": sp.simplify(
                    differentiated_mellin_moment - factorial_harmonic_moment
                )
                == 0,
            }
        )

    below_threshold_weight = sp.simplify(
        sp.EulerGamma
        + sp.log(sp.exp(-3 * sp.EulerGamma) / 2) / 3
    )
    above_threshold_weight = sp.simplify(
        sp.EulerGamma
        + sp.log(2 * sp.exp(-3 * sp.EulerGamma)) / 3
    )
    return {
        "schema": "erdos1049-zudilin-phi1-mellin-measure/1",
        "moment_records": records,
        "all_exact_moment_regressions_hold": all(
            row["identity_holds"] for row in records
        ),
        "mellin_transform": "Gamma(s)^3",
        "canonical_density_factor": "EulerGamma + log(t)/3",
        "sign_change_threshold": "exp(-3*EulerGamma)",
        "below_threshold_sample_factor": str(below_threshold_weight),
        "above_threshold_sample_factor": str(above_threshold_weight),
        "below_threshold_factor_is_negative": bool(below_threshold_weight < 0),
        "above_threshold_factor_is_positive": bool(above_threshold_weight > 0),
        "zeroth_moment_is_zero": records[0]["factorial_harmonic_moment"] == "0",
        "canonical_shifted_density_is_not_positive": True,
        "authority_boundary": (
            "This eliminates only the canonical product-exponential Mellin density "
            "as a positive Gram measure. It does not rule out another representing "
            "measure or a direct positive-definiteness proof."
        ),
    }


def build_payload(max_index: int) -> dict[str, Any]:
    result = compute(max_index)
    contract = build_experiment_contract(
        problem_id="erdos_1049",
        target_statement="Prove irrationality of the Lambert value at p=3/2.",
        claim_ceiling=(
            "Exact elimination of the canonical product-exponential Mellin density "
            "as a positive measure for the shifted Phi_1 factorial-harmonic kernel; "
            "not a no-go for all positivity proofs."
        ),
        hypothesis_id="canonical_factorial_cube_mellin_measure_is_positive",
        hypothesis_statement=(
            "The factorial cube in m_n=(n!)^3 H_n should supply a direct positive "
            "product-exponential moment measure for the shifted Hankel kernel."
        ),
        probe_id="differentiate_product_exponential_mellin_transform",
        probe_question=(
            "What exact density represents (n!)^3 H_n under the canonical "
            "Gamma(s)^3 Mellin transform, and does it stay nonnegative?"
        ),
        computation=(
            "Differentiate Gamma(s)^3, add EulerGamma times the original Mellin "
            "transform, specialize at s=n+1, and determine the exact sign of the "
            "resulting density factor around exp(-3*EulerGamma)."
        ),
        falsifier=(
            "The representing factor EulerGamma+log(t)/3 is strictly negative "
            "below exp(-3*EulerGamma) and strictly positive above it."
        ),
        stop_condition=(
            "Stop after the exact sign-changing density is derived; do not infer "
            "failure of alternate measures or of direct determinant positivity."
        ),
        survival_consequence=(
            "A nonnegative canonical density would immediately make every shifted "
            "factorial-harmonic Hankel matrix a Gram matrix."
        ),
        falsification_consequence=(
            "The direct product-exponential Gram proof is unavailable; a surviving "
            "route needs another positive functional or determinant recurrence."
        ),
        consumer_ref=CONSUMER_REF,
        analysis_refs=[ANALYSIS_REF, KERNEL_ANALYSIS_REF],
        source_refs=[SOURCE_REF, KERNEL_ANALYSIS_REF],
        input_receipt_refs=[KERNEL_RECEIPT_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "The canonical Mellin density for (n!)^3 H_n is "
            "f_3(t)(EulerGamma+log(t)/3), which changes sign at "
            "exp(-3*EulerGamma); the source-natural positive-measure mechanism is "
            "therefore eliminated exactly."
        ),
        progress_class="mechanism_eliminated",
        decision_basis=(
            "The sign change follows from an all-s Mellin derivative identity and "
            "an exact threshold, not from numerical quadrature or finite minors."
        ),
        next_analytic_target=(
            "Construct an alternate positive functional for the shifted moments or "
            "prove their Hankel signs through condensation/sign-regularity; do not "
            "extend the leading-minor audit."
        ),
        resource_bounds={"maximum_exact_integer_regression_index": max_index},
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos1049-zudilin-phi1-mellin-measure-receipt/1",
        "status": "exact_mechanism_eliminated",
        "result": result,
        "experiment_contract": contract,
        "source_records": [
            source_record(REPO_ROOT, path)
            for path in (SOURCE_REF, ANALYSIS_REF, KERNEL_ANALYSIS_REF)
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-index", type=int, default=20)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.max_index < 0:
        parser.error("--max-index must be nonnegative")

    rendered = json.dumps(build_payload(args.max_index), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.exists() or args.output.read_text(encoding="utf-8") != rendered:
            print(f"stale receipt: {args.output}", file=sys.stderr)
            return 1
        print(json.dumps({"status": "current", "output": str(args.output)}))
        return 0
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(args.output)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
