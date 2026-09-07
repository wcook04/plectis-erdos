#!/usr/bin/env python3
"""Regression checker for the all-rank Phi_1 factorial-harmonic kernel."""

from __future__ import annotations

import argparse
import json
from math import comb, factorial, lcm
from pathlib import Path
import sys
from typing import Any

import sympy as sp


REPO_ROOT = Path(__file__).resolve().parents[5]
SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(REPO_ROOT))
sys.path.insert(0, str(SCRIPT_DIR))

from check_zudilin_residual_border_charge import residual_exponent  # noqa: E402
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)
from system.lib.formal_math_tropical_determinant import (  # noqa: E402
    minimum_weight_determinant,
)


SOURCE_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "ZudilinPhi1AssociatedGradedKernel.md"
)
TROPICAL_ENGINE_REF = "system/lib/formal_math_tropical_determinant.py"
MINIMUM_PROBE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/"
    "check_zudilin_minimum_term_cancellation.py"
)
SCALAR_SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/"
    "check_zudilin_scalar_content.py"
)
PRIMARY_SOURCE_REF = "annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/extracted.md"
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "AdelicHeightBridge.lean"
)
INPUT_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_minimum_term_cancellation_receipt.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_phi1_kernel_receipt.json"
)


def lcm_upto(index: int) -> int:
    return lcm(*range(1, index + 1)) if index >= 2 else 1


def harmonic(index: int) -> sp.Rational:
    return sp.harmonic(index)


def moment(index: int) -> sp.Rational:
    return sp.Integer(factorial(index)) ** 3 * harmonic(index)


def diagonal_scale(index: int) -> sp.Rational:
    if index == 0:
        return sp.Integer(1)
    return sp.Rational((-1) ** index * lcm_upto(index), factorial(index) ** 3)


def primitive_limit(index: int) -> sp.Expr:
    if index == 0:
        return sp.symbols("mu")
    return (-1) ** (index + 1) * 3 * lcm_upto(index) * harmonic(index)


def source_sum_checks(max_index: int) -> list[dict[str, Any]]:
    rows = []
    for n in range(1, max_index + 1):
        legendre_sum = sum(
            (-1) ** k * comb(n, k) * comb(n + k, k)
            for k in range(n + 1)
        )
        harmonic_sum = sum(
            (-1) ** k * comb(n, k) * comb(n + k, k) * harmonic(k)
            for k in range(n + 1)
        )
        convolution_values = [
            sum(
                (-1) ** k * comb(n, k) * comb(n + ell - k, n)
                for k in range(ell + 1)
            )
            for ell in range(n)
        ]
        rows.append(
            {
                "index": n,
                "legendre_endpoint_identity": legendre_sum == (-1) ** n,
                "harmonic_legendre_identity": (
                    harmonic_sum == (-1) ** n * 2 * harmonic(n)
                ),
                "convolution_identity": all(value == 1 for value in convolution_values),
                "primitive_moment_limit": str(primitive_limit(n)),
            }
        )
    return rows


def associated_graded_entry(row: int, column: int, mu: sp.Symbol) -> sp.Expr:
    index = row + column
    if index == 0:
        return mu
    if row == 0 or column == 0:
        return -3 * diagonal_scale(index) * moment(index)
    return -3 * diagonal_scale(row) * diagonal_scale(column) * moment(index)


def rank_check(rank: int) -> dict[str, Any]:
    mu = sp.symbols("mu")
    weights = [
        [residual_exponent(1, row, column) for column in range(rank)]
        for row in range(rank)
    ]
    coefficients = [
        [associated_graded_entry(row, column, mu) for column in range(rank)]
        for row in range(rank)
    ]
    tropical = minimum_weight_determinant(
        weights,
        coefficients,
        one=sp.Integer(1),
        zero=sp.Integer(0),
        normalize=sp.expand,
    )
    hankel = sp.Matrix(
        rank,
        rank,
        lambda row, column: moment(row + column),
    )
    scale_square = sp.prod(diagonal_scale(index) ** 2 for index in range(1, rank))
    closed_form = sp.factor((-3) ** rank * scale_square * hankel.det(method="domain-ge"))
    coefficient = sp.factor(tropical.signed_coefficient)
    return {
        "rank": rank,
        "minimum_order": tropical.minimum_weight,
        "expected_minimum_order": rank - 2,
        "minimum_permutation_count": tropical.minimum_permutation_count,
        "expected_minimum_permutation_count": (rank - 1) * factorial(rank - 1),
        "subset_state_count": tropical.subset_state_count,
        "signed_minimum_coefficient": str(coefficient),
        "factorial_harmonic_hankel_formula": str(closed_form),
        "formula_matches": sp.expand(coefficient - closed_form) == 0,
        "coefficient_is_mu_independent": mu not in coefficient.free_symbols,
        "coefficient_is_nonzero": coefficient != 0,
        "full_hankel_determinant_sign": int(sp.sign(hankel.det(method="domain-ge"))),
    }


def compute(max_index: int, max_rank: int) -> dict[str, Any]:
    source_checks = source_sum_checks(max_index)
    rank_checks = [rank_check(rank) for rank in range(2, max_rank + 1)]
    return {
        "schema": "erdos1049-zudilin-phi1-associated-graded-kernel/1",
        "source_sum_checks": source_checks,
        "rank_checks": rank_checks,
        "all_source_sum_regressions_hold": all(
            row["legendre_endpoint_identity"]
            and row["harmonic_legendre_identity"]
            and row["convolution_identity"]
            for row in source_checks
        ),
        "all_bordered_formula_regressions_hold": all(
            row["formula_matches"] for row in rank_checks
        ),
        "all_minimum_layers_are_mu_independent": all(
            row["coefficient_is_mu_independent"] for row in rank_checks
        ),
        "analytic_identity": (
            "L_N=(-3)^N*(prod_{1<=i<N}((-1)^i*lcm(1..i)/(i!)^3)^2)"
            "*det_{0<=i,j<N}(((i+j)!)^3*H_{i+j})"
        ),
        "authority_boundary": (
            "The all-rank identity is established by the source-limit and "
            "bordered-determinant algebra in the bound analysis note. Finite "
            "checks validate the translation but do not prove nonvanishing."
        ),
    }


def build_payload(max_index: int, max_rank: int) -> dict[str, Any]:
    result = compute(max_index, max_rank)
    contract = build_experiment_contract(
        problem_id="erdos_1049",
        target_statement="Prove irrationality of the Lambert value at p=3/2.",
        claim_ceiling=(
            "All-rank independence of the minimum Phi_1 layer from mu and its "
            "exact reduction to a factorial-harmonic Hankel determinant; not a "
            "nonvanishing theorem or irrationality proof."
        ),
        hypothesis_id="phi1_minimum_layer_depends_on_pade_parameter",
        hypothesis_statement=(
            "Extra Phi_1 order might arise through cancellation between the mu "
            "coefficient channel and the two inhomogeneous source channels."
        ),
        probe_id="source_limit_to_factorial_harmonic_hankel_kernel",
        probe_question=(
            "Which exact all-rank coefficient controls the minimum Phi_1 layer, "
            "and can the Padé parameter mu participate in its cancellation?"
        ),
        computation=(
            "Check the Legendre endpoint, harmonic-weighted Legendre, and "
            "binomial-convolution identities; independently compute the weighted "
            "determinant layer by subset DP and compare it with the closed bordered "
            "factorial-harmonic Hankel determinant."
        ),
        falsifier=(
            "The source A-channel has one additional p-1 factor, while the B and C "
            "limits combine to a fixed nonzero primitive sequence; hence mu cannot "
            "appear in the minimum determinant layer at any rank."
        ),
        stop_condition=(
            "Stop after the all-rank kernel identity and existing-rank regressions; "
            "do not count additional positive finite Hankel minors as nonvanishing."
        ),
        resource_bounds={
            "maximum_source_identity_regression_index": max_index,
            "maximum_bordered_formula_regression_rank": max_rank,
        },
        result_status="exact_one_way_result",
        result_summary=(
            "The minimum Phi_1 layer is mu-independent at every rank and equals an "
            "explicit nonzero scalar times det(((i+j)!)^3 H_{i+j}); this eliminates "
            "mu-tuned cancellation and isolates conditional positivity as the sole "
            "remaining Phi_1 minimum-layer mechanism."
        ),
        decision_basis=(
            "The conclusion comes from an all-rank source limit and exact bordered "
            "determinant factorization, not from extrapolating the finite rank table."
        ),
        survival_consequence=(
            "Any extra Phi_1 order must be an intrinsic zero of the explicit "
            "factorial-harmonic Hankel determinant, uniformly in mu."
        ),
        falsification_consequence=(
            "The approximation parameter cannot be tuned to create or remove "
            "minimum-layer Phi_1 cancellation at any rank."
        ),
        progress_class="mechanism_eliminated",
        next_analytic_target=(
            "Prove the southeast shifted factorial-harmonic Hankel matrix positive "
            "definite, or find an exact rank where its determinant changes sign; "
            "finite positive-minor extension alone is not progress."
        ),
        source_refs=[
            SOURCE_REF,
            TROPICAL_ENGINE_REF,
            MINIMUM_PROBE_REF,
            SCALAR_SOURCE_REF,
            PRIMARY_SOURCE_REF,
        ],
        analysis_refs=[ANALYSIS_REF],
        input_receipt_refs=[INPUT_RECEIPT_REF],
        consumer_ref=CONSUMER_REF,
        consumer_declarations=["zudilinScalarPlusBorder_cannot_meet_required_charge"],
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos1049-zudilin-phi1-associated-graded-kernel-receipt/1",
        "status": "exact_mechanism_eliminated",
        "result": result,
        "experiment_contract": contract,
        "source_records": [
            source_record(REPO_ROOT, path)
            for path in (
                SOURCE_REF,
                TROPICAL_ENGINE_REF,
                MINIMUM_PROBE_REF,
                SCALAR_SOURCE_REF,
                PRIMARY_SOURCE_REF,
                ANALYSIS_REF,
                CONSUMER_REF,
            )
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-index", type=int, default=12)
    parser.add_argument("--max-rank", type=int, default=6)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.max_index < 1 or not 2 <= args.max_rank <= 8:
        parser.error("require max-index >= 1 and 2 <= max-rank <= 8")

    rendered = json.dumps(
        build_payload(args.max_index, args.max_rank),
        indent=2,
        sort_keys=True,
    ) + "\n"
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
