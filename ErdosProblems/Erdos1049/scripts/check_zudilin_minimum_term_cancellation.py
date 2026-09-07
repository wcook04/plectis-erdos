#!/usr/bin/env python3
"""Test genuine minimum-order cancellation in Zudilin residual determinants.

The existing border-charge experiment proves a tropical lower bound
``ord_{Phi_d}(det) >= N - 2d`` and exhibits permutations attaining that
weight.  Attainment by individual permutations does not decide whether their
leading coefficients cancel.  This checker computes that signed leading sum
exactly at ``Phi_1 = p-1`` and ``Phi_2 = p+1`` after specializing the auxiliary
variable ``mu`` to 0 and 1.

A nonzero leading sum at either specialization proves that no additional
universal copy of the tested cyclotomic factor divides the determinant at that
rank.  A zero sum at both specializations is only a candidate opening: it must
still be promoted from two specializations to coefficientwise content.
"""

from __future__ import annotations

import argparse
from itertools import permutations
import json
from math import factorial
from pathlib import Path
import sys
from typing import Any

import sympy as sp


REPO_ROOT = Path(__file__).resolve().parents[5]
SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(REPO_ROOT))
sys.path.insert(0, str(SCRIPT_DIR))

from check_zudilin_residual_border_charge import residual_exponent  # noqa: E402
from check_zudilin_scalar_content import (  # noqa: E402
    cleared_row,
    mu,
    p,
    predicted_content,
)
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


SOURCE_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
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
    "ZudilinMinimumTermCancellationLab.md"
)
BLOCK_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "SoutheastBlockDeterminant.lean"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "AdelicHeightBridge.lean"
)
INPUT_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_residual_border_charge_receipt.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_minimum_term_cancellation_receipt.json"
)


def permutation_sign(permutation: tuple[int, ...]) -> int:
    inversions = sum(
        permutation[i] > permutation[j]
        for i in range(len(permutation))
        for j in range(i + 1, len(permutation))
    )
    return -1 if inversions % 2 else 1


def root_leading_term(
    expression: sp.Expr, *, root: int, search_depth: int
) -> tuple[int, sp.Expr] | None:
    """Return exact root order and leading Taylor coefficient, or ``None``."""

    polynomial = sp.Poly(sp.expand(expression), p)
    if polynomial.is_zero:
        return None
    for order in range(search_depth + 1):
        value = sp.expand(polynomial.eval(root))
        if value:
            return order, sp.cancel(value / factorial(order))
        polynomial = polynomial.diff()
    raise AssertionError(
        f"root order exceeded declared search depth {search_depth}"
    )


def primitive_residual_moments(max_rank: int) -> tuple[list[sp.Expr], list[sp.Expr]]:
    rows = [cleared_row(index) for index in range(2 * max_rank - 1)]
    moments = [
        a.as_expr() * mu - b.as_expr() - c.as_expr() for a, b, c in rows
    ]
    row_content = [
        sp.cancel(predicted_content(index) / p ** (index + 1))
        for index in range(max_rank)
    ]
    return moments, row_content


def minimum_term_probe(
    *,
    rank: int,
    cyclotomic_index: int,
    mu_specialization: int | None,
    moments: list[sp.Expr],
    row_content: list[sp.Expr],
) -> dict[str, Any]:
    if cyclotomic_index not in {1, 2}:
        raise ValueError("this exact rational-root probe supports only Phi_1 and Phi_2")
    if 2 * cyclotomic_index >= rank:
        raise ValueError("the tested cyclotomic factor must have positive border order")

    root = 1 if cyclotomic_index == 1 else -1
    cells: dict[tuple[int, int], tuple[int, sp.Expr] | None] = {}
    for row in range(rank):
        for column in range(rank):
            moment = moments[row + column]
            if mu_specialization is not None:
                moment = moment.subs(mu, mu_specialization)
            expression = sp.cancel(moment / (row_content[row] * row_content[column]))
            expected = residual_exponent(cyclotomic_index, row, column)
            cells[row, column] = root_leading_term(
                expression,
                root=root,
                search_depth=expected + 8,
            )

    minimum_order: int | None = None
    minimum_term_count = 0
    leading_sum = sp.Integer(0)
    sample_permutations: list[list[int]] = []
    for permutation in permutations(range(rank)):
        selected = [cells[row, permutation[row]] for row in range(rank)]
        if any(cell is None for cell in selected):
            continue
        nonzero_cells = [cell for cell in selected if cell is not None]
        order = sum(cell[0] for cell in nonzero_cells)
        coefficient = sp.Integer(permutation_sign(permutation))
        for cell in nonzero_cells:
            coefficient *= cell[1]
        if minimum_order is None or order < minimum_order:
            minimum_order = order
            minimum_term_count = 1
            leading_sum = coefficient
            sample_permutations = [list(permutation)]
        elif order == minimum_order:
            minimum_term_count += 1
            leading_sum += coefficient
            if len(sample_permutations) < 8:
                sample_permutations.append(list(permutation))

    if minimum_order is None:
        raise AssertionError("every determinant permutation vanished identically")
    leading_sum = sp.cancel(sp.expand(leading_sum))
    forced_order = rank - 2 * cyclotomic_index
    return {
        "rank": rank,
        "cyclotomic_index": cyclotomic_index,
        "cyclotomic_root": root,
        "mu_specialization": (
            mu_specialization if mu_specialization is not None else "coefficientwise"
        ),
        "forced_border_order": forced_order,
        "minimum_permutation_order": minimum_order,
        "minimum_term_count": minimum_term_count,
        "signed_leading_sum": str(sp.factor(leading_sum)),
        "signed_leading_sum_nonzero": leading_sum != 0,
        "associated_graded_determinant_nonzero": leading_sum != 0,
        "forced_order_is_exact": minimum_order == forced_order and leading_sum != 0,
        "no_extra_order_at_specialization": (
            minimum_order == forced_order and leading_sum != 0
        ),
        "candidate_minimum_term_cancellation": leading_sum == 0,
        "sample_minimum_permutations": sample_permutations,
    }


def compute(max_rank: int) -> dict[str, Any]:
    moments, row_content = primitive_residual_moments(max_rank)
    records = [
        minimum_term_probe(
            rank=rank,
            cyclotomic_index=cyclotomic_index,
            mu_specialization=mu_specialization,
            moments=moments,
            row_content=row_content,
        )
        for rank in range(3, max_rank + 1)
        for cyclotomic_index in range(1, min(2, (rank - 1) // 2) + 1)
        for mu_specialization in (0, 1)
    ]
    rank_maximum = [row for row in records if row["rank"] == max_rank]
    tested_indices = range(1, min(2, (max_rank - 1) // 2) + 1)
    unresolved_indices = [
        cyclotomic_index
        for cyclotomic_index in tested_indices
        if all(
            row["candidate_minimum_term_cancellation"]
            for row in rank_maximum
            if row["cyclotomic_index"] == cyclotomic_index
        )
    ]
    coefficientwise_records = [
        minimum_term_probe(
            rank=max_rank,
            cyclotomic_index=cyclotomic_index,
            mu_specialization=None,
            moments=moments,
            row_content=row_content,
        )
        for cyclotomic_index in unresolved_indices
    ]
    return {
        "schema": "erdos1049-zudilin-minimum-term-cancellation-probe/1",
        "maximum_rank": max_rank,
        "specializations": [0, 1],
        "cyclotomic_indices": [1, 2],
        "records": records,
        "coefficientwise_maximum_rank_records": coefficientwise_records,
        "all_lower_rank_regressions_have_no_extra_order": all(
            row["no_extra_order_at_specialization"]
            for row in records
            if row["rank"] <= 5
        ),
        "maximum_rank_has_candidate_cancellation": any(
            row["candidate_minimum_term_cancellation"] for row in rank_maximum
        ),
        "maximum_rank_has_no_extra_phi1_phi2_order_at_both_specializations": all(
            row["no_extra_order_at_specialization"] for row in rank_maximum
        ),
        "maximum_rank_unresolved_cyclotomic_indices": unresolved_indices,
        "maximum_rank_has_genuine_coefficientwise_cancellation": any(
            row["candidate_minimum_term_cancellation"]
            for row in coefficientwise_records
        ),
        "maximum_rank_universal_extra_phi1_phi2_factor_eliminated": all(
            any(
                row["no_extra_order_at_specialization"]
                for row in rank_maximum
                if row["cyclotomic_index"] == cyclotomic_index
            )
            for cyclotomic_index in tested_indices
        ),
        "authority_boundary": (
            "A nonzero specialized leading sum rules out one extra universal "
            "Phi_d factor at that rank. Specialized cancellation alone does not "
            "prove coefficientwise determinant content or irrationality."
        ),
    }


def build_payload(max_rank: int) -> dict[str, Any]:
    result = compute(max_rank)
    cancellation = result[
        "maximum_rank_has_genuine_coefficientwise_cancellation"
    ]
    if cancellation:
        progress_class = "mechanism_opened"
        result_summary = (
            "At rank six the coefficientwise associated-graded determinant "
            "vanishes for at least one of Phi_1 or Phi_2, proving genuine "
            "cancellation among every minimum-order permutation term."
        )
        next_target = (
            "Compute the exact extra cyclotomic order and determine whether the "
            "cancellation persists with cubic-density charge at all ranks."
        )
    else:
        progress_class = "mechanism_eliminated"
        result_summary = (
            "At rank six the coefficientwise associated-graded determinants for "
            "Phi_1 and Phi_2 are both nonzero, so their orders equal the forced "
            "border orders and minimum-term cancellation supplies no extra copy "
            "of either factor at the first previously undecided rank."
        )
        next_target = (
            "Derive an all-rank associated-graded determinant formula or test a "
            "structurally different cyclotomic family; do not extend the rank-six "
            "audit without such a pattern."
        )
    contract = build_experiment_contract(
        problem_id="erdos_1049",
        target_statement="Prove irrationality of the Lambert value at p=3/2.",
        claim_ceiling=(
            "Exact coefficientwise decision for minimum-term Phi_1/Phi_2 "
            "cancellation at residual Hankel rank six; not an all-rank content "
            "theorem or an irrationality proof."
        ),
        hypothesis_id="rank_six_minimum_cyclotomic_terms_cancel",
        hypothesis_statement=(
            "At the first rank beyond the exact specialization sandwich, the "
            "signed minimum-order determinant terms cancel coefficientwise in mu "
            "and create cyclotomic content deeper than the forced border factor."
        ),
        probe_id="coefficientwise_associated_graded_residual_determinant",
        probe_question=(
            "Do the exact minimum-Phi_1 or minimum-Phi_2 permutation terms of the "
            "rank-six primitive residual determinant cancel as polynomials in mu?"
        ),
        computation=(
            "Extract exact Taylor-leading residual-entry coefficients at p=1 and "
            "p=-1 after mu=0 and mu=1, enumerate the rank-six determinant "
            "permutations, retain the minimum-order terms, and sum them with signs. "
            "One nonzero specialization proves the associated-graded polynomial "
            "is not identically zero."
        ),
        falsifier=(
            "A nonzero associated-graded determinant polynomial for both Phi_1 "
            "and Phi_2 proves exact forced order and eliminates extra rank-six "
            "content from minimum-term cancellation."
        ),
        stop_condition=(
            "Stop after the coefficientwise rank-six decision; do not substitute "
            "a higher-rank scan for an all-rank algebraic pattern."
        ),
        survival_consequence=(
            "Coefficientwise cancellation opens the only remaining source-native "
            "way for this Hankel model to gain charge without changing its rows."
        ),
        falsification_consequence=(
            "The rank-six Phi_1/Phi_2 border orders are exact; any surviving "
            "Hankel route needs a different cyclotomic index, a genuine all-rank "
            "identity, or a different integral model."
        ),
        consumer_ref=CONSUMER_REF,
        consumer_declarations=[
            "zudilinScalarPlusBorder_cannot_meet_required_charge"
        ],
        analysis_refs=[ANALYSIS_REF],
        source_refs=[
            SOURCE_REF,
            BORDER_SOURCE_REF,
            SCALAR_SOURCE_REF,
            BLOCK_REF,
        ],
        input_receipt_refs=[INPUT_RECEIPT_REF],
        result_status="exact_one_way_result",
        result_summary=result_summary,
        progress_class=progress_class,
        decision_basis=(
            "The computation evaluates the structurally new associated-graded "
            "determinant coefficientwise, rather than extending an entry-valuation "
            "table or a finite analytic horizon."
        ),
        next_analytic_target=next_target,
        resource_bounds={
            "maximum_exact_rank": max_rank,
            "maximum_permutation_count": factorial(max_rank),
            "rational_root_cyclotomic_index_count": 2,
            "specialization_regression_count": 2,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    refs = [
        SOURCE_REF,
        BORDER_SOURCE_REF,
        SCALAR_SOURCE_REF,
        ANALYSIS_REF,
        BLOCK_REF,
        CONSUMER_REF,
    ]
    return {
        "schema": "erdos1049-zudilin-minimum-term-cancellation/1",
        "status": (
            "exact_mechanism_opened" if cancellation else "exact_mechanism_eliminated"
        ),
        "result": result,
        "experiment_contract": contract,
        "source_records": [source_record(REPO_ROOT, ref) for ref in refs],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-rank", type=int, default=6)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if not 3 <= args.max_rank <= 6:
        parser.error("--max-rank must lie in [3,6]")
    if args.check and args.output is None:
        parser.error("--check requires --output")
    payload = json.dumps(build_payload(args.max_rank), indent=2, sort_keys=True) + "\n"
    if args.output is None:
        print(payload, end="")
        return 0
    output = args.output.resolve()
    if args.check:
        if not output.exists() or output.read_text(encoding="utf-8") != payload:
            print(f"stale receipt: {output}", file=sys.stderr)
            return 1
        print(json.dumps({"status": "current", "output": str(output)}))
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(payload, encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(output)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
