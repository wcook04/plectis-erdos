#!/usr/bin/env python3
"""Decide rank-seven Phi_3 minimum-term cancellation in Zudilin's residual.

The rational-root probe handles Phi_1 and Phi_2.  This checker enters the first
structurally different cyclotomic quotient, Q[p]/(Phi_3), at the first rank
where the forced Phi_3 border order is positive.  It extracts exact entry
valuations and leading residues, then uses subset dynamic programming to sum
all minimum-weight determinant terms with their signs.

A nonzero residue polynomial in ``mu`` proves that the rank-seven determinant
has exactly the forced Phi_3 order.  A zero residue polynomial proves genuine
minimum-layer cancellation.  Neither outcome is promoted to an all-rank
content theorem or to irrationality of the target Lambert value.
"""

from __future__ import annotations

import argparse
from functools import lru_cache
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
from system.lib.formal_math_tropical_determinant import (  # noqa: E402
    minimum_weight_determinant,
)


RANK = 7
CYCLOTOMIC_INDEX = 3
REFERENCE_ROW_MAXIMUM = 4
SOURCE_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
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
    "ZudilinPhi3AssociatedGradedLab.md"
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
    "erdos1049_zudilin_minimum_term_cancellation_receipt.json",
]
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_phi3_associated_graded_receipt.json"
)


def _polynomial_domain(mu_specialization: int | None) -> Any:
    if mu_specialization is None:
        return sp.QQ.poly_ring(mu)
    return sp.QQ


@lru_cache(None)
def positive_pochhammer(index: int) -> sp.Poly:
    """Return prod_(1<=j<=index) (p^j-1) over Z[p]."""

    if index == 0:
        return sp.Poly(1, p, domain=sp.ZZ)
    return positive_pochhammer(index - 1) * sp.Poly(
        p**index - 1,
        p,
        domain=sp.ZZ,
    )


@lru_cache(None)
def gaussian_polynomial(top: int, bottom: int) -> sp.Poly:
    return positive_pochhammer(top).exquo(
        positive_pochhammer(bottom) * positive_pochhammer(top - bottom)
    )


@lru_cache(None)
def fast_cleared_row(index: int) -> tuple[sp.Poly, sp.Poly, sp.Poly]:
    """Construct the exact cleared source row without rational simplification.

    Multiplying the primary-source sums by the clearing factor cancels every
    Pochhammer denominator term by term.  Keeping those cancellations in
    ``Z[p]`` avoids building a large rational expression merely to cancel it
    globally at the end.
    """

    pochhammer_cube = positive_pochhammer(index) ** 3
    a_polynomial = sp.Poly(0, p, domain=sp.ZZ)
    b_polynomial = sp.Poly(0, p, domain=sp.ZZ)
    for k in range(index + 1):
        shifted_product = sp.Poly(
            sp.prod(p ** (k + j) - 1 for j in range(1, index + 1)),
            p,
            domain=sp.ZZ,
        )
        base = (
            pochhammer_cube.exquo(
                positive_pochhammer(k) * positive_pochhammer(index - k)
            )
            * shifted_product
            * sp.Poly(
                (-1) ** (index + k) * p ** (k * (k + 1) // 2),
                p,
                domain=sp.ZZ,
            )
        )
        a_polynomial += base
        for ell in range(1, k + 1):
            b_polynomial += base.exquo(
                sp.Poly(p**ell - 1, p, domain=sp.ZZ)
            )

    c_polynomial = sp.Poly(0, p, domain=sp.ZZ)
    for ell in range(index):
        inner = sp.Poly(0, p, domain=sp.ZZ)
        for k in range(ell + 1):
            inner += (
                gaussian_polynomial(index, k)
                * gaussian_polynomial(index + ell - k, index)
                * sp.Poly(
                    (-1) ** k * p ** ((index - k) * (index - k + 1) // 2),
                    p,
                    domain=sp.ZZ,
                )
            )
        c_polynomial += pochhammer_cube.exquo(
            sp.Poly(p ** (index - ell) - 1, p, domain=sp.ZZ)
        ) * inner

    scale = sp.Poly(p ** (index + 1), p, domain=sp.ZZ)
    return (
        scale * a_polynomial,
        scale * b_polynomial,
        scale * c_polynomial,
    )


def _leading_residue(
    expression: sp.Expr,
    *,
    cyclotomic: sp.Poly,
    domain: Any,
) -> tuple[int, sp.Expr] | None:
    numerator, denominator = sp.fraction(sp.cancel(expression))
    if sp.expand(denominator) != 1:
        raise AssertionError(f"primitive residual entry is not polynomial: {denominator}")
    quotient = sp.Poly(sp.expand(numerator), p, domain=domain)
    if quotient.is_zero:
        return None
    order = 0
    while True:
        next_quotient, remainder = quotient.div(cyclotomic)
        if not remainder.is_zero:
            residue = quotient.rem(cyclotomic).as_expr()
            return order, residue
        quotient = next_quotient
        order += 1


def associated_graded_probe(
    *,
    rank: int,
    cyclotomic_index: int,
    moments: list[sp.Expr],
    row_content: list[sp.Expr],
    mu_specialization: int | None,
) -> dict[str, Any]:
    domain = _polynomial_domain(mu_specialization)
    cyclotomic = sp.Poly(
        sp.cyclotomic_poly(cyclotomic_index, p),
        p,
        domain=domain,
    )

    weights: list[list[int | None]] = []
    coefficients: list[list[sp.Expr]] = []
    entry_order_mismatches: list[dict[str, int]] = []
    specialized_zero_entries: list[dict[str, int]] = []
    for row in range(rank):
        weight_row: list[int | None] = []
        coefficient_row: list[sp.Expr] = []
        for column in range(rank):
            moment = moments[row + column]
            if mu_specialization is not None:
                moment = moment.subs(mu, mu_specialization)
            expression = sp.cancel(
                moment / (row_content[row] * row_content[column])
            )
            leading = _leading_residue(
                expression,
                cyclotomic=cyclotomic,
                domain=domain,
            )
            if leading is None:
                specialized_zero_entries.append({"row": row, "column": column})
                weight_row.append(None)
                coefficient_row.append(sp.Integer(0))
                continue
            order, residue = leading
            expected = residual_exponent(cyclotomic_index, row, column)
            if order != expected:
                entry_order_mismatches.append(
                    {
                        "row": row,
                        "column": column,
                        "expected_order": expected,
                        "observed_order": order,
                    }
                )
            weight_row.append(order)
            coefficient_row.append(residue)
        weights.append(weight_row)
        coefficients.append(coefficient_row)

    def reduce_mod_cyclotomic(expression: sp.Expr) -> sp.Expr:
        return sp.Poly(sp.expand(expression), p, domain=domain).rem(
            cyclotomic
        ).as_expr()

    determinant = minimum_weight_determinant(
        weights,
        coefficients,
        one=sp.Integer(1),
        zero=sp.Integer(0),
        normalize=reduce_mod_cyclotomic,
    )
    signed_coefficient = reduce_mod_cyclotomic(determinant.signed_coefficient)
    forced_order = rank - 2 * cyclotomic_index
    return {
        "rank": rank,
        "cyclotomic_index": cyclotomic_index,
        "cyclotomic_polynomial": str(sp.cyclotomic_poly(cyclotomic_index, p)),
        "mu_specialization": (
            mu_specialization if mu_specialization is not None else "coefficientwise"
        ),
        "forced_border_order": forced_order,
        "minimum_permutation_order": determinant.minimum_weight,
        "minimum_permutation_count": determinant.minimum_permutation_count,
        "subset_state_count": determinant.subset_state_count,
        "signed_leading_residue": str(sp.factor(signed_coefficient)),
        "signed_leading_residue_nonzero": signed_coefficient != 0,
        "forced_order_is_exact": (
            determinant.minimum_weight == forced_order and signed_coefficient != 0
        ),
        "genuine_minimum_layer_cancellation": signed_coefficient == 0,
        "entry_order_mismatch_count": len(entry_order_mismatches),
        "entry_order_mismatches": entry_order_mismatches,
        "specialized_zero_entry_count": len(specialized_zero_entries),
        "specialized_zero_entries": specialized_zero_entries,
    }


def enrich_first_appearance_support_theory(result: dict[str, Any]) -> dict[str, Any]:
    """Bind the exact first-appearance support count to a computed result.

    At rank ``2d+1``, the residual-exponent graph has exactly
    ``(d+1) * 2**d`` minimum-weight perfect matchings.  Keeping this derived
    check beside the quotient-ring sum prevents a future residue computation
    from silently using the wrong assignment graph.
    """

    enriched = dict(result)
    rank = int(enriched["rank"])
    cyclotomic_index = int(enriched["cyclotomic_index"])
    applicable = rank == 2 * cyclotomic_index + 1
    expected_count = (
        (cyclotomic_index + 1) * 2**cyclotomic_index if applicable else None
    )
    observed_count = enriched["records"][-1]["minimum_permutation_count"]
    enriched["first_appearance_support_theory"] = {
        "applicable": applicable,
        "formula": "(d+1) * 2^d",
        "expected_minimum_permutation_count": expected_count,
        "observed_minimum_permutation_count": observed_count,
        "matches": expected_count == observed_count if applicable else None,
    }
    return enriched


def compute(
    *,
    rank: int = RANK,
    cyclotomic_index: int = CYCLOTOMIC_INDEX,
    reference_row_maximum: int = REFERENCE_ROW_MAXIMUM,
) -> dict[str, Any]:
    if rank <= 2 * cyclotomic_index:
        raise ValueError("rank must exceed twice the cyclotomic index")
    row_constructor_regressions = [
        {
            "index": index,
            "matches_reference_constructor": (
                fast_cleared_row(index) == cleared_row(index)
            ),
        }
        for index in range(reference_row_maximum + 1)
    ]
    rows = [fast_cleared_row(index) for index in range(2 * rank - 1)]
    moments = [
        a.as_expr() * mu - b.as_expr() - c.as_expr() for a, b, c in rows
    ]
    row_content = [
        sp.cancel(predicted_content(index) / p ** (index + 1))
        for index in range(rank)
    ]
    records = [
        associated_graded_probe(
            rank=rank,
            cyclotomic_index=cyclotomic_index,
            moments=moments,
            row_content=row_content,
            mu_specialization=mu_specialization,
        )
        for mu_specialization in (0, 1, None)
    ]
    coefficientwise = records[-1]
    return enrich_first_appearance_support_theory({
        "schema": "erdos1049-zudilin-cyclotomic-associated-graded/2",
        "rank": rank,
        "cyclotomic_index": cyclotomic_index,
        "records": records,
        "row_constructor_regressions": row_constructor_regressions,
        "fast_row_constructor_matches_reference": all(
            row["matches_reference_constructor"]
            for row in row_constructor_regressions
        ),
        "all_nonzero_entry_orders_match_residual_formula": all(
            record["entry_order_mismatch_count"] == 0 for record in records
        ),
        "coefficientwise_has_no_zero_entries": (
            records[-1]["specialized_zero_entry_count"] == 0
        ),
        "minimum_layer_cancels_coefficientwise": coefficientwise[
            "genuine_minimum_layer_cancellation"
        ],
        "forced_cyclotomic_order_is_exact": coefficientwise["forced_order_is_exact"],
        "authority_boundary": (
            f"The quotient-ring computation decides exact rank-{rank} Phi_"
            f"{cyclotomic_index} minimum-layer cancellation. It neither proves "
            "an all-rank content formula nor irrationality at p=3/2."
        ),
    })


def build_payload(result: dict[str, Any]) -> dict[str, Any]:
    support_theory = result["first_appearance_support_theory"]
    if support_theory["applicable"] and not support_theory["matches"]:
        raise AssertionError("minimum assignment graph violates support theorem")
    cancellation = result["minimum_layer_cancels_coefficientwise"]
    if cancellation:
        progress_class = "mechanism_opened"
        status = "exact_mechanism_opened"
        result_summary = (
            "At its first positive border rank, the complete minimum-Phi_3 "
            "determinant layer cancels in Q[mu,p]/(Phi_3), opening a genuinely "
            "deeper cyclotomic-content mechanism."
        )
        next_target = (
            "Extract the next Phi_3 layer and test whether its extra order has "
            "an all-rank residue-class mechanism."
        )
    else:
        progress_class = "mechanism_eliminated"
        status = "exact_mechanism_eliminated"
        result_summary = (
            "At the first rank with positive forced Phi_3 border order, the "
            "coefficientwise associated-graded determinant is nonzero modulo "
            "Phi_3, so minimum-term cancellation supplies no extra Phi_3 copy."
        )
        next_target = (
            "Derive a residue-class all-rank noncancellation theorem or rotate "
            "to the first structurally different cyclotomic index; do not treat "
            "a larger rank at Phi_3 as progress by itself."
        )

    contract = build_experiment_contract(
        problem_id="erdos_1049",
        target_statement="Prove irrationality of the Lambert value at p=3/2.",
        claim_ceiling=(
            "Exact rank-seven decision for minimum-term Phi_3 cancellation in "
            "the primitive residual Hankel determinant; not an all-rank content "
            "theorem or an irrationality proof."
        ),
        hypothesis_id="rank_seven_minimum_phi3_terms_cancel",
        hypothesis_statement=(
            "At the first rank where Phi_3 has positive forced border order, "
            "the signed minimum-order determinant terms cancel coefficientwise "
            "and create a second Phi_3 factor."
        ),
        probe_id="quotient_ring_subset_dp_phi3_minimum_determinant",
        probe_question=(
            "Does the exact rank-seven minimum-weight determinant coefficient "
            "vanish in Q[mu,p]/(p^2+p+1)?"
        ),
        computation=(
            "Cancel the primary-source Pochhammer denominators term by term in "
            "Z[p], extract every primitive residual entry's exact Phi_3 valuation "
            "and leading quotient-ring residue, then use subset dynamic programming "
            "to sum all minimum-weight determinant terms with Leibniz signs in "
            "Q[mu,p]/(Phi_3)."
        ),
        falsifier=(
            "A nonzero coefficientwise minimum-layer residue proves that the "
            "rank-seven Phi_3 order equals the forced border order one."
        ),
        stop_condition=(
            "Stop after the exact coefficientwise rank-seven Phi_3 decision; a "
            "higher-rank scan requires a new residue-class identity."
        ),
        resource_bounds={
            "rank": RANK,
            "maximum_subset_count": 2**RANK,
            "cyclotomic_index": CYCLOTOMIC_INDEX,
            "specialization_regression_count": 2,
            "reference_row_constructor_regression_maximum": REFERENCE_ROW_MAXIMUM,
        },
        result_status="exact_one_way_result",
        result_summary=result_summary,
        decision_basis=(
            "This is the first non-rational-root cyclotomic quotient and the "
            "first rank where its forced border order is positive, so it tests "
            "a structurally distinct cancellation mechanism rather than extending "
            "the Phi_1/Phi_2 horizon."
        ),
        survival_consequence=(
            "Coefficientwise vanishing would open an extra Phi_3 content layer "
            "not visible in the tropical entry valuations."
        ),
        falsification_consequence=(
            "Nonvanishing eliminates minimum-layer Phi_3 cancellation at its "
            "first possible rank; any gain needs a new all-rank identity, another "
            "cyclotomic family, or a different integral model."
        ),
        progress_class=progress_class,
        next_analytic_target=next_target,
        source_refs=[
            SOURCE_REF,
            TROPICAL_ENGINE_REF,
            BORDER_SOURCE_REF,
            SCALAR_SOURCE_REF,
            BLOCK_REF,
        ],
        analysis_refs=[ANALYSIS_REF],
        input_receipt_refs=INPUT_RECEIPTS,
        consumer_ref=CONSUMER_REF,
        consumer_declarations=["zudilinScalarPlusBorder_cannot_meet_required_charge"],
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos1049-zudilin-phi3-associated-graded-receipt/1",
        "status": status,
        "result": result,
        "experiment_contract": contract,
        "source_records": [
            source_record(REPO_ROOT, path)
            for path in (
                SOURCE_REF,
                TROPICAL_ENGINE_REF,
                BORDER_SOURCE_REF,
                SCALAR_SOURCE_REF,
                BLOCK_REF,
                ANALYSIS_REF,
                CONSUMER_REF,
            )
        ],
    }


def _read_result(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("schema") != "erdos1049-zudilin-cyclotomic-associated-graded/2":
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
        result = existing["result"]
        expected = _render(build_payload(result))
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
