#!/usr/bin/env python3
"""Regress the all-n pole-separation proof for Zudilin's B-2C channel."""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from math import comb
from pathlib import Path
import sys
from typing import Any

import sympy as sp


REPO_ROOT = Path(__file__).resolve().parents[5]
SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(REPO_ROOT))
sys.path.insert(0, str(SCRIPT_DIR))

from check_zudilin_phi3_associated_graded import gaussian_polynomial  # noqa: E402
from check_zudilin_scalar_content import p  # noqa: E402
from system.lib.formal_math_cyclotomic_local import CyclotomicLocalRing  # noqa: E402
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


TARGET_CYCLOTOMIC_INDICES = tuple(range(1, 6))
TARGET_QUOTIENT_BLOCKS = (2, 3, 4)
ORDINARY_REGRESSION_MAX = 12
SOURCE_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
LOCAL_ENGINE_REF = "system/lib/formal_math_cyclotomic_local.py"
GLOBAL_SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/"
    "check_zudilin_phi3_associated_graded.py"
)
PRIMARY_SOURCE_REF = "annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/extracted.md"
PHI1_ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "ZudilinPhi1AssociatedGradedKernel.md"
)
PREVIOUS_ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "ZudilinChannelDivisibilityLab.md"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "ZudilinChannelDivisibilityProof.md"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "AdelicHeightBridge.lean"
)
INPUT_RECEIPTS = [
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_phi1_kernel_receipt.json",
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_phi1_block_collapse_receipt.json",
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_channel_divisibility_receipt.json",
]
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_pole_separation_receipt.json"
)
RAW_SCHEMA = "erdos1049-zudilin-pole-separation-result/1"


def harmonic(index: int) -> Fraction:
    return sum((Fraction(1, j) for j in range(1, index + 1)), start=Fraction())


def ordinary_block_vectors(quotient: int) -> dict[str, Any]:
    b_vector = []
    c_vector = []
    for pole_block in range(1, quotient + 1):
        b_value = sum(
            (-1) ** (quotient + index)
            * comb(quotient + index, index)
            * comb(quotient, index)
            for index in range(pole_block, quotient + 1)
        )
        c_value = sum(
            (-1) ** index
            * comb(quotient, index)
            * comb(2 * quotient - pole_block - index, quotient)
            for index in range(quotient - pole_block + 1)
        )
        b_vector.append(b_value)
        c_vector.append(c_value)
    difference_vector = [
        b_value - 2 * c_value
        for b_value, c_value in zip(b_vector, c_vector, strict=True)
    ]
    weighted_difference = sum(
        (
            Fraction(value, pole_block)
            for pole_block, value in enumerate(difference_vector, start=1)
        ),
        start=Fraction(),
    )
    legendre_harmonic_sum = sum(
        (
            Fraction(
                (-1) ** (quotient + index)
                * comb(quotient + index, index)
                * comb(quotient, index)
            )
            * harmonic(index)
            for index in range(1, quotient + 1)
        ),
        start=Fraction(),
    )
    return {
        "quotient_block": quotient,
        "B_tail_vector": b_vector,
        "C_coefficient_vector": c_vector,
        "difference_vector": difference_vector,
        "all_C_coefficients_equal_one": all(value == 1 for value in c_vector),
        "legendre_harmonic_sum": str(legendre_harmonic_sum),
        "twice_harmonic_number": str(2 * harmonic(quotient)),
        "legendre_harmonic_identity_holds": (
            legendre_harmonic_sum == 2 * harmonic(quotient)
        ),
        "weighted_difference_sum": str(weighted_difference),
        "weighted_difference_sum_is_zero": weighted_difference == 0,
    }


def _local_vectors(d: int, quotient: int, residue: int) -> dict[str, Any]:
    n = quotient * d + residue
    ring = CyclotomicLocalRing(p, d, precision=1)
    gaussian = ring.gaussian_table(2 * n)

    def reduce_integer(expression: sp.Expr | sp.Poly) -> sp.Poly:
        return ring.reduce(expression)

    cyclotomic = sp.Poly(ring.cyclotomic.as_expr(), p, domain=sp.QQ)

    def reduce_rational(expression: sp.Expr) -> sp.Expr:
        return sp.Poly(sp.expand(expression), p, domain=sp.QQ).rem(
            cyclotomic
        ).as_expr()

    b_vector = []
    c_vector = []
    for pole_block in range(1, quotient + 1):
        pole_index = pole_block * d
        b_value = ring.poly(0)
        for index in range(pole_index, n + 1):
            b_value = reduce_integer(
                b_value
                + ring.multiply(
                    gaussian[(n + index, index)],
                    gaussian[(n, index)],
                    ring.poly(
                        (-1) ** (n + index)
                        * p ** (index * (index + 1) // 2)
                    ),
                )
            )
        c_value = ring.poly(0)
        for index in range(n - pole_index + 1):
            c_value = reduce_integer(
                c_value
                + ring.multiply(
                    gaussian[(n, index)],
                    gaussian[(2 * n - pole_index - index, n)],
                    ring.poly(
                        (-1) ** index
                        * p ** ((n - index) * (n - index + 1) // 2)
                    ),
                )
            )
        b_vector.append(b_value.as_expr())
        c_vector.append(c_value.as_expr())

    ordinary = ordinary_block_vectors(quotient)
    kappa = c_vector[0]
    b_separates = all(
        reduce_rational(observed - kappa * expected) == 0
        for observed, expected in zip(
            b_vector, ordinary["B_tail_vector"], strict=True
        )
    )
    c_separates = all(
        reduce_rational(observed - kappa * expected) == 0
        for observed, expected in zip(
            c_vector, ordinary["C_coefficient_vector"], strict=True
        )
    )
    difference_vector = [
        reduce_rational(b_value - 2 * c_value)
        for b_value, c_value in zip(b_vector, c_vector, strict=True)
    ]
    difference_separates = all(
        reduce_rational(observed - kappa * expected) == 0
        for observed, expected in zip(
            difference_vector, ordinary["difference_vector"], strict=True
        )
    )
    weighted_residue = reduce_rational(
        sum(
            (
                sp.Rational(1, pole_block) * value
                for pole_block, value in enumerate(difference_vector, start=1)
            ),
            start=sp.Integer(0),
        )
    )
    return {
        "cyclotomic_index": d,
        "quotient_block": quotient,
        "residue_class": residue,
        "source_index": n,
        "cyclotomic_polynomial": str(sp.cyclotomic_poly(d, p)),
        "common_residue_factor_kappa": str(sp.factor(kappa)),
        "common_residue_factor_nonzero": kappa != 0,
        "B_vector": [str(sp.factor(value)) for value in b_vector],
        "C_vector": [str(sp.factor(value)) for value in c_vector],
        "difference_vector": [
            str(sp.factor(value)) for value in difference_vector
        ],
        "ordinary_B_vector": ordinary["B_tail_vector"],
        "ordinary_C_vector": ordinary["C_coefficient_vector"],
        "ordinary_difference_vector": ordinary["difference_vector"],
        "B_q_lucas_separates": b_separates,
        "C_q_lucas_separates": c_separates,
        "difference_q_lucas_separates": difference_separates,
        "weighted_pole_residue": str(sp.factor(weighted_residue)),
        "weighted_pole_residue_is_zero": weighted_residue == 0,
        "maximum_gaussian_top": 2 * n,
    }


def _naive_telescope_counterexample() -> dict[str, Any]:
    n = 2
    numerators = []
    for pole_index in (1, 2):
        b_value = sp.Poly(0, p, domain=sp.ZZ)
        for index in range(pole_index, n + 1):
            b_value += (
                gaussian_polynomial(n + index, index)
                * gaussian_polynomial(n, index)
                * sp.Poly(
                    (-1) ** (n + index) * p ** (index * (index + 1) // 2),
                    p,
                )
            )
        c_value = sp.Poly(0, p, domain=sp.ZZ)
        for index in range(n - pole_index + 1):
            c_value += (
                gaussian_polynomial(n, index)
                * gaussian_polynomial(2 * n - pole_index - index, n)
                * sp.Poly(
                    (-1) ** index
                    * p ** ((n - index) * (n - index + 1) // 2),
                    p,
                )
            )
        numerator = b_value - 2 * c_value
        divisor = sp.Poly(p**pole_index - 1, p)
        _, remainder = sp.div(numerator, divisor, domain=sp.ZZ)
        numerators.append(
            {
                "pole_index": pole_index,
                "numerator": str(sp.factor(numerator.as_expr())),
                "remainder_mod_p_to_r_minus_one": str(
                    sp.factor(remainder.as_expr())
                ),
                "denominator_divides_numerator": remainder.is_zero,
            }
        )
    residual_cancellation = sp.cancel(
        sp.sympify(numerators[0]["remainder_mod_p_to_r_minus_one"])
        / (p - 1)
        + sp.sympify(numerators[1]["remainder_mod_p_to_r_minus_one"])
        / (p**2 - 1)
    )
    return {
        "row_index": n,
        "records": numerators,
        "denominator_by_denominator_telescope_fails": not all(
            record["denominator_divides_numerator"] for record in numerators
        ),
        "cross_pole_remainder_sum": str(residual_cancellation),
        "cross_pole_remainders_cancel": residual_cancellation == 0,
    }


def compute(cyclotomic_indices: list[int]) -> dict[str, Any]:
    indices = sorted(set(cyclotomic_indices))
    ordinary_records = [
        ordinary_block_vectors(quotient)
        for quotient in range(1, ORDINARY_REGRESSION_MAX + 1)
    ]
    local_records = [
        _local_vectors(d, quotient, residue)
        for d in indices
        for quotient in TARGET_QUOTIENT_BLOCKS
        for residue in range(d)
    ]
    return {
        "schema": RAW_SCHEMA,
        "cyclotomic_indices": indices,
        "ordinary_records": ordinary_records,
        "local_records": local_records,
        "naive_telescope_counterexample": _naive_telescope_counterexample(),
        "all_ordinary_C_identities_hold": all(
            record["all_C_coefficients_equal_one"] for record in ordinary_records
        ),
        "all_legendre_harmonic_identities_hold": all(
            record["legendre_harmonic_identity_holds"]
            for record in ordinary_records
        ),
        "all_ordinary_weighted_residues_vanish": all(
            record["weighted_difference_sum_is_zero"]
            for record in ordinary_records
        ),
        "all_local_B_vectors_separate": all(
            record["B_q_lucas_separates"] for record in local_records
        ),
        "all_local_C_vectors_separate": all(
            record["C_q_lucas_separates"] for record in local_records
        ),
        "all_local_difference_vectors_separate": all(
            record["difference_q_lucas_separates"] for record in local_records
        ),
        "all_local_weighted_pole_residues_vanish": all(
            record["weighted_pole_residue_is_zero"] for record in local_records
        ),
        "all_common_residue_factors_nonzero": all(
            record["common_residue_factor_nonzero"] for record in local_records
        ),
        "authority_boundary": (
            "Finite computations regress the source factorization used by the "
            "authored all-n proof. The universal quantifiers come from the "
            "q-Lucas and coefficient-extraction argument, not this range."
        ),
    }


def build_payload(result: dict[str, Any]) -> dict[str, Any]:
    if result["cyclotomic_indices"] != list(TARGET_CYCLOTOMIC_INDICES):
        raise ValueError(
            f"canonical receipt requires indices {TARGET_CYCLOTOMIC_INDICES}"
        )
    survives = (
        result["all_ordinary_C_identities_hold"]
        and result["all_legendre_harmonic_identities_hold"]
        and result["all_ordinary_weighted_residues_vanish"]
        and result["all_local_B_vectors_separate"]
        and result["all_local_C_vectors_separate"]
        and result["all_local_difference_vectors_separate"]
        and result["all_local_weighted_pole_residues_vanish"]
        and result["all_common_residue_factors_nonzero"]
        and result["naive_telescope_counterexample"][
            "denominator_by_denominator_telescope_fails"
        ]
        and result["naive_telescope_counterexample"][
            "cross_pole_remainders_cancel"
        ]
    )
    if not survives:
        raise AssertionError("canonical proof regression failed")
    result_summary = (
        "The authored all-n argument proves p^(n+1)P_n^3 divides the cleared "
        "Zudilin difference B_n-2C_n: q-Lucas separates every primitive-root "
        "pole vector into one residue factor times an ordinary binomial vector; "
        "the C vector is identically one, and the harmonic Legendre identity "
        "makes its weighted difference sum zero. Exact regressions cover all "
        "d=1,...,5 residue classes at quotient blocks 2,3,4 and the ordinary "
        "identities through quotient 12. The tempting denominator-by-denominator "
        "telescope is exactly falsified at n=2, where only cross-pole residues "
        "cancel. Thus B=2C on every leading Phi_d layer, all n and d<=n."
    )
    next_target = (
        "Apply the same q-Lucas residue-window factorization to the single C "
        "source row and prove its quotient-block constants 1, 11/4, 50/3 "
        "uniformly in d and the residue class."
    )
    contract = build_experiment_contract(
        problem_id="erdos_1049",
        target_statement="Prove irrationality of the Lambert value at p=3/2.",
        claim_ceiling=(
            "Authored all-n polynomial-divisibility proof with exact finite "
            "source regressions; not a Lean formalization, full determinant "
            "charge theorem, or irrationality proof."
        ),
        hypothesis_id="zudilin_cyclotomic_pole_vectors_q_lucas_separate",
        hypothesis_statement=(
            "At n=qd+s and a primitive d-th root, the B and C pole-residue "
            "vectors share one residue factor and reduce to ordinary binomial "
            "vectors whose weighted difference vanishes."
        ),
        probe_id="exact_pole_separation_and_ordinary_binomial_regression",
        probe_question=(
            "Does the proposed all-n pole cancellation factor through a universal "
            "ordinary vector, and does the stronger termwise telescope fail?"
        ),
        computation=(
            "Construct exact pole vectors in QQ[p]/(Phi_d), compare them with "
            "ordinary binomial tails, replay the coefficient-extraction and "
            "harmonic Legendre identities, and exhibit the n=2 termwise failure."
        ),
        falsifier=(
            "A failed vector separation, nonzero weighted residue, failed "
            "ordinary identity, or survival of the purported n=2 counterexample "
            "invalidates the corresponding proof step."
        ),
        stop_condition=(
            "Stop cyclotomic sampling after all d<=5 residue classes and quotient "
            "blocks 2,3,4 replay the factorization; the all-n quantifiers must "
            "come from the displayed source algebra."
        ),
        survival_consequence=(
            "The authored proof eliminates B/C imbalance at every leading "
            "cyclotomic layer and reduces block collapse to the single C channel."
        ),
        falsification_consequence=(
            "Failure would retain only the finite global divisibility evidence "
            "and return the proof to cross-pole partial fractions."
        ),
        consumer_ref=CONSUMER_REF,
        consumer_declarations=["zudilinScalarPlusBorder_cannot_meet_required_charge"],
        analysis_refs=[ANALYSIS_REF, PREVIOUS_ANALYSIS_REF, PHI1_ANALYSIS_REF],
        source_refs=[
            SOURCE_REF,
            LOCAL_ENGINE_REF,
            GLOBAL_SOURCE_REF,
            PRIMARY_SOURCE_REF,
        ],
        input_receipt_refs=INPUT_RECEIPTS,
        result_status="exact_one_way_result",
        result_summary=result_summary,
        progress_class="mechanism_eliminated",
        decision_basis=(
            "The proof removes an all-index source channel from the surviving "
            "boundary mechanism and falsifies a stronger but incorrect telescope."
        ),
        next_analytic_target=next_target,
        resource_bounds={
            "minimum_cyclotomic_index": min(TARGET_CYCLOTOMIC_INDICES),
            "maximum_cyclotomic_index": max(TARGET_CYCLOTOMIC_INDICES),
            "cyclotomic_index_count": len(TARGET_CYCLOTOMIC_INDICES),
            "maximum_quotient_block": max(TARGET_QUOTIENT_BLOCKS),
            "local_separation_case_count": len(result["local_records"]),
            "ordinary_regression_maximum": ORDINARY_REGRESSION_MAX,
            "maximum_gaussian_top": max(
                int(record["maximum_gaussian_top"])
                for record in result["local_records"]
            ),
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    refs = (
        SOURCE_REF,
        LOCAL_ENGINE_REF,
        GLOBAL_SOURCE_REF,
        PRIMARY_SOURCE_REF,
        ANALYSIS_REF,
        PREVIOUS_ANALYSIS_REF,
        PHI1_ANALYSIS_REF,
        CONSUMER_REF,
    )
    return {
        "schema": "erdos1049-zudilin-pole-separation-receipt/1",
        "status": "authored_all_n_mechanism_eliminated",
        "analytic_theorem": {
            "statement": (
                "For every n>=1, p^(n+1)P_n(p)^3 divides the cleared source "
                "difference Btilde_n(p)-2*Ctilde_n(p). Consequently B=2C on "
                "the leading Phi_d layer for every d<=n."
            ),
            "proof_ref": ANALYSIS_REF,
            "proof_lemmas": [
                "source_denominator_regrouping",
                "primitive_root_pole_criterion",
                "q_lucas_pole_vector_separation",
                "ordinary_C_vector_coefficient_extraction",
                "harmonic_Legendre_weighted_cancellation",
            ],
            "authority": "authored_mathematical_argument",
            "lean_formalized": False,
        },
        "result": result,
        "experiment_contract": contract,
        "source_records": [source_record(REPO_ROOT, ref) for ref in refs],
    }


def _render(payload: dict[str, Any]) -> str:
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def _read_result(path: Path) -> dict[str, Any]:
    result = json.loads(path.read_text(encoding="utf-8"))
    if result.get("schema") != RAW_SCHEMA:
        raise ValueError(f"unexpected raw result schema in {path}")
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cyclotomic-index", type=int, action="append")
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
    result = (
        _read_result(args.from_result)
        if args.from_result is not None
        else compute(args.cyclotomic_index or list(TARGET_CYCLOTOMIC_INDICES))
    )
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
