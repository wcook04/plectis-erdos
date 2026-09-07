#!/usr/bin/env python3
"""Certify all-index nonsingularity of the Zudilin first-block cross matrix."""

from __future__ import annotations

import argparse
from fractions import Fraction
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
from system.lib.formal_math_cyclotomic_local import CyclotomicLocalRing  # noqa: E402
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)
from system.lib.formal_math_tropical_determinant import (  # noqa: E402
    minimum_weight_determinant,
)
from system.lib.formal_math_wrapped_hankel import (  # noqa: E402
    certify_wrapped_hankel_antidiagonal,
    wrapped_hankel_assignment_weights,
    wrapped_hankel_resultant,
)


SOURCE_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
INFRA_REF = "system/lib/formal_math_wrapped_hankel.py"
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "ZudilinFirstBlockResultantProof.md"
)
BLOCK_PROOF_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "ZudilinSingleChannelBlockFormulaProof.md"
)
BORDER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "ZudilinFirstAppearanceBorderFormLab.md"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "AdelicHeightBridge.lean"
)
BLOCK_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_single_channel_block_formula_receipt.json"
)
BORDER_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_first_appearance_border_form_receipt.json"
)
INPUT_RECEIPTS = [BLOCK_RECEIPT_REF, BORDER_RECEIPT_REF]
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_first_block_resultant_receipt.json"
)
RAW_SCHEMA = "erdos1049-zudilin-first-block-resultant-result/1"


def _two_adic_order(value: int) -> int:
    if value <= 0:
        raise ValueError("two-adic order requires a positive integer")
    order = 0
    while value % 2 == 0:
        value //= 2
        order += 1
    return order


def dyadic_weight_sum(limit: int) -> int:
    """Return ``sum_(1<=c<=limit) 2^v2(c)``."""

    return sum(2 ** _two_adic_order(value) for value in range(1, limit + 1))


def _valuation_record(d: int) -> dict[str, Any]:
    if d % 2:
        weights = [0] * d
        wrap_weight = 2
        slope = Fraction(1, d)
        two_power_exponent = 0
        odd_part = d
        ramification_index = 1
        dyadic_bound_holds = True
        terminal_weight_formula_holds = True
    else:
        two_power_exponent = _two_adic_order(d)
        odd_part = d // 2**two_power_exponent
        ramification_index = 2 ** (two_power_exponent - 1)
        block_count = 2**two_power_exponent
        weights = [
            3 * dyadic_weight_sum(index // odd_part)
            for index in range(d)
        ]
        wrap_weight = (
            (3 * two_power_exponent + 5) * ramification_index
        )
        slope = Fraction(3 * two_power_exponent + 4, 2 * odd_part)
        dyadic_bound_holds = all(
            2 * dyadic_weight_sum(limit)
            <= (two_power_exponent + 1) * limit
            for limit in range(1, block_count)
        )
        terminal_weight_formula_holds = (
            weights[-1]
            == 3 * two_power_exponent * ramification_index
        )

    certificate = certify_wrapped_hankel_antidiagonal(
        weights,
        wrap_weight,
        slope,
    )
    return {
        "cyclotomic_index": d,
        "two_power_exponent": two_power_exponent,
        "odd_part": odd_part,
        "ramification_index": ramification_index,
        "wrap_weight": wrap_weight,
        "supporting_slope": str(slope),
        "terminal_first_block_weight": weights[-1],
        "antidiagonal_weight": certificate.antidiagonal_weight,
        "minimum_strict_gap": (
            None
            if certificate.minimum_strict_gap is None
            else str(certificate.minimum_strict_gap)
        ),
        "dyadic_average_bound_holds": dyadic_bound_holds,
        "terminal_weight_formula_holds": terminal_weight_formula_holds,
        "unique_antidiagonal_minimum": (
            certificate.unique_antidiagonal_minimum
        ),
    }


def _tropical_replay(d: int) -> dict[str, Any]:
    valuation = _valuation_record(d)
    if d % 2:
        weights = [0] * d
    else:
        odd_part = int(valuation["odd_part"])
        weights = [
            3 * dyadic_weight_sum(index // odd_part)
            for index in range(d)
        ]
    wrap_weight = int(valuation["wrap_weight"])
    determinant = minimum_weight_determinant(
        wrapped_hankel_assignment_weights(weights, wrap_weight),
        [[1] * d for _ in range(d)],
        one=1,
        zero=0,
    )
    return {
        "cyclotomic_index": d,
        "minimum_weight": determinant.minimum_weight,
        "antidiagonal_weight": valuation["antidiagonal_weight"],
        "minimum_permutation_count": determinant.minimum_permutation_count,
        "matches_affine_certificate": (
            determinant.minimum_weight == valuation["antidiagonal_weight"]
            and determinant.minimum_permutation_count == 1
        ),
    }


def _first_block_symbols(d: int) -> tuple[list[sp.Expr], sp.Expr]:
    ring = CyclotomicLocalRing(p, d, 1)
    gaussian = ring.gaussian_table(2 * d)
    prefix = ring.poly(1)
    first_block: list[sp.Expr] = []
    for residue in range(d):
        if residue:
            prefix = ring.multiply(prefix, p**residue - 1)
        finite_sum = ring.poly(0)
        for index in range(residue + 1):
            term = ring.multiply(
                (-1) ** index * p ** (index * (index + 1) // 2),
                gaussian[(residue, index)],
                gaussian[(residue + index, index)],
            )
            finite_sum = ring.reduce(finite_sum + term)
        symbol = ring.multiply(
            (-1) ** residue * p**residue,
            prefix,
            prefix,
            prefix,
            finite_sum,
        )
        first_block.append(symbol.as_expr())

    cyclotomic = sp.Poly(sp.cyclotomic_poly(d, p), p, domain=sp.ZZ)
    proper_factor = sp.div(
        sp.Poly(p**d - 1, p, domain=sp.ZZ),
        cyclotomic,
    )[0]
    multiplier = ring.reduce(12 * d**3 * proper_factor**3).as_expr()
    return first_block, multiplier


def _cyclotomic_record(d: int, *, direct_resultant: bool) -> dict[str, Any]:
    ring = CyclotomicLocalRing(p, d, 1)
    first_block, multiplier = _first_block_symbols(d)
    expected_terminal = ring.reduce(d**3 * p ** (d - 1)).as_expr()
    record: dict[str, Any] = {
        "cyclotomic_index": d,
        "cyclotomic_polynomial": str(sp.cyclotomic_poly(d, p)),
        "first_block_terminal": str(sp.factor(first_block[-1])),
        "expected_terminal_d_cubed_zeta_inverse": str(
            sp.factor(expected_terminal)
        ),
        "terminal_identity_holds": (
            ring.reduce(first_block[-1] - expected_terminal).is_zero
        ),
        "wrap_multiplier": str(sp.factor(multiplier)),
        "direct_resultant_replayed": direct_resultant,
    }
    if direct_resultant:
        variable = sp.symbols("x")
        determinant = ring.reduce(
            wrapped_hankel_resultant(first_block, multiplier, variable)
        ).as_expr()
        record.update(
            {
                "first_block_determinant": str(sp.factor(determinant)),
                "first_block_determinant_nonzero": determinant != 0,
            }
        )
    else:
        record["first_block_determinant_nonzero"] = None
    return record


def compute() -> dict[str, Any]:
    valuation_records = [_valuation_record(d) for d in range(1, 257)]
    tropical_replays = [_tropical_replay(d) for d in range(1, 15)]
    cyclotomic_records = [
        _cyclotomic_record(d, direct_resultant=d <= 6)
        for d in range(1, 13)
    ]
    return {
        "schema": RAW_SCHEMA,
        "valuation_records": valuation_records,
        "tropical_replays": tropical_replays,
        "cyclotomic_records": cyclotomic_records,
        "all_affine_certificates_strict": all(
            record["unique_antidiagonal_minimum"]
            for record in valuation_records
        ),
        "all_dyadic_bounds_hold": all(
            record["dyadic_average_bound_holds"]
            for record in valuation_records
        ),
        "all_terminal_weight_formulas_hold": all(
            record["terminal_weight_formula_holds"]
            for record in valuation_records
        ),
        "all_tropical_replays_match": all(
            record["matches_affine_certificate"]
            for record in tropical_replays
        ),
        "all_terminal_symbol_identities_hold": all(
            record["terminal_identity_holds"]
            for record in cyclotomic_records
        ),
        "all_direct_resultants_nonzero": all(
            record["first_block_determinant_nonzero"] is not False
            for record in cyclotomic_records
        ),
        "authority_boundary": (
            "Finite certificate and exact-resultant replays regress the authored "
            "all-d valuation proof. The universal quantifier comes from the "
            "dyadic-sum inequality and affine-support argument in the proof note."
        ),
    }


def build_payload(result: dict[str, Any]) -> dict[str, Any]:
    survives = all(
        result[field]
        for field in (
            "all_affine_certificates_strict",
            "all_dyadic_bounds_hold",
            "all_terminal_weight_formulas_hold",
            "all_tropical_replays_match",
            "all_terminal_symbol_identities_hold",
            "all_direct_resultants_nonzero",
        )
    )
    if not survives:
        raise AssertionError("first-block wrapped-Hankel certificate failed")

    result_summary = (
        "For every cyclotomic index d, the normalized first source block gives "
        "a wrapped Hankel matrix. At a prime above 2, an explicit affine line "
        "strictly supports every entry valuation above the anti-diagonal; the "
        "anti-diagonal is therefore the unique minimum determinant term and "
        "the d-by-d block is nonsingular. Combined with the all-d source block "
        "law and fixed factor-73 border identity, this proves noncancellation "
        "of the complete cyclotomic first-appearance layer for every d."
    )
    next_target = (
        "Exploit the now-proved all-d first-appearance residues in a global "
        "cyclotomic resultant/norm estimate. Decide whether their cumulative "
        "degree beats the known scalar-plus-border ceiling, rather than sampling "
        "larger local ranks."
    )
    contract = build_experiment_contract(
        problem_id="erdos_1049",
        target_statement="Prove irrationality of the Lambert value at p=3/2.",
        claim_ceiling=(
            "Authored all-d nonsingularity and consequent first-appearance "
            "cyclotomic noncancellation; not an asymptotic cumulative valuation, "
            "required denominator charge, or irrationality proof."
        ),
        hypothesis_id="zudilin_first_block_is_uniformly_nonsingular",
        hypothesis_statement=(
            "Every normalized d-by-d first source block has a nonzero wrapped-"
            "Hankel determinant in Q(zeta_d)."
        ),
        probe_id="two_adic_affine_support_and_resultant",
        probe_question=(
            "Does a 2-adic supporting line isolate one determinant permutation "
            "for every odd, even, and six-divisible cyclotomic index?"
        ),
        computation=(
            "Construct exact dyadic valuation lower bounds, certify the affine "
            "gaps through d=256, replay subset-DP minima through d=14, and "
            "reconstruct the cyclotomic first-block symbol through d=12."
        ),
        falsifier=(
            "A nonpositive affine gap, tied tropical minimum, failed terminal "
            "symbol identity, or zero direct resultant refutes the mechanism."
        ),
        stop_condition=(
            "Stop local index extension once the all-d affine inequalities are "
            "proved; further first-appearance horizons are equivalent audits."
        ),
        survival_consequence=(
            "The first-block rank obstruction and expanding homogeneous boundary "
            "mode are eliminated for all d; the route advances to cumulative "
            "global cyclotomic charge."
        ),
        falsification_consequence=(
            "A failed index would expose an exact singular boundary mode and a "
            "structurally distinct cancellation mechanism."
        ),
        consumer_ref=CONSUMER_REF,
        consumer_declarations=[
            "zudilinScalarPlusBorder_cannot_meet_required_charge"
        ],
        analysis_refs=[ANALYSIS_REF, BLOCK_PROOF_REF, BORDER_REF],
        source_refs=[SOURCE_REF, INFRA_REF],
        input_receipt_refs=INPUT_RECEIPTS,
        result_status="exact_one_way_result",
        result_summary=result_summary,
        progress_class="mechanism_eliminated",
        decision_basis=(
            "A unique lowest nonzero 2-adic determinant term precludes algebraic "
            "cancellation at every cyclotomic index."
        ),
        next_analytic_target=next_target,
        resource_bounds={
            "maximum_affine_certificate_index": 256,
            "maximum_subset_dp_index": 14,
            "maximum_cyclotomic_symbol_index": 12,
            "maximum_direct_resultant_index": 6,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    refs = (
        SOURCE_REF,
        INFRA_REF,
        ANALYSIS_REF,
        BLOCK_PROOF_REF,
        BORDER_REF,
        CONSUMER_REF,
        *INPUT_RECEIPTS,
    )
    return {
        "schema": "erdos1049-zudilin-first-block-resultant-receipt/1",
        "status": "authored_all_d_first_appearance_noncancellation",
        "analytic_theorem": {
            "statement": (
                "For every d>=1, the normalized d-by-d first-block cross "
                "matrix is nonsingular over Q(zeta_d); consequently the full "
                "Zudilin first-appearance associated-graded residue is nonzero."
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
        print(
            json.dumps(
                {"status": "result_written", "output": str(args.result_output)}
            )
        )
        return 0
    payload = build_payload(result)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(_render(payload), encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(args.output)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
