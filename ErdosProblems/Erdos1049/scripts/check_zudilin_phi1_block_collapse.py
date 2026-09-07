#!/usr/bin/env python3
"""Falsify the full Phi_d-to-Phi_1 source-row block collapse exactly."""

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

from check_zudilin_endpoint_recurrence import _q_lucas_regression  # noqa: E402
from check_zudilin_scalar_content import p  # noqa: E402
from system.lib.formal_math_cyclotomic_local import CyclotomicLocalRing  # noqa: E402
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)
from zudilin_cyclotomic_local import (  # noqa: E402
    local_cleared_row,
    primitive_row_residue,
    scalar_unit_residue,
)


TARGET_INDICES = (1, 2, 3, 4, 5)
QUOTIENT_BLOCKS = (2, 3, 4)
SOURCE_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
LOCAL_ADAPTER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/"
    "zudilin_cyclotomic_local.py"
)
LOCAL_ENGINE_REF = "system/lib/formal_math_cyclotomic_local.py"
PREVIOUS_ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "ZudilinEndpointRecurrenceLab.md"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "ZudilinPhi1BlockCollapseLab.md"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "AdelicHeightBridge.lean"
)
INPUT_RECEIPTS = [
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_phi1_kernel_receipt.json",
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_endpoint_recurrence_receipt.json",
]
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_zudilin_phi1_block_collapse_receipt.json"
)
RAW_SCHEMA = "erdos1049-zudilin-phi1-block-collapse-result/2"


def harmonic(index: int) -> sp.Rational:
    return sum(
        (sp.Rational(1, denominator) for denominator in range(1, index + 1)),
        start=sp.Rational(0),
    )


def phi1_block_constant(quotient: int) -> sp.Rational:
    """Return the normalized Phi_1 harmonic moment c_q."""

    return sp.Rational(math.factorial(quotient) ** 3, 12 ** (quotient - 1)) * harmonic(
        quotient
    )


def _record(cyclotomic_index: int) -> dict[str, Any]:
    d = cyclotomic_index
    if d < 1:
        raise ValueError("cyclotomic index must be positive")
    ring = CyclotomicLocalRing(p, d, precision=1)
    cyclotomic = sp.Poly(ring.cyclotomic.as_expr(), p, domain=sp.QQ)

    def reduce_residue(expression: sp.Expr) -> sp.Expr:
        return sp.Poly(sp.expand(expression), p, domain=sp.QQ).rem(
            cyclotomic
        ).as_expr()

    def inverse(expression: sp.Expr) -> sp.Expr:
        polynomial = sp.Poly(expression, p, domain=sp.QQ).rem(cyclotomic)
        if polynomial.is_zero:
            raise AssertionError("attempted to invert a zero source residue")
        return sp.Poly(sp.invert(polynomial, cyclotomic), p, domain=sp.QQ).as_expr()

    source_cache: dict[int, tuple[sp.Expr, sp.Expr, sp.Expr]] = {}
    primitive_mu_coefficients_vanish = True

    def source_components(index: int) -> tuple[sp.Expr, sp.Expr, sp.Expr]:
        nonlocal primitive_mu_coefficients_vanish
        if index not in source_cache:
            a_residue, b_residue, c_residue = primitive_row_residue(index, d)
            if index >= d and not a_residue.is_zero:
                primitive_mu_coefficients_vanish = False
            unit = scalar_unit_residue(index, d).as_expr()
            b_component = reduce_residue(-b_residue.as_expr() * unit)
            c_component = reduce_residue(-c_residue.as_expr() * unit)
            source_cache[index] = (
                b_component,
                c_component,
                reduce_residue(b_component + c_component),
            )
        return source_cache[index]

    def source_residue(index: int) -> sp.Expr:
        return source_components(index)[2]

    base = source_residue(d)
    base_nonzero = base != 0
    multiplier = reduce_residue(source_residue(2 * d) * inverse(base))
    multiplier_nonzero = multiplier != 0
    channel_bases = source_components(d)[:2]
    channel_base_nonzero = all(component != 0 for component in channel_bases)
    channel_multipliers = tuple(
        reduce_residue(source_components(2 * d)[channel] * inverse(channel_bases[channel]))
        for channel in range(2)
    )
    channel_multipliers_equal = all(
        reduce_residue(channel_multiplier - multiplier) == 0
        for channel_multiplier in channel_multipliers
    )
    checks = []
    failures = []
    for quotient in QUOTIENT_BLOCKS:
        constant = phi1_block_constant(quotient)
        for residue in range(d):
            left_index = quotient * d + residue
            right_index = d + residue
            observed = source_residue(left_index)
            predicted = reduce_residue(
                multiplier ** (quotient - 1)
                * constant
                * source_residue(right_index)
            )
            difference = reduce_residue(observed - predicted)
            channel_checks = {}
            for channel_index, channel_name in enumerate(("B", "C")):
                channel_observed = source_components(left_index)[channel_index]
                channel_predicted = reduce_residue(
                    multiplier ** (quotient - 1)
                    * constant
                    * source_components(right_index)[channel_index]
                )
                channel_difference = reduce_residue(
                    channel_observed - channel_predicted
                )
                channel_checks[channel_name] = {
                    "observed": str(sp.factor(channel_observed)),
                    "predicted": str(sp.factor(channel_predicted)),
                    "difference": str(sp.factor(channel_difference)),
                    "matches": channel_difference == 0,
                }
            check = {
                "quotient": quotient,
                "residue_class": residue,
                "left_index": left_index,
                "right_index": right_index,
                "phi1_block_constant": str(constant),
                "observed": str(sp.factor(observed)),
                "predicted": str(sp.factor(predicted)),
                "difference": str(sp.factor(difference)),
                "matches": difference == 0,
                "channel_checks": channel_checks,
                "both_channels_match_separately": all(
                    channel["matches"] for channel in channel_checks.values()
                ),
            }
            checks.append(check)
            if difference != 0 or not check["both_channels_match_separately"]:
                failures.append(check)

    required_indices = list(range(d, 5 * d))
    maximum_local_modulus_degree = max(
        local_cleared_row(index, d)[1].modulus.degree()
        for index in required_indices
    )
    q_lucas = _q_lucas_regression(d)
    return {
        "cyclotomic_index": d,
        "cyclotomic_polynomial": str(sp.cyclotomic_poly(d, p)),
        "cyclotomic_degree": int(sp.totient(d)),
        "source_block_multiplier_K": str(sp.factor(multiplier)),
        "channel_block_multipliers": {
            "B": str(sp.factor(channel_multipliers[0])),
            "C": str(sp.factor(channel_multipliers[1])),
        },
        "channel_block_multipliers_equal_combined_K": channel_multipliers_equal,
        "source_base_residue_S_d": str(sp.factor(base)),
        "source_base_residue_nonzero": base_nonzero,
        "channel_base_residues_nonzero": channel_base_nonzero,
        "source_block_multiplier_nonzero": multiplier_nonzero,
        "primitive_mu_coefficients_vanish": primitive_mu_coefficients_vanish,
        "quotient_blocks": list(QUOTIENT_BLOCKS),
        "residue_class_count": d,
        "identity_check_count": len(checks),
        "identity_failure_count": len(failures),
        "all_block_identities_hold": not failures,
        "all_channelwise_block_identities_hold": all(
            check["both_channels_match_separately"] for check in checks
        ),
        "checks": checks,
        "failures": failures,
        "q_lucas_regression": q_lucas,
        "required_source_indices": required_indices,
        "maximum_local_modulus_degree": int(maximum_local_modulus_degree),
    }


def _enrich_record(record: dict[str, Any]) -> dict[str, Any]:
    """Derive the channel-ratio consequence from replayable recorded values."""

    enriched = dict(record)
    d = int(enriched["cyclotomic_index"])
    cyclotomic = sp.Poly(sp.cyclotomic_poly(d, p), p, domain=sp.QQ)

    def reduce_residue(expression: sp.Expr) -> sp.Expr:
        return sp.Poly(sp.expand(expression), p, domain=sp.QQ).rem(
            cyclotomic
        ).as_expr()

    observed_ratio_checks = []
    for check in enriched["checks"]:
        b_observed = sp.sympify(
            check["channel_checks"]["B"]["observed"], locals={"p": p}
        )
        c_observed = sp.sympify(
            check["channel_checks"]["C"]["observed"], locals={"p": p}
        )
        observed_ratio_checks.append(
            reduce_residue(b_observed - 2 * c_observed) == 0
        )
    all_observed_ratios = all(observed_ratio_checks)
    complete_strip_ratio = (
        all_observed_ratios
        and enriched["all_channelwise_block_identities_hold"]
        and enriched["channel_block_multipliers_equal_combined_K"]
        and enriched["source_block_multiplier_nonzero"]
        and enriched["channel_base_residues_nonzero"]
    )
    enriched["observed_B_equals_twice_C_check_count"] = len(
        observed_ratio_checks
    )
    enriched["all_observed_B_equals_twice_C"] = all_observed_ratios
    enriched["B_equals_twice_C_on_complete_source_strip"] = complete_strip_ratio
    return enriched


def _summarize(records: list[dict[str, Any]]) -> dict[str, Any]:
    records = [_enrich_record(record) for record in records]
    return {
        "schema": RAW_SCHEMA,
        "records": records,
        "phi1_block_constants": {
            str(quotient): str(phi1_block_constant(quotient))
            for quotient in QUOTIENT_BLOCKS
        },
        "all_block_identities_hold": all(
            record["all_block_identities_hold"] for record in records
        ),
        "all_channelwise_block_identities_hold": all(
            record["all_channelwise_block_identities_hold"] for record in records
        ),
        "all_channel_multipliers_equal": all(
            record["channel_block_multipliers_equal_combined_K"]
            for record in records
        ),
        "all_B_equals_twice_C_on_complete_source_strips": all(
            record["B_equals_twice_C_on_complete_source_strip"]
            for record in records
        ),
        "all_source_bases_and_multipliers_nonzero": all(
            record["source_base_residue_nonzero"]
            and record["source_block_multiplier_nonzero"]
            and record["channel_base_residues_nonzero"]
            for record in records
        ),
        "all_primitive_mu_coefficients_vanish": all(
            record["primitive_mu_coefficients_vanish"] for record in records
        ),
        "all_q_lucas_regressions_hold": all(
            record["q_lucas_regression"]["matches"] for record in records
        ),
        "authority_boundary": (
            "The exact computation decides every listed quotient/residue identity "
            "at the listed cyclotomic indices. It does not prove the identity for "
            "all d or all quotient blocks."
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
            records_by_index[int(record["cyclotomic_index"])] = record
    return _summarize([records_by_index[index] for index in sorted(records_by_index)])


def build_payload(result: dict[str, Any]) -> dict[str, Any]:
    indices = [int(record["cyclotomic_index"]) for record in result["records"]]
    if indices != list(TARGET_INDICES):
        raise ValueError(f"canonical receipt requires indices {TARGET_INDICES}")
    survives = (
        result["all_block_identities_hold"]
        and result["all_channelwise_block_identities_hold"]
        and result["all_channel_multipliers_equal"]
        and result["all_B_equals_twice_C_on_complete_source_strips"]
        and result["all_source_bases_and_multipliers_nonzero"]
        and result["all_primitive_mu_coefficients_vanish"]
        and result["all_q_lucas_regressions_hold"]
    )
    if survives:
        progress_class = "mechanism_opened"
        status = "exact_mechanism_opened"
        result_summary = (
            "For every d=1,...,5, q=2,3,4, and 0<=s<d, the exact B and C "
            "source channels separately satisfy S_(qd+s)=K_d^(q-1)c_q "
            "S_(d+s), with the same K_d and c_q=(q!)^3 H_q/12^(q-1). "
            "Moreover B=2C throughout every complete source strip, so the "
            "combined collapse is three times a single channel and cannot "
            "depend on B/C cancellation. All source bases and multipliers are "
            "nonzero, all primitive mu coefficients vanish, and the finite "
            "q-Lucas regressions hold. This opens a uniform root-of-unity "
            "block-collapse proof from one Zudilin source sum to the Phi_1 "
            "harmonic kernel."
        )
        next_target = (
            "Derive the block-collapse symbolically by splitting the terminating "
            "source sum at n=qd+s into quotient and residue variables, proving "
            "that the quotient sum is the normalized Phi_1 harmonic moment."
        )
    else:
        progress_class = "mechanism_eliminated"
        status = "exact_mechanism_eliminated"
        result_summary = (
            "At least one exact quotient/residue, channelwise, or B=2C identity "
            "fails for d<=5, eliminating the proposed strong Phi_d-to-Phi_1 "
            "block collapse."
        )
        next_target = (
            "Use the first recorded failed quotient/residue class to derive the "
            "missing correction term while retaining the endpoint-only identities."
        )
    contract = build_experiment_contract(
        problem_id="erdos_1049",
        target_statement="Prove irrationality of the Lambert value at p=3/2.",
        claim_ceiling=(
            "Exact full-strip block-collapse decisions at d=1,...,5 and "
            "q=2,3,4; not an all-d theorem or irrationality proof."
        ),
        hypothesis_id="phi_d_source_rows_collapse_to_phi1_harmonic_blocks",
        hypothesis_statement=(
            "After scalar extraction, B=2C and both channels separately obey "
            "the same quotient-block law K_d^(q-1)c_q, uniformly over residue "
            "classes s, with c_q=(q!)^3 H_q/12^(q-1)."
        ),
        probe_id="exact_d1_d5_full_residue_strip_block_collapse",
        probe_question=(
            "Does the stronger source-row block law hold in every residue class, "
            "including the new degree-four d=5 strip?"
        ),
        computation=(
            "Construct S_n=(-B_n-C_n)U_n exactly in QQ[p]/(Phi_d) for "
            "d<=n<5d, infer K_d=S_(2d)/S_d, and compare every q=2,3,4, "
            "0<=s<d source residue against the Phi_1 harmonic prediction."
        ),
        falsifier=(
            "Any nonzero exact block-law difference in either source channel, "
            "or any failure of B=2C, kills the strong block-collapse mechanism."
        ),
        stop_condition=(
            "Stop after the complete d=1,...,5 strips decide the mechanism; "
            "do not substitute further index sampling for the symbolic reduction."
        ),
        survival_consequence=(
            "Survival opens a symbolic q-Lucas/Pochhammer proof whose quotient "
            "sum is exactly the committed Phi_1 harmonic moment."
        ),
        falsification_consequence=(
            "Failure eliminates full block collapse and names the first exact "
            "residue correction that a weaker endpoint proof must retain."
        ),
        consumer_ref=CONSUMER_REF,
        consumer_declarations=["zudilinScalarPlusBorder_cannot_meet_required_charge"],
        analysis_refs=[ANALYSIS_REF, PREVIOUS_ANALYSIS_REF],
        source_refs=[SOURCE_REF, LOCAL_ADAPTER_REF, LOCAL_ENGINE_REF],
        input_receipt_refs=INPUT_RECEIPTS,
        result_status="exact_one_way_result",
        result_summary=result_summary,
        progress_class=progress_class,
        decision_basis=(
            "The channelwise full residue strip strictly strengthens the committed "
            "endpoint recurrence, tests reduction to one source channel, and "
            "either exposes an analytic source identity or kills it."
        ),
        next_analytic_target=next_target,
        resource_bounds={
            "minimum_cyclotomic_index": min(indices),
            "maximum_cyclotomic_index": max(indices),
            "cyclotomic_index_count": len(indices),
            "maximum_quotient_block": max(QUOTIENT_BLOCKS),
            "identity_check_count": sum(
                int(record["identity_check_count"]) for record in result["records"]
            ),
            "separately_recorded_channel_and_combined_comparison_count": 3
            * sum(
                int(record["identity_check_count"])
                for record in result["records"]
            ),
            "maximum_local_modulus_degree": max(
                int(record["maximum_local_modulus_degree"])
                for record in result["records"]
            ),
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    refs = (
        SOURCE_REF,
        LOCAL_ADAPTER_REF,
        LOCAL_ENGINE_REF,
        ANALYSIS_REF,
        PREVIOUS_ANALYSIS_REF,
        CONSUMER_REF,
    )
    return {
        "schema": "erdos1049-zudilin-phi1-block-collapse-receipt/2",
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
    parser.add_argument("--cyclotomic-index", type=int, action="append")
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
        result = compute(args.cyclotomic_index or list(TARGET_INDICES))
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
