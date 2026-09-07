#!/usr/bin/env python3
"""Exact regression for the Erdős #249 pointwise-totient boundary countermodel."""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[5]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_affine_word import constant_boundary_mode  # noqa: E402
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
)


SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/scripts/"
    "check_pure_dyadic_pointwise_countermodel.py"
)
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/"
    "PeriodMultipleEscape.lean"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/"
    "PointwiseTotientCountermodelLab.md"
)
UTILITY_REF = "system/lib/formal_math_affine_word.py"
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/"
    "CyclotomicAnchoredKill.lean"
)
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "erdos249_pure_dyadic_pointwise_countermodel_receipt.json"
)
THEOREMS = [
    "ErdosProblems.Erdos249.PeriodMultipleEscape.endpointWordBlock_const",
    "ErdosProblems.Erdos249.PeriodMultipleEscape.pointwiseTotientValued_const_two",
    "ErdosProblems.Erdos249.PeriodMultipleEscape."
    "exists_pointwiseTotientValued_permanent_endpointTrap",
    "ErdosProblems.Erdos249.PeriodMultipleEscape."
    "exists_actualTotientLetter_ne_two",
    "ErdosProblems.Erdos249.PeriodMultipleEscape."
    "actualTotientWord_ne_const_two",
]


def euler_totient(value: int) -> int:
    return sum(math.gcd(candidate, value) == 1 for candidate in range(1, value + 1))


def build_receipt(max_depth: int) -> dict[str, object]:
    if max_depth < 1:
        raise ValueError("max_depth must be positive")
    if euler_totient(3) != 2:
        raise AssertionError("phi(3)=2 regression failed")
    requested_depths = [0, 1, 2, 8, 64, 512, max_depth]
    depths = sorted(set(depth for depth in requested_depths if depth <= max_depth))
    rows = []
    for depth in depths:
        certificate = constant_boundary_mode(2, depth)
        rows.append(
            {
                "depth": depth,
                "block_bit_length": int(certificate["block"]).bit_length(),
                "mersenne_bit_length": int(
                    certificate["mersenne_modulus"]
                ).bit_length(),
                "fixed_quotient": certificate["fixed_quotient"],
                "all_endpoint_errors_zero": certificate[
                    "all_endpoint_errors_zero"
                ],
            }
        )

    contract = build_experiment_contract(
        problem_id="erdos_249",
        target_statement="Prove irrationality of sum_(n>=1) phi(n)/2^n.",
        claim_ceiling=(
            "This is a no-go for pointwise/envelope-only anti-shadowing, not a "
            "counterexample for the actual consecutive totient word and not an "
            "irrationality proof."
        ),
        hypothesis_id="pointwise_totient_data_forces_endpoint_escape",
        hypothesis_statement=(
            "Positivity, evenness, the moving upper envelope, and individual "
            "membership of every letter in the image of Euler's totient suffice "
            "to force fixed-quotient endpoint escape."
        ),
        probe_id="constant_two_permanent_boundary_mode",
        probe_question=(
            "Can an infinite word satisfy every pointwise totient/envelope condition "
            "while its signed Mersenne endpoint error stays identically zero?"
        ),
        computation=(
            "Replay the constant letter 2 exactly at logarithmically separated depths, "
            "check B_H=2(2^H-1), and verify the fixed-quotient error recurrence."
        ),
        falsifier=(
            "Any depth where the constant-two block differs from 2(2^H-1), or "
            "phi(3) differs from 2."
        ),
        stop_condition=(
            "Stop once Lean proves the all-depth countermodel; larger finite depth is "
            "then coordinate regression only."
        ),
        survival_consequence=(
            "Failure would reopen pointwise totient-image or envelope bounds as a "
            "possible anti-shadowing producer."
        ),
        falsification_consequence=(
            "Future anti-shadowing must use correlations tying phi(c+H) to the "
            "consecutive arguments, not merely legal letters one at a time."
        ),
        consumer_ref=CONSUMER_REF,
        consumer_declarations=THEOREMS,
        analysis_refs=[ANALYSIS_REF],
        source_refs=[SCRIPT_REF, UTILITY_REF, LEAN_REF, ANALYSIS_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "The constant-two word is positive, even, within every moving envelope "
            "based at c>=2, and pointwise totient-valued because phi(3)=2, yet its "
            "fixed-quotient endpoint error is zero at every depth. Lean separately "
            "excludes this homogeneous word from every shifted actual consecutive-"
            "totient sequence by inserting an arbitrarily large prime index."
        ),
    )
    return {
        "schema": "erdos249-pure-dyadic-pointwise-countermodel/1",
        "claim_ceiling": contract["problem"]["claim_ceiling"],
        "parameters": {"maximum_regression_depth": max_depth},
        "exact_result": {
            "letter": 2,
            "totient_witness": 3,
            "totient_witness_value": 2,
            "tested_depths": depths,
            "all_endpoint_errors_zero": True,
            "rows": rows,
        },
        "structural_consequence": {
            "eliminated_mechanism": (
                "pointwise totient-image membership plus positivity, parity, and "
                "moving-envelope bounds"
            ),
            "required_new_information": (
                "relations between Euler totients at the actual consecutive arguments"
            ),
            "actual_word_consequence": (
                "the constant-two permanent boundary mode is impossible for every "
                "shifted actual consecutive-totient word"
            ),
            "lean_theorems": THEOREMS,
        },
        "experiment_contract": contract,
        "sources": [
            source_record(REPO_ROOT, SCRIPT_REF),
            source_record(REPO_ROOT, UTILITY_REF),
            source_record(REPO_ROOT, LEAN_REF),
            source_record(REPO_ROOT, ANALYSIS_REF),
        ],
    }


def emit(payload: dict[str, object], output: Path, check: bool) -> int:
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    output = output.resolve()
    if check:
        if not output.exists() or output.read_text(encoding="utf-8") != rendered:
            print(f"stale receipt: {output}", file=sys.stderr)
            return 1
        print(json.dumps({"status": "current", "output": str(output)}))
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(output)}))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-depth", type=int, default=4096)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    return emit(build_receipt(args.max_depth), args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
