#!/usr/bin/env python3
"""Deterministic aggregate inverse-ray probe for Erdős #1041.

For every admissible simple critical point, the two descending inverse-ray
branches form a root-to-root edge with total length L_c.  The pointwise route
is known to fail at selected critical points.  This probe tests the genuinely
different aggregate inequality

    sum_c L_c < 2 * (# admissible critical hubs),

which would force at least one short hub.  Numerical continuation is candidate
evidence only; the checker records ODE residual gates and the sharp regular-
polygon stress family for analytic follow-up.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any

import numpy as np


REPO_ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(REPO_ROOT))

from formal_math.erdos257_period_noncollapse.ErdosProblems.Erdos1041.scripts.search_counterexample import (  # noqa: E402
    inverse_ray_aggregate_score,
    perturbed_regular_roots,
    random_roots,
)
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/"
    "check_erdos1041_inverse_ray_aggregate.py"
)
ENGINE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/"
    "search_counterexample.py"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "InverseRayAggregateComputationalLab.md"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "research_packet.json"
)
EXACT_COUNTEREXAMPLE_ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "NewtonBranchHubCounterexampleComputationalLab.md"
)
EXACT_COUNTEREXAMPLE_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1041_newton_branch_hub_counterexample_receipt.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1041_inverse_ray_aggregate_receipt.json"
)


def encoded_roots(roots: np.ndarray) -> list[list[float]]:
    return [[float(root.real), float(root.imag)] for root in roots]


def aggregate_row(roots: np.ndarray, max_step: float) -> dict[str, Any] | None:
    normalized_average, detail = inverse_ray_aggregate_score(roots, max_step)
    hubs = detail.get("all_admissible_simple_critical_hubs", [])
    if not hubs:
        return None
    lengths = [float(hub["total_length"]) for hub in hubs]
    maximum_endpoint_error = max(
        float(branch["endpoint_error"])
        for hub in hubs
        for branch in hub["branches"]
    )
    maximum_level_residual = max(
        float(branch["maximum_level_residual"])
        for hub in hubs
        for branch in hub["branches"]
    )
    if abs(normalized_average - sum(lengths) / (2.0 * len(lengths))) > 1.0e-12:
        raise AssertionError("aggregate objective disagrees with complete hub table")
    return {
        "degree": len(roots),
        "admissible_simple_critical_hub_count": len(hubs),
        "total_inverse_ray_edge_length": sum(lengths),
        "normalized_average_length": normalized_average,
        "minimum_edge_length": min(lengths),
        "maximum_edge_length": max(lengths),
        "aggregate_candidate_survives": normalized_average < 1.0,
        "maximum_endpoint_error": maximum_endpoint_error,
        "maximum_level_residual": maximum_level_residual,
        "roots": encoded_roots(roots),
        "hub_rows": hubs,
    }


def retain_maximum(rows: list[dict[str, Any]]) -> dict[str, Any]:
    return max(rows, key=lambda row: float(row["normalized_average_length"]))


def balanced_quintic_roots() -> np.ndarray:
    return np.asarray(
        [
            900099 / 902000,
            999j / 1000,
            -999j / 1000,
            -450549 / 901000 + 38961j / 45050,
            -450549 / 901000 - 38961j / 45050,
        ],
        dtype=np.complex128,
    )


def compute(random_trials: int, regular_trials: int, max_step: float, seed: int) -> dict[str, Any]:
    rng = np.random.default_rng(seed)
    random_summaries = []
    all_rows: list[dict[str, Any]] = []
    for degree in range(3, 9):
        rows = []
        for _ in range(random_trials):
            row = aggregate_row(random_roots(rng, degree), max_step)
            if row is not None:
                rows.append(row)
                all_rows.append(row)
        random_summaries.append(
            {
                "degree": degree,
                "valid_sample_count": len(rows),
                "maximum_normalized_average_row": retain_maximum(rows),
            }
        )

    regular_summaries = []
    for degree in range(3, 10):
        for scale in (0.1, 0.03, 0.01, 0.003):
            rows = []
            for _ in range(regular_trials):
                row = aggregate_row(
                    perturbed_regular_roots(rng, degree, scale), max_step
                )
                if row is not None:
                    rows.append(row)
                    all_rows.append(row)
            regular_summaries.append(
                {
                    "degree": degree,
                    "perturbation_scale": scale,
                    "valid_sample_count": len(rows),
                    "maximum_normalized_average_row": retain_maximum(rows),
                }
            )

    balanced = aggregate_row(balanced_quintic_roots(), min(max_step, 0.005))
    if balanced is None:
        raise AssertionError("balanced quintic produced no admissible hub")
    all_rows.append(balanced)
    global_maximum = retain_maximum(all_rows)
    return {
        "aggregate_hypothesis": "sum_c L_c < 2 * number_of_admissible_simple_critical_hubs",
        "random_family_summaries": random_summaries,
        "regular_boundary_family_summaries": regular_summaries,
        "balanced_quintic_row": balanced,
        "global_maximum_normalized_average_row": global_maximum,
        "all_configured_aggregate_checks_survive": all(
            bool(row["aggregate_candidate_survives"]) for row in all_rows
        ),
        "configured_valid_polynomial_count": len(all_rows),
    }


def build_payload(random_trials: int, regular_trials: int, max_step: float, seed: int) -> dict[str, Any]:
    result = compute(random_trials, regular_trials, max_step, seed)
    maximum = result["global_maximum_normalized_average_row"]
    contract = build_experiment_contract(
        problem_id="erdos_1041",
        target_statement=(
            "Find two roots joined by a curve of length less than two inside "
            "the strict unit lemniscate."
        ),
        claim_ceiling=(
            "Deterministic numerical continuation selects an aggregate theorem "
            "candidate. It proves neither the aggregate inequality nor Erdős #1041."
        ),
        hypothesis_id="all_critical_inverse_ray_average_below_two",
        hypothesis_statement=(
            "The sum of the two-branch inverse-ray edge lengths over admissible "
            "simple critical points is less than twice their number."
        ),
        probe_id="complete_critical_hub_aggregate_stress",
        probe_question=(
            "Does the all-critical average survive random configurations, the "
            "sharp regular-polygon boundary, and the exact long-hub quintic?"
        ),
        computation=(
            "Numerically continue both inverse-ray branches at every admissible "
            "simple critical point, gate endpoint and level residuals, and record "
            "the complete edge-length aggregate for deterministic stress families."
        ),
        falsifier=(
            "One validated numerical candidate with normalized aggregate at least "
            "one; it must then be exactified before mathematical use."
        ),
        stop_condition=(
            "Stop after the configured distinct families; do not replace an "
            "analytic sum inequality by a longer random search."
        ),
        survival_consequence=(
            "Seek a coarea, area, or Reeb-tree bound for the total inverse-ray edge "
            "length. The average inequality would immediately select a short hub."
        ),
        falsification_consequence=(
            "Exactify the first aggregate score at least one and abandon all "
            "unweighted average-selection proofs."
        ),
        consumer_ref=PACKET_REF,
        analysis_refs=[ANALYSIS_REF, EXACT_COUNTEREXAMPLE_ANALYSIS_REF],
        source_refs=[SOURCE_REF, ENGINE_REF],
        input_receipt_refs=[EXACT_COUNTEREXAMPLE_RECEIPT_REF],
        result_status="finite_support",
        result_summary=(
            f"All {result['configured_valid_polynomial_count']} configured "
            "polynomials satisfy the aggregate candidate. The maximum normalized "
            f"average is {maximum['normalized_average_length']:.12g}; boundary-near "
            "regular cubics approach the sharp value one from below."
        ),
        progress_class="inconclusive",
        decision_basis=(
            "The computation compares a new complete-tree aggregate, not the "
            "previously explored pointwise minimum hub score."
        ),
        next_analytic_target=(
            "Express the sum of inverse-ray edge lengths as a level-set or Reeb-tree "
            "integral and prove a strict 2m upper bound with data-dependent slack."
        ),
        resource_bounds={
            "random_trials_per_degree": random_trials,
            "regular_trials_per_degree_scale": regular_trials,
            "minimum_degree": 3,
            "maximum_degree": 9,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos1041-inverse-ray-aggregate/1",
        "status": "finite_numerical_aggregate_mechanism_support",
        "parameters": {
            "random_trials_per_degree": random_trials,
            "regular_trials_per_degree_scale": regular_trials,
            "flow_max_step": max_step,
            "seed": seed,
        },
        "result": result,
        "experiment_contract": contract,
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [SOURCE_REF, ENGINE_REF, ANALYSIS_REF, PACKET_REF, EXACT_COUNTEREXAMPLE_ANALYSIS_REF, EXACT_COUNTEREXAMPLE_RECEIPT_REF]
        ],
    }


def emit(payload: dict[str, Any], output: Path, check: bool) -> int:
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
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
    parser.add_argument("--random-trials", type=int, default=6)
    parser.add_argument("--regular-trials", type=int, default=4)
    parser.add_argument("--flow-max-step", type=float, default=0.01)
    parser.add_argument("--seed", type=int, default=10410825)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.random_trials < 1 or args.regular_trials < 1:
        parser.error("trial counts must be positive")
    if not 0 < args.flow_max_step <= 0.05:
        parser.error("--flow-max-step must lie in (0,0.05]")
    return emit(
        build_payload(args.random_trials, args.regular_trials, args.flow_max_step, args.seed),
        args.output,
        args.check,
    )


if __name__ == "__main__":
    raise SystemExit(main())
