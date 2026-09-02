#!/usr/bin/env python3
"""Replay the radial-lift coarea identity and its critical-ray sampling gap.

The exact area formula controls the angular average of the total length of all
inverse lifts of a value-plane radius.  The family

    f_eps(z) = z^n + eps*z - r^n

has n-1 simple critical values whose arguments coalesce at pi as eps tends to
zero.  Thus the coarea average cannot be sampled once at every critical ray
without a separate multiplicity-aware charge.  This checker records the exact
family algebra and deterministic numerical conditioning; it does not refute
the all-critical inverse-ray aggregate conjecture.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import sys
from typing import Any

import numpy as np


REPO_ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/"
    "check_erdos1041_radial_lift_coarea_gap.py"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "RadialLiftCoareaGapLab.md"
)
AGGREGATE_ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "InverseRayAggregateComputationalLab.md"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "research_packet.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1041_radial_lift_coarea_gap_receipt.json"
)


def wrapped_angle_distance(left: float, right: float) -> float:
    return abs((left - right + math.pi) % (2.0 * math.pi) - math.pi)


def family_row(degree: int, radius: float, epsilon: float) -> dict[str, Any]:
    rouche_unit_disk_margin = 1.0 - (radius**degree + epsilon)
    if rouche_unit_disk_margin <= 0.0:
        raise AssertionError("Rouche root-containment margin is not positive")
    # f'(z)=n*z^(n-1)+epsilon, so these are the exact simple critical points.
    rho = (epsilon / degree) ** (1.0 / (degree - 1))
    base_angle = math.pi / (degree - 1)
    critical_points = np.asarray(
        [
            rho * np.exp(1j * (base_angle + 2.0 * math.pi * k / (degree - 1)))
            for k in range(degree - 1)
        ],
        dtype=np.complex128,
    )
    critical_values = (
        critical_points**degree
        + epsilon * critical_points
        - radius**degree
    )
    critical_value_unit_disk_margin = 1.0 - max(abs(critical_values))
    if critical_value_unit_disk_margin <= 0.0:
        raise AssertionError("a critical value left the unit disk")
    # At a critical point epsilon*c=-n*c^n, hence
    # f(c)=-r^n-(n-1)c^n exactly.
    identity_residual = np.max(
        np.abs(
            critical_values
            - (-radius**degree - (degree - 1) * critical_points**degree)
        )
    )
    angle_spread = max(
        wrapped_angle_distance(float(np.angle(value)), math.pi)
        for value in critical_values
    )
    critical_ray_descending_length = degree * radius
    critical_ray_total_lift_length = degree * (
        radius + (1.0 - radius**degree) ** (1.0 / degree)
    )
    return {
        "degree": degree,
        "radius": radius,
        "epsilon": epsilon,
        "simple_critical_point_count": degree - 1,
        "rouche_unit_disk_root_containment_margin": rouche_unit_disk_margin,
        "critical_value_unit_disk_margin": critical_value_unit_disk_margin,
        "maximum_critical_value_argument_distance_from_pi": angle_spread,
        "maximum_critical_value_identity_residual": float(identity_residual),
        "degenerate_limit_critical_ray_descending_length": (
            critical_ray_descending_length
        ),
        "degenerate_limit_critical_ray_total_lift_length": (
            critical_ray_total_lift_length
        ),
        "repeated_full_lift_majorant": (
            (degree - 1) * critical_ray_total_lift_length
        ),
        "desired_aggregate_scale": 2.0 * (degree - 1),
        "full_lift_majorant_already_exceeds_desired_scale": (
            (degree - 1) * critical_ray_total_lift_length
            > 2.0 * (degree - 1)
        ),
    }


def compute() -> dict[str, Any]:
    radius = 0.9
    epsilons = (1.0e-2, 1.0e-4, 1.0e-6, 1.0e-8)
    rows = [
        family_row(degree, radius, epsilon)
        for degree in range(3, 10)
        for epsilon in epsilons
    ]
    by_degree = []
    for degree in range(3, 10):
        degree_rows = [row for row in rows if row["degree"] == degree]
        spreads = [
            float(row["maximum_critical_value_argument_distance_from_pi"])
            for row in degree_rows
        ]
        by_degree.append(
            {
                "degree": degree,
                "argument_spreads_by_decreasing_epsilon": spreads,
                "strictly_decreasing_argument_spread": all(
                    right < left for left, right in zip(spreads, spreads[1:])
                ),
                "smallest_argument_spread": spreads[-1],
                "limiting_repeated_full_lift_majorant": degree_rows[-1][
                    "repeated_full_lift_majorant"
                ],
                "desired_aggregate_scale": 2.0 * (degree - 1),
            }
        )
    if not all(row["strictly_decreasing_argument_spread"] for row in by_degree):
        raise AssertionError("critical-value arguments did not coalesce monotonically")
    if not all(
        row["full_lift_majorant_already_exceeds_desired_scale"] for row in rows
    ):
        raise AssertionError("the repeated radial-lift majorant missed the target gap")
    if max(row["maximum_critical_value_identity_residual"] for row in rows) > 1e-13:
        raise AssertionError("critical-value algebra replay lost conditioning")
    return {
        "radial_lift_area_identity": (
            "integral_0^2pi R(theta) dtheta = "
            "integral_{|f|<1} |f'(z)|/|f(z)| dA(z)"
        ),
        "family": "f_epsilon(z)=z^n+epsilon*z-r^n",
        "exact_critical_point_equation": "c^(n-1)=-epsilon/n",
        "exact_critical_value_equation": "f_epsilon(c)=-r^n-(n-1)c^n",
        "degenerate_critical_ray_formula": (
            "R(pi)=n*(r+(1-r^n)^(1/n)); descending part=n*r"
        ),
        "rows": rows,
        "degree_summaries": by_degree,
        "mechanism_verdict": (
            "unweighted_coarea_average_to_critical_ray_sampling_eliminated"
        ),
        "aggregate_conjecture_status": (
            "still_open_requires_multiplicity_aware_edge_charge"
        ),
    }


def build_payload() -> dict[str, Any]:
    result = compute()
    contract = build_experiment_contract(
        problem_id="erdos_1041",
        target_statement=(
            "Find two roots joined by a curve of length less than two inside "
            "the strict unit lemniscate."
        ),
        claim_ceiling=(
            "The exact change-of-variables identity and explicit perturbation "
            "family eliminate only an unweighted sampling of the coarea angular "
            "average at critical-value rays. They do not refute the aggregate "
            "inverse-ray inequality or prove Erdos #1041."
        ),
        hypothesis_id="coarea_average_directly_controls_critical_ray_hub_sum",
        hypothesis_statement=(
            "The angular average of total radial inverse-lift length can be "
            "sampled at every critical-value argument to bound the unweighted "
            "sum of critical inverse-ray hubs at scale 2h."
        ),
        probe_id="regular_polygon_critical_ray_coalescence",
        probe_question=(
            "Can distinct simple critical-value arguments cluster while the "
            "same full-lift pointwise majorant is charged once per critical point?"
        ),
        computation=(
            "Replay the exact critical point and value formulas for "
            "z^n+epsilon*z-r^n, verify angular coalescence, and compare the "
            "repeated limiting full-lift majorant with the desired 2(n-1) scale."
        ),
        falsifier=(
            "A uniform angular separation of the n-1 critical values, or a "
            "repeated full-lift majorant no larger than 2(n-1)."
        ),
        stop_condition=(
            "Stop once the exact family algebra and decreasing angular spread "
            "are replayed for degrees 3 through 9."
        ),
        survival_consequence=(
            "Abandon direct L1-average sampling and require a multiplicity-aware "
            "Reeb-edge or attachment charge that does not count one angular spike "
            "once per nearby critical point."
        ),
        falsification_consequence=(
            "Retain direct coarea-average sampling as a possible aggregate proof."
        ),
        consumer_ref=PACKET_REF,
        analysis_refs=[ANALYSIS_REF, AGGREGATE_ANALYSIS_REF],
        source_refs=[SOURCE_REF],
        input_receipt_refs=[],
        result_status="exact_one_way_result",
        result_summary=(
            "The radial-lift area identity is an angular L1 statement, while "
            "z^n+epsilon*z-r^n has n-1 simple critical-value arguments coalescing "
            "at pi. Repeating the same critical-ray full-lift majorant already "
            "exceeds the desired aggregate scale."
        ),
        progress_class="mechanism_eliminated",
        decision_basis=(
            "The family changes the analytic consumer: aggregate selection can "
            "no longer be obtained by evaluating an angular average at the "
            "critical rays without a new multiplicity-aware charge."
        ),
        next_analytic_target=(
            "Charge only the descending Reeb edge below each saddle, with overlap "
            "or multiplicity cancellation before any angular integration."
        ),
        resource_bounds={
            "minimum_degree": 3,
            "maximum_degree": 9,
            "epsilon_count_per_degree": 4,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos1041-radial-lift-coarea-gap/1",
        "status": "exact_coarea_sampling_mechanism_elimination",
        "result": result,
        "experiment_contract": contract,
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [SOURCE_REF, ANALYSIS_REF, AGGREGATE_ANALYSIS_REF, PACKET_REF]
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
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    return emit(build_payload(), args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
