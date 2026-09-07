#!/usr/bin/env python3
"""Bind the exact Cassini no-uniform-slack mechanism elimination for #1041."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path

from system.lib.formal_math_experiment_contract import (
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


REPO_ROOT = Path(__file__).resolve().parents[5]
SOURCE_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "CassiniTreeBudget.lean"
)
LAB_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "UniformSlackNoGoComputationalLab.md"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "research_packet.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1041_uniform_slack_no_go_receipt.json"
)


def build_result(bound: int) -> dict[str, object]:
    rows = []
    for m in range(2, bound + 1):
        radius = Fraction(m - 1, m)
        root_distance = 2 * radius
        deficit = 2 - root_distance
        if not (0 < radius < 1 and deficit == Fraction(2, m)):
            raise AssertionError("Cassini boundary-family identity failed")
        rows.append(
            {
                "m": m,
                "radius": str(radius),
                "root_distance": str(root_distance),
                "deficit_from_two": str(deficit),
            }
        )

    contract = build_experiment_contract(
        problem_id="erdos_1041",
        target_statement=(
            "Join two roots by a curve of length strictly below two inside the "
            "strict unit lemniscate."
        ),
        claim_ceiling=(
            "Eliminates only a polynomial-independent positive length margin; "
            "Erdos #1041 and data-dependent strict slack remain open."
        ),
        hypothesis_id="uniform_global_short_path_slack",
        hypothesis_statement=(
            "There is a delta>0 such that every admissible polynomial has a "
            "root pair joinable with length at most 2-delta."
        ),
        probe_id="cassini_boundary_family_exact_deficit",
        probe_question=(
            "Can the quadratic family z^2-a^2 force every connecting path to "
            "have length arbitrarily close to two?"
        ),
        computation=(
            "Replay a_m=(m-1)/m exactly and verify that the root distance is "
            "2-2/m for every sampled m; Lean proves the quantified no-go."
        ),
        falsifier=(
            "For every positive proposed margin delta, an admissible radius a "
            "with 2a>2-delta."
        ),
        stop_condition=(
            "Stop after the symbolic identity 2-2a_m=2/m is exact and the "
            "quantified Lean theorem rejects every delta>0."
        ),
        survival_consequence=(
            "A uniform-margin perturbation transfer would remain viable."
        ),
        falsification_consequence=(
            "Generic perturbation and root transfer must preserve a "
            "polynomial-dependent strict slack rather than spend a global one."
        ),
        consumer_ref=PACKET_REF,
        consumer_declarations=[
            "not_exists_uniform_cassini_rootDistance_slack"
        ],
        analysis_refs=[LAB_REF, LEAN_REF],
        source_refs=[SOURCE_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "The exact Cassini radii a_m=(m-1)/m have root distance 2-2/m; "
            "Lean proves that no positive polynomial-independent slack exists."
        ),
        resource_bounds={"exact_family_prefix": bound},
        progress_class="mechanism_eliminated",
        decision_basis=(
            "The quantified Lean theorem consumes arbitrary positive delta; the "
            "finite rows are regression witnesses, not the quantifier authority."
        ),
        next_analytic_target=(
            "Prove data-dependent component/slack continuity under generic "
            "perturbation, or select a short critical hub without uniform slack."
        ),
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos1041-uniform-slack-no-go/1",
        "status": "exact_mechanism_elimination",
        "family": "f_m(z)=z^2-((m-1)/m)^2",
        "exact_rows": rows,
        "quantified_lean_consumer": (
            "ErdosProblems.Erdos1041.CassiniTreeBudget."
            "not_exists_uniform_cassini_rootDistance_slack"
        ),
        "experiment_contract": contract,
        "sources": [
            source_record(REPO_ROOT, ref)
            for ref in (SOURCE_REF, LEAN_REF, LAB_REF, PACKET_REF)
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bound", type=int, default=64)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.bound < 2:
        parser.error("--bound must be at least two")
    payload = build_result(args.bound)
    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    output = args.output if args.output.is_absolute() else REPO_ROOT / args.output
    if args.check:
        if not output.exists() or output.read_text(encoding="utf-8") != encoded:
            raise SystemExit(f"stale or missing receipt: {output}")
        print(json.dumps({"status": "current", "output": str(output)}))
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(encoded, encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(output)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
