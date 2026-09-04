#!/usr/bin/env python3
"""Bind the Cassini tree-budget falsifier to both unrestricted #1041 drafts.

The two drafts use differently numbered propositions but the same load-bearing
claim: every positive epsilon admits a root-spanning tree whose length is at
most the level-length tail budget plus epsilon.  This checker pins those source
statements and replays the exact rational part of the Cassini witness.  The
calculus majorant is proved in the companion lab; Lean checks the resulting
logical contradiction and rational slack.
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
)


SOURCE_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
MAIN_REF = "annexes/erdos1041-general-candidate-draft-main/extracted.md"
REVISED_REF = "annexes/erdos1041-general-candidate-draft-revised/extracted.md"
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "CassiniTreeBudget.lean"
)
LAB_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "CassiniAttachmentDeficitLab.md"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "research_packet.json"
)
PAPER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/papers/"
    "erdos-1041-lemniscate-newton-flow.tex"
)
DIGEST_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/papers/"
    "contributions-digest.tex"
)
PRIOR_ART_REF = (
    "formal_math/erdos257_period_noncollapse/prior_art_routes/"
    "erdos1041_lemniscate_short_path_v0.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1041_candidate_tree_budget_source_audit_receipt.json"
)


def proposition_record(ref: str, proposition: str, anchor: str) -> dict[str, Any]:
    text = (REPO_ROOT / ref).read_text(encoding="utf-8")
    offset = text.find(anchor)
    if offset < 0:
        raise AssertionError(f"missing {proposition} source anchor in {ref}")
    tail = text[offset : offset + 1800]
    required = (
        "for every ε > 0",
        "finite embedded tree",
        "containing all m zeros",
        "len(G",
    )
    missing = [token for token in required if token not in tail]
    if missing:
        raise AssertionError(f"incomplete {proposition} source statement: {missing}")
    line = text.count("\n", 0, offset) + 1
    return {
        "source_ref": ref,
        "proposition": proposition,
        "line_start": line,
        "statement_shape": (
            "Every positive epsilon admits a finite embedded tree containing "
            "all component roots with length at most the level-length tail "
            "budget plus epsilon."
        ),
        "load_bearing": True,
    }


def build_result() -> dict[str, Any]:
    propositions = [
        proposition_record(
            MAIN_REF,
            "Proposition 12",
            "Proposition 12. Let 0 ≤ c < 2α",
        ),
        proposition_record(
            REVISED_REF,
            "Proposition 7",
            "Proposition 7. Assume that:",
        ),
    ]

    a = Fraction(9, 10)
    radicand = a * a + a
    rational_sqrt_upper = Fraction(131, 100)
    if not rational_sqrt_upper * rational_sqrt_upper > radicand:
        raise AssertionError("rational square-root upper certificate failed")
    budget_upper = 4 * (rational_sqrt_upper - a)
    root_distance = 2 * a
    certified_gap = Fraction(4, 25)
    if not budget_upper + certified_gap == root_distance:
        raise AssertionError("Cassini rational slack identity failed")
    if not budget_upper < root_distance:
        raise AssertionError("Cassini tree-budget separation failed")

    summary = (
        "The March unrestricted draft's Proposition 12 and the shorter revised "
        "draft's Proposition 7 assert the same epsilon-sharp spanning-tree "
        "budget. The Cassini witness a=9/10 makes the true budget strictly less "
        "than 41/25 while every root-spanning connected set has length at least "
        "9/5, with certified gap greater than 4/25. Both propositions are false."
    )
    return {
        "schema": "erdos1041-candidate-tree-budget-source-audit/1",
        "problem_id": "erdos_1041",
        "claim_ceiling": (
            "Exact refutation of two named candidate-proof propositions; not a "
            "counterexample to Erdős #1041 and not a proof of the conjecture."
        ),
        "source_propositions": propositions,
        "cassini_witness": {
            "a": str(a),
            "radicand": str(radicand),
            "rational_sqrt_upper": str(rational_sqrt_upper),
            "rational_sqrt_upper_square": str(
                rational_sqrt_upper * rational_sqrt_upper
            ),
            "budget_strict_upper": str(budget_upper),
            "root_distance": str(root_distance),
            "certified_gap_strictly_greater_than": str(certified_gap),
            "exact_rational_replay_passed": True,
        },
        "both_load_bearing_tree_budget_propositions_refuted": True,
        "result_summary": summary,
        "mechanism_effect": (
            "Eliminates epsilon-small saddle attachment as a repair of the "
            "unchanged 1/(2π) strip-average budget in both unrestricted drafts."
        ),
        "consequence_decisions": [
            {
                "decision": "update_now",
                "files": [
                    PACKET_REF,
                    LAB_REF,
                    PAPER_REF,
                    DIGEST_REF,
                    PRIOR_ART_REF,
                    "formal_math/erdos257_period_noncollapse/ErdosProblems/"
                    "papers/README.md",
                    "formal_math/erdos257_period_noncollapse/ErdosProblems/"
                    "assimilation_manifest.json",
                ],
                "reason": (
                    "These authorities previously described only a generic "
                    "budget warning or local proof gap; they now bind the exact "
                    "dual-draft refutation and surviving metric routes."
                ),
            },
            {
                "decision": "verified_no_change",
                "files": [
                    "docs/formal_math/type_b_packets/"
                    "comparator_residual_2026_08_19/manifest_p07.json",
                    "formal_math/erdos257_period_noncollapse/ErdosProblems/"
                    "Erdos1041/AllStraightSegmentsCounterexampleComputationalLab.md",
                    "formal_math/erdos257_period_noncollapse/ErdosProblems/"
                    "Erdos1041/NewtonBranchHubCounterexampleComputationalLab.md",
                    "formal_math/erdos257_period_noncollapse/README.md",
                    "formal_math/erdos257_period_noncollapse/scripts/"
                    "check_erdos1041_all_straight_segments.py",
                    "formal_math/erdos257_period_noncollapse/scripts/"
                    "check_erdos1041_newton_branch_hub.py",
                    "formal_math/erdos257_period_noncollapse/scripts/lean_fast_build.py",
                ],
                "reason": (
                    "The comparator already bans the Cassini-false budget; the "
                    "other surfaces govern distinct counterexamples, root-level "
                    "orientation, or generic validation infrastructure."
                ),
            },
            {
                "decision": "outside_scope",
                "files": [
                    "formal_math/erdos257_period_noncollapse/ErdosProblems/papers/"
                    "erdos-68-factorial-denominator-irrationality.tex",
                    "formal_math/erdos257_period_noncollapse/scripts/"
                    "check_actual_foreign_residue_projection.py",
                    "formal_math/erdos257_period_noncollapse/scripts/"
                    "check_adelic_height_obstruction.py",
                ],
                "reason": "Namespace or manifest bridges only; no #1041 mathematics.",
            },
            {
                "decision": "defer_with_reason",
                "files": [
                    "tools/meta/factory/"
                    "build_lean_mathematics_microcosm_projection.py"
                ],
                "reason": (
                    "Run the owner projection after the source commit so the "
                    "generated navigation binds a stable source identity."
                ),
                "reentry": "after_scoped_source_commit",
            },
        ],
        "authority_boundary": (
            "The source matcher pins the printed proposition shapes and the "
            "script replays their exact rational falsifier. The Cassini coarea "
            "majorant is the ordinary proof in the companion lab; Lean theorem "
            "cassini_nine_tenths_falsifies_tree_budget checks the contradiction."
        ),
        "experiment_contract": build_experiment_contract(
            problem_id="erdos_1041",
            target_statement=(
                "Prove that two roots admit a path of length less than two inside "
                "the strict unit lemniscate."
            ),
            claim_ceiling=(
                "Refutes the two named spanning-tree budget propositions only; "
                "Erdős #1041 remains open."
            ),
            hypothesis_id="epsilon_sharp_strip_average_tree_budget",
            hypothesis_statement=(
                "The level-length tail divided by 2π, plus arbitrary epsilon, "
                "bounds a connected tree spanning every root in the component."
            ),
            probe_id="cassini_dual_draft_source_linked_falsifier",
            probe_question=(
                "Do the printed tree-budget propositions survive the exact "
                "Cassini component at a=9/10?"
            ),
            computation=(
                "Pin both proposition statements, replay the rational square-root "
                "upper certificate, and compare the resulting budget with the "
                "unavoidable distance between the two roots."
            ),
            falsifier=(
                "A valid component satisfying the proposition hypotheses whose "
                "level-length budget is strictly below every spanning-tree length."
            ),
            stop_condition=(
                "Once both printed proposition statements are source-pinned and "
                "the same exact Cassini witness refutes each, stop auditing local "
                "repairs of that unchanged metric claim and rotate mechanisms."
            ),
            survival_consequence=(
                "If the budget survived, audit the remaining perturbation and "
                "root-transfer fan-in."
            ),
            falsification_consequence=(
                "Both unrestricted proof drafts lose their load-bearing spanning-"
                "tree estimate; any repair must pay positive attachment overhead "
                "or use a different direct two-root metric consumer."
            ),
            consumer_ref=LEAN_REF,
            consumer_declarations=[
                "ErdosProblems.Erdos1041.CassiniTreeBudget."
                "cassini_nine_tenths_falsifies_tree_budget",
                "ErdosProblems.Erdos1041.CassiniTreeBudget."
                "cassini_nine_tenths_forces_attachment_overhead",
            ],
            analysis_refs=[LAB_REF, PACKET_REF, PAPER_REF, DIGEST_REF, PRIOR_ART_REF],
            source_refs=[SOURCE_REF, MAIN_REF, REVISED_REF],
            result_status="exact_one_way_result",
            result_summary=summary,
            progress_class="mechanism_eliminated",
            decision_basis=(
                "Both source statements share the refuted epsilon-sharp budget, "
                "and the strict Cassini gap exceeds 4/25."
            ),
            next_analytic_target=(
                "Select one short root pair directly, or prove a global inequality "
                "that explicitly pays the nonlocal saddle-attachment cost."
            ),
        ),
        "sources": [
            source_record(REPO_ROOT, ref)
            for ref in [SOURCE_REF, MAIN_REF, REVISED_REF, LEAN_REF, LAB_REF]
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(build_result(), indent=2, sort_keys=True) + "\n"
    output = args.output.resolve()
    if args.check:
        if not output.exists() or output.read_text(encoding="utf-8") != rendered:
            print(f"stale or missing receipt: {output}", file=sys.stderr)
            return 1
        print(json.dumps({"status": "current", "output": str(output)}))
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(output)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
