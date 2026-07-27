#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Use a semantic slice to assemble and kernel-check a new scratch corollary."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Any

import query_corpus


DOGFOOD_SCHEMA = "erdos249257-semantic-proof-dogfood/1"
DEFAULT_QUERY = (
    "which premises let either sharp curvature or exponent only three "
    "transport prove irrationality of the totient series"
)
REQUIRED_DECLARATIONS = {
    "irrational_totientSeries_of_sharpCurvatureSupply",
    "irrational_totient_series_of_exponentOnlyThreeTransportSupply",
}
HALF_QUERY = (
    "which proof sockets let either terminal scaled vanishing or middle "
    "producer tail escape prove half membership"
)
HALF_REQUIRED_DECLARATIONS = {
    "half_mem_mersenneAchievementSet_of_terminalScaledVanishing",
    "half_mem_mersenneAchievementSet_of_middleProducerTailEscapeExceptNegThree",
}
SCRATCH_THEOREM = """\
import Erdos249257.CurvatureCarry
import Erdos249257.ExponentOnlyTransport
import Erdos249257.TerminalOnlyScaledVanishing
import Erdos249257.HalfCylinderLastProducerContradiction

open scoped BigOperators

/- A query-derived composition of two independent conditional proof sockets.
   This does not assert either open supply. -/
theorem semanticCompiler_disjunctiveSupplySocket
    (h :
      Erdos249257.TotientTailPeriodKiller.SharpCurvatureSupply ∨
        Erdos249257.ExponentOnlyTransport.ExponentOnlyThreeTransportSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  rcases h with hcurvature | htransport
  · exact
      Erdos249257.TotientTailPeriodKiller.irrational_totientSeries_of_sharpCurvatureSupply
        hcurvature
  · exact
      Erdos249257.ExponentOnlyTransport.irrational_totient_series_of_exponentOnlyThreeTransportSupply
        htransport

/- A query-derived disjunction between two sufficient half-membership
   sockets. This does not assert either antecedent. -/
theorem semanticCompiler_halfMembershipAlternative
    (h :
      Nonempty
          Erdos249257.HalfCarryReachability.HalfTerminalOnlyScaledVanishingSequence ∨
        Erdos249257.SeamMiddleProducerTailEscapeExceptNegThree) :
    (1 / 2 : ℝ) ∈ Erdos249257.mersenneAchievementSet := by
  rcases h with hterminal | hmiddle
  · rcases hterminal with ⟨S⟩
    exact
      Erdos249257.HalfCarryReachability.half_mem_mersenneAchievementSet_of_terminalScaledVanishing
        S
  · exact
      Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerTailEscapeExceptNegThree
        hmiddle
"""


def retrieved_declarations(packet: dict[str, Any]) -> set[str]:
    names: set[str] = set()
    for cell in packet["semantic_cells"]:
        if cell["kind"] == "declaration":
            names.add(cell["handle"])
        elif cell["kind"] == "claim":
            names.update(
                row["name"]
                for row in cell["content"]["claim_record"].get(
                    "declarations", []
                )
            )
    return names


def dogfood_packet(query: str) -> dict[str, Any]:
    task_specs = (
        ("transport_supply_alternatives", query, REQUIRED_DECLARATIONS),
        ("half_membership_alternatives", HALF_QUERY, HALF_REQUIRED_DECLARATIONS),
    )
    tasks = []
    all_required: set[str] = set()
    all_recovered: set[str] = set()
    all_ranked: set[str] = set()
    missing_any: set[str] = set()
    for task_id, task_query, required in task_specs:
        ranked_search = query_corpus.search_packet(
            task_query, query_corpus.MAX_SEMANTIC_CELLS
        )
        ranked_declarations = {
            query_corpus.semantic_result_handle(result)
            for result in ranked_search["results"]
            if result["kind"] == "declaration"
        }
        semantic_slice = query_corpus.semantic_slice_packet(task_query, 4)
        recovered = retrieved_declarations(semantic_slice)
        synthesized_consumers = {
            row["name"]: row["signature"]
            for row in semantic_slice["operator_synthesis"].get(
                "checked_consumer_signatures", []
            )
        }
        missing = sorted(
            required - recovered - set(synthesized_consumers)
        )
        tasks.append(
            {
                "id": task_id,
                "query": task_query,
                "semantic_slice_id": semantic_slice.get("slice_id"),
                "semantic_operator": semantic_slice[
                    "query_interpretation"
                ]["operator"]["id"],
                "required_declarations": sorted(required),
                "retrieved_declarations": sorted(recovered),
                "synthesized_consumer_signatures": synthesized_consumers,
                "ranked_search_recovered_required_declarations": sorted(
                    required & ranked_declarations
                ),
                "missing_required_declarations": missing,
                "semantic_expansion_gain": (
                    len(required & (recovered | set(synthesized_consumers)))
                    - len(required & ranked_declarations)
                ),
            }
        )
        all_required.update(required)
        all_recovered.update(recovered)
        all_ranked.update(ranked_declarations)
        missing_any.update(missing)
    if missing_any:
        return {
            "kind": "semantic_proof_dogfood",
            "schema_version": DOGFOOD_SCHEMA,
            "proof_tasks": tasks,
            "passed": False,
            "stage": "semantic_retrieval",
            "missing_required_declarations": sorted(missing_any),
        }

    started = time.monotonic()
    with tempfile.TemporaryDirectory(
        prefix="semantic-proof-dogfood-"
    ) as temp_dir:
        source = Path(temp_dir) / "SemanticCompilerDogfood.lean"
        source.write_text(SCRATCH_THEOREM, encoding="utf-8")
        completed = subprocess.run(
            ["lake", "env", "lean", str(source)],
            cwd=query_corpus.ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
    elapsed = time.monotonic() - started
    return {
        "kind": "semantic_proof_dogfood",
        "schema_version": DOGFOOD_SCHEMA,
        "proof_tasks": tasks,
        "passed": completed.returncode == 0,
        "stage": "kernel_validation",
        "retrieved_declarations": sorted(all_recovered),
        "required_declarations": sorted(all_required),
        "ranked_search_recovered_required_declarations": sorted(
            all_required & all_ranked
        ),
        "semantic_expansion_gain": sum(
            task["semantic_expansion_gain"] for task in tasks
        ),
        "scratch_theorem_sha256": hashlib.sha256(
            SCRATCH_THEOREM.encode("utf-8")
        ).hexdigest(),
        "scratch_posture": (
            "temporary_new_corollary_not_a_new_supply_claim_or_open_problem_solution"
        ),
        "lean_command": "lake env lean <temporary>/SemanticCompilerDogfood.lean",
        "lean_exit_code": completed.returncode,
        "lean_output": completed.stdout,
        "elapsed_seconds": round(elapsed, 3),
        "authority_posture": (
            "semantic_compiler_selects_premises;Lean_kernel_validates_the_composition"
        ),
    }


def render_card(packet: dict[str, Any]) -> str:
    if packet["stage"] == "semantic_retrieval":
        return (
            f"semantic proof dogfood | FAIL retrieval "
            f"| missing={','.join(packet['missing_required_declarations'])}"
        )
    return (
        f"semantic proof dogfood {packet['schema_version']} "
        f"| {'PASS' if packet['passed'] else 'FAIL'} "
        f"| tasks={len(packet['proof_tasks'])} "
        f"| declarations={len(packet['required_declarations'])} "
        f"| lean_exit={packet['lean_exit_code']} "
        f"| elapsed={packet['elapsed_seconds']}s"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--query", default=DEFAULT_QUERY)
    parser.add_argument("--format", choices=("json", "card"), default="card")
    args = parser.parse_args()
    packet = dogfood_packet(args.query)
    if args.format == "json":
        print(json.dumps(packet, ensure_ascii=False, indent=2))
    else:
        print(render_card(packet))
    return 0 if packet["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
