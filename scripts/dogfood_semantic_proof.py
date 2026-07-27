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
DIRECT_CURVATURE_QUERY = (
    "which exact theorem turns a direct dyadic curvature certificate into "
    "nonintegrality of the curvature expression"
)
DIRECT_CURVATURE_REQUIRED_DECLARATIONS = {
    "curvature_notMem_int_of_sharpCurvatureCert",
}
FORMAL_TRACE_QUERY = (
    "trace why sharp curvature supply proves irrationality of the totient "
    "series"
)
FORMAL_TRACE_REQUIRED_DEPENDENCIES = {
    "curvature_notMem_int_of_sharpCurvatureCert",
    "rational_totient_series_forces_lcm_cone_flatness",
}
FORMAL_PATH_QUERY = (
    "trace the formal chain from sharp curvature irrationality "
    "to denominator divisibility"
)
FORMAL_PATH_REQUIRED_DECLARATIONS = {
    "rational_totient_series_forces_lcm_cone_flatness",
    "eventual_period_of_not_irrational",
    "tail_diff_int_of_den_dvd",
}
SCRATCH_THEOREM = """\
import Erdos249257.CurvatureCarry
import Erdos249257.ExponentOnlyTransport
import Erdos249257.TerminalOnlyScaledVanishing
import Erdos249257.HalfCylinderLastProducerContradiction

open scoped BigOperators
open Erdos249257.TotientTailPeriodKiller

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

/- A query-derived exact consumer for the direct dyadic curvature
   certificate. The query selected both the authored module and this theorem. -/
theorem semanticCompiler_directCurvatureConsumer {H L : ℕ} (hH : 1 ≤ H)
    (hcert :
      Erdos249257.TotientTailPeriodKiller.sharpCurvatureCert H L) :
    Erdos249257.TotientTailPeriodKiller.curvatureTail H ∉
      Set.range ((↑) : ℤ → ℝ) := by
  exact
    Erdos249257.TotientTailPeriodKiller.curvature_notMem_int_of_sharpCurvatureCert
      hH hcert

/- A proof-cone reconstruction of the lcm-cone flatness bridge.  The semantic
   path exposes `eventual_period_of_not_irrational` as the exact intermediate
   between curvature irrationality and denominator-divisibility arithmetic. -/
theorem semanticCompiler_reconstructedConeFlatness
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ t₁ : ℕ, ∀ t, t₁ ≤ t → ∀ q m : ℕ, 0 < q →
      totientTail (q * periodLcm t + m * periodLcm t) -
        totientTail (q * periodLcm t) ∈ Set.range ((↑) : ℤ → ℝ) := by
  obtain ⟨h₀, hpos, N₀, hint⟩ := eventual_period_of_not_irrational hrat
  refine ⟨max h₀ N₀, fun t ht q m hq => ?_⟩
  have hdvdH : h₀ ∣ periodLcm t :=
    dvd_periodLcm hpos (le_trans (le_max_left _ _) ht)
  have hdvd : h₀ ∣ m * periodLcm t := hdvdH.mul_left m
  have hN : N₀ ≤ q * periodLcm t := by
    have h1 : N₀ ≤ t := le_trans (le_max_right _ _) ht
    have h2 : t ≤ periodLcm t := le_periodLcm t
    have h3 : periodLcm t ≤ q * periodLcm t := by
      calc
        periodLcm t = 1 * periodLcm t := (one_mul _).symm
        _ ≤ q * periodLcm t := Nat.mul_le_mul_right _ hq
    omega
  obtain ⟨c, hc⟩ := hdvd
  have hmem := tail_diff_mul_mem_int hint c (q * periodLcm t) hN
  have heq : c * h₀ = m * periodLcm t := by
    rw [hc]
    ring
  rwa [heq] at hmem

/- A dependency-index reconstruction of the curvature supply proof socket.
   The proof deliberately uses the two exact theorem dependencies recovered
   from the elaborated body instead of invoking the packaged consumer. -/
theorem semanticCompiler_reconstructedCurvatureChain
    (hsupply : SharpCurvatureSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  obtain ⟨t₁, hflat⟩ :=
    semanticCompiler_reconstructedConeFlatness hrat
  obtain ⟨t, ht, hcert⟩ := hsupply (max t₁ 1)
  have ht₁ : t₁ ≤ t := (le_max_left _ _).trans ht
  have htpos : 1 ≤ t := (le_max_right _ _).trans ht
  obtain ⟨a, ha⟩ := hflat t ht₁ 1 1 (by omega)
  obtain ⟨b, hb⟩ := hflat t ht₁ 2 2 (by omega)
  have hHpos : 1 ≤ periodLcm t := periodLcm_pos t
  apply curvature_notMem_int_of_sharpCurvatureCert hHpos hcert
  refine ⟨b - 2 * a, ?_⟩
  unfold curvatureTail
  push_cast
  have htwo : periodLcm t + periodLcm t = 2 * periodLcm t := by omega
  have hfour : 2 * periodLcm t + 2 * periodLcm t = 4 * periodLcm t := by
    omega
  norm_num at ha hb
  rw [htwo] at ha
  rw [hfour] at hb
  have ha' :
      (a : ℝ) =
        totientTail (2 * periodLcm t) - totientTail (periodLcm t) := by
    exact ha
  have hb' :
      (b : ℝ) =
        totientTail (4 * periodLcm t) - totientTail (2 * periodLcm t) := by
    exact hb
  linarith [ha', hb']
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
        (
            "direct_curvature_consumer",
            DIRECT_CURVATURE_QUERY,
            DIRECT_CURVATURE_REQUIRED_DECLARATIONS,
        ),
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
    trace_ranked = query_corpus.search_packet(
        FORMAL_TRACE_QUERY, query_corpus.MAX_SEMANTIC_CELLS
    )
    trace_ranked_declarations = {
        query_corpus.semantic_result_handle(result)
        for result in trace_ranked["results"]
        if result["kind"] == "declaration"
    }
    trace_slice = query_corpus.semantic_slice_packet(FORMAL_TRACE_QUERY, 4)
    formal_dependencies = {
        dependency["name"]
        for neighbourhood in trace_slice["operator_synthesis"].get(
            "formal_dependency_neighbourhoods", []
        )
        for dependency in neighbourhood["direct_dependencies"]
    }
    missing_trace = sorted(
        FORMAL_TRACE_REQUIRED_DEPENDENCIES - formal_dependencies
    )
    tasks.append(
        {
            "id": "formal_dependency_reconstruction",
            "query": FORMAL_TRACE_QUERY,
            "semantic_slice_id": trace_slice.get("slice_id"),
            "semantic_operator": trace_slice[
                "query_interpretation"
            ]["operator"]["id"],
            "required_declarations": sorted(
                FORMAL_TRACE_REQUIRED_DEPENDENCIES
            ),
            "retrieved_declarations": sorted(formal_dependencies),
            "synthesized_consumer_signatures": {},
            "ranked_search_recovered_required_declarations": sorted(
                FORMAL_TRACE_REQUIRED_DEPENDENCIES
                & trace_ranked_declarations
            ),
            "missing_required_declarations": missing_trace,
            "semantic_expansion_gain": (
                len(
                    FORMAL_TRACE_REQUIRED_DEPENDENCIES
                    & formal_dependencies
                )
                - len(
                    FORMAL_TRACE_REQUIRED_DEPENDENCIES
                    & trace_ranked_declarations
                )
            ),
            "dependency_authority": (
                "elaborated_Lean_type_and_value_constant_references"
            ),
        }
    )
    all_required.update(FORMAL_TRACE_REQUIRED_DEPENDENCIES)
    all_recovered.update(formal_dependencies)
    all_ranked.update(trace_ranked_declarations)
    missing_any.update(missing_trace)
    formal_path_slice = query_corpus.semantic_slice_packet(
        FORMAL_PATH_QUERY, 20
    )
    formal_path = formal_path_slice["operator_synthesis"].get(
        "formal_dependency_path", {}
    )
    formal_path_declarations = {
        node["name"] for node in formal_path.get("nodes", [])[1:]
    }
    missing_path = sorted(
        FORMAL_PATH_REQUIRED_DECLARATIONS - formal_path_declarations
    )
    tasks.append(
        {
            "id": "formal_multihop_cone_reconstruction",
            "query": FORMAL_PATH_QUERY,
            "semantic_slice_id": formal_path_slice.get("slice_id"),
            "semantic_operator": formal_path_slice[
                "query_interpretation"
            ]["operator"]["id"],
            "required_declarations": sorted(
                FORMAL_PATH_REQUIRED_DECLARATIONS
            ),
            "retrieved_declarations": sorted(
                formal_path_declarations
            ),
            "synthesized_consumer_signatures": {},
            "ranked_search_recovered_required_declarations": [],
            "missing_required_declarations": missing_path,
            "semantic_expansion_gain": len(
                FORMAL_PATH_REQUIRED_DECLARATIONS
                & formal_path_declarations
            ),
            "dependency_authority": (
                "shortest_elaborated_value_reference_path"
            ),
            "dependency_hop_count": formal_path.get("hop_count"),
        }
    )
    all_required.update(FORMAL_PATH_REQUIRED_DECLARATIONS)
    all_recovered.update(formal_path_declarations)
    missing_any.update(missing_path)
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
