#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Held-out reasoning benchmark for the witness-carrying corpus compiler."""

from __future__ import annotations

import argparse
import json
from typing import Any

import query_corpus


BENCHMARK_SCHEMA = "erdos249257-semantic-reasoning-benchmark/1"

# Development questions are the motivating failures that shaped the first
# semantic vocabulary. Held-out questions use unseen phrasing and must route
# without matching any authored vocabulary row.
TASKS: tuple[dict[str, Any], ...] = (
    {
        "id": "dev_rank_two_value",
        "split": "development",
        "query": "is rank two worth pursuing",
        "operator": "falsify",
        "required_cells": (
            ("declaration", "rank2_kill_sound_but_not_shallower_at_cell"),
        ),
        "required_text": ("NOT shallower", "LcmConeFlatness.lean:626"),
        "required_edges": (
            (
                "declaration:Erdos249257.TotientTailPeriodKiller.rank2_kill_sound_but_not_shallower_at_cell",
                "elaborated_at",
                "Erdos249257/LcmConeFlatness.lean:626",
            ),
        ),
    },
    {
        "id": "dev_half_value_frontier",
        "split": "development",
        "query": "what should I try next for the half value problem",
        "operator": "frontier",
        "required_cells": (
            ("reading_route", "erdos257_half_story"),
            ("open_proposition", "remaining_open.half_value_membership"),
        ),
        "required_text": (
            "Decide whether 1/2 lies in the Mersenne achievement set",
            "neither half-membership nor universal Erdős #257 is proved",
        ),
        "required_edges": (
            (
                "open_proposition:remaining_open.half_value_membership",
                "keeps_open",
                "claim:universal_257",
            ),
        ),
    },
    {
        "id": "dev_affine_transport_ceiling",
        "split": "development",
        "query": "can affine transport solve erdos 249",
        "operator": "falsify",
        "required_cells": (
            ("claim", "transport_curvature_reductions"),
            (
                "open_proposition",
                "remaining_open.unbounded_certificate_supply",
            ),
        ),
        "required_text": (
            "Every supply hypothesis remains open",
            "Produce certified non-integrality witnesses at unbounded parameters",
        ),
        "required_edges": (
            (
                "claim:transport_curvature_reductions",
                "bounded_by",
                "open_proposition:remaining_open.unbounded_certificate_supply",
            ),
        ),
    },
    {
        "id": "dev_half_alternative_support",
        "split": "development",
        "query": (
            "which proof sockets let either terminal scaled vanishing or "
            "middle producer tail escape prove half membership"
        ),
        "operator": "support",
        "required_cells": (
            (
                "declaration",
                "half_mem_mersenneAchievementSet_of_terminalScaledVanishing",
            ),
            (
                "declaration",
                "half_mem_mersenneAchievementSet_of_middleProducerTailEscapeExceptNegThree",
            ),
        ),
        "required_text": (
            "support_alternative_left",
            "support_alternative_right",
            "HalfTerminalOnlyScaledVanishingSequence",
            "SeamMiddleProducerTailEscapeExceptNegThree",
        ),
    },
    {
        "id": "dev_full_target_supply_boundary",
        "split": "development",
        "query": (
            "can full target prime adjacency provide the unbounded "
            "certificate supply for erdos 249"
        ),
        "operator": "support",
        "required_cells": (
            (
                "declaration",
                "fullTarget_primeAdjunction_diamond_iff_root",
            ),
            (
                "open_proposition",
                "remaining_open.unbounded_certificate_supply",
            ),
            ("module", "Erdos249257.FullTargetPrimeAdjunctionNoGo"),
        ),
        "required_text": (
            "apply Erdos249257.FullTargetPrimeAdjunctionNoGo.fullTarget_primeAdjunction_diamond_iff_root",
            "Produce certified non-integrality witnesses at unbounded parameters",
            "unproved_requirements",
        ),
        "required_edges": (
            (
                "open_proposition:remaining_open.unbounded_certificate_supply",
                "keeps_open",
                "claim:erdos_249",
            ),
        ),
    },
    {
        "id": "heldout_affine_annihilation_location",
        "split": "held_out",
        "query": "where is the exact theorem for affine old channel annihilation",
        "operator": "locate",
        "required_cells": (
            ("claim", "affine_transport_annihilation"),
            ("declaration", "oldChannel_affine_moment_annihilation"),
        ),
        "required_text": ("oldChannel_affine_moment_annihilation",),
    },
    {
        "id": "heldout_curvature_support",
        "split": "held_out",
        "query": "what do I need to prove to get irrationality from curvature",
        "operator": "support",
        "required_cells": (
            ("claim", "transport_curvature_reductions"),
        ),
        "required_text": (
            "unbounded supply would imply irrationality",
            "Every supply hypothesis remains open",
        ),
    },
    {
        "id": "heldout_fixed_precision_trace",
        "split": "held_out",
        "query": "why does fixed precision transport fail",
        "operator": "trace",
        "required_cells": (
            ("reading_route", "transport_curvature_programme"),
            ("claim", "fixed_precision_transport_no_go"),
            ("declaration", "fixedPrecisionTropicalNoGo"),
        ),
        "required_text": (
            "fixedPrecisionTropicalNoGo",
            "vu_word_has_prefix_locked_completion",
            "source_lexical_dependency_candidate_not_elaborator_dependency_proof",
        ),
    },
    {
        "id": "heldout_half_programme_analogy",
        "split": "held_out",
        "query": (
            "compare half carry compactness with the half achievement set route"
        ),
        "operator": "analogy",
        "required_cells": (
            ("reading_route", "half_carry_compactness_programme"),
            ("reading_route", "erdos257_half_story"),
        ),
        "required_text": (
            "analogy_left_subject",
            "analogy_right_subject",
            "Structural similarity is not transported as a proof",
        ),
    },
    {
        "id": "heldout_boolean_mobius_digest",
        "split": "held_out",
        "query": "explain the boolean mobius carry story",
        "operator": "digest",
        "required_cells": (
            ("reading_route", "boolean_mobius_constraints"),
            ("claim", "boolean_mobius_carry"),
            ("declaration", "mobius_carryQuotient_boolean"),
        ),
        "required_text": ("mobius_carryQuotient_boolean",),
    },
    {
        "id": "heldout_half_seam_frontier",
        "split": "held_out",
        "query": "what remains after the half seam classification",
        "operator": "frontier",
        "required_cells": (
            ("claim", "half_membership_seam_classification"),
            ("open_proposition", "remaining_open.half_value_membership"),
        ),
        "required_text": (
            "Nearby proved reductions do not discharge the exact remaining-open proposition",
        ),
    },
    {
        "id": "heldout_last_producer_location",
        "split": "held_out",
        "query": "where is the exact last producer tail escape reduction",
        "operator": "locate",
        "required_cells": (
            ("claim", "last_producer_tail_escape_reduction"),
        ),
        "required_text": ("Last-producer tail-escape reduction",),
    },
    {
        "id": "heldout_module_header_location",
        "split": "held_out",
        "query": "where is the module for a direct dyadic curvature certificate",
        "operator": "locate",
        "required_cells": (
            ("module", "Erdos249257.CurvatureCarry"),
        ),
        "required_text": (
            "Curvature carry for the totient tail",
            "source_current_authored_digestion",
        ),
    },
    {
        "id": "heldout_lean_goal_support",
        "split": "held_out",
        "query": (
            "I need to prove Irrational (∑' n : ℕ, "
            "(Nat.totient n : ℝ) / 2 ^ n) from a SharpCurvatureSupply"
        ),
        "operator": "support",
        "required_cells": (
            (
                "declaration",
                "irrational_totientSeries_of_sharpCurvatureSupply",
            ),
        ),
        "required_text": (
            "rational_totient_series_forces_lcm_cone_flatness",
            "curvature_notMem_int_of_sharpCurvatureCert",
            "apply Erdos249257.TotientTailPeriodKiller.irrational_totientSeries_of_sharpCurvatureSupply",
        ),
    },
    {
        "id": "heldout_direct_curvature_consumer",
        "split": "held_out",
        "query": (
            "which exact theorem turns a direct dyadic curvature certificate "
            "into nonintegrality of the curvature expression"
        ),
        "operator": "support",
        "required_cells": (
            (
                "declaration",
                "curvature_notMem_int_of_sharpCurvatureCert",
            ),
            ("module", "Erdos249257.CurvatureCarry"),
        ),
        "required_text": (
            "apply Erdos249257.TotientTailPeriodKiller.curvature_notMem_int_of_sharpCurvatureCert",
            "sharpCurvatureCert H L",
            "source_current_authored_digestion",
        ),
        "required_edges": (
            (
                "declaration:Erdos249257.TotientTailPeriodKiller.curvature_notMem_int_of_sharpCurvatureCert",
                "elaborated_at",
                "Erdos249257/CurvatureCarry.lean:159",
            ),
        ),
    },
)


def authority_fidelity_errors(packet: dict[str, Any]) -> list[str]:
    registry = query_corpus.load("docs/claims.json")
    claim_status = {row["id"]: row["status"] for row in registry["claims"]}
    open_ids = {
        row["id"] for row in registry["remaining_open_propositions"]
    }
    errors: list[str] = []
    for cell in packet["semantic_cells"]:
        expected_planes = {"kernel", "status", "digestion", "navigation"}
        actual_planes = {row["plane"] for row in cell["typed_provenance"]}
        if actual_planes != expected_planes:
            errors.append(
                f"{cell['cell_id']}: provenance planes {sorted(actual_planes)}"
            )
        if cell["kind"] == "claim":
            claim = cell["content"]["claim_record"]
            if claim_status.get(claim["id"]) != claim["status"]:
                errors.append(f"{cell['cell_id']}: claim status drift")
        elif cell["kind"] == "open_proposition":
            open_record = cell["content"]["open_record"]
            if open_record["id"] not in open_ids:
                errors.append(f"{cell['cell_id']}: unregistered open boundary")
        elif cell["kind"] == "reading_route":
            programme = cell["content"].get("programme")
            if programme:
                for claim in programme["core_claims"]:
                    if claim_status.get(claim["id"]) != claim["status"]:
                        errors.append(
                            f"{cell['cell_id']}: route claim status drift for "
                            f"{claim['id']}"
                        )
        elif cell["kind"] == "declaration":
            witness = cell["content"]["formal_witness"]
            source_path = query_corpus.ROOT / witness["module"]
            if not source_path.is_file():
                errors.append(
                    f"{cell['cell_id']}: missing Lean source {witness['module']}"
                )
            if not witness.get("signature") or not witness.get("source_ref"):
                errors.append(f"{cell['cell_id']}: incomplete kernel witness")
    return errors


def evaluate_task(task: dict[str, Any]) -> dict[str, Any]:
    packet = query_corpus.semantic_slice_packet(task["query"], 20)
    baseline_results = query_corpus.search_packet(
        task["query"], query_corpus.MAX_SEMANTIC_CELLS
    )["results"]
    baseline_cells = {
        (result["kind"], query_corpus.semantic_result_handle(result))
        for result in baseline_results
    }
    encoded = json.dumps(
        packet, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    cells = {
        (cell["kind"], cell["handle"]) for cell in packet["semantic_cells"]
    }
    edges = {
        (edge["from"], edge["relation"], edge["to"])
        for edge in packet["minimal_witness_subgraph"]["edges"]
    }
    text = encoded.decode("utf-8")
    failures: list[str] = []
    actual_operator = packet["query_interpretation"]["operator"]["id"]
    if actual_operator != task["operator"]:
        failures.append(
            f"operator expected {task['operator']} got {actual_operator}"
        )
    for required in task["required_cells"]:
        if required not in cells:
            failures.append(f"missing semantic cell {required[0]}:{required[1]}")
    for fragment in task.get("required_text", ()):
        if fragment not in text:
            failures.append(f"missing witness text {fragment!r}")
    for edge in task.get("required_edges", ()):
        if edge not in edges:
            failures.append(f"missing witness edge {edge}")
    if len(encoded) > query_corpus.OUTPUT_BUDGET_BYTES:
        failures.append(
            f"packet size {len(encoded)} exceeds {query_corpus.OUTPUT_BUDGET_BYTES}"
        )
    if task["split"] == "held_out":
        matched = query_corpus.matched_semantic_vocabulary(task["query"])
        if matched:
            failures.append(
                "held-out query unexpectedly matches authored vocabulary: "
                + ",".join(row["id"] for row in matched)
            )
    failures.extend(authority_fidelity_errors(packet))
    return {
        "id": task["id"],
        "split": task["split"],
        "query": task["query"],
        "passed": not failures,
        "operator": actual_operator,
        "required_handle_count": len(task["required_cells"]),
        "baseline_recovered_required_handle_count": sum(
            required in baseline_cells for required in task["required_cells"]
        ),
        "recovered_required_handle_count": sum(
            required in cells for required in task["required_cells"]
        ),
        "cell_count": len(cells),
        "witness_edge_count": len(edges),
        "packet_bytes": len(encoded),
        "failures": failures,
    }


def benchmark_packet(split: str) -> dict[str, Any]:
    selected = [
        task for task in TASKS if split == "all" or task["split"] == split
    ]
    results = [evaluate_task(task) for task in selected]
    required = sum(row["required_handle_count"] for row in results)
    recovered = sum(
        row["recovered_required_handle_count"] for row in results
    )
    baseline_recovered = sum(
        row["baseline_recovered_required_handle_count"] for row in results
    )
    passed = sum(row["passed"] for row in results)
    return {
        "kind": "semantic_reasoning_benchmark",
        "schema_version": BENCHMARK_SCHEMA,
        "split": split,
        "benchmark_posture": (
            "query_compilation_and_evidence_fidelity_not_a_claim_of_general_mathematical_omniscience"
        ),
        "held_out_contract": (
            "held-out questions use no phrase that activates the authored "
            "semantic vocabulary; they exercise compositional lexical, graph, "
            "and operator routing."
        ),
        "summary": {
            "task_count": len(results),
            "passed_task_count": passed,
            "task_accuracy": passed / len(results) if results else 1.0,
            "ranked_search_required_handle_recall": (
                baseline_recovered / required if required else 1.0
            ),
            "required_handle_recall": recovered / required if required else 1.0,
            "semantic_compiler_recall_uplift": (
                (recovered - baseline_recovered) / required
                if required
                else 0.0
            ),
            "maximum_packet_bytes": max(
                (row["packet_bytes"] for row in results), default=0
            ),
            "output_budget_bytes": query_corpus.OUTPUT_BUDGET_BYTES,
        },
        "tasks": results,
        "passed": passed == len(results),
    }


def render_card(packet: dict[str, Any]) -> str:
    summary = packet["summary"]
    rows = [
        f"semantic reasoning benchmark {packet['schema_version']} "
        f"| split={packet['split']} | passed="
        f"{summary['passed_task_count']}/{summary['task_count']} "
        f"| search_recall={summary['ranked_search_required_handle_recall']:.3f} "
        f"| compiled_recall={summary['required_handle_recall']:.3f} "
        f"| max_packet={summary['maximum_packet_bytes']}B"
    ]
    rows.extend(
        f"{'PASS' if task['passed'] else 'FAIL'} {task['id']} "
        f"| operator={task['operator']} "
        f"| search={task['baseline_recovered_required_handle_count']}/"
        f"{task['required_handle_count']} "
        f"| handles={task['recovered_required_handle_count']}/"
        f"{task['required_handle_count']} | packet={task['packet_bytes']}B"
        + (
            ""
            if task["passed"]
            else " | " + "; ".join(task["failures"])
        )
        for task in packet["tasks"]
    )
    return "\n".join(rows)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--split",
        choices=("all", "development", "held_out"),
        default="all",
    )
    parser.add_argument("--format", choices=("json", "card"), default="card")
    args = parser.parse_args()
    packet = benchmark_packet(args.split)
    if args.format == "json":
        print(json.dumps(packet, ensure_ascii=False, indent=2))
    else:
        print(render_card(packet))
    return 0 if packet["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
