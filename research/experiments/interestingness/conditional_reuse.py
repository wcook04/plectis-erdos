#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""A frozen paper workload and exact cuts in its indexed source dependency graph.

Availability means that a declaration may be used without inspecting its proof.
This measures an inspection subtotal, not mathematical value, optimal proofs,
actual review time, or a prospective benefit from moving existing lemmas.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from collections import Counter
from pathlib import Path

from run import ROOT, closure_cost, load_indexed_cost_graph


DEFAULT_OUTPUT = Path(__file__).with_suffix(".json")
TARGET_ROWS = (
    "erdos-251-prime-gap-dyadic-series#res:sparserationalisation",
    "erdos-269-three-prime-running-lcm#res:infinite-rank",
    "erdos-269-three-prime-running-lcm#res:denominator-reduction",
    "erdos-269-three-prime-running-lcm#res:exact-onset",
    "erdos-269-three-prime-running-lcm#res:windowconsumer",
)
SHORTLIST_SIZE = 6
PAIR_POOL_SIZE = 30
BREADTH_TARGETS = (
    (68, "erdos-68-factorial-denominator-irrationality#res:finite-channel-moment-certificate",
     "ErdosProblems.Erdos68.PaperComplete.finite_channel_moment_certificate",
     "A finite-channel moment certificate represents the paper's arithmetic mechanism; "
     "it is not the open irrationality assertion."),
    (243, "erdos-243-reciprocal-tail-rigidity#res:cubicrate",
     "ErdosProblems.Erdos243.PaperCompleteR21.cubic_rate_irrationality_unconditional",
     "The paper's cubic-rate irrationality theorem, with its displayed asymptotic hypothesis."),
    (249, "erdos-249-binary-totient-series#thm:kkernelrank",
     "ErdosProblems.Erdos249.PaperCompleteR8.displayed_all_base_kernel",
     "The exact all-base kernel-rank statement, not an equivalent reformulation of irrationality."),
    (251, "erdos-251-prime-gap-dyadic-series#res:sparserationalisation",
     "ErdosProblems.Erdos251.PaperR9.SparseAmbient.arbitrary_word_sparse_rationalisation_uniform",
     "The arbitrary-envelope sparse correction clause, preserving the uniform cutoff quantifiers."),
    (257, "erdos-257-mersenne-support-subseries#res:weighted-support",
     "ErdosProblems.Erdos257.PaperCompleteR8.divisibilityWeightedClaim",
     "The ranked finite-prime weighted-support irrationality criterion, under its summability premise."),
    (269, "erdos-269-three-prime-running-lcm#res:infinite-rank",
     "ErdosProblems.Erdos269.PaperR7.paper_uniform_rank_and_nonseparation",
     "The arbitrary-order nonsingular-minor and nonseparation theorem, not the open series endpoint."),
    (1041, "erdos-1041-lemniscate-newton-flow#res:ani-degree-seven-counterexample",
     "Erdos1041.Counterexample.erdos1041_counterexample_hausdorff",
     "Ani's degree-seven Hausdorff-length counterexample; no claim about the unreviewed 1958 wording."),
    (1049, "erdos-1049-rational-base-lambert#res:rational-base-threshold",
     "ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_threshold",
     "The stated rational-base contour theorem; it does not include the unresolved base 3/2."),
)
# These choices are an authored inspection decision, not another numeric score.
# The source reads distinguish load-bearing bodies from high-scoring transports.
REVIEW_CHOICES = (
    (
        "ErdosProblems.Erdos269.exists_uniform_nonsingular_threePrimeKernel_minor",
        "The three-line prime-specialisation wrapper scores higher, but this 53-line "
        "body exposes the staircase indices, kernel factorisation and nonzero determinant.",
        "Check that the same selected indices work for every layer k, and that the "
        "NoIntegerOrbit hypotheses are exactly what the staircase construction consumes. "
        "Reject a proposed generalisation if either uniformity or the orbit premise fails.",
    ),
    (
        "ErdosProblems.Erdos251.PaperR9.SparseAmbient.generated_ambient_filling_uniform",
        "Its 28-line body transports interval filling to an ambient correction sequence; "
        "both frozen sparse-rationalisation target declarations consume it.",
        "Trace generated_interval_filling through ambient support, the capacity budget "
        "and congruenceCutoff. Check that the support and congruence cutoff are fixed "
        "before the target value; reject the explanation if it swaps these quantifiers.",
    ),
    (
        "ErdosProblems.Erdos251.PaperR11.SparsePolylog.polylog_extended_rate_withQ",
        "The short polylog_extended_rate wrapper scores higher; this 50-line body "
        "contains the support-cardinality estimate beneath the uniform-rate conclusion.",
        "Check the dependence of the constant on alpha and Q and the threshold on start; "
        "then verify the separation-to-cardinality bound for every permitted L <= 2 X. "
        "Reject any uniform-in-start threshold claim not supplied by the statement.",
    ),
)


def reachable(targets, adjacency, available=()):
    """Union of reachable nodes, stopping at available declarations, cycle safe."""
    blocked, seen, stack = set(available), set(), list(targets)
    while stack:
        node = stack.pop()
        if node in seen or node in blocked:
            continue
        seen.add(node)
        stack.extend(adjacency[node])
    return seen


def workload_cost(targets, adjacency, costs, available=(), mode="union"):
    if mode == "union":
        return sum(costs[i] for i in reachable(targets, adjacency, available))
    if mode == "independent":
        return sum(closure_cost(i, adjacency, costs, available) for i in targets)
    raise ValueError(f"unknown workload mode: {mode}")


def marginal(targets, candidate, adjacency, costs, available=(), mode="union"):
    available = set(available)
    return workload_cost(targets, adjacency, costs, available, mode) - workload_cost(
        targets, adjacency, costs, available | {candidate}, mode
    )


def pair_interaction(targets, left, right, adjacency, costs, available=()):
    """Positive means complementary cuts; negative means overlapping reductions."""
    available = set(available)
    joint = workload_cost(targets, adjacency, costs, available) - workload_cost(
        targets, adjacency, costs, available | {left, right}
    )
    return joint - marginal(targets, left, adjacency, costs, available) - marginal(
        targets, right, adjacency, costs, available
    )


def sha(path):
    return "sha256:" + hashlib.sha256(Path(path).read_bytes()).hexdigest()


def breadth_check(root, rows, nodes, adjacency, costs, generated):
    """One manually chosen mapped theorem per problem; missing targets stay missing."""
    by_handle = {n["handle"]: n["node_id"] for n in nodes}
    chosen, resolved = [], []
    for problem, row_id, handle, reason in BREADTH_TARGETS:
        row = rows[row_id]
        declaration = next(d for d in row["lean"]["declarations"] if d["name"] == handle)
        item = {
            "problem": problem, "paper_row": row_id, "handle": handle,
            "selection_reason": reason, "paper_source_ref": row["source"],
            "statement_sha256": row["statement_sha256"],
            "recorded_lean_relation": row["lean"]["status"],
            "source_file": declaration["file"],
            "source_sha256": sha(root / declaration["file"]),
            "graph_resolution": "resolved" if handle in by_handle else "absent_not_substituted",
        }
        if handle in by_handle:
            i = by_handle[handle]
            resolved.append(i)
            ancestry = reachable([i], adjacency)
            item.update({
                "source_ref": nodes[i]["source_ref"],
                "indexed_subtotal": sum(costs[j] for j in ancestry),
                "omitted_internal_references": sum(
                    nodes[j]["omitted_internal_reference_count"] for j in ancestry),
            })
        chosen.append(item)
    cone = reachable(resolved, adjacency)
    candidates = [i for i in cone if i not in resolved and
                  nodes[i]["declaration_kind"] in {"theorem", "lemma"} and
                  not generated[i] and costs[i] >= 3]
    reductions = {i: marginal(resolved, i, adjacency, costs) for i in candidates}
    ranked = sorted(candidates, key=lambda i: (-reductions[i], nodes[i]["handle"]))
    return {
        "selection_contract": "One explicitly selected representative declaration for each "
                              "of eight problem papers, chosen before computing cuts. A single "
                              "declaration may cover only one clause of its paper row. This is "
                              "a breadth probe, not a complete census or a significance ranking.",
        "targets": chosen,
        "resolved_problems": [x["problem"] for x in chosen if x["graph_resolution"] == "resolved"],
        "unresolved_problems": [x["problem"] for x in chosen if x["graph_resolution"] != "resolved"],
        "boundary": "All subtotals below concern only resolved targets. Missing targets are "
                    "neither zero-cost nor silently replaced. Omitted helpers limit even "
                    "resolved targets; none of these subtotals establishes proof simplicity.",
        "baseline_union_subtotal_resolved_only": workload_cost(resolved, adjacency, costs),
        "baseline_independent_subtotal_resolved_only": workload_cost(
            resolved, adjacency, costs, mode="independent"),
        "candidate_count": len(candidates),
        "repeated_reachable_declarations_across_resolved_targets": sum(
            len(reachable([i], adjacency)) for i in resolved) - len(cone),
        "source_hashes_for_resolved_union": {
            p: sha(root / p) for p in sorted({nodes[i]["module"] for i in cone})},
        "top_initial_marginals_resolved_only": [{
            "handle": nodes[i]["handle"], "source_ref": nodes[i]["source_ref"],
            "source_sha256": sha(root / nodes[i]["module"]),
            "own_source_lines": costs[i], "marginal_union_reduction": reductions[i],
            "beneficiaries": [{"handle": nodes[t]["handle"],
                "marginal_subtotal_reduction": marginal([t], i, adjacency, costs)}
                for t in resolved if marginal([t], i, adjacency, costs) > 0],
        } for i in ranked[:10]],
    }


def build_report(root=ROOT):
    root = Path(root)
    nodes, adjacency, costs, generated = load_indexed_cost_graph(root)
    by_handle = {n["handle"]: n["node_id"] for n in nodes}
    coverage_path = root / "docs/paper_lean_coverage.json"
    coverage = json.loads(coverage_path.read_text())
    rows = {r["id"]: r for r in coverage["rows"]}
    targets, target_records = [], []
    for row_id in TARGET_ROWS:
        row = rows[row_id]
        for declaration in row["lean"]["declarations"]:
            i = by_handle[declaration["name"]]
            if nodes[i]["module"] != declaration["file"]:
                raise ValueError(f"paper source mismatch: {declaration['name']}")
            targets.append(i)
            target_records.append({
                "paper_row": row_id, "paper_source_ref": row["source"],
                "statement_sha256": row["statement_sha256"],
                "paper_source_sha256": sha(root / row["source"].rsplit(":", 1)[0]),
                "recorded_lean_relation": row["lean"]["status"],
                "handle": nodes[i]["handle"], "source_ref": nodes[i]["source_ref"],
                "source_sha256": sha(root / nodes[i]["module"]),
                "indexed_subtotal": closure_cost(i, adjacency, costs),
            })
    if len(targets) != len(set(targets)):
        raise ValueError("frozen workload repeats a declaration")
    cone = reachable(targets, adjacency)
    excluded = Counter()
    candidates = []
    for i in sorted(cone):
        reason = (
            "target_itself" if i in targets else
            "not_theorem_or_lemma" if nodes[i]["declaration_kind"] not in {"theorem", "lemma"} else
            "generated_certificate" if generated[i] else
            "body_under_three_source_lines" if costs[i] < 3 else None
        )
        if reason:
            excluded[reason] += 1
        else:
            candidates.append(i)
    direct_users = [set() for _ in nodes]
    for i, deps in enumerate(adjacency):
        for dep in deps:
            direct_users[dep].add(i)
    expanded = {i: closure_cost(i, adjacency, costs) for i in candidates}
    single = {i: marginal(targets, i, adjacency, costs) for i in candidates}
    independent = {
        i: marginal(targets, i, adjacency, costs, mode="independent") for i in candidates
    }
    by_score = sorted(candidates, key=lambda i: (-single[i], nodes[i]["handle"]))
    by_utility = sorted(candidates, key=lambda i: (
        -len(direct_users[i]) * expanded[i], nodes[i]["handle"]
    ))
    utility_rank = {i: rank for rank, i in enumerate(by_utility, 1)}

    def record(i, available=()):
        available = set(available)
        beneficiaries = [
            {"handle": nodes[t]["handle"],
             "marginal_subtotal_reduction": marginal([t], i, adjacency, costs, available)}
            for t in targets if marginal([t], i, adjacency, costs, available) > 0
        ]
        return {
            "handle": nodes[i]["handle"], "source_ref": nodes[i]["source_ref"],
            "source_sha256": sha(root / nodes[i]["module"]),
            "own_source_lines": costs[i], "indexed_subtotal": expanded[i],
            "direct_users": len(direct_users[i]),
            "direct_use_times_subtotal": len(direct_users[i]) * expanded[i],
            "direct_use_times_subtotal_rank_in_same_pool": utility_rank[i],
            "marginal_union_reduction": marginal(targets, i, adjacency, costs, available),
            "marginal_independent_reduction": marginal(
                targets, i, adjacency, costs, available, "independent"
            ),
            "beneficiaries": beneficiaries,
            "next_falsifiable_review_action": (
                f"Read {nodes[i]['source_ref']} and its stated hypotheses; then inspect the "
                "listed beneficiary proof paths. Reject this review priority if the removed "
                "indexed body is routine, omitted helpers carry the argument, or the lemma "
                "cannot be explained independently. A cut alone establishes no time saving."
            ),
        }

    available, greedy = set(), []
    for step in range(min(SHORTLIST_SIZE, len(candidates))):
        remaining = [i for i in candidates if i not in available]
        best = min(remaining, key=lambda i: (
            -marginal(targets, i, adjacency, costs, available), nodes[i]["handle"]
        ))
        if marginal(targets, best, adjacency, costs, available) == 0:
            break
        entry = record(best, available)
        entry["step"] = step + 1
        entry["available_before"] = sorted(nodes[i]["handle"] for i in available)
        entry["baseline_single_reduction"] = single[best]
        available.add(best)
        entry["remaining_union_subtotal"] = workload_cost(targets, adjacency, costs, available)
        greedy.append(entry)
    pair_pool = by_score[:PAIR_POOL_SIZE]
    pairs = []
    for left, right in itertools.combinations(pair_pool, 2):
        interaction = pair_interaction(targets, left, right, adjacency, costs)
        if interaction > 0:
            pairs.append({
                "handles": [nodes[left]["handle"], nodes[right]["handle"]],
                "source_refs": [nodes[left]["source_ref"], nodes[right]["source_ref"]],
                "source_sha256": [sha(root / nodes[left]["module"]),
                                  sha(root / nodes[right]["module"])],
                "single_reductions": [single[left], single[right]],
                "joint_union_reduction": single[left] + single[right] + interaction,
                "complementarity": interaction,
            })
    pairs.sort(key=lambda p: (-p["complementarity"], p["handles"]))
    source_paths = sorted({nodes[i]["module"] for i in cone})
    return {
        "schema": "indexed-conditional-reuse/1",
        "source": "https://arxiv.org/abs/2609.28603",
        "question": "Which existing inspectable lemma proofs can be treated as available "
                    "to reduce the indexed proof-source subtotal of this frozen workload?",
        "context": {
            "initial_available_indexed_declarations": [],
            "external_dependencies": "mathlib and other unindexed declarations are uncosted",
            "cost_unit": "nonempty source proof lines from the shared declaration-span parser",
            "union": "Count each reachable indexed declaration once across all eight targets; "
                     "stop traversing when an available declaration is reached.",
            "independent": "Sum eight separately checked target closures; shared prerequisites "
                           "may be charged once per target but never twice within one target.",
            "selection": "Greedy marginal union reduction, recalculated after every cut; no "
                         "optimality guarantee. Complementary cuts violate diminishing returns.",
            "candidate_screen": "Reachable indexed theorem/lemma, not a target, not atlas-tagged "
                                "generated, at least three own proof-source lines. The body-length "
                                "screen is explicit and does not judge short lemmas unimportant.",
            "boundary": "No shortest-proof, novelty, significance, learned predictor, review-time, "
                        "or prospective allocation claim. Private helpers and unresolved edges "
                        "are absent; source spans are heuristic. Availability is a hypothetical "
                        "inspection context, not new mathematical reuse.",
            "validation": "The Python graph calculation is replayed; no Lean kernel or "
                          "Comparator replay is run by this analysis.",
        },
        "provenance": {
            "dependency_index_sha256": sha(root / "docs/lean_dependency_index.json"),
            "declaration_atlas_sha256": sha(root / "docs/declaration_atlas.json"),
            "paper_coverage_sha256": sha(coverage_path),
            "lean_sources_sha256": {p: sha(root / p) for p in source_paths},
            "implementation_sha256": sha(Path(__file__)),
            "shared_cost_implementation_sha256": sha(Path(__file__).with_name("run.py")),
        },
        "targets": target_records,
        "summary": {
            "target_declarations": len(targets), "paper_rows": len(TARGET_ROWS),
            "target_modules": len({nodes[i]["module"] for i in targets}),
            "reachable_declarations": len(cone), "candidate_count": len(candidates),
            "excluded_by_first_matching_rule": dict(sorted(excluded.items())),
            "baseline_union_subtotal": workload_cost(targets, adjacency, costs),
            "baseline_independent_subtotal": workload_cost(targets, adjacency, costs, mode="independent"),
            "omitted_internal_references_in_union": sum(
                nodes[i]["omitted_internal_reference_count"] for i in cone
            ),
            "greedy_final_union_subtotal": workload_cost(targets, adjacency, costs, available),
        },
        "top_initial_marginals": [record(i) for i in by_score[:10]],
        "direct_use_times_subtotal_comparator_same_pool": [record(i) for i in by_utility[:10]],
        "greedy_shortlist": greedy,
        "authored_review_dispatch": {
            "status": "source bodies inspected; proposed next review actions remain unperformed",
            "decision": "Inspect mechanisms in the three declarations below. Do not treat the "
                        "largest cut as mathematical importance: the first greedy winner only "
                        "transports an existing irrationality equivalence, and two other "
                        "winners are three-line wrappers. Prefer the named mechanism bodies "
                        "when allocating explanation effort; no observed review benefit is claimed.",
            "selected": [
                {**record(by_handle[handle]), "reason_after_source_read": reason,
                 "next_falsifiable_review_action": action}
                for handle, reason, action in REVIEW_CHOICES
            ],
            "companion_comparison": "profile.json reports the unrestricted corpus users-times-"
                                    "subtotal ranking and generated ancestry. The comparator here "
                                    "uses the identical screened workload pool so that differences "
                                    "are attributable to the objective, not different candidates.",
        },
        "bounded_pair_probe": {
            "pool_rule": f"Top {PAIR_POOL_SIZE} baseline union marginals, ties by handle",
            "pool_handles": [nodes[i]["handle"] for i in pair_pool],
            "pairs_tested": len(pair_pool) * (len(pair_pool) - 1) // 2,
            "positive_complementarity_pairs": len(pairs),
            "top_complementary_pairs": pairs[:5],
            "boundary": "A bounded interaction probe, not exhaustive pair optimisation.",
        },
        "eight_problem_breadth_check": breadth_check(root, rows, nodes, adjacency, costs, generated),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    text = json.dumps(build_report(), indent=2, ensure_ascii=False) + "\n"
    if args.check:
        if args.output.read_text() != text:
            raise SystemExit("conditional reuse report differs; regenerate it")
        print("conditional reuse report is current")
    else:
        args.output.write_text(text)
        print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
