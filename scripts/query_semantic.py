#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Answer the standing questions about the corpus from the semantic graph.

``query_corpus.py`` routes a reader to one claim, declaration or paper anchor.
It cannot answer questions *about the shape of the corpus* -- what is a result
rather than a reformulation, which barrier leaves which engine alive, what a
paper actually covers -- because until the semantic graph existed there was no
surface that knew.  Those questions were previously answered by reading, which
is how a barrier came to be described as closing a family of engines when a
weaker sibling engine in the same file survived it.

Each subcommand is one of those questions, and each is a query rather than a
maintained prose list, so it cannot fall out of date the way a written census
does.

    python3 scripts/query_semantic.py nonrecurring --problem 257
    python3 scripts/query_semantic.py bare-equivalences
    python3 scripts/query_semantic.py finite-instances
    python3 scripts/query_semantic.py classical
    python3 scripts/query_semantic.py engines
    python3 scripts/query_semantic.py barriers
    python3 scripts/query_semantic.py open-antecedents
    python3 scripts/query_semantic.py expert-questions
    python3 scripts/query_semantic.py expert-questions XQ249-pivot-decorrelation
    python3 scripts/query_semantic.py prior-art-review
    python3 scripts/query_semantic.py coverage
    python3 scripts/query_semantic.py semantic-reviews
    python3 scripts/query_semantic.py inventory
    python3 scripts/query_semantic.py inventory selectedMersenneTail_lt_weight
    python3 scripts/query_semantic.py inventory --module ErdosProblems/Erdos257
    python3 scripts/query_semantic.py paper-coverage
    python3 scripts/query_semantic.py population-backlog
    python3 scripts/query_semantic.py population-backlog --paper erdos249-totient-reasoning-surface
    python3 scripts/query_semantic.py motifs
    python3 scripts/query_semantic.py node <node_id>

The routes below read the theory-lab layer, which sits above the graph and holds
the mechanisms, the typed interventions performed on them, and the blinded
evaluations that test whether the explanations transfer.

    python3 scripts/query_semantic.py mechanisms --problem 257
    python3 scripts/query_semantic.py mechanism <mechanism_id>
    python3 scripts/query_semantic.py explains <node_id>
    python3 scripts/query_semantic.py unexplained
    python3 scripts/query_semantic.py interventions
    python3 scripts/query_semantic.py discrepancies
    python3 scripts/query_semantic.py receipts
    python3 scripts/query_semantic.py benchmark
"""

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict
from pathlib import Path

from build_semantic_corpus import semantic_input_fingerprint

ROOT = Path(__file__).resolve().parent.parent
CORPUS = ROOT / "docs" / "semantic_corpus.json"
CONTRACT = ROOT / "docs" / "publication_contract.json"
LAB = ROOT / "docs" / "theory_lab.json"

BUDGET = 64 * 1024


def load() -> dict:
    if not CORPUS.is_file():
        raise SystemExit(
            "docs/semantic_corpus.json missing; run python3 scripts/build_semantic_corpus.py"
        )
    corpus = json.loads(CORPUS.read_text(encoding="utf-8"))
    if corpus.get("semantic_input_fingerprint") != semantic_input_fingerprint():
        raise SystemExit(
            "docs/semantic_corpus.json is stale relative to its inputs; "
            "run python3 scripts/build_semantic_corpus.py"
        )
    return corpus


def emit(payload: object) -> int:
    text = json.dumps(payload, indent=1, ensure_ascii=False)
    if len(text) > BUDGET:
        text = json.dumps(
            {
                "truncated": True,
                "budget_bytes": BUDGET,
                "hint": "narrow with --problem or --limit",
                "head": json.loads(text[: BUDGET // 2] + "]}")
                if False
                else "response exceeded the 64 KB packet budget",
            },
            indent=1,
        )
    print(text)
    return 0


def nodes_by_id(corpus: dict) -> dict[str, dict]:
    return {n["id"]: n for n in corpus["statement_nodes"]}


def compact(node: dict) -> dict:
    return {
        "id": node["id"],
        "problem": node.get("problem"),
        "class": node.get("logical_class"),
        "statement": node.get("canonical_statement"),
        "prior_art": node.get("prior_art_state"),
        "evidence": [
            f"{e.get('module')}:{e.get('line')}:{e.get('declaration')}"
            for e in node.get("evidence", [])[:4]
        ],
        "scope_caveat": node.get("scope_caveat") or None,
        "confidence": node.get("confidence"),
    }


def filtered(corpus: dict, problem: str | None) -> list[dict]:
    out = []
    for node in corpus["statement_nodes"]:
        if problem and node.get("problem") not in (problem, "both"):
            continue
        out.append(node)
    return out


def cmd_nonrecurring(corpus: dict, args) -> int:
    ids = set(corpus["views"]["nonrecurring"]["nodes"])
    rows = [compact(n) for n in filtered(corpus, args.problem) if n["id"] in ids]
    return emit(
        {
            "question": (
                "mechanically filtered nonrecurring candidates within the "
                "selected statement graph"
            ),
            "problem": args.problem or "all",
            "rule": corpus["views"]["nonrecurring"]["rule"],
            "count": len(rows),
            "selection_ceiling": (
                "This is not a census of all Lean results and not an adjudicated "
                "novelty set. Use reviewed_shortlist and complete prior-art review "
                "before public result or novelty language."
            ),
            "candidates": rows[: args.limit],
            "reviewed_shortlist": corpus["views"]["nonrecurring"].get(
                "reviewed_shortlist", []
            ),
        }
    )


def cmd_bare_equivalences(corpus: dict, args) -> int:
    rows = [
        compact(n)
        for n in filtered(corpus, args.problem)
        if n.get("logical_class") == "equivalence_or_classification"
        and n.get("is_restatement_of_open_problem")
    ]
    return emit(
        {
            "question": "exact equivalences whose unresolved side is still the original difficulty",
            "count": len(rows),
            "results": rows[: args.limit],
        }
    )


def cmd_finite_instances(corpus: dict, args) -> int:
    edges = [
        e
        for e in corpus["relations"]
        if e.get("relation") == "finite_instance_of" and not e.get("suppressed_in_views")
    ]
    index = nodes_by_id(corpus)
    rows = [
        {
            "instance": e["from"],
            "instantiates": e["to"],
            "family_statement": (index.get(e["to"]) or {}).get("canonical_statement"),
            "basis": e.get("basis"),
        }
        for e in edges
    ]
    orphan = [
        compact(n)
        for n in corpus["statement_nodes"]
        if n.get("logical_class") == "finite_instance"
        and not any(e["from"] == n["id"] for e in edges)
    ]
    return emit(
        {
            "question": "every finite result and the infinite family it instantiates",
            "attached": rows[: args.limit],
            "finite_results_with_no_extrapolation_theorem": orphan[: args.limit],
            "generated_families": [
                {
                    "id": f["id"],
                    "declarations": f["declaration_count"],
                    "template": f["template_statement"],
                }
                for f in corpus["generated_families"]
            ],
        }
    )


def cmd_classical(corpus: dict, args) -> int:
    rows = [
        {**compact(n), "prior_art_note": n.get("prior_art_note")}
        for n in filtered(corpus, args.problem)
        if n.get("logical_class") == "classical_formalised"
        or n.get("prior_art_state") in ("known_classical", "prior_art_found")
    ]
    return emit(
        {
            "question": "every classical theorem merely re-formalised here",
            "count": len(rows),
            "results": rows[: args.limit],
        }
    )


def cmd_engines(corpus: dict, args) -> int:
    engines: dict[str, dict] = defaultdict(lambda: {"nodes": [], "concepts": set()})
    for node in filtered(corpus, args.problem):
        engine = node.get("engine")
        if not engine:
            continue
        engines[engine]["nodes"].append(node["id"])
        engines[engine]["concepts"].update(node.get("concepts", []))
    rows = [
        {"engine": k, "reaches": sorted(v["concepts"]), "nodes": v["nodes"][:12]}
        for k, v in sorted(engines.items())
    ]
    return emit(
        {
            "question": (
                "free-text mechanism labels authored on selected statement nodes"
            ),
            "measurement_contract": (
                "These labels are descriptive and not a normalized engine "
                "vocabulary. The separately authored engine_hierarchy contains "
                "the small curated family-level view."
            ),
            "count": len(rows),
            "node_authored_mechanism_labels": rows[: args.limit],
            "curated_engine_hierarchy": corpus.get("frontier", {}).get(
                "engine_hierarchy", []
            ),
        }
    )


def cmd_barriers(corpus: dict, args) -> int:
    index = nodes_by_id(corpus)
    blocked = defaultdict(list)
    for e in corpus["relations"]:
        if e.get("relation") == "barrier_for":
            blocked[e["from"]].append(e["to"])
    rows = []
    for node in filtered(corpus, args.problem):
        if node.get("logical_class") != "barrier_no_go":
            continue
        rows.append(
            {
                **compact(node),
                "blocks": [
                    {"node": t, "statement": (index.get(t) or {}).get("canonical_statement")}
                    for t in blocked.get(node["id"], [])
                ],
                "does_not_rule_out": node.get("scope_caveat"),
            }
        )
    return emit(
        {
            "question": (
                "selected barrier nodes, their structured targets where authored, "
                "and their prose scope caveats"
            ),
            "measurement_contract": (
                "A barrier_for edge is structured reach. A nonempty prose caveat "
                "is not an exhaustive sibling-engine contract."
            ),
            "count": len(rows),
            "with_structured_barrier_targets": sum(
                1 for row in rows if row["blocks"]
            ),
            "without_structured_barrier_targets": sum(
                1 for row in rows if not row["blocks"]
            ),
            "results": rows[: args.limit],
        }
    )


def cmd_open_antecedents(corpus: dict, args) -> int:
    frontier = corpus.get("frontier", {}).get("open_antecedents", [])
    if frontier:
        raw_mentions = [
            antecedent
            for node in filtered(corpus, args.problem)
            for antecedent in node.get("open_antecedents", [])
        ]
        return emit(
            {
                "question": (
                    "curated open-antecedent clusters with their closest recorded "
                    "producer"
                ),
                "measurement_contract": (
                    "The clusters are authored and selective. Node antecedents are "
                    "still free text, so this is not an exhaustive normalization of "
                    "every antecedent mention."
                ),
                "curated_cluster_count": len(frontier),
                "raw_antecedent_mentions_in_selected_nodes": len(raw_mentions),
                "distinct_raw_antecedent_strings": len(set(raw_mentions)),
                "results": frontier[: args.limit],
            }
        )
    rows = []
    for node in filtered(corpus, args.problem):
        for antecedent in node.get("open_antecedents", []):
            rows.append({"node": node["id"], "antecedent": antecedent, "problem": node.get("problem")})
    return emit(
        {
            "question": "raw open-antecedent mentions in selected statement nodes",
            "count": len(rows),
            "results": rows[: args.limit],
        }
    )


def cmd_expert_questions(corpus: dict, args) -> int:
    """Exact open inputs with checked consumers and falsifiable working guesses."""
    frontier = corpus.get("frontier", {})
    rows = frontier.get("expert_questions", [])
    if args.problem:
        rows = [row for row in rows if row.get("problem") == args.problem]
    if args.node_id:
        rows = [row for row in rows if row.get("id") == args.node_id]
        if not rows:
            return emit(
                {
                    "error": f"no expert question {args.node_id!r}",
                    "hint": "run expert-questions without an id to list the available questions",
                }
            )
        result_rows = rows
        packet_kind = "full_question"
    else:
        result_rows = [
            {
                "id": row["id"],
                "problem": row["problem"],
                "classification": row["classification"],
                "status": row["status"],
                "exact_ask": row["exact_ask"],
                "boundary": row["boundary"],
                "current_hypothesis": row["current_hypothesis"],
                "hypothesis_confidence": row["hypothesis_confidence"],
                "plausible_alternatives": [
                    {
                        "id": alternative["id"],
                        "statement": alternative["statement"],
                    }
                    for alternative in row["plausible_alternatives"]
                ],
                "current_evidence": row["current_evidence"],
                "discriminating_evidence": row["discriminating_evidence"],
                "checked_consumers": [
                    (
                        f"{consumer['module']}:{consumer['line']}:"
                        f"{consumer['declaration']}"
                    )
                    for consumer in row["consumer_declarations"]
                ],
                "detail_command": (
                    "python3 scripts/query_semantic.py expert-questions "
                    f"{row['id']}"
                ),
            }
            for row in rows[: args.limit]
        ]
        packet_kind = "compact_index"
    return emit(
        {
            "question": "exact mathematical inputs requested from a human expert",
            "rule": (
                "Every row names its closure scope, checked consumer, boundary, "
                "current low-confidence answer, plausible alternatives and the "
                "evidence that would distinguish them."
            ),
            "packet_kind": packet_kind,
            "count": len(rows),
            "classification_legend": {
                "endpoint_equivalent": "the ask is exactly as hard as the endpoint",
                "sufficient_for_erdos_249": "a positive answer proves Erdős #249",
                "sufficient_for_counterexample": (
                    "a positive answer refutes universal Erdős #257 by producing "
                    "an infinite-support rational value"
                ),
            },
            "limits": frontier.get("expert_question_limits", []),
            "results": result_rows,
        }
    )


def cmd_prior_art_review(corpus: dict, args) -> int:
    rows = [
        compact(n)
        for n in filtered(corpus, args.problem)
        if n.get("prior_art_state") in ("candidate_new_statement", "external_review_pending")
    ]
    return emit(
        {
            "question": "candidate results requiring public prior-art review before any novelty language",
            "rule": "prior-art state is never inferred from Lean; it is a staged editorial judgement",
            "count": len(rows),
            "results": rows[: args.limit],
        }
    )


def paper_citation_keys(module: str, declaration: str) -> set[tuple[str, str]]:
    """Return symmetric module and declaration aliases used by papers.

    Authored roles retain qualified declaration names so their evidence is
    unambiguous.  Manuscript links normally use the declaration spelling at the
    cited source line.  Match both without weakening the module coordinate: a
    short declaration name is never resolved repo-wide.
    """
    module_aliases = {module, Path(module).name}
    parts = Path(module).parts
    if parts and parts[0] in ("ErdosProblems", "Erdos249257"):
        module_aliases.add("/".join(parts[1:]))
    declaration_aliases = {declaration, declaration.rsplit(".", 1)[-1]}
    return {
        (module_alias, declaration_alias)
        for module_alias in module_aliases
        for declaration_alias in declaration_aliases
    }


def paper_citation_role_index(
    corpus: dict,
) -> dict[tuple[str, str], list[dict]]:
    index: dict[tuple[str, str], list[dict]] = defaultdict(list)
    for role in corpus["declaration_roles"]:
        module = role.get("module")
        declaration = role.get("declaration")
        if not module or not declaration:
            continue
        for key in paper_citation_keys(module, declaration):
            index[key].append(role)
    return index


def paper_lean_citations(text: str) -> set[tuple[str, int, str]]:
    """Extract both public-paper source links and reasoning-surface Lean links."""
    public_link_re = re.compile(
        r"\\[lm](?:word|ref|refx|loc)\{([^{}]+)\}\{(\d+)\}(?:\{([^{}]+)\})?"
    )
    reasoning_link_re = re.compile(r"\\lean\{([^{}]+)\}\{([^{}]+)\}")
    citations = {
        (match.group(1), int(match.group(2)), match.group(3))
        for match in public_link_re.finditer(text)
        if match.group(3)
    }
    for match in reasoning_link_re.finditer(text):
        declaration = match.group(1).replace(r"\_", "_")
        locator = match.group(2)
        locator_match = re.match(r"(.+?\.lean):(\d+)", locator)
        if locator_match:
            citations.add(
                (
                    locator_match.group(1),
                    int(locator_match.group(2)),
                    declaration,
                )
            )
    return citations


def cmd_paper_coverage(corpus: dict, args) -> int:
    """Which statement nodes are reached by explicit Lean citations in each manuscript?"""
    contract = json.loads(CONTRACT.read_text(encoding="utf-8"))
    index = nodes_by_id(corpus)

    # The declaration role receipt, not a node's short evidence list, owns the
    # exhaustive citation route.  An earlier version used evidence lists and
    # consequently labelled node-routed citations "unmatched" whenever an
    # author had not repeated every supporting declaration on the node.
    declaration_routes: dict[tuple[str, str], set[str]] = defaultdict(set)
    known_declarations: set[tuple[str, str]] = set()
    for role in corpus["declaration_roles"]:
        module = role.get("module")
        declaration = role.get("declaration")
        if not module or not declaration:
            continue
        for key in paper_citation_keys(module, declaration):
            known_declarations.add(key)
            if role.get("statement_node"):
                declaration_routes[key].add(role["statement_node"])

    rows = []
    for artifact in contract.get("artifacts", []):
        source = ROOT / artifact["source_path"]
        if not source.is_file():
            continue
        text = source.read_text(encoding="utf-8")
        cited = {
            (module, declaration)
            for module, _, declaration in paper_lean_citations(text)
        }
        def routed_nodes(citation: tuple[str, str]) -> set[str]:
            return set().union(
                *(
                    declaration_routes.get(key, set())
                    for key in paper_citation_keys(*citation)
                )
            )

        def known_citation(citation: tuple[str, str]) -> bool:
            return any(
                key in known_declarations
                for key in paper_citation_keys(*citation)
            )

        reached: set[str] = set()
        for citation in cited:
            reached.update(routed_nodes(citation))
        node_routed = sorted(
            f"{module}:{declaration}"
            for module, declaration in cited
            if routed_nodes((module, declaration))
        )
        zone_only = sorted(
            f"{module}:{declaration}"
            for module, declaration in cited
            if known_citation((module, declaration))
            and not routed_nodes((module, declaration))
        )
        absent = sorted(
            f"{module}:{declaration}"
            for module, declaration in cited
            if not known_citation((module, declaration))
        )
        per_problem = {}
        for problem in ("249", "257", "both", "shared_substrate"):
            total = sum(1 for n in corpus["statement_nodes"] if n.get("problem") == problem)
            hit = sum(1 for nid in reached if (index.get(nid) or {}).get("problem") == problem)
            if total:
                per_problem[problem] = {
                    "nodes_reached": hit,
                    "nodes_total": total,
                    "explicit_citation_reach_fraction": round(hit / total, 4),
                }
        rows.append(
            {
                "artifact": artifact["id"],
                "source": artifact["source_path"],
                "declarations_cited": len(cited),
                "statement_nodes_reached": len(reached),
                "node_routed_declaration_citations": len(node_routed),
                "node_routed_citations_total": len(node_routed),
                "node_routed_citations": node_routed[: args.limit],
                "zone_only_declaration_citations_total": len(zone_only),
                "zone_only_declaration_citations": zone_only[: args.limit],
                "atlas_absent_declaration_citations_total": len(absent),
                "atlas_absent_declaration_citations": absent[: args.limit],
                "per_problem": per_problem,
            }
        )
    return emit(
        {
            "question": (
                "which authored statement nodes are reached by explicit "
                "module-and-declaration citations in each manuscript"
            ),
            "measurement_contract": (
                "This is citation reach, not explanatory or semantic completeness. "
                "Prose can explain a statement without an explicit Lean citation, and "
                "a citation can occur without explaining the statement."
            ),
            "results": rows,
        }
    )


def cmd_population_backlog(corpus: dict, args) -> int:
    """Rank paper-selected Lean citations that still lack statement semantics."""
    role_index = paper_citation_role_index(corpus)
    candidate_cap = min(args.limit, 12 if args.paper else 5)
    module_cap = min(args.limit, 12 if args.paper else 8)
    paper_cap = min(args.limit, 1 if args.paper else 3)
    source_rows = []
    sources = sorted((ROOT / "paper").glob("*.tex"))
    if args.paper:
        needle = args.paper.casefold()
        sources = [
            source
            for source in sources
            if needle in source.name.casefold()
            or needle in str(source.relative_to(ROOT)).casefold()
        ]
    for source in sources:
        text = source.read_text(encoding="utf-8")
        citations = sorted(paper_lean_citations(text))
        linked_by_role: dict[str, dict] = {}
        unlinked_by_role: dict[str, dict] = {}
        absent = []
        for module, line, declaration in citations:
            roles_by_id = {
                role["id"]: role
                for key in paper_citation_keys(module, declaration)
                for role in role_index.get(key, [])
            }
            roles = list(roles_by_id.values())
            occurrence = {
                "paper_module": module,
                "paper_line": line,
                "paper_declaration": declaration,
            }
            if not roles:
                absent.append({**occurrence, "resolved_role_ids": []})
                continue
            for role in roles:
                target = (
                    linked_by_role
                    if role.get("statement_node")
                    else unlinked_by_role
                )
                row = target.setdefault(
                    role["id"],
                    {
                        "role_id": role["id"],
                        "module": role["module"],
                        "declaration": role["declaration"],
                        "semantic_zone": role.get("zone"),
                        "statement_node": role.get("statement_node"),
                        "paper_occurrences": [],
                    },
                )
                row["paper_occurrences"].append(occurrence)
        if not citations:
            continue
        # A declaration resolved through both qualified and short aliases is one
        # backlog item.  If any exact role already carries statement semantics,
        # do not also offer an unlinked alias for population.
        for role_id in linked_by_role:
            unlinked_by_role.pop(role_id, None)
        linked = list(linked_by_role.values())
        unlinked = list(unlinked_by_role.values())
        by_module: dict[str, list[dict]] = defaultdict(list)
        for row in unlinked:
            by_module[row["module"]].append(row)
        source_rows.append(
            {
                "paper": str(source.relative_to(ROOT)),
                "raw_citation_count": len(citations),
                "statement_linked_declaration_count": len(linked),
                "statement_unlinked_live_declaration_count": len(unlinked),
                "atlas_absent_citation_count": len(absent),
                "unlinked_module_groups": [
                    {
                        "module": module,
                        "declaration_count": len(rows),
                        "candidates": rows[:candidate_cap],
                    }
                    for module, rows in sorted(
                        by_module.items(),
                        key=lambda item: (-len(item[1]), item[0]),
                    )
                ][:module_cap],
                "atlas_absent_citations": absent[:candidate_cap],
            }
        )
    source_rows.sort(
        key=lambda row: (
            -row["statement_unlinked_live_declaration_count"],
            row["paper"],
        )
    )
    return emit(
        {
            "question": (
                "Which exact live Lean declarations were selected by authored "
                "papers but still lack proposition-level semantic linkage?"
            ),
            "selection_rule": (
                "Papers nominate high-value targets; exact module/declaration "
                "resolution supplies the backlog. Repeated helpers and generated "
                "leaves are not promoted merely to increase a percentage."
            ),
            "authority_posture": (
                "paper_seeded_population_priority_not_Lean_proof_authority_or_"
                "automatic_statement_interpretation"
            ),
            "paper_filter": args.paper,
            "paper_count": len(source_rows),
            "statement_unlinked_live_declaration_count": sum(
                row["statement_unlinked_live_declaration_count"]
                for row in source_rows
            ),
            "papers": source_rows[:paper_cap],
            "papers_omitted": max(0, len(source_rows) - paper_cap),
            "next_action": (
                "Cluster one paper/module family by mathematically distinct "
                "proposition, inspect exact signatures and proof cones, then author "
                "a bounded zone packet with typed relations and explicit nonclaims."
            ),
        }
    )


def cmd_coverage(corpus: dict, args) -> int:
    """Report the coverage tiers without collapsing them into one percentage."""
    summary = corpus["summary"]
    coverage = summary["coverage"]
    return emit(
        {
            "question": "What kind of coverage does the semantic corpus actually establish?",
            "posture": corpus.get("coverage_contract", {}).get("posture"),
            "anti_filler_rule": corpus.get("coverage_contract", {}).get(
                "anti_filler"
            ),
            "tiers": {
                "inventory": {
                    "declarations": summary["declarations"],
                    "authority": "docs/declaration_atlas.json",
                },
                "typed_routing": {
                    "live_declarations_routed": coverage["declarations_owned"],
                    "orphan_declarations": coverage["orphan_count"],
                    "automatic_inventory_fallback_declarations": coverage[
                        "automatic_inventory_fallback_count"
                    ],
                    "duplicate_role_assignments": coverage[
                        "duplicate_role_assignment_count"
                    ],
                    "claim": (
                        "Every live declaration has one role-and-zone route or "
                        "one generated-family route."
                    ),
                },
                "statement_level_interpretation": {
                    "statement_nodes_including_generated_families": summary[
                        "statement_nodes"
                    ],
                    "authored_statement_nodes": summary[
                        "authored_statement_nodes"
                    ],
                    "authored_theorem_like_declarations": summary[
                        "authored_theorem_like"
                    ],
                    "authored_theorem_like_node_linked": coverage[
                        "authored_theorem_like_node_linked"
                    ],
                    "authored_theorem_like_direct_evidence": coverage[
                        "authored_theorem_like_direct_evidence"
                    ],
                    "authored_theorem_like_contextual_node_links": coverage[
                        "authored_theorem_like_contextual_node_links"
                    ],
                    "authored_theorem_like_zone_only": coverage[
                        "authored_theorem_like_zone_only"
                    ],
                    "node_linked_fraction": coverage[
                        "authored_theorem_like_node_linked_fraction"
                    ],
                    "claim": (
                        "Only node-linked declarations participate in an authored "
                        "canonical mathematical statement. Direct evidence anchors "
                        "are counted separately so bulk contextual helper links "
                        "cannot masquerade as new statement evidence."
                    ),
                },
                "typed_relations": {
                    "relations": summary["relations"],
                    "claim": (
                        "Every retained relation has a typed label, live endpoints, "
                        "and an authored evidence basis."
                    ),
                },
                "reviewed_semantic_fidelity": {
                    "status": (
                        "not_measured"
                        if not coverage[
                            "statement_nodes_with_semantic_review_receipt"
                        ]
                        and not coverage[
                            "relations_with_semantic_review_receipt"
                        ]
                        else "partial"
                    ),
                    "statement_node_receipts": coverage[
                        "statement_nodes_with_semantic_review_receipt"
                    ],
                    "relation_receipts": coverage[
                        "relations_with_semantic_review_receipt"
                    ],
                    "readme_headline_claims": coverage[
                        "readme_headline_claims"
                    ],
                    "readme_headline_claims_with_reviewed_node": coverage[
                        "readme_headline_claims_with_reviewed_node"
                    ],
                    "headline_coverage_ceiling": (
                        "A headline family is counted when at least one linked "
                        "statement node has a current receipt; this does not mean "
                        "every supporting declaration or every sentence was reviewed."
                    ),
                    "claim": corpus.get("coverage_contract", {}).get(
                        "reviewed_semantic_fidelity"
                    ),
                },
                "curated_public_claims": {
                    "declarations": coverage["curated_claim_declarations"],
                    "without_statement_node": coverage[
                        "curated_claim_declarations_without_node"
                    ],
                },
            },
            "not_established": corpus.get("coverage_contract", {}).get(
                "accuracy_boundary"
            ),
        }
    )


def cmd_semantic_reviews(corpus: dict, args) -> int:
    """List the exact semantic subjects carrying digest-bound review."""
    reviewed_nodes = []
    for node in filtered(corpus, args.problem):
        receipt = node.get("semantic_review")
        if not receipt:
            continue
        reviewed_nodes.append(
            {
                "subject_kind": "statement_node",
                "subject_id": node["id"],
                "problem": node.get("problem"),
                "class": node.get("logical_class"),
                "statement": node.get("canonical_statement"),
                "review": receipt,
            }
        )

    index = nodes_by_id(corpus)
    reviewed_relations = []
    for edge in corpus.get("relations", []):
        receipt = edge.get("semantic_review")
        if not receipt or edge.get("suppressed_in_views"):
            continue
        edge_problem = (index.get(edge.get("from")) or {}).get("problem")
        if args.problem and edge_problem not in (args.problem, "both"):
            continue
        reviewed_relations.append(
            {
                "subject_kind": "relation",
                "subject_id": (
                    f"{edge.get('from')}|{edge.get('relation')}|{edge.get('to')}"
                ),
                "from": edge.get("from"),
                "relation": edge.get("relation"),
                "to": edge.get("to"),
                "basis": edge.get("basis"),
                "review": receipt,
            }
        )

    rows = [*reviewed_nodes, *reviewed_relations]
    if args.node_id:
        rows = [
            row
            for row in rows
            if args.node_id.casefold() in row["subject_id"].casefold()
        ]
    return emit(
        {
            "question": "Which authored semantic subjects have digest-bound review?",
            "authority_posture": (
                "reviewed_navigation_meaning_with_per_receipt_claim_ceiling_"
                "not_Lean_proof_authority"
            ),
            "coverage": {
                "reviewed_statement_nodes": len(reviewed_nodes),
                "all_statement_nodes": len(corpus.get("statement_nodes", [])),
                "reviewed_relations": len(reviewed_relations),
                "all_relations": sum(
                    1
                    for edge in corpus.get("relations", [])
                    if not edge.get("suppressed_in_views")
                ),
                "readme_headline_claims": corpus.get("summary", {})
                .get("coverage", {})
                .get("readme_headline_claims"),
                "readme_headline_claims_with_reviewed_node": corpus.get(
                    "summary", {}
                )
                .get("coverage", {})
                .get("readme_headline_claims_with_reviewed_node"),
                "headline_coverage_ceiling": (
                    "At least one linked node per headline family, not exhaustive "
                    "review of its declarations or prose."
                ),
            },
            "selection": args.node_id or "all reviewed subjects",
            "results": rows[: args.limit],
            "next": (
                "Use `node <id>` for its complete semantic neighborhood and "
                "`semantic_review.py --check` for receipt freshness."
            ),
        }
    )


def cmd_inventory(corpus: dict, args) -> int:
    """Search the exhaustive declaration routes without inferring mathematics."""
    needle = (args.node_id or "").casefold()
    module_filter = (args.module or "").casefold()
    role_filter = (args.role or "").casefold()
    zone_filter = (args.zone or "").casefold()

    matches = []
    for route in corpus["declaration_roles"]:
        searchable = " ".join(
            str(route.get(field) or "")
            for field in ("id", "module", "declaration", "statement_node")
        ).casefold()
        if needle and needle not in searchable:
            continue
        if module_filter and module_filter not in str(route.get("module") or "").casefold():
            continue
        if role_filter and role_filter != str(route.get("role") or "").casefold():
            continue
        if zone_filter and zone_filter != str(route.get("zone") or "").casefold():
            continue
        matches.append(
            {
                "id": route["id"],
                "module": route.get("module"),
                "declaration": route.get("declaration"),
                "role": route.get("role"),
                "zone": route.get("zone"),
                "statement_node": route.get("statement_node"),
                "routing_origin": route.get("routing_origin", "authored"),
            }
        )

    return emit(
        {
            "question": "Which live Lean declarations match this general inventory route?",
            "authority_posture": "exhaustive_inventory_navigation_not_semantic_interpretation",
            "measurement_contract": (
                "Every result is a live declaration route from the exhaustive atlas. "
                "A zone or automatic fallback makes the declaration discoverable; it "
                "does not infer a mathematical claim. Only statement_node links carry "
                "authored statement-level interpretation."
            ),
            "filters": {
                "search": args.node_id or "",
                "module": args.module or "",
                "role": args.role or "",
                "zone": args.zone or "",
            },
            "total_matches": len(matches),
            "returned": min(len(matches), args.limit),
            "omitted": max(0, len(matches) - args.limit),
            "results": matches[: args.limit],
        }
    )


def cmd_motifs(corpus: dict, args) -> int:
    """Graph shapes worth interpolating over, rather than individual results."""
    index = nodes_by_id(corpus)
    by_engine = defaultdict(list)
    for n in corpus["statement_nodes"]:
        if n.get("engine"):
            by_engine[n["engine"]].append(n)

    parallel_shapes = []
    for engine, group in by_engine.items():
        problems = {n.get("problem") for n in group}
        if len({p for p in problems if p in ("249", "257")}) == 2:
            parallel_shapes.append(
                {
                    "engine": engine,
                    "note": "the same engine appears on both problems; its transports may be portable",
                    "nodes": [n["id"] for n in group][:10],
                }
            )

    transports = defaultdict(set)
    for e in corpus["relations"]:
        if e.get("relation") in ("transport_of", "reformulates"):
            src = index.get(e["from"], {})
            transports[src.get("problem")].add(e.get("relation"))
    asymmetric = {
        "249_only": sorted(transports.get("249", set()) - transports.get("257", set())),
        "257_only": sorted(transports.get("257", set()) - transports.get("249", set())),
    }

    dead_ends = [
        compact(n)
        for n in corpus["statement_nodes"]
        if n.get("logical_class") == "finite_instance"
        and not any(
            e["from"] == n["id"] and e.get("relation") == "finite_instance_of"
            for e in corpus["relations"]
        )
    ]

    return emit(
        {
            "question": "graph motifs: the substrate for interpolation rather than another restatement",
            "shared_engines_across_problems": parallel_shapes[: args.limit],
            "transport_asymmetry": asymmetric,
            "finite_deposits_without_extrapolation": dead_ends[: args.limit],
            "unblocked_engines": corpus.get("frontier", {}).get("engine_hierarchy", []),
        }
    )


def cmd_node(corpus: dict, args) -> int:
    index = nodes_by_id(corpus)
    node = index.get(args.node_id)
    if node is None:
        return emit({"error": f"no statement node {args.node_id!r}"})
    edges = [
        e
        for e in corpus["relations"]
        if args.node_id in (e.get("from"), e.get("to")) and not e.get("suppressed_in_views")
    ]
    return emit({"node": node, "relations": edges})


def load_lab() -> dict:
    if not LAB.is_file():
        raise SystemExit(
            "docs/theory_lab.json missing; run python3 scripts/build_theory_lab.py"
        )
    return json.loads(LAB.read_text(encoding="utf-8"))


def cmd_mechanisms(corpus: dict, args) -> int:
    lab = load_lab()
    rows = lab.get("mechanisms", [])
    if args.problem:
        rows = [m for m in rows if m.get("problem_reach") in (args.problem, "both", "shared_substrate")]
    return emit(
        {
            "question": "What are the few mechanisms underneath these proofs?",
            "rule": (
                "A mechanism is an invariant plus a transformation plus the observable "
                "it controls. It is not a theorem family and not a restatement."
            ),
            "count": len(rows),
            "mechanisms": [
                {
                    "mechanism_id": m["mechanism_id"],
                    "human_name": m.get("human_name"),
                    "core_idea": m.get("core_idea"),
                    "invariant": m.get("invariant"),
                    "problem_reach": m.get("problem_reach"),
                    "mechanism_kind": m.get("mechanism_kind"),
                    "claim_ceiling": m.get("claim_ceiling"),
                    "explains_nodes": len(m.get("statement_nodes") or ()),
                    "sharp_failures": len(m.get("sharp_failures") or ()),
                    "confidence": m.get("confidence"),
                }
                for m in rows[: args.limit]
            ],
        }
    )


def cmd_mechanism(corpus: dict, args) -> int:
    lab = load_lab()
    target = args.node_id
    if not target:
        raise SystemExit("usage: query_semantic.py mechanism <mechanism_id>")
    for mech in lab.get("mechanisms", []):
        if mech["mechanism_id"] == target:
            capsule = next(
                (c for c in lab.get("capsules", []) if c.get("mechanism_id") == target), None
            )
            receipts = [
                r
                for r in lab.get("failure_receipts", [])
                if r.get("mechanism_scope_exceeded") == target
                or target in (r.get("mechanisms_not_ruled_out") or ())
            ]
            return emit({"mechanism": mech, "capsule": capsule, "receipts": receipts})
    raise SystemExit(f"unknown mechanism {target}")


def cmd_explains(corpus: dict, args) -> int:
    lab = load_lab()
    target = args.node_id
    if not target:
        raise SystemExit("usage: query_semantic.py explains <node_id>")
    node = nodes_by_id(corpus).get(target)
    owners = [
        {
            "mechanism_id": m["mechanism_id"],
            "core_idea": m.get("core_idea"),
            "invariant": m.get("invariant"),
        }
        for m in lab.get("mechanisms", [])
        if target in (m.get("statement_nodes") or ())
    ]
    return emit(
        {
            "node": compact(node) if node else None,
            "explained_by": owners,
            "note": (
                "No mechanism means the statement is explained by nothing in the basis "
                "yet. That is a finding about the basis, not about the statement."
            )
            if not owners
            else "",
        }
    )


def cmd_unexplained(corpus: dict, args) -> int:
    lab = load_lab()
    view = lab.get("views", {}).get("unexplained_residual", {})
    ids = view.get("nodes", [])
    index = nodes_by_id(corpus)
    if args.problem:
        ids = [i for i in ids if index.get(i, {}).get("problem") == args.problem]
    buckets: dict[str, int] = defaultdict(int)
    for node_id in ids:
        node = index.get(node_id)
        if node:
            buckets[node["logical_class"]] += 1
    return emit(
        {
            "question": "Which statements does the mechanism basis fail to explain?",
            "rule": view.get("rule"),
            "count": len(ids),
            "by_logical_class": dict(sorted(buckets.items(), key=lambda kv: -kv[1])),
            "nodes": [compact(index[i]) for i in ids[: args.limit] if i in index],
        }
    )


def cmd_interventions(corpus: dict, args) -> int:
    lab = load_lab()
    rows = lab.get("interventions", [])
    return emit(
        {
            "question": "What was perturbed, what was predicted, and what happened?",
            "rule": (
                "The prediction fingerprint is stamped when the prediction is recorded. "
                "An outcome that cites a fingerprint which no longer recomputes is "
                "rejected by the contract, so 'we predicted this' stays auditable."
            ),
            "count": len(rows),
            "interventions": [
                {
                    "intervention_id": r["intervention_id"],
                    "operator": r.get("operator"),
                    "interpretation": r.get("mathematical_interpretation"),
                    "predicted_preserved": r.get("predicted_preserved"),
                    "predicted_broken": r.get("predicted_broken"),
                    "outcome_state": r.get("outcome_state", "predicted_only"),
                    "discrepancy": r.get("discrepancy", ""),
                }
                for r in rows[: args.limit]
            ],
        }
    )


def cmd_discrepancies(corpus: dict, args) -> int:
    lab = load_lab()
    view = lab.get("views", {}).get("prediction_discrepancies", {})
    index = {r["intervention_id"]: r for r in lab.get("interventions", [])}
    return emit(
        {
            "question": "Where did the mechanism layer predict wrongly?",
            "rule": view.get("rule"),
            "count": len(view.get("entries", [])),
            "entries": [
                {
                    "intervention_id": e["intervention_id"],
                    "operator": index.get(e["intervention_id"], {}).get("operator"),
                    "discrepancy": e["discrepancy"],
                    "outcome_evidence": index.get(e["intervention_id"], {}).get(
                        "outcome_evidence", ""
                    ),
                }
                for e in view.get("entries", [])[: args.limit]
            ],
        }
    )


def cmd_receipts(corpus: dict, args) -> int:
    lab = load_lab()
    rows = lab.get("failure_receipts", [])
    return emit(
        {
            "question": "What was tried and failed, and what does the failure rule out?",
            "rule": (
                "A failure with no reusable diagnosis is noise. Each receipt distinguishes "
                "a candidate route ruled out from an existing mechanism used beyond its "
                "scope, resolves its evidence, and exhausts a declared sibling family."
            ),
            "count": len(rows),
            "receipts": [
                {
                    "receipt_id": r.get("receipt_id"),
                    "candidate": r.get("candidate"),
                    "smallest_failing_hypothesis": r.get("smallest_failing_hypothesis"),
                    "failure_kind": r.get("failure_kind"),
                    "candidate_route_ruled_out": r.get(
                        "candidate_route_ruled_out"
                    ),
                    "mechanism_scope_exceeded": r.get(
                        "mechanism_scope_exceeded"
                    ),
                    "mechanisms_not_ruled_out": r.get("mechanisms_not_ruled_out"),
                    "sibling_family": r.get("sibling_family"),
                    "nearest_repair": r.get("nearest_repair"),
                    "repair_verdict": r.get("repair_verdict"),
                    "reentry_condition": r.get("reentry_condition"),
                }
                for r in rows[: args.limit]
            ],
        }
    )


def cmd_benchmark(corpus: dict, args) -> int:
    lab = load_lab()
    bench = lab.get("benchmark", {})
    return emit(
        {
            "question": "Does the scaffolding help recover mathematics it was not shown?",
            "rule": (
                "Each item holds out a declaration by checking the repository out at "
                "the commit before it landed, so the target is absent by construction. "
                "Arms are cumulative: signatures, then the statement graph, then "
                "mechanisms, then the negative-space records."
            ),
            "arm_tally": lab.get("summary", {}).get("arm_tally", {}),
            "items": [
                {
                    "item_id": i["item_id"],
                    "problem": i.get("problem"),
                    "logical_class": i.get("logical_class"),
                    "cut_commit": i.get("cut_commit")[:8] if i.get("cut_commit") else None,
                    "commits_of_prior_development": i.get("commits_of_prior_development"),
                    "selection_rationale": i.get("selection_rationale"),
                }
                for i in bench.get("items", [])
            ],
            "results": [
                {
                    "result_id": r.get("result_id"),
                    "item_id": r.get("item_id"),
                    "arm": r.get("arm"),
                    "statement_recovered": r.get("statement_recovered"),
                    "mechanism_recovered": r.get("mechanism_recovered"),
                    "semantic_distance": r.get("semantic_distance"),
                    "notes": r.get("notes", "")[:200],
                }
                for r in bench.get("results", [])[: args.limit]
            ],
        }
    )


COMMANDS = {
    "nonrecurring": cmd_nonrecurring,
    "bare-equivalences": cmd_bare_equivalences,
    "finite-instances": cmd_finite_instances,
    "classical": cmd_classical,
    "engines": cmd_engines,
    "barriers": cmd_barriers,
    "open-antecedents": cmd_open_antecedents,
    "expert-questions": cmd_expert_questions,
    "prior-art-review": cmd_prior_art_review,
    "coverage": cmd_coverage,
    "semantic-reviews": cmd_semantic_reviews,
    "inventory": cmd_inventory,
    "paper-coverage": cmd_paper_coverage,
    "population-backlog": cmd_population_backlog,
    "motifs": cmd_motifs,
    "node": cmd_node,
    "mechanisms": cmd_mechanisms,
    "mechanism": cmd_mechanism,
    "explains": cmd_explains,
    "unexplained": cmd_unexplained,
    "interventions": cmd_interventions,
    "discrepancies": cmd_discrepancies,
    "receipts": cmd_receipts,
    "benchmark": cmd_benchmark,
}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=sorted(COMMANDS))
    parser.add_argument(
        "node_id",
        nargs="?",
        help="detail id for node, mechanism, explains, or expert-questions",
    )
    parser.add_argument("--problem", choices=("249", "257", "shared_substrate"))
    parser.add_argument(
        "--module",
        help="inventory-only case-insensitive module path filter",
    )
    parser.add_argument(
        "--role",
        help="inventory-only exact declaration-role filter",
    )
    parser.add_argument(
        "--zone",
        help="inventory-only exact semantic-zone filter",
    )
    parser.add_argument(
        "--paper",
        help="population-backlog case-insensitive paper path/name filter",
    )
    parser.add_argument("--limit", type=int, default=40)
    args = parser.parse_args()
    return COMMANDS[args.command](load(), args)


if __name__ == "__main__":
    raise SystemExit(main())
