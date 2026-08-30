#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Query the public mathematical corpus without loading its exhaustive files.

This is a read-only navigation projection. It does not elaborate Lean and does
not acquire proof authority. Run from any directory; output is JSON by default.
"""

from __future__ import annotations

import argparse
import bisect
import hashlib
import json
import re
import sys
import unicodedata
from collections import Counter, deque
from functools import lru_cache
from pathlib import Path
from typing import Any, Mapping

from build_module_synopsis_index import (
    OWNER_ADOPTION as MODULE_SYNOPSIS_OWNER_ADOPTION,
    QUERY_CONTRACT as MODULE_SYNOPSIS_QUERY_CONTRACT,
    SCHEMA as MODULE_SYNOPSIS_SCHEMA,
)

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_LIMIT = 20
MAX_LIMIT = 100
MODULE_PACKET_LIMIT = 12
MAX_SEMANTIC_CELLS = 4
OUTPUT_BUDGET_BYTES = 73_000
AGENT_TOUR_BASE_BUDGET_BYTES = 18_000
# The tour carries the complete reviewed result-family index as well as the
# problem map.  The allowance scales with the canonical eight-problem and
# reviewed-family census so it does not reject a complete, non-truncated tour.
AGENT_TOUR_PER_PROBLEM_BUDGET_BYTES = 5_100
SOURCE_LINE_WINDOW = 3
CONNECTION_CARD_SCHEMA = "lean-connection-card/2"
SEMANTIC_DICTIONARY_SCHEMA = "erdos249257-semantic-dictionary/2"
SEMANTIC_SLICE_SCHEMA = "erdos249257-semantic-slice/1"


def agent_tour_budget_bytes(indexed_problem_count: int) -> int:
    """Scale the bounded tour with the canonical problem registry."""
    return (
        AGENT_TOUR_BASE_BUDGET_BYTES
        + AGENT_TOUR_PER_PROBLEM_BUDGET_BYTES * indexed_problem_count
    )

# The atlas builder strips nested Lean comments and recognizes heads whose
# keyword and identifier are split across lines.  This compatibility set must
# remain exactly equal to any false declaration rows independently detected by
# the whole-corpus audit; it is empty for the current atlas.
SUPPRESSED_DECLARATION_ATLAS_ROWS: frozenset[str] = frozenset()

SEMANTIC_QUERY_OPERATORS = (
    {
        "id": "locate",
        "intent": "Find an exact declaration, definition, claim, paper anchor, or source coordinate.",
        "cues": ("find", "where", "locate", "source", "declaration"),
    },
    {
        "id": "support",
        "intent": "Find a jointly useful premise or strategy support set.",
        "cues": (
            "need to prove",
            "need",
            "premise",
            "support",
            "approach",
            "proof socket",
            "socket",
            "provide",
            "yield",
            "imply",
        ),
    },
    {
        "id": "frontier",
        "intent": "Recover the exact open proposition and its nearest proved reductions or blockers.",
        "cues": ("what remains", "what blocks", "missing", "next", "try next"),
    },
    {
        "id": "analogy",
        "intent": "Compare structurally corresponding arguments without treating similarity as proof.",
        "cues": ("analog", "analogy", "compare", "transfer"),
    },
    {
        "id": "trace",
        "intent": "Explain why a claim holds through typed argument and source relationships.",
        "cues": ("why", "depends on", "builds on", "trace"),
    },
    {
        "id": "digest",
        "intent": "Return a bounded formal-plus-authored mathematical explanation.",
        "cues": ("explain", "understand", "overview", "story"),
    },
    {
        "id": "falsify",
        "intent": "Find non-claims, failed analogies, obstructions, and exact claim ceilings.",
        "cues": (
            "cannot",
            "counterexample",
            "dead end",
            "does not",
            "failed",
            "worth pursuing",
        ),
    },
)

# This is deliberately a small translation layer, not a generated mini-paper.
# Rows bridge ordinary questions to the corpus's authored terms of art and typed
# handles. They never create proof, claim-status, or editorial authority.
SEMANTIC_VOCABULARY = (
    {
        "id": "rank_two_certificate_value",
        "vocabulary_kind": "entity",
        "pref_label": "rank-2 certificate shallowness",
        "alt_labels": (
            "rank two worth pursuing",
            "second difference certificate",
            "better than rank one",
            "rank two certificate",
            "worth pursuing",
        ),
        "query_expansions": (
            "rank 2 not shallower",
            "promotion gate denied",
        ),
        "route_hints": (
            "--declaration rank2_kill_sound_but_not_shallower_at_cell",
        ),
    },
    {
        "id": "negative_mathematical_result",
        "vocabulary_kind": "intent",
        "pref_label": "obstruction or no-go result",
        "alt_labels": (
            "dead end",
            "failed approach",
            "not worth pursuing",
            "why it fails",
            "what is ruled out",
        ),
        "query_expansions": (
            "obstruction no go countermodel",
            "claim ceiling does not prove",
        ),
        "route_hints": (
            "--route transport_curvature_programme",
        ),
    },
    {
        "id": "open_producer",
        "vocabulary_kind": "intent",
        "pref_label": "remaining open producer",
        "alt_labels": (
            "missing step",
            "missing producer",
            "what blocks",
            "what should i try next",
            "what remains to prove",
        ),
        "query_expansions": (
            "remaining open supply producer",
            "sufficient interface open",
        ),
        "route_hints": (
            "--open <remaining_open.id>",
        ),
    },
    {
        "id": "unbounded_certificate_supply",
        "vocabulary_kind": "entity",
        "pref_label": "unbounded certified non-integrality supply",
        "alt_labels": (
            "unbounded certificate supply",
            "cofinal certificate producer",
            "certificates at unbounded parameters",
        ),
        "query_expansions": (
            "certified non-integrality witnesses at unbounded parameters",
            "lcm diagonal sufficient producer",
        ),
        "route_hints": (
            "--open remaining_open.unbounded_certificate_supply",
        ),
    },
    {
        "id": "half_value_membership",
        "vocabulary_kind": "entity",
        "pref_label": "half-value achievement-set membership",
        "alt_labels": (
            "1/2 problem",
            "half value",
            "one half",
            "rational support counterexample",
        ),
        "query_expansions": (
            "half membership mersenne achievement",
            "greedy half last producer",
        ),
        "route_hints": (
            "--route erdos257_half_story",
            "--open remaining_open.half_value_membership",
        ),
    },
    {
        "id": "one_over_twenty_one_frontier",
        "vocabulary_kind": "entity",
        "pref_label": "one-over-twenty-one achievement-set frontier",
        "alt_labels": (
            "1/21",
            "1/21 problem",
            "1/21 target",
            "one over twenty one",
            "one-over-twenty-one target",
            "twenty one denominator",
        ),
        "query_expansions": (
            "one over twenty one finite support obstruction",
            "primitive 23 solutions mul ten",
        ),
        "route_hints": (
            "--declaration finiteErdosSum_ne_one_div_twenty_one",
            "--declaration exists_two_primitive23_solutions_mul_ten",
            "--claim universal_257",
            "--open remaining_open.universal_257_all_infinite_supports",
        ),
        "semantic_node_hints": (
            "Z65::one_over_twenty_one_has_no_finite_support_on_ranks_at_least_two",
            "Z65::primitive_23_cone_has_rank_ten_defect_and_recurrent_multiplicity",
        ),
    },
    {
        "id": "formal_assumptions",
        "vocabulary_kind": "intent",
        "pref_label": "axiom footprint",
        "alt_labels": (
            "assumptions",
            "what does this theorem assume",
            "trusted base",
        ),
        "query_expansions": (
            "axiom footprint hypothesis",
        ),
        "route_hints": (
            "--declaration <Lean_name>",
        ),
    },
    {
        "id": "counterexample_language",
        "vocabulary_kind": "intent",
        "pref_label": "countermodel",
        "alt_labels": (
            "counterexample",
            "false friend",
            "disproof example",
        ),
        "query_expansions": (
            "countermodel obstruction no go",
        ),
        "route_hints": (
            "--search countermodel",
        ),
    },
    {
        "id": "semantic_population_backlog",
        "vocabulary_kind": "intent",
        "pref_label": "paper-seeded semantic population backlog",
        "alt_labels": (
            "semantic work remains",
            "paper proofs lack semantic interpretation",
            "populate the semantic graph",
            "semantic coverage gap",
        ),
        "query_expansions": (
            "paper cited live declarations without statement nodes",
            "proposition level semantic backlog",
        ),
        "route_hints": (
            "--route agent_native_corpus_navigation",
        ),
    },
)


@lru_cache(maxsize=None)
def load(rel: str) -> dict[str, Any]:
    return json.loads((ROOT / rel).read_text(encoding="utf-8"))


def atlas_declarations(atlas: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        row
        for row in atlas["declarations"]
        if row["id"] not in SUPPRESSED_DECLARATION_ATLAS_ROWS
    ]


def lean_code_projection(text: str) -> str:
    """Replace Lean comments and strings with spaces while preserving lines."""
    projected: list[str] = []
    block_depth = 0
    in_string = False
    escaped = False
    cursor = 0
    while cursor < len(text):
        pair = text[cursor : cursor + 2]
        char = text[cursor]
        if block_depth:
            if pair == "/-":
                projected.extend((" ", " "))
                block_depth += 1
                cursor += 2
            elif pair == "-/":
                projected.extend((" ", " "))
                block_depth -= 1
                cursor += 2
            else:
                projected.append("\n" if char == "\n" else " ")
                cursor += 1
            continue
        if in_string:
            projected.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            cursor += 1
            continue
        if pair == "--":
            while cursor < len(text) and text[cursor] != "\n":
                projected.append(" ")
                cursor += 1
            continue
        if pair == "/-":
            projected.extend((" ", " "))
            block_depth = 1
            cursor += 2
            continue
        if char == '"':
            projected.append(" ")
            in_string = True
            cursor += 1
            continue
        projected.append(char)
        cursor += 1
    return "".join(projected)


@lru_cache(maxsize=512)
def module_synopsis_index() -> dict[str, str | None]:
    path = ROOT / "docs/module_synopsis_index.json"
    if not path.is_file():
        return {}
    try:
        packet = json.loads(path.read_text(encoding="utf-8"))
        atlas = load("docs/declaration_atlas.json")
    except (json.JSONDecodeError, OSError, KeyError):
        return {}
    if (
        packet.get("schema_version") != MODULE_SYNOPSIS_SCHEMA
        or packet.get("source_fingerprint") != atlas.get("source_fingerprint")
        or packet.get("query_contract") != MODULE_SYNOPSIS_QUERY_CONTRACT
        or packet.get("owner_adoption") != MODULE_SYNOPSIS_OWNER_ADOPTION
    ):
        return {}
    return {
        row["path"]: row.get("synopsis")
        for row in packet.get("modules", [])
        if isinstance(row, dict) and isinstance(row.get("path"), str)
    }


@lru_cache(maxsize=512)
def module_synopsis(rel: str) -> str | None:
    """Return a fingerprint-bound authored module header, with a local fallback."""
    indexed = module_synopsis_index()
    if rel in indexed:
        return indexed[rel]
    path = ROOT / rel
    if not path.is_file():
        return None
    with path.open(encoding="utf-8") as source:
        prefix = source.read(64_000)
    match = re.search(r"/-!(.*?)-/", prefix, re.S)
    if match is None:
        return None
    lines = []
    for raw in match.group(1).splitlines():
        line = raw.strip()
        if line.startswith("#"):
            line = line.lstrip("#").strip()
        lines.append(line)
    synopsis = re.sub(r"\s+", " ", " ".join(lines)).strip()
    return synopsis[:1600] or None


@lru_cache(maxsize=1)
def lean_dependency_index() -> dict[str, Any] | None:
    path = ROOT / "docs/lean_dependency_index.json"
    if not path.is_file():
        return None
    try:
        packet = json.loads(path.read_text(encoding="utf-8"))
        atlas = load("docs/declaration_atlas.json")
    except (json.JSONDecodeError, OSError, KeyError):
        return None
    if (
        packet.get("schema_version")
        != "erdos249257-lean-dependency-index/3"
        or packet.get("source_fingerprint") != atlas.get("source_fingerprint")
        or not isinstance(packet.get("nodes"), list)
        or not isinstance(packet.get("edges"), list)
    ):
        return None
    return packet


@lru_cache(maxsize=1)
def lean_dependency_adjacency() -> dict[str, Any] | None:
    packet = lean_dependency_index()
    if packet is None:
        return None
    nodes_by_id = {
        row["node_id"]: row
        for row in packet["nodes"]
        if isinstance(row, dict) and isinstance(row.get("node_id"), int)
    }
    nodes_by_handle = {
        row["handle"]: row
        for row in nodes_by_id.values()
        if isinstance(row.get("handle"), str)
    }
    forward: dict[str, list[dict[str, Any]]] = {}
    reverse: dict[str, list[dict[str, Any]]] = {}
    relation_legend = packet.get("edge_relation_bit_legend", {})
    for edge in packet["edges"]:
        if (
            not isinstance(edge, list)
            or len(edge) != 3
            or edge[0] not in nodes_by_id
            or edge[1] not in nodes_by_id
            or not isinstance(edge[2], int)
        ):
            continue
        source = nodes_by_id[edge[0]]
        target = nodes_by_id[edge[1]]
        relations = [
            label
            for bit, label in sorted(
                (
                    (int(bit), label)
                    for bit, label in relation_legend.items()
                )
            )
            if edge[2] & bit
        ]
        target_row = {
            key: target[key]
            for key in (
                "handle",
                "name",
                "declaration_kind",
                "source_ref",
            )
        }
        target_row["relations"] = relations
        forward.setdefault(source["handle"], []).append(target_row)
        source_row = {
            key: source[key]
            for key in (
                "handle",
                "name",
                "declaration_kind",
                "source_ref",
            )
        }
        source_row["relations"] = relations
        reverse.setdefault(target["handle"], []).append(source_row)
    theorem_kinds = {"theorem", "lemma", "corollary", "proposition"}
    for rows in (*forward.values(), *reverse.values()):
        rows.sort(
            key=lambda row: (
                0
                if row["declaration_kind"] in theorem_kinds
                else 1,
                0 if "value_reference" in row["relations"] else 1,
                row["handle"],
            )
        )
    formal_type_affordances = {}
    affordance_packet = packet.get("formal_type_affordances", {})
    symbol_table = affordance_packet.get("symbol_table", [])
    binder_name_table = affordance_packet.get("binder_name_table", [])
    binder_info_legend = affordance_packet.get(
        "binder_info_code_legend", {}
    )
    for row in affordance_packet.get("rows", []):
        if (
            not isinstance(row, list)
            or len(row) != 5
            or row[0] not in nodes_by_id
            or not isinstance(row[1], int)
            or not isinstance(row[2], int)
            or not isinstance(row[3], list)
            or not isinstance(row[4], list)
            or not 0 <= row[2] < len(symbol_table)
            or any(
                not isinstance(symbol_id, int)
                or not 0 <= symbol_id < len(symbol_table)
                for symbol_id in row[3]
            )
            or any(
                not isinstance(binder, list)
                or len(binder) != 5
                or not isinstance(binder[0], int)
                or not 0 <= binder[0] < len(binder_name_table)
                or str(binder[1]) not in binder_info_legend
                or not isinstance(binder[2], bool)
                or not isinstance(binder[3], int)
                or not 0 <= binder[3] < len(symbol_table)
                or not isinstance(binder[4], list)
                or any(
                    not isinstance(symbol_id, int)
                    or not 0 <= symbol_id < len(symbol_table)
                    for symbol_id in binder[4]
                )
                for binder in row[4]
            )
        ):
            continue
        formal_type_affordances[nodes_by_id[row[0]]["handle"]] = {
            "forall_binder_count": row[1],
            "conclusion_head": symbol_table[row[2]],
            "conclusion_symbols": [
                symbol_table[symbol_id] for symbol_id in row[3]
            ],
            "binders": [
                {
                    "index": index,
                    "name": binder_name_table[binder[0]],
                    "binder_info": binder_info_legend[str(binder[1])],
                    "is_proposition": binder[2],
                    "type_head": symbol_table[binder[3]],
                    "type_symbols": [
                        symbol_table[symbol_id]
                        for symbol_id in binder[4]
                    ],
                }
                for index, binder in enumerate(row[4])
            ],
        }
    return {
        "packet": packet,
        "nodes_by_handle": nodes_by_handle,
        "forward": forward,
        "reverse": reverse,
        "formal_type_affordances": formal_type_affordances,
    }


def formal_dependency_neighbourhood(
    handle: str, limit: int = 8
) -> dict[str, Any]:
    adjacency = lean_dependency_adjacency()
    if adjacency is None:
        return {
            "availability": "unavailable_or_stale",
            "authority_posture": (
                "no_elaborated_dependency_index_loaded;lexical_candidates_"
                "remain_navigation_only"
            ),
            "validation": (
                "python3 scripts/build_lean_dependency_index.py --check"
            ),
        }
    node = adjacency["nodes_by_handle"].get(handle)
    if node is None:
        return {
            "availability": "handle_not_source_resolved",
            "handle": handle,
            "authority_posture": (
                "index_gap_not_evidence_of_no_formal_dependencies"
            ),
            "validation": (
                "python3 scripts/build_lean_dependency_index.py --check"
            ),
        }
    dependencies = adjacency["forward"].get(handle, [])
    consumers = adjacency["reverse"].get(handle, [])
    two_hop_theorem_paths = []
    theorem_kinds = {"theorem", "lemma", "corollary", "proposition"}
    for middle in dependencies:
        if middle["declaration_kind"] not in theorem_kinds:
            continue
        for target in adjacency["forward"].get(middle["handle"], []):
            if target["declaration_kind"] not in theorem_kinds:
                continue
            two_hop_theorem_paths.append(
                {
                    "source": handle,
                    "via": middle["handle"],
                    "target": target["handle"],
                    "edge_relations": [
                        middle["relations"],
                        target["relations"],
                    ],
                }
            )
            if len(two_hop_theorem_paths) >= limit:
                break
        if len(two_hop_theorem_paths) >= limit:
            break
    return {
        "availability": "available",
        "handle": handle,
        "source_ref": node["source_ref"],
        "direct_dependencies": dependencies[:limit],
        "direct_consumers": consumers[:limit],
        "two_hop_theorem_paths": two_hop_theorem_paths,
        "receipt": {
            "direct_dependency_total": len(dependencies),
            "direct_dependency_emitted": min(len(dependencies), limit),
            "direct_consumer_total": len(consumers),
            "direct_consumer_emitted": min(len(consumers), limit),
            "omitted_internal_reference_count": node[
                "omitted_internal_reference_count"
            ],
        },
        "authority_posture": (
            "direct_constant_references_from_elaborated_Lean_types_and_values_"
            "with_source_coordinates;two_hop_paths_are_compositions_of_exact_"
            "direct_edges"
        ),
        "expansion": {
            "proof_cone": (
                f"python3 scripts/query_corpus.py --proof-cone {handle} "
                "--depth 4 --limit 20"
            ),
            "path_to": (
                "python3 scripts/query_corpus.py --dependency-path "
                f"{handle} <target_declaration> --depth 8"
            ),
        },
        "validation": "python3 scripts/build_lean_dependency_index.py --check",
    }


def resolve_formal_dependency_handle(
    requested: str, adjacency: dict[str, Any]
) -> dict[str, Any]:
    if requested in adjacency["nodes_by_handle"]:
        return {
            "availability": "available",
            "requested": requested,
            "handle": requested,
            "resolution": "exact_canonical_handle",
        }
    matches = sorted(
        handle
        for handle, node in adjacency["nodes_by_handle"].items()
        if node["name"] == requested
    )
    if len(matches) == 1:
        return {
            "availability": "available",
            "requested": requested,
            "handle": matches[0],
            "resolution": "unique_short_name",
        }
    if matches:
        return {
            "availability": "ambiguous_short_name",
            "requested": requested,
            "candidate_count": len(matches),
            "candidate_handles": matches[:20],
            "omitted_candidate_count": max(0, len(matches) - 20),
        }
    return {
        "availability": "handle_not_source_resolved",
        "requested": requested,
    }


def compact_formal_dependency_node(
    node: dict[str, Any], depth: int
) -> dict[str, Any]:
    return {
        "handle": node["handle"],
        "name": node["name"],
        "declaration_kind": node["declaration_kind"],
        "source_ref": node["source_ref"],
        "depth": depth,
    }


def formal_dependency_proof_cone(
    requested: str,
    max_depth: int = 4,
    node_limit: int = 20,
) -> dict[str, Any]:
    """Return a bounded proof-term dependency cone with exact omission counts."""
    if not 1 <= max_depth <= 8:
        raise ValueError("formal dependency cone depth must be between 1 and 8")
    if not 1 <= node_limit <= MAX_LIMIT:
        raise ValueError(
            f"formal dependency cone limit must be between 1 and {MAX_LIMIT}"
        )
    adjacency = lean_dependency_adjacency()
    if adjacency is None:
        return {
            "kind": "formal_dependency_proof_cone",
            "availability": "unavailable_or_stale",
            "requested": requested,
            "validation": (
                "python3 scripts/build_lean_dependency_index.py --check"
            ),
        }
    resolution = resolve_formal_dependency_handle(requested, adjacency)
    if resolution["availability"] != "available":
        return {
            "kind": "formal_dependency_proof_cone",
            **resolution,
            "validation": (
                "python3 scripts/build_lean_dependency_index.py --check"
            ),
        }
    handle = resolution["handle"]
    depths = {handle: 0}
    queue = deque([handle])
    exact_edges: dict[
        tuple[str, str], tuple[str, ...]
    ] = {}
    while queue:
        source = queue.popleft()
        source_depth = depths[source]
        if source_depth >= max_depth:
            continue
        for target in adjacency["forward"].get(source, []):
            if "value_reference" not in target["relations"]:
                continue
            target_handle = target["handle"]
            exact_edges[(source, target_handle)] = tuple(
                target["relations"]
            )
            if target_handle not in depths:
                depths[target_handle] = source_depth + 1
                queue.append(target_handle)
    ordered_handles = list(depths)
    theorem_kinds = {"theorem", "lemma", "corollary", "proposition"}
    prioritized_handles = [
        handle,
        *[
            candidate
            for candidate in ordered_handles[1:]
            if adjacency["nodes_by_handle"][candidate][
                "declaration_kind"
            ]
            in theorem_kinds
        ],
        *[
            candidate
            for candidate in ordered_handles[1:]
            if adjacency["nodes_by_handle"][candidate][
                "declaration_kind"
            ]
            not in theorem_kinds
        ],
    ]
    selected = set(prioritized_handles[:node_limit])
    selected_handles = [
        candidate for candidate in ordered_handles if candidate in selected
    ]
    emitted_edges = [
        {
            "from": source,
            "relation": "uses_in_elaborated_value",
            "to": target,
            "edge_relations": list(relations),
            "authority": "kernel_elaborated_environment",
        }
        for (source, target), relations in exact_edges.items()
        if source in selected and target in selected
    ]
    omitted_handles = [
        candidate
        for candidate in prioritized_handles
        if candidate not in selected
    ]
    return {
        "kind": "formal_dependency_proof_cone",
        "availability": "available",
        "requested": requested,
        "resolved_handle": handle,
        "handle_resolution": resolution["resolution"],
        "max_depth": max_depth,
        "edge_policy": "elaborated_value_references_only",
        "selection_policy": (
            "root_then_theorem_like_dependencies_then_other_constants_"
            "with_stable_breadth_first_order_inside_each_class"
        ),
        "nodes": [
            compact_formal_dependency_node(
                adjacency["nodes_by_handle"][node_handle],
                depths[node_handle],
            )
            for node_handle in selected_handles
        ],
        "edges": emitted_edges,
        "omission_receipt": {
            "reachable_node_count_within_depth": len(ordered_handles),
            "emitted_node_count": len(selected_handles),
            "omitted_node_count": len(omitted_handles),
            "reachable_edge_count_within_depth": len(exact_edges),
            "emitted_edge_count": len(emitted_edges),
            "omitted_edge_count": len(exact_edges) - len(emitted_edges),
            "first_omitted_handles": omitted_handles[:8],
            "node_limit": node_limit,
        },
        "authority_posture": (
            "bounded_composition_of_exact_elaborated_value_reference_edges_"
            "not_a_claim_that_every_reference_is_a_mathematically_decisive_"
            "premise"
        ),
        "follow": {
            "expand": (
                "python3 scripts/query_corpus.py --proof-cone "
                f"{handle} --depth {min(8, max_depth + 1)} "
                f"--limit {min(MAX_LIMIT, max(node_limit * 2, 20))}"
            ),
            "declaration": (
                "python3 scripts/query_corpus.py --declaration "
                "<node.handle>"
            ),
        },
        "validation": "python3 scripts/build_lean_dependency_index.py --check",
    }


def formal_dependency_path(
    requested_source: str,
    requested_target: str,
    max_depth: int = 8,
) -> dict[str, Any]:
    """Return an exact shortest directed proof-term dependency path."""
    if not 1 <= max_depth <= 8:
        raise ValueError("formal dependency path depth must be between 1 and 8")
    adjacency = lean_dependency_adjacency()
    if adjacency is None:
        return {
            "kind": "formal_dependency_path",
            "availability": "unavailable_or_stale",
            "requested_source": requested_source,
            "requested_target": requested_target,
            "validation": (
                "python3 scripts/build_lean_dependency_index.py --check"
            ),
        }
    source_resolution = resolve_formal_dependency_handle(
        requested_source, adjacency
    )
    target_resolution = resolve_formal_dependency_handle(
        requested_target, adjacency
    )
    if (
        source_resolution["availability"] != "available"
        or target_resolution["availability"] != "available"
    ):
        return {
            "kind": "formal_dependency_path",
            "availability": "unresolved_endpoint",
            "source_resolution": source_resolution,
            "target_resolution": target_resolution,
            "validation": (
                "python3 scripts/build_lean_dependency_index.py --check"
            ),
        }
    source = source_resolution["handle"]
    target = target_resolution["handle"]
    predecessor: dict[str, tuple[str, tuple[str, ...]]] = {}
    depths = {source: 0}
    queue = deque([source])
    while queue and target not in depths:
        current = queue.popleft()
        if depths[current] >= max_depth:
            continue
        for dependency in adjacency["forward"].get(current, []):
            if "value_reference" not in dependency["relations"]:
                continue
            dependency_handle = dependency["handle"]
            if dependency_handle in depths:
                continue
            depths[dependency_handle] = depths[current] + 1
            predecessor[dependency_handle] = (
                current,
                tuple(dependency["relations"]),
            )
            queue.append(dependency_handle)
    if target not in depths:
        return {
            "kind": "formal_dependency_path",
            "availability": "no_path_within_bound",
            "source": source,
            "target": target,
            "max_depth": max_depth,
            "explored_node_count": len(depths),
            "edge_policy": "elaborated_value_references_only",
            "authority_posture": (
                "bounded_negative_navigation_result_not_proof_of_global_"
                "dependency_absence"
            ),
            "validation": (
                "python3 scripts/build_lean_dependency_index.py --check"
            ),
        }
    path_handles = [target]
    path_relations = []
    while path_handles[-1] != source:
        previous, relations = predecessor[path_handles[-1]]
        path_relations.append(relations)
        path_handles.append(previous)
    path_handles.reverse()
    path_relations.reverse()
    return {
        "kind": "formal_dependency_path",
        "availability": "available",
        "requested_source": requested_source,
        "requested_target": requested_target,
        "source": source,
        "target": target,
        "hop_count": len(path_handles) - 1,
        "max_depth": max_depth,
        "minimality_posture": (
            "shortest_directed_path_in_the_source_resolved_value_reference_"
            "graph_within_the_depth_bound"
        ),
        "nodes": [
            compact_formal_dependency_node(
                adjacency["nodes_by_handle"][handle], depth
            )
            for depth, handle in enumerate(path_handles)
        ],
        "edges": [
            {
                "from": path_handles[index],
                "relation": "uses_in_elaborated_value",
                "to": path_handles[index + 1],
                "edge_relations": list(path_relations[index]),
                "authority": "kernel_elaborated_environment",
            }
            for index in range(len(path_relations))
        ],
        "explored_node_count": len(depths),
        "authority_posture": (
            "shortest_composition_of_exact_elaborated_value_reference_edges_"
            "not_a_semantic_causality_or_minimal_premise_proof"
        ),
        "follow": {
            "source_cone": (
                f"python3 scripts/query_corpus.py --proof-cone {source} "
                f"--depth {max_depth}"
            ),
            "declaration": (
                "python3 scripts/query_corpus.py --declaration "
                "<node.handle>"
            ),
        },
        "validation": "python3 scripts/build_lean_dependency_index.py --check",
    }


@lru_cache(maxsize=1)
def declaration_row_indexes() -> dict[str, dict[str, Any]]:
    """Index atlas rows without eagerly resolving every Lean namespace."""
    atlas = load("docs/declaration_atlas.json")
    by_name: dict[str, list[dict[str, Any]]] = {}
    by_module: dict[str, list[dict[str, Any]]] = {}
    for row in atlas_declarations(atlas):
        by_name.setdefault(row["name"], []).append(row)
        by_module.setdefault(row["module"], []).append(row)
    for rows in by_module.values():
        rows.sort(key=lambda row: (row["line"], row["name"]))
    return {
        "by_name": by_name,
        "by_module": by_module,
    }


@lru_cache(maxsize=1)
def declaration_rows_by_qualified_name() -> dict[str, dict[str, Any]]:
    """Resolve qualified handles lazily; bare-name queries use the cheap index."""
    atlas = load("docs/declaration_atlas.json")
    return {
        qualified_declaration_name(row): row
        for row in atlas_declarations(atlas)
    }


def declaration_rows_for_handle(name: str) -> list[dict[str, Any]]:
    """Return exact bare-name or qualified-name matches from cached indexes."""
    by_name = declaration_row_indexes()["by_name"]
    matches = by_name.get(name)
    if matches is not None:
        return list(matches)
    if "." not in name:
        return []
    parts = name.split(".")
    candidates: dict[str, dict[str, Any]] = {}
    for index in range(1, len(parts)):
        for row in by_name.get(".".join(parts[index:]), []):
            candidates[row["id"]] = row
    return [
        row
        for row in candidates.values()
        if qualified_declaration_name(row) == name
    ]


def support_goal_request(query: str) -> dict[str, str] | None:
    """Extract a goal and optional premise context from a support question."""
    patterns = (
        (
            r"\b(?:need|want|trying)\s+to\s+prove\s+(.+?)\s+"
            r"(?:from|assuming|given)\s+(.+?)(?:[;?]|$)",
            True,
        ),
        (
            r"\b(?:need|want|trying)\s+to\s+prove\s+(.+?)(?:[;?]|$)",
            False,
        ),
        (r"\bgoal\s*(?:is|:)\s*(.+?)(?:[;?]|$)", False),
    )
    for pattern, has_context in patterns:
        match = re.search(pattern, query, flags=re.IGNORECASE)
        if match is None:
            continue
        return {
            "goal": match.group(1).strip(),
            "context": (
                match.group(2).strip() if has_context else ""
            ),
            "extraction": "ordinary_language_goal_pattern",
        }
    return None


def formal_goal_shape_cues(goal: str) -> list[str]:
    terms = search_terms(goal)
    cues = []
    if "integrality" in terms:
        cues.append("direct_integer_membership")
    if "irrational" in terms:
        cues.append("irrationality")
    if "mem" in terms:
        cues.append("membership")
    if "exist" in terms or "exists" in terms:
        cues.append("existence")
    if (
        "=" in goal
        or "equal" in terms
        or "equality" in terms
    ):
        cues.append("equality")
    if any(token in goal for token in ("≤", "<", "≥", ">")):
        cues.append("order_relation")
    return cues


def formal_affordance_shape_matches(
    cues: list[str], affordance: dict[str, Any]
) -> list[str]:
    head = affordance["conclusion_head"]
    symbols = set(affordance["conclusion_symbols"])
    direct_membership = (
        head.endswith("Membership.mem")
        or head.endswith("Set.Mem")
        or head == "Membership.mem"
    )
    integer_range = any(
        symbol.endswith("Set.range") for symbol in symbols
    ) and any(
        symbol.endswith("Int.cast")
        or "IntCast" in symbol
        or symbol.endswith("Int.ofNat")
        for symbol in symbols
    )
    matches = []
    if (
        "direct_integer_membership" in cues
        and direct_membership
        and integer_range
    ):
        matches.append("direct_integer_membership")
    if (
        "irrationality" in cues
        and head.endswith("Irrational")
    ):
        matches.append("irrationality")
    if "membership" in cues and direct_membership:
        matches.append("membership")
    if "existence" in cues and head.endswith("Exists"):
        matches.append("existence")
    if "equality" in cues and head.endswith("Eq"):
        matches.append("equality")
    if (
        "order_relation" in cues
        and (
            head.endswith("LE.le")
            or head.endswith("LT.lt")
            or head.endswith("GE.ge")
            or head.endswith("GT.gt")
        )
    ):
        matches.append("order_relation")
    return matches


def formal_context_symbol_matches(
    context_terms: set[str], affordance: dict[str, Any]
) -> list[str]:
    """Match premise-language context against elaborated binder type symbols.

    This is deliberately separate from conclusion matching: conclusion shape
    establishes that a theorem can close the requested goal, while binder
    symbols distinguish which of several conclusion-compatible theorems fits
    the premises the operator says are available.
    """
    binder_symbols = {
        symbol
        for binder in affordance.get("binders", [])
        for symbol in (
            binder.get("type_head", ""),
            *binder.get("type_symbols", []),
        )
        if symbol
    }
    binder_symbol_terms = set().union(
        *(search_terms(symbol) for symbol in binder_symbols)
    )
    return sorted(
        context_term
        for context_term in context_terms
        if any(
            context_term == symbol_term
            or (
                min(len(context_term), len(symbol_term)) >= 3
                and (
                    context_term.startswith(symbol_term)
                    or symbol_term.startswith(context_term)
                )
            )
            for symbol_term in binder_symbol_terms
        )
    )


def formal_goal_support_packet(
    query: str,
    limit: int,
    *,
    explicit_goal: bool = False,
) -> dict[str, Any]:
    """Rank theorem candidates by elaborated conclusion affordances."""
    request = support_goal_request(query)
    if request is None and explicit_goal:
        request = {
            "goal": query.strip(),
            "context": "",
            "extraction": "explicit_goal_argument",
        }
    if request is None:
        return {
            "kind": "formal_goal_support",
            "availability": "no_goal_expression",
            "query": query,
        }
    adjacency = lean_dependency_adjacency()
    if adjacency is None:
        return {
            "kind": "formal_goal_support",
            "availability": "unavailable_or_stale",
            "query": query,
            "goal_request": request,
            "validation": (
                "python3 scripts/build_lean_dependency_index.py --check"
            ),
        }
    generic_terms = {
        "applie",
        "cast",
        "erdo",
        "goal",
        "int",
        "nat",
        "prove",
        "real",
        "result",
        "set",
        "theorem",
    }
    goal_terms = {
        term
        for term in semantic_content_terms(request["goal"])
        if len(term) > 1 and term not in generic_terms
    }
    context_terms = {
        term
        for term in search_terms(request["context"])
        if len(term) > 1 and term not in generic_terms
    }
    context_phrase = re.sub(
        r"^(?:a|an|the)\s+",
        "",
        normalized_search_text(request["context"]),
    )
    shape_cues = formal_goal_shape_cues(request["goal"])
    declaration_rows = declaration_rows_by_qualified_name()
    ranked = []
    for handle, affordance in adjacency[
        "formal_type_affordances"
    ].items():
        node = adjacency["nodes_by_handle"][handle]
        if node["declaration_kind"] not in {
            "theorem",
            "lemma",
            "corollary",
            "proposition",
        }:
            continue
        declaration = declaration_rows.get(handle)
        if (
            declaration is None
            or not declaration_externally_addressable(declaration)
        ):
            continue
        symbol_terms = set().union(
            *(
                search_terms(symbol)
                for symbol in (
                    affordance["conclusion_head"],
                    *affordance["conclusion_symbols"],
                )
            )
        )
        statement_text = " ".join(
            str(value)
            for value in (
                declaration.get("signature"),
                declaration.get("docstring"),
            )
            if value
        )
        statement_terms = search_terms(statement_text)
        context_phrase_match = bool(
            context_phrase
            and context_phrase
            in normalized_search_text(statement_text)
        )
        shape_matches = formal_affordance_shape_matches(
            shape_cues, affordance
        )
        formal_matches = sorted(goal_terms & symbol_terms)
        goal_statement_matches = sorted(goal_terms & statement_terms)
        context_matches = sorted(context_terms & statement_terms)
        formal_context_matches = formal_context_symbol_matches(
            context_terms, affordance
        )
        if (
            not shape_matches
            and len(formal_matches) < 2
            and len(goal_statement_matches) < 2
        ):
            continue
        ranked.append(
            (
                # Applicability precedence: exact conclusion shape, then
                # elaborated premise-context coverage, then lexical/formal
                # goal evidence.  Telescope size is only a late tie-breaker.
                -len(shape_matches),
                -len(formal_context_matches),
                -len(formal_matches),
                -int(context_phrase_match),
                -len(context_matches),
                -len(goal_statement_matches),
                affordance["forall_binder_count"],
                handle,
                declaration,
                affordance,
                shape_matches,
                formal_context_matches,
                formal_matches,
                context_phrase_match,
                context_matches,
                goal_statement_matches,
            )
        )
    ranked.sort(key=lambda row: row[:8])
    candidates = []
    for rank_index, row in enumerate(ranked[:limit]):
        (
            _,
            _,
            _,
            _,
            _,
            _,
            _,
            handle,
            declaration,
            affordance,
            shape_matches,
            formal_context_matches,
            formal_matches,
            context_phrase_match,
            context_matches,
            goal_statement_matches,
        ) = row
        conclusion_symbols = affordance["conclusion_symbols"]
        candidates.append(
            {
                "kind": "declaration",
                **compact_declaration(declaration),
                "signature_excerpt": str(
                    declaration.get("signature") or ""
                )[:480],
                "formal_goal_rank": rank_index,
                "formal_affordance": {
                    "forall_binder_count": affordance[
                        "forall_binder_count"
                    ],
                    "conclusion_head": affordance[
                        "conclusion_head"
                    ],
                    "conclusion_symbols": conclusion_symbols[:16],
                    "omitted_conclusion_symbol_count": max(
                        0, len(conclusion_symbols) - 16
                    ),
                },
                "match_receipt": {
                    "shape_matches": shape_matches,
                    "formal_context_symbol_matches": (
                        formal_context_matches
                    ),
                    "formal_goal_term_matches": formal_matches,
                    "context_phrase_match": context_phrase_match,
                    "context_statement_matches": context_matches,
                    "goal_statement_matches": (
                        goal_statement_matches
                    ),
                },
                "lean_application_candidate": f"apply {handle}",
            }
        )
    return {
        "kind": "formal_goal_support",
        "availability": (
            "available" if candidates else "no_candidate_within_contract"
        ),
        "query": query,
        "goal_request": request,
        "goal_terms": sorted(goal_terms),
        "context_terms": sorted(context_terms),
        "goal_shape_cues": shape_cues,
        "candidate_count": len(ranked),
        "candidates": candidates,
        "omission_receipt": {
            "candidate_count": len(ranked),
            "emitted_candidate_count": len(candidates),
            "omitted_candidate_count": max(
                0, len(ranked) - len(candidates)
            ),
            "limit": limit,
        },
        "authority_posture": (
            "elaborated_conclusion_shape_and_symbol_candidate_ranking_"
            "requires_Lean_elaboration_at_the_target_goal_not_a_unification_"
            "or_applicability_proof"
        ),
        "validation": "python3 scripts/build_lean_dependency_index.py --check",
    }


def formal_application_obligations(
    query: str,
    goal_request: dict[str, str],
    affordance: dict[str, Any],
) -> dict[str, Any]:
    """Classify an application telescope against explicitly stated context."""
    context_terms = {
        term
        for term in semantic_content_terms(goal_request["context"])
        if len(term) > 1
    }
    normalized_query = normalized_search_text(query)
    obligations = []
    for binder in affordance["binders"]:
        type_terms = set().union(
            *(
                search_terms(symbol)
                for symbol in (
                    binder["type_head"],
                    *binder["type_symbols"],
                )
            )
        )
        context_matches = sorted(context_terms & type_terms)
        binder_name = binder["name"]
        name_mentioned = bool(
            binder_name
            and binder_name != "_"
            and re.search(
                rf"(?<![A-Za-z0-9_]){re.escape(binder_name)}"
                rf"(?![A-Za-z0-9_])",
                query,
            )
        )
        if binder["binder_info"] == "instance_implicit":
            status = "instance_synthesis_required"
        elif binder["is_proposition"]:
            status = (
                "context_matched_proposition_candidate"
                if context_matches
                else "unmatched_proposition_obligation"
            )
        else:
            status = (
                "term_parameter_mentioned"
                if name_mentioned
                else "term_parameter_required"
            )
        obligations.append(
            {
                **binder,
                "role": (
                    "proposition_hypothesis"
                    if binder["is_proposition"]
                    else "term_parameter"
                ),
                "status": status,
                "context_term_matches": context_matches,
                "binder_name_mentioned": name_mentioned,
                "type_symbols": binder["type_symbols"][:16],
                "omitted_type_symbol_count": max(
                    0, len(binder["type_symbols"]) - 16
                ),
            }
        )
    proposition_obligations = [
        row
        for row in obligations
        if row["role"] == "proposition_hypothesis"
        and row["binder_info"] != "instance_implicit"
    ]
    unmatched = [
        row
        for row in proposition_obligations
        if row["status"] == "unmatched_proposition_obligation"
    ]
    return {
        "query_context": goal_request["context"],
        "normalized_query": normalized_query,
        "obligations": obligations,
        "obligation_count": len(obligations),
        "term_parameter_count": sum(
            row["role"] == "term_parameter" for row in obligations
        ),
        "proposition_obligation_count": len(proposition_obligations),
        "context_matched_proposition_count": (
            len(proposition_obligations) - len(unmatched)
        ),
        "unmatched_proposition_count": len(unmatched),
        "application_status": (
            "blocked_by_unmatched_proposition_obligations"
            if unmatched
            else "all_proposition_obligations_have_context_matches"
        ),
        "authority_posture": (
            "binder_roles_and_type_shapes_from_elaborated_Lean_context_"
            "matching_is_lexical_navigation_not_local_context_unification"
        ),
    }


def formal_proof_plan_packet(
    query: str,
    limit: int,
    depth: int,
    *,
    explicit_goal: bool = False,
) -> dict[str, Any]:
    """Build a bounded, hypothesis-aware application and proof-spine packet."""
    support = formal_goal_support_packet(
        query,
        max(3, min(limit, MAX_SEMANTIC_CELLS)),
        explicit_goal=explicit_goal,
    )
    if support.get("availability") != "available":
        return {
            "kind": "formal_proof_plan",
            "availability": support.get("availability", "unavailable"),
            "query": query,
            "formal_goal_support": support,
        }
    terminal = support["candidates"][0]
    terminal_handle = terminal["qualified_name"]
    adjacency = lean_dependency_adjacency()
    if (
        adjacency is None
        or terminal_handle not in adjacency["formal_type_affordances"]
    ):
        return {
            "kind": "formal_proof_plan",
            "availability": "formal_telescope_unavailable",
            "query": query,
            "terminal_candidate": terminal,
        }
    affordance = adjacency["formal_type_affordances"][terminal_handle]
    obligations = formal_application_obligations(
        query,
        support["goal_request"],
        affordance,
    )
    cone = formal_dependency_proof_cone(
        terminal_handle,
        depth,
        max(limit, 24),
    )
    cone_edges = cone.get("edges", [])
    theorem_kinds = {"theorem", "lemma", "corollary", "proposition"}
    spine_steps = []
    for node in sorted(
        (
            row
            for row in cone.get("nodes", [])
            if row["handle"] != terminal_handle
            and row["declaration_kind"] in theorem_kinds
        ),
        key=lambda row: (-row["depth"], row["handle"]),
    ):
        step_affordance = adjacency["formal_type_affordances"].get(
            node["handle"]
        )
        spine_steps.append(
            {
                **node,
                "conclusion_head": (
                    step_affordance["conclusion_head"]
                    if step_affordance is not None
                    else None
                ),
                "forall_binder_count": (
                    step_affordance["forall_binder_count"]
                    if step_affordance is not None
                    else None
                ),
                "used_by": sorted(
                    edge["from"]
                    for edge in cone_edges
                    if edge["to"] == node["handle"]
                ),
            }
        )
    return {
        "kind": "formal_proof_plan",
        "availability": "available",
        "query": query,
        "goal_request": support["goal_request"],
        "terminal_candidate": terminal,
        "application": {
            "lean_tactic_candidate": (
                terminal["lean_application_candidate"]
            ),
            **obligations,
        },
        "exact_dependency_spine": {
            "edge_policy": cone.get("edge_policy"),
            "steps": spine_steps,
            "edges": [
                edge
                for edge in cone_edges
                if edge["from"] == terminal_handle
                or edge["to"] in {
                    step["handle"] for step in spine_steps
                }
            ],
            "omission_receipt": cone.get("omission_receipt"),
        },
        "plan_status": obligations["application_status"],
        "dynamic_transition_expansion": {
            "runtime_owner": "scripts/proof_state_compiler.py",
            "pilot_command": (
                "python3 scripts/proof_state_compiler.py --pilot-controls"
            ),
            "request_schema": "erdos249257-proof-state-request/1",
            "packet_schema": (
                "erdos249257-proof-state-compilation/1"
            ),
            "boundary": (
                "the static proof plan nominates candidates; only the "
                "runtime owner's pinned Lean application receipt can assert "
                "that a candidate produced particular subgoals or closed"
            ),
        },
        "authority_posture": (
            "terminal_and_dependency_edges_from_elaborated_Lean_environment_"
            "binder_context_matches_are_navigation_candidates_and_all_tactic_"
            "steps_require_Lean_elaboration"
        ),
        "validation": (
            "python3 scripts/dogfood_semantic_proof.py && "
            "python3 scripts/build_lean_dependency_index.py --check"
        ),
    }


def publication_contract() -> dict[str, Any]:
    return load("docs/publication_contract.json")


def publication_evidence() -> dict[str, Any]:
    return load("docs/publication_evidence.json")


def reviewed_result_family_rows(
    claims: dict[str, Any], problem_number: str | int
) -> list[dict[str, Any]]:
    """Read the per-problem result-family census from claim-registry authority."""
    token = str(problem_number)
    review_matrix = claims.get("external_verification_packet", {}).get(
        "review_matrix", []
    )
    for review_row in review_matrix:
        if str(review_row.get("problem")) != token:
            continue
        return [
            family
            for family in review_row.get("families", [])
            if isinstance(family, dict) and isinstance(family.get("id"), str)
        ]
    return []


def claim_registry_context_for_claim(
    claims: dict[str, Any], claim_id: str
) -> list[dict[str, Any]]:
    """Return canonical selection context that explicitly names a claim.

    Some source-current claims are intentionally not individual Comparator
    families.  The claims registry can still record their shared mathematical
    significance and next-method boundary in either the external review
    matrix or the publication-assembly contribution families.  Expose that
    existing authority on the claim-family route without promoting the
    grouping into a duplicate family or inferring significance from roster
    order.
    """
    contexts = []
    context_sources = (
        (
            "docs/claims.json::external_verification_packet.review_matrix",
            claims.get("external_verification_packet", {}).get(
                "review_matrix", []
            ),
        ),
        (
            "docs/claims.json::machine_readable_paper.publication_assembly.contribution_families",
            claims.get("machine_readable_paper", {})
            .get("publication_assembly", {})
            .get("contribution_families", []),
        ),
    )
    for source, rows in context_sources:
        for review_row in rows:
            if claim_id not in review_row.get("claim_ids", []):
                continue
            contexts.append(
                {
                    "id": review_row.get("id"),
                    "claim_ids": review_row.get("claim_ids", []),
                    "status_summary": review_row.get("status_summary"),
                    "prior_art_posture": review_row.get("prior_art_posture"),
                    "primary_narrative_owner": review_row.get(
                        "primary_narrative_owner"
                    ),
                    "source_route": review_row.get("source_route"),
                    "consumer_or_open_obligation": review_row.get(
                        "consumer_or_open_obligation"
                    ),
                    "view_decision": review_row.get("view_decision"),
                    "source": source,
                    "authority_posture": (
                        "claim_registry_selection_context_not_independent_"
                        "family_or_proof_authority"
                    ),
                }
            )
    return contexts


def reviewed_result_family_census(
    claims: dict[str, Any],
) -> list[dict[str, Any]]:
    """Return every reviewed result family, grouped by public problem number.

    ``docs/problems.json`` is a generated reader projection and may lag the
    claim registry while a family review is being assimilated.  Discovery
    counts therefore come from ``docs/claims.json`` and retain review-matrix
    order as the significance ordering supplied by that authority.
    """
    review_matrix = claims.get("external_verification_packet", {}).get(
        "review_matrix", []
    )
    census = []
    for review_row in review_matrix:
        try:
            problem_number = int(review_row["problem"])
        except (KeyError, TypeError, ValueError):
            continue
        families = reviewed_result_family_rows(claims, problem_number)
        dispositions = Counter(
            str(family.get("comparator_disposition") or "unspecified")
            for family in families
        )
        census.append(
            {
                "erdos_number": problem_number,
                "family_count": len(families),
                "family_ids": [family["id"] for family in families],
                "disposition_counts": dict(sorted(dispositions.items())),
                "source": (
                    "docs/claims.json::external_verification_packet."
                    "review_matrix"
                ),
                "ordering": "claim-registry review-matrix order",
            }
        )
    return census


def reviewed_result_family_source_rows(
    claims: dict[str, Any], problem_number: str | int, family_id: str
) -> list[dict[str, Any]]:
    """Join a reviewed family to its governed source records when bound.

    The review matrix is the complete family census, but some families are
    intentionally recorded there without declaration handles.  The external
    verification packet's ``main_results`` is the governed join for those
    rows: it carries the family id, source declaration, and (when available)
    corresponding reviewed claim id.  Keeping all matching rows matters when
    one family groups more than one independently reviewed declaration.
    """
    return [
        row
        for row in claims.get("external_verification_packet", {}).get(
            "main_results", []
        )
        if str(row.get("problem")) == str(problem_number)
        and row.get("review_family") == family_id
    ]


def reviewed_result_family_atlas_source_rows(
    family: Mapping[str, Any], module_path: str
) -> list[dict[str, Any]]:
    """Resolve review-matrix declarations when no main-result transport exists.

    The review matrix is the canonical family census.  A source-current family
    can be admitted there before its external-verification ``main_results``
    transport lands, so module navigation must still follow the exact declared
    atlas rows rather than silently dropping the family or inventing a wrapper.
    """
    rows: list[dict[str, Any]] = []
    seen: set[str] = set()
    for declaration in family.get("declarations", []):
        if not isinstance(declaration, str) or not declaration:
            continue
        for atlas_row in declaration_rows_for_handle(declaration):
            if atlas_row.get("module") != module_path:
                continue
            qualified_name = qualified_declaration_name(atlas_row)
            if qualified_name in seen:
                continue
            seen.add(qualified_name)
            rows.append(
                {
                    "original_declaration": qualified_name,
                    "original_source": module_path,
                    "wrapper_declaration": None,
                    "claim_id": None,
                    "source_authority": (
                        "docs/claims.json::external_verification_packet."
                        "review_matrix declarations resolved through "
                        "docs/declaration_atlas.json"
                    ),
                }
            )
    return rows


def reviewed_result_family_source_declarations(
    claims: dict[str, Any], problem_number: str | int, family_id: str
) -> list[str]:
    """Return exact declaration names from the family source authority."""
    claim_index = {
        claim["id"]: claim
        for claim in claims.get("claims", [])
        if isinstance(claim, Mapping) and isinstance(claim.get("id"), str)
    }
    declarations: list[str] = []
    for source_row in reviewed_result_family_source_rows(
        claims, problem_number, family_id
    ):
        claim_id = source_row.get("claim_id")
        claim = claim_index.get(claim_id) if isinstance(claim_id, str) else None
        if claim is not None:
            for declaration in claim.get("declarations", []):
                if (
                    isinstance(declaration, Mapping)
                    and isinstance(declaration.get("name"), str)
                ):
                    declarations.append(declaration["name"])
            continue
        original_declaration = source_row.get("original_declaration")
        if isinstance(original_declaration, str) and original_declaration:
            declarations.append(original_declaration.rsplit(".", 1)[-1])
    return list(dict.fromkeys(declarations))


def reviewed_result_family_index(
    claims: dict[str, Any],
) -> list[dict[str, Any]]:
    """Flatten the complete reviewed-family census for bounded discovery."""
    index = []
    for census_row in reviewed_result_family_census(claims):
        for rank, family_id in enumerate(census_row["family_ids"], 1):
            family = reviewed_result_family_rows(
                claims, census_row["erdos_number"]
            )[rank - 1]
            index.append(
                {
                    "erdos_number": census_row["erdos_number"],
                    "rank": rank,
                    "id": family_id,
                    "contribution_class": family.get("contribution_class"),
                    "evidence_mode": family.get("evidence_mode"),
                    "comparator_disposition": family.get(
                        "comparator_disposition"
                    ),
                    "problem_route": (
                        "python3 scripts/query_corpus.py --route erdos_"
                        f"{census_row['erdos_number']}"
                    ),
                }
            )
    return index


def current_corpus_census() -> dict[str, Any]:
    claims = load("docs/claims.json")
    atlas = load("docs/declaration_atlas.json")
    atlas_summary = atlas["summary"]
    effective_declaration_count = len(atlas_declarations(atlas))
    assembly = claims["machine_readable_paper"]["publication_assembly"]
    reviewed_families = reviewed_result_family_census(claims)
    return {
        "snapshot_kind": "current_worktree_navigation_state",
        "claims_source": "docs/claims.json",
        "declaration_atlas_source": "docs/declaration_atlas.json",
        "module_count": atlas_summary["module_count"],
        "declaration_count": atlas_summary["declaration_count"],
        "effective_query_declaration_count": effective_declaration_count,
        "suppressed_declaration_projection_row_count": (
            atlas_summary["declaration_count"] - effective_declaration_count
        ),
        "theorem_like_count": atlas_summary["theorem_like_count"],
        "generated_certificate_declaration_count": atlas_summary[
            "generated_certificate_declaration_count"
        ],
        "curated_claim_count": len(claims["claims"]),
        "contribution_family_count": len(assembly["contribution_families"]),
        "reviewed_result_family_count": sum(
            row["family_count"] for row in reviewed_families
        ),
        "reviewed_result_family_count_by_problem": {
            str(row["erdos_number"]): row["family_count"]
            for row in reviewed_families
        },
        "reviewed_result_family_ids_by_problem": {
            str(row["erdos_number"]): row["family_ids"]
            for row in reviewed_families
        },
        "reviewed_result_family_source": (
            "docs/claims.json::external_verification_packet.review_matrix"
        ),
        "status_count": len(claims["status_taxonomy"]),
        "remaining_open_proposition_count": len(
            claims["remaining_open_propositions"]
        ),
    }


def assurance_entrypoints(claims: dict[str, Any]) -> list[dict[str, Any]]:
    """Project exact external-assurance owners as bounded reading routes.

    Comparator and Palomar are adjacent but non-equivalent review surfaces.
    Keeping their route ids here lets a cold clone select either contract
    without scanning declarations or treating a file name as an authority.
    The route payloads are derived from their existing owner documents; they
    do not create a new verification, qualification, or publication verdict.
    """
    external = claims["external_verification_packet"]
    comparator = external["comparator"]
    reconciliation = load("docs/PALOMAR_POLICY_RECONCILIATION.json")
    qualification = reconciliation["qualification_decision"]
    requirement_counts: dict[str, int] = {}
    for row in reconciliation["requirements"]:
        status = str(row["status"])
        requirement_counts[status] = requirement_counts.get(status, 0) + 1
    return [
        {
            "id": "comparator_assurance",
            "route_kind": "external_assurance",
            "intent": (
                "Inspect the exact Comparator statement, axiom, replay, and "
                "receipt boundary without treating Comparator as novelty or "
                "independent-verification authority."
            ),
            "discovery_terms": [
                "comparator assurance",
                "comparator configuration",
                "external verification",
                "separately declared statement",
            ],
            "read": [
                "docs/EXTERNAL_VERIFICATION.md",
                "docs/claims.json::external_verification_packet",
                comparator["config"],
            ],
            "query_steps": [
                "python3 scripts/build_external_verification.py --check",
                "python3 scripts/test_external_verification.py",
            ],
            "authority_posture": (
                "configured_statement_axiom_and_kernel_assurance_not_novelty_"
                "significance_source_fidelity_or_peer_review"
            ),
            "assurance": {
                "status": external["review_status"],
                "config": comparator["config"],
                "challenge_module": comparator["challenge_module"],
                "solution_module": comparator["solution_module"],
                "permitted_axioms": comparator["permitted_axioms"],
                "runtime_receipt": external["receipt_contract"]["runtime_output"],
                "public_wording": external["receipt_contract"]["public_wording"],
                "forbidden_wording": external["receipt_contract"]["forbidden_wording"],
                "boundary": external["boundary"],
            },
        },
        {
            "id": "palomar_qualification",
            "route_kind": "external_assurance",
            "intent": (
                "Inspect the current Palomar qualification decision, exact "
                "remaining gates, and operator-owned submission boundary."
            ),
            "discovery_terms": [
                "palomar qualification",
                "palomar readiness",
                "palomar submission",
                "registry qualification",
            ],
            "read": [
                "docs/PALOMAR_QUALIFICATION.md",
                "docs/PALOMAR_POLICY_RECONCILIATION.json",
                "docs/PALOMAR_RESULT_SHOWCASE.json",
            ],
            "query_steps": [
                "python3 scripts/check_palomar_qualification.py --json",
                "python3 scripts/test_palomar_qualification.py",
            ],
            "authority_posture": (
                "repository_local_qualification_projection_not_palomar_"
                "acceptance_registration_or_publication_authority"
            ),
            "assurance": {
                "decision": qualification["decision"],
                "reason": qualification["reason"],
                "readiness_rule": qualification["readiness_rule"],
                "requirement_status_counts": dict(sorted(requirement_counts.items())),
                "safe_local_repairs_remaining": qualification[
                    "safe_local_repairs_remaining"
                ],
                "operator_only_residuals": qualification[
                    "operator_only_residuals"
                ],
            },
        },
    ]


def all_entrypoints(claims: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        *claims["machine_readable_paper"]["entrypoints"],
        *publication_contract().get("entrypoints", []),
        *assurance_entrypoints(claims),
    ]


def formal_source_identity(claims: dict[str, Any]) -> dict[str, Any]:
    """Return the immutable Lean checkpoint that owns the claim registry."""
    release = claims["release"]
    return {
        **release["formal_source"],
        "repository": release["repository"],
    }


def lean_source_identity_for_paper(
    claims: dict[str, Any], paper_source: str | None
) -> dict[str, Any]:
    """Return the immutable Lean identity used by one authored paper.

    Every authored paper is pinned to the current committed formal-source
    checkpoint.  A companion that cites post-tag modules cannot truthfully
    retain the older release tag as its source identity.
    """
    return formal_source_identity(claims)


@lru_cache(maxsize=1)
def artifact_inventory() -> list[dict[str, Any]]:
    """Flatten the descriptor's registered content identities into handles."""
    descriptor = load("docs/corpus_descriptor.json")
    inventory: list[dict[str, Any]] = []
    follow_by_id = {
        "machine_readable_paper": ["--claim <claim_id>", "--open <remaining_open.id>"],
        "claims_document": ["--claim <claim_id>", "--open <remaining_open.id>"],
        "declaration_atlas": ["--declaration <Lean_name>", "--source <module.lean:line>"],
        "methodology_contract": ["docs/methodology.json"],
        "bounded_orientation": ["--route <route_id>"],
        "human_exposition": ["--paper-anchor <TeX_label_or_source_ref>"],
        "technical_companion": ["--paper-anchor <TeX_label_or_source_ref>"],
        "paper_source_sigils": ["--module <paper_sigil>"],
    }
    for artifact_id, row in descriptor["identity"]["content"].items():
        common = {
            "artifact_id": artifact_id,
            "artifact_role": row.get("artifact_role", artifact_id),
            "authority_posture": row.get(
                "authority_posture", "registered_navigation_artifact_not_proof_authority"
            ),
            "follow": follow_by_id.get(artifact_id, []),
            "validation": "python3 scripts/build_corpus_descriptor.py --check",
        }
        if row.get("path") and row.get("content_digest"):
            path = row["path"]
            file_path = path.split("::", 1)[0]
            resolved_path = ROOT / file_path
            inventory.append(
                {
                    **common,
                    "artifact_kind": "json_fragment" if "::" in path else "registered_file",
                    "artifact_handle": path,
                    "file_path": file_path,
                    "fragment": path.split("::", 1)[1] if "::" in path else None,
                    "content_digest": row["content_digest"],
                    "availability": (
                        "present" if resolved_path.is_file() else "missing"
                    ),
                    "size_bytes": (
                        resolved_path.stat().st_size
                        if resolved_path.is_file()
                        else None
                    ),
                }
            )
        for variant in ("source", "rendered"):
            path = row.get(f"{variant}_path")
            digest = row.get(f"{variant}_content_digest")
            if path and digest:
                resolved_path = ROOT / path
                inventory.append(
                    {
                        **common,
                        "artifact_kind": f"authored_paper_{variant}",
                        "artifact_handle": path,
                        "file_path": path,
                        "fragment": None,
                        "content_digest": digest,
                        "availability": (
                            "present" if resolved_path.is_file() else "missing"
                        ),
                        "size_bytes": (
                            resolved_path.stat().st_size
                            if resolved_path.is_file()
                            else None
                        ),
                    }
                )
    return sorted(inventory, key=lambda row: (row["artifact_handle"], row["artifact_id"]))


def artifact_packet(handle: str) -> dict[str, Any]:
    matches = [
        row
        for row in artifact_inventory()
        if handle in (row["artifact_handle"], row["content_digest"])
    ]
    if not matches:
        raise KeyError(f"unknown registered artifact or content digest: {handle}")
    return {
        "kind": "artifact",
        "authority_posture": "descriptor_registered_content_identity_not_proof_authority",
        "handle": handle,
        "matches": matches,
        "cardinality_receipt": {
            "match_count": len(matches),
            "complete": True,
            "owner": "docs/corpus_descriptor.json::identity.content",
        },
        "expansion": "docs/corpus_descriptor.json",
        "validation": "python3 scripts/build_corpus_descriptor.py --check",
    }


def publication_artifact_packet(artifact_id: str) -> dict[str, Any]:
    contract = publication_contract()
    artifact = next(
        (row for row in contract["artifacts"] if row["id"] == artifact_id),
        None,
    )
    if artifact is None:
        raise KeyError(f"unknown publication artifact id: {artifact_id}")
    identities = []
    for variant in ("source", "rendered"):
        path = artifact[f"{variant}_path"]
        expected = artifact[f"{variant}_content_digest"]
        actual = "sha256:" + hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
        identities.append(
            {
                "variant": variant,
                "path": path,
                "expected_content_digest": expected,
                "current_content_digest": actual,
                "status": "current" if actual == expected else "drifted",
            }
        )
    return {
        "kind": "publication_artifact",
        "authority_posture": contract["authority_posture"],
        "artifact": artifact,
        "content_identities": identities,
        "content_identity_status": (
            "current"
            if all(row["status"] == "current" for row in identities)
            else "drifted"
        ),
        "coverage_contract": contract["coverage_contract"],
        "reproducibility": contract["reproducibility"],
        "validation": "python3 scripts/check_publication_contract.py",
    }


def publication_evidence_packet(mutation_id: str) -> dict[str, Any]:
    receipt = publication_evidence()
    evaluation_snapshot = receipt["evaluation"]["corpus_snapshot"]
    current_snapshot = current_corpus_census()
    numeric_fields = [
        key
        for key, value in evaluation_snapshot.items()
        if isinstance(value, int) and not isinstance(value, bool)
    ]
    snapshot_delta = {
        key: current_snapshot[key] - evaluation_snapshot[key]
        for key in numeric_fields
    }
    mutation = None
    if mutation_id != "summary":
        mutation = next(
            (
                row
                for row in receipt["evaluation"]["mutations"]
                if row["id"].casefold() == mutation_id.casefold()
            ),
            None,
        )
        if mutation is None:
            raise KeyError(f"unknown publication mutation id: {mutation_id}")
    return {
        "kind": "publication_evidence",
        "authority_posture": receipt["authority_posture"],
        "record_id": receipt["record_id"],
        "record_kind": receipt["record_kind"],
        "publication_artifact_id": receipt["publication_artifact_id"],
        "checkpoint": receipt["evaluation"]["checkpoint"],
        "baseline": receipt["evaluation"]["baseline"],
        "corpus_snapshot": evaluation_snapshot,
        "current_corpus_census": current_snapshot,
        "time_axis": {
            "same_as_evaluation_snapshot": all(
                delta == 0 for delta in snapshot_delta.values()
            ),
            "current_minus_evaluation": snapshot_delta,
            "rule": (
                "Use corpus_snapshot for evaluation-time claims and "
                "current_corpus_census for present-tense repository claims."
            ),
        },
        "summary": receipt["evaluation"]["summary"],
        "mutation": mutation,
        "post_repair": receipt["post_repair"],
        "provenance": receipt["provenance"],
        "threats_to_validity": receipt["threats_to_validity"],
        "expansion": "docs/publication_evidence.json",
        "validation": "python3 scripts/check_publication_contract.py",
    }


def compact_claim(claim: dict[str, Any]) -> dict[str, Any]:
    return {
        "id": claim["id"],
        "label": claim["label"],
        "status": claim["status"],
        "paper_label": claim.get("paper_label"),
    }


def compact_status_claim(claim: dict[str, Any]) -> dict[str, Any]:
    """Keep a status browse packet bounded while preserving its exact ceilings."""
    row = {
        **compact_claim(claim),
        "statement_excerpt": claim["statement"][:280],
        "declaration_count": len(claim["declarations"]),
    }
    if claim.get("remaining_open_proposition_ids"):
        row["remaining_open_proposition_ids"] = claim[
            "remaining_open_proposition_ids"
        ]
    if claim.get("bounded_domain"):
        row["bounded_domain"] = claim["bounded_domain"]
    return row


@lru_cache(maxsize=1)
def paper_anchor_inventory() -> list[dict[str, Any]]:
    """Derive typed human-paper anchors without promoting them to claim authority."""
    claims = load("docs/claims.json")
    paper_rows = public_paper_rows(claims)
    claims_by_label: dict[str, list[dict[str, Any]]] = {}
    for claim in claims["claims"]:
        label = claim.get("paper_label")
        if label:
            claims_by_label.setdefault(label, []).append(compact_claim(claim))
    open_by_anchor = {
        (
            row["paper_anchor"]["source"],
            row["paper_anchor"]["environment"],
            row["paper_anchor"]["title"],
        ): row
        for row in claims["remaining_open_propositions"]
        if row.get("paper_anchor")
    }

    inventory: list[dict[str, Any]] = []
    for paper_row in paper_rows:
        relative = paper_row["source"]
        lean_source_identity = lean_source_identity_for_paper(claims, relative)
        path = ROOT / relative
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8")
        lines = text.splitlines()
        theorem_sources = [text]
        for input_match in re.finditer(r"\\input\{([^}]+)\}", text):
            input_path = path.parent / input_match.group(1)
            if input_path.suffix == "":
                input_path = input_path.with_suffix(".tex")
            if input_path.is_file():
                theorem_sources.append(input_path.read_text(encoding="utf-8"))
        environments = set(
            re.findall(
                r"\\newtheorem\*?\{([^}]+)\}",
                "\n".join(theorem_sources),
            )
        )
        starts: list[dict[str, Any]] = []

        section_pattern = re.compile(
            r"\\(?P<kind>section|subsection|subsubsection|paragraph)\{(?P<title>[^\n}]*)\}"
            r"[^\n]*(?:\n[ \t]*)?\\label\{(?P<label>[^}]+)\}"
        )
        for match in section_pattern.finditer(text):
            starts.append(
                {
                    "offset": match.start(),
                    "anchor_kind": match.group("kind"),
                    "title": match.group("title"),
                    "label": match.group("label"),
                    "environment": None,
                }
            )

        # Standalone problem notes may present their result inventory as
        # labelled enumerate items rather than theorem environments.  Scan
        # those only when the paper row supplies an explicit allowlist: this
        # makes the selected claim anchors queryable without turning every
        # incidental list item in every companion into a public paper anchor.
        if paper_row.get("anchor_label_allowlist") is not None:
            item_pattern = re.compile(
                r"\\item(?:\[[^]]*\])?[^\n]*?\\label\{(?P<label>[^}]+)\}"
            )
            for match in item_pattern.finditer(text):
                starts.append(
                    {
                        "offset": match.start(),
                        "anchor_kind": "enumerated_result",
                        "title": None,
                        "label": match.group("label"),
                        "environment": None,
                    }
                )

            # A dedicated note can put an exact source-linked explanation in
            # an unlabelled subsection or paragraph.  Keep those starts
            # available for the source-ref fallback below; they are admitted
            # only when their own region contains an authored source link.
            labelled_offsets = {start["offset"] for start in starts}
            unlabeled_pattern = re.compile(
                r"\\(?P<kind>section|subsection|subsubsection|paragraph)"
                r"\{(?P<title>[^\n}]*)\}"
            )
            for match in unlabeled_pattern.finditer(text):
                if match.start() in labelled_offsets:
                    continue
                starts.append(
                    {
                        "offset": match.start(),
                        "anchor_kind": match.group("kind"),
                        "title": match.group("title"),
                        "label": None,
                        "environment": None,
                    }
                )

        if environments:
            environment_pattern = re.compile(
                r"\\begin\{(?P<environment>"
                + "|".join(re.escape(name) for name in sorted(environments))
                + r")\}(?:\[(?P<title>[^]]*)\])?"
            )
            for match in environment_pattern.finditer(text):
                environment = match.group("environment")
                end_marker = rf"\end{{{environment}}}"
                end = text.find(end_marker, match.end())
                if end < 0:
                    end = match.end()
                else:
                    end += len(end_marker)
                body = text[match.start():end]
                label_match = re.search(r"\\label\{([^}]+)\}", body)
                starts.append(
                    {
                        "offset": match.start(),
                        "anchor_kind": "formal_environment",
                        "title": match.group("title"),
                        "label": label_match.group(1) if label_match else None,
                        "environment": environment,
                    }
                )

        if paper_row.get("anchor_label_allowlist") is not None:
            first_anchor_offset = min(
                (start["offset"] for start in starts), default=len(text)
            )
            opening_region = text[:first_anchor_offset]
            if re.search(
                r"\\(?:lref|lrefx|lword|mref|mword|lloc|mloc)\{[^}]+\}\{\d+\}",
                opening_region,
            ):
                # Some dedicated notes put their formal-source guide in the
                # unlabelled problem preamble.  Give that exact source-link
                # region a stable source-ref handle so result families can
                # return to it without inventing a paper label.
                starts.append(
                    {
                        "offset": 0,
                        "anchor_kind": "preamble",
                        "title": "Opening guide to the formal sources",
                        "label": None,
                        "environment": None,
                    }
                )

        starts.sort(key=lambda row: row["offset"])
        for index, start in enumerate(starts):
            label_allowlist = paper_row.get("anchor_label_allowlist")
            region_end = starts[index + 1]["offset"] if index + 1 < len(starts) else len(text)
            region = text[start["offset"]:region_end]
            source_link_pattern = (
                r"\\(?P<macro>lref|lrefx|lword|mref|mword|lloc|mloc)"
                r"\{(?P<file>[^}]+)\}\{(?P<line>\d+)\}\s*"
                r"(?:\{(?P<name>[^}]*)\})?\s*"
                r"(?:\{(?P<label>(?:[^{}]|\{[^{}]*\})*)\})?"
            )
            has_source_links = re.search(source_link_pattern, region) is not None
            source_ref_fallback = (
                label_allowlist is not None
                and has_source_links
                and start["label"] not in label_allowlist
            )
            # Dedicated notes may allowlist only their selected result labels,
            # but labelled appendix sections remain canonical structural
            # anchors.  In particular, the formal-source appendix can contain
            # the exact \\lref/\\lword declaration links for a family whose
            # result prose has no separately labelled theorem environment.  A
            # labelled section with an authored source link is the same kind
            # of exact return surface: hiding it would make a declaration-
            # bearing family appear to have no paper route.
            is_structural_navigation = start["anchor_kind"] == "preamble" or (
                start["anchor_kind"] in {
                    "section",
                    "subsection",
                    "subsubsection",
                    "paragraph",
                }
                and (
                    source_ref_fallback
                    or (
                        isinstance(start["label"], str)
                        and start["label"].startswith("app:")
                    )
                )
            ) or (
                start["anchor_kind"] == "formal_environment"
                and source_ref_fallback
            )
            if (
                label_allowlist is not None
                and start["label"] not in label_allowlist
                and not is_structural_navigation
            ):
                continue
            line = text.count("\n", 0, start["offset"]) + 1
            source_ref_fallback = source_ref_fallback or (
                label_allowlist is not None
                and is_structural_navigation
                and start["label"] not in label_allowlist
            )
            original_label = start["label"]
            # A source-linked fallback is a stable coordinate, not a newly
            # registered paper label.  Dedicated notes can reuse labels from
            # other papers (for example ``res:rank``); keeping the TeX label
            # here would make the global label index ambiguous.  The exact
            # source coordinate remains queryable through canonical_handle.
            label = None if source_ref_fallback else original_label
            source_ref = f"{relative}:{line}"
            attached_claims = sorted(
                claims_by_label.get(original_label, [])
                if not source_ref_fallback
                else [],
                key=lambda row: row["id"],
            )
            open_proposition = open_by_anchor.get(
                (relative, start["environment"], start["title"])
            )
            attached_open_propositions = [open_proposition] if open_proposition else []
            if attached_open_propositions:
                anchor_class = "remaining_open_proposition_anchor"
            elif attached_claims:
                anchor_class = "registered_claim_anchor"
            elif start["anchor_kind"] == "formal_environment":
                anchor_class = "authored_formal_anchor_without_registered_claim"
            else:
                anchor_class = "section_navigation_anchor"

            source_links = []
            for link in re.finditer(source_link_pattern, region):
                file_name = link.group("file")
                macro = link.group("macro")
                if file_name.startswith("Erdos249257/"):
                    module = file_name
                elif file_name.startswith("ErdosProblems/"):
                    module = file_name
                elif re.match(r"Erdos\d+/", file_name):
                    module = f"ErdosProblems/{file_name}"
                elif macro.startswith("m"):
                    module = f"ErdosProblems/{file_name}"
                else:
                    module = f"Erdos249257/{file_name}"
                source_links.append(
                    {
                        "edge_kind": "authored_source_link",
                        "macro": macro,
                        "module": module,
                        "line": int(link.group("line")),
                        "source_ref": f"{module}:{link.group('line')}",
                        "source_identity": dict(lean_source_identity),
                        "declaration": link.group("name") or None,
                        "display_label": link.group("label") or None,
                    }
                )

            canonical_handle = (
                source_ref if is_structural_navigation else (label or source_ref)
            )
            inventory.append(
                {
                    "canonical_handle": canonical_handle,
                    "label": label,
                    "paper": {
                        "label": label,
                        "source": relative,
                        "line": line,
                        "source_ref": source_ref,
                        "rendered": paper_row["rendered"],
                        "lean_source_identity": dict(lean_source_identity),
                    },
                    "anchor_kind": start["anchor_kind"],
                    "environment": start["environment"],
                    "title": start["title"],
                    "anchor_class": anchor_class,
                    "authority_posture": "authored_exposition_navigation_not_proof_authority",
                    "attached_claims": attached_claims,
                    "attached_open_propositions": attached_open_propositions,
                    "source_links": source_links,
                }
            )

    for index, row in enumerate(inventory):
        same_paper_before = [
            candidate
            for candidate in inventory[:index]
            if candidate["paper"]["source"] == row["paper"]["source"]
        ]
        same_paper_after = [
            candidate
            for candidate in inventory[index + 1:]
            if candidate["paper"]["source"] == row["paper"]["source"]
        ]
        row["anchor_neighbourhood"] = {
            "previous": same_paper_before[-1]["canonical_handle"] if same_paper_before else None,
            "next": same_paper_after[0]["canonical_handle"] if same_paper_after else None,
        }
        row["cardinality_receipt"] = {
            "attached_claim_count": len(row["attached_claims"]),
            "attached_open_proposition_count": len(row["attached_open_propositions"]),
            "source_link_count": len(row["source_links"]),
            "complete": True,
        }
    return inventory


def public_paper_rows(claims: dict[str, Any]) -> list[dict[str, Any]]:
    """Merge claim-registry papers with every dedicated problem-note source.

    The claim registry owns publication identity, while ``docs/problems.json``
    is the generated public roster of dedicated notes.  A note can be present
    in the roster before it is listed as a companion, so anchor discovery must
    consume both surfaces and de-duplicate by exact TeX source path.
    """
    rows_by_source: dict[str, dict[str, Any]] = {}

    def add(row: dict[str, Any]) -> None:
        source = row.get("source")
        if not isinstance(source, str) or not source:
            return
        candidate = dict(row)
        existing = rows_by_source.get(source)
        if existing is None:
            rows_by_source[source] = candidate
            return
        for key, value in candidate.items():
            if existing.get(key) is None and value is not None:
                existing[key] = value

    machine_paper = claims["machine_readable_paper"]["paper"]
    add(machine_paper)
    for row in machine_paper.get("companion_sources", []):
        if isinstance(row, dict):
            add(row)

    for problem in load("docs/problems.json").get("problems", []):
        paper = problem.get("paper")
        note = problem.get("note")
        if not isinstance(paper, dict) or not isinstance(note, dict):
            continue
        source = paper.get("source") or note.get("source_path")
        rendered = note.get("rendered_path") or paper.get("pdf")
        if (
            isinstance(rendered, str)
            and not (ROOT / rendered).is_file()
            and (ROOT / "paper" / rendered).is_file()
        ):
            rendered = f"paper/{rendered}"
        add(
            {
                "title": paper.get("title") or note.get("title"),
                "source": source,
                "rendered": rendered,
                "role": note.get("authority_posture") or "dedicated_problem_note",
            }
        )
    return list(rows_by_source.values())


def paper_anchor_routes_for_declarations(
    source: str | None, declarations: list[str]
) -> list[dict[str, Any]]:
    """Find exact paper anchors whose authored source links name a family declaration."""
    if not source or not declarations:
        return []
    declaration_names = {
        declaration.rsplit(".", 1)[-1] for declaration in declarations
    }
    routes = []
    for anchor in paper_anchor_inventory():
        if anchor["paper"]["source"] != source:
            continue
        matched = sorted(
            {
                link["declaration"]
                for link in anchor["source_links"]
                if link.get("declaration") in declaration_names
            }
        )
        if not matched:
            continue
        routes.append(
            {
                "canonical_handle": anchor["canonical_handle"],
                "source_ref": anchor["paper"]["source_ref"],
                "command": (
                    "python3 scripts/query_corpus.py --paper-anchor "
                    f"{anchor['canonical_handle']}"
                ),
                "matched_declarations": matched,
            }
        )
    return routes


def paper_source_packet(source: str) -> dict[str, Any]:
    """List every discovered anchor for one dedicated paper source."""
    rows = [row for row in public_paper_rows(load("docs/claims.json")) if row["source"] == source]
    if not rows:
        raise KeyError(f"unknown public paper source: {source}")
    anchors = [
        {
            "canonical_handle": anchor["canonical_handle"],
            "label": anchor["label"],
            "source_ref": anchor["paper"]["source_ref"],
            "anchor_kind": anchor["anchor_kind"],
            "anchor_class": anchor["anchor_class"],
            "title": anchor["title"],
            "attached_claim_count": len(anchor["attached_claims"]),
            "attached_open_proposition_count": len(
                anchor["attached_open_propositions"]
            ),
            "source_link_count": len(anchor["source_links"]),
            "follow": (
                "python3 scripts/query_corpus.py --paper-anchor "
                f"{anchor['canonical_handle']}"
            ),
        }
        for anchor in paper_anchor_inventory()
        if anchor["paper"]["source"] == source
    ]
    paper = rows[0]
    return {
        "kind": "paper_source",
        "authority_posture": "paper_source_anchor_discovery_not_proof_authority",
        "paper": {
            "source": source,
            "title": paper.get("title"),
            "rendered": paper.get("rendered"),
            "role": paper.get("role"),
        },
        "anchors": anchors,
        "coverage_receipt": {
            "anchor_count": len(anchors),
            "complete": True,
            "source": "query_corpus.paper_anchor_inventory",
        },
        "follow": {
            "anchor": (
                "python3 scripts/query_corpus.py --paper-anchor "
                "<anchor canonical_handle>"
            ),
            "problem_route": (
                "python3 scripts/query_corpus.py --route erdos_<problem_number>"
            ),
        },
        "validation": "python3 scripts/check_release.py",
    }


@lru_cache(maxsize=1)
def paper_label_index() -> dict[str, dict[str, Any]]:
    index: dict[str, dict[str, Any]] = {}
    for anchor in paper_anchor_inventory():
        # Appendix sections are navigation handles, not registered paper
        # labels.  Their labels (for example, ``app:index``) can repeat in
        # separate papers and must not shadow claim labels or make claim
        # lookup ambiguous.
        if anchor["anchor_class"] == "section_navigation_anchor":
            continue
        label = anchor["label"]
        if label is None:
            continue
        if label in index:
            raise ValueError(
                f"duplicate paper label {label!r}: "
                f"{index[label]['source_ref']} and {anchor['paper']['source_ref']}"
            )
        index[label] = anchor["paper"]
    return index


def paper_coordinate(label: str | None, index: dict[str, dict[str, Any]]) -> dict[str, Any] | None:
    if label is None:
        return None
    coordinate = index.get(label)
    if coordinate is None:
        return {
            "label": label,
            "source": None,
            "line": None,
            "source_ref": None,
            "rendered": None,
            "availability": "authored_source_unavailable_in_worktree",
            "authority_posture": (
                "unresolved_navigation_anchor_not_claim_or_proof_authority"
            ),
        }
    return coordinate


def claim_packet(claim_id: str) -> dict[str, Any]:
    claims = load("docs/claims.json")
    claim_index = {row["id"]: row for row in claims["claims"]}
    open_index = {
        row["id"]: row for row in claims["remaining_open_propositions"]
    }
    claim = claim_index.get(claim_id)
    if claim is None:
        raise KeyError(f"unknown claim id: {claim_id}")
    graph = claims["machine_readable_paper"]["argument_graph"]
    label_index = paper_label_index()
    edges = graph["edges"]
    incoming = [row for row in edges if row["to"] == claim_id]
    outgoing = [row for row in edges if row["from"] == claim_id]

    def resolved_edge(edge: dict[str, Any], neighbour_key: str) -> dict[str, Any]:
        row = {
            "relation": edge["relation"],
            "relation_meaning": graph["edge_semantics"][edge["relation"]],
            "neighbour": compact_claim(claim_index[edge[neighbour_key]]),
        }
        if "remaining_open_effect" in edge:
            row["remaining_open_effect"] = edge["remaining_open_effect"]
        return row

    open_ids = set(claim.get("remaining_open_proposition_ids", []))
    programme_routes = [
        row
        for row in all_entrypoints(claims)
        if row.get("route_kind") == "mathematical_programme"
        and claim_id in row.get("core_claim_ids", [])
    ]
    programme_open_ids = {
        open_id
        for route in programme_routes
        for open_id in route.get("remaining_open_proposition_ids", [])
    }
    claim_paper = paper_coordinate(claim.get("paper_label"), label_index)
    programme_contexts = []
    for route in programme_routes:
        context = {
            "id": route["id"],
            "title": route["title"],
            "claim_ceiling": route["claim_ceiling"],
            "problem_targets": [
                compact_claim(claim_index[target_id])
                for target_id in route.get("problem_target_claim_ids", [])
            ],
            "remaining_open_proposition_ids": route.get(
                "remaining_open_proposition_ids", []
            ),
            "follow": f"python3 scripts/query_corpus.py --route {route['id']}",
        }
        problem_number = route_memory_problem_number(route)
        if problem_number is not None:
            context["route_memory"] = {
                "problem_number": problem_number,
                "command": (
                    "python3 scripts/query_route_memory.py --problem "
                    f"{problem_number} --route {route['id']}"
                ),
                "authority_posture": (
                    "derived_resume_handoff_not_claim_or_proof_authority"
                ),
                "identity_contract": (
                    "The route-memory command binds this route to the selected "
                    "problem and current tracked source digests before resume."
                ),
            }
        programme_contexts.append(context)

    return {
        "kind": "claim",
        "authority_posture": "navigation_projection_not_proof_authority",
        "lean_source_identity": lean_source_identity_for_paper(
            claims, claim_paper and claim_paper.get("source")
        ),
        "claim": claim,
        "route_memory": claim_route_memory_projection(claim_id, claims),
        "incoming_edges": incoming,
        "outgoing_edges": outgoing,
        "argument_neighbourhood": {
            "incoming": [resolved_edge(row, "from") for row in incoming],
            "outgoing": [resolved_edge(row, "to") for row in outgoing],
            "exhaustive": "docs/claims.json::machine_readable_paper.argument_graph",
            "follow": "python3 scripts/query_corpus.py --claim <neighbour_id>",
        },
        "remaining_open_propositions": [
            open_index[open_id] for open_id in sorted(open_ids)
        ],
        "programme_contexts": programme_contexts,
        "wider_programme_open_propositions": [
            open_index[open_id]
            for open_id in sorted(programme_open_ids - open_ids)
        ],
        "paper": claim_paper,
        "validation": "python3 scripts/check_release.py",
    }


def paper_anchor_packet(handle: str, kind: str = "paper_anchor") -> dict[str, Any]:
    matches = [
        row
        for row in paper_anchor_inventory()
        if handle in (row["canonical_handle"], row["label"], row["paper"]["source_ref"])
    ]
    if not matches:
        raise KeyError(f"unknown paper anchor: {handle}")
    if len(matches) != 1:
        locations = ", ".join(sorted(row["paper"]["source_ref"] for row in matches))
        raise ValueError(f"ambiguous paper anchor {handle!r}: {locations}")
    anchor = matches[0]
    claims = load("docs/claims.json")
    attached_claim_ids = {row["id"] for row in anchor["attached_claims"]}
    attached_open_ids = {
        row["id"] for row in anchor["attached_open_propositions"]
    }
    route_memory_bindings = []
    for route in all_entrypoints(claims):
        if route.get("route_kind") != "mathematical_programme":
            continue
        if not (
            attached_claim_ids.intersection(
                route.get("core_claim_ids", [])
                + route.get("problem_target_claim_ids", [])
            )
            or attached_open_ids.intersection(
                route.get("remaining_open_proposition_ids", [])
            )
        ):
            continue
        problem_number = route_memory_problem_number(route)
        if problem_number is None:
            continue
        route_memory_bindings.append(
            {
                "route_id": route["id"],
                "problem_number": problem_number,
                "command": (
                    "python3 scripts/query_route_memory.py --problem "
                    f"{problem_number} --route {route['id']}"
                ),
                "authority_posture": (
                    "derived_resume_handoff_not_claim_or_proof_authority"
                ),
                "identity_contract": (
                    "The route-memory command binds this route to the selected "
                    "problem and current tracked source digests before resume."
                ),
            }
        )
    route_memory = {
        "status": "bound" if route_memory_bindings else "unbound",
        "bindings": route_memory_bindings,
        "authority_posture": "derived_resume_handoff_not_claim_or_proof_authority",
        "boundary": (
            "Route-memory bindings are navigation handoffs only; they do not "
            "promote paper anchors or replace claim and Lean authority."
        ),
    }
    if not route_memory_bindings:
        route_memory["unbound_reason"] = (
            "anchor attachments do not resolve to a canonical mathematical "
            "programme; no resume route was invented"
        )
    return {
        "kind": kind,
        "authority_posture": "navigation_projection_not_proof_authority",
        "canonical_handle": anchor["canonical_handle"],
        "paper": anchor["paper"],
        "lean_source_identity": anchor["paper"]["lean_source_identity"],
        "anchor_class": anchor["anchor_class"],
        "environment": anchor["environment"],
        "title": anchor["title"],
        "attached_claims": anchor["attached_claims"],
        "attached_open_propositions": anchor["attached_open_propositions"],
        "source_links": anchor["source_links"],
        "anchor_neighbourhood": anchor["anchor_neighbourhood"],
        "route_memory": route_memory,
        "attachment_receipt": {
            "claim_count": len(anchor["attached_claims"]),
            "open_proposition_count": len(anchor["attached_open_propositions"]),
            "source_link_count": len(anchor["source_links"]),
            "complete": True,
            "owners": [anchor["paper"]["source"], "docs/claims.json"],
        },
        "follow": {
            "claim": "python3 scripts/query_corpus.py --claim <attached_claim_id>",
            "declaration": "python3 scripts/query_corpus.py --declaration <source_link.declaration>",
            "adjacent_anchor": "python3 scripts/query_corpus.py --paper-anchor <canonical_handle>",
        },
        "validation": "python3 scripts/check_release.py",
    }


def paper_label_packet(label: str) -> dict[str, Any]:
    if label not in paper_label_index():
        claims = load("docs/claims.json")
        attached_claims = [
            compact_claim(claim)
            for claim in claims["claims"]
            if claim.get("paper_label") == label
        ]
        if not attached_claims:
            raise ValueError(f"unknown paper label: {label}")
        return {
            "kind": "paper_label",
            "authority_posture": (
                "registered_claim_label_with_authored_source_unavailable"
            ),
            "canonical_handle": label,
            "paper": paper_coordinate(label, paper_label_index()),
            "attached_claims": attached_claims,
            "attached_open_propositions": [],
            "source_links": [],
            "availability": "authored_source_unavailable_in_worktree",
            "proof_authority": "Lean source checked by the pinned Lean kernel",
            "follow": {
                "claim": (
                    "python3 scripts/query_corpus.py --claim "
                    "<attached_claim_id>"
                ),
                "artifact": (
                    "python3 scripts/query_corpus.py --artifact "
                    "<registered_paper_path>"
                ),
            },
        }
    return paper_anchor_packet(label, kind="paper_label")


def open_proposition_packet(open_id: str) -> dict[str, Any]:
    claims = load("docs/claims.json")
    proposition = next(
        (row for row in claims["remaining_open_propositions"] if row["id"] == open_id), None
    )
    if proposition is None:
        raise KeyError(f"unknown remaining-open proposition id: {open_id}")
    claim_index = {row["id"]: row for row in claims["claims"]}
    linked_claims = [
        compact_claim(row)
        for row in claims["claims"]
        if open_id in row.get("remaining_open_proposition_ids", [])
        and row["id"] != proposition["open_target_claim"]
    ]
    advancing_claims = []
    for edge in claims["machine_readable_paper"]["argument_graph"]["edges"]:
        effect = edge.get("remaining_open_effect")
        if not effect or effect.get("remaining_open_proposition_id") != open_id:
            continue
        advancing_claims.append(
            {
                "claim": compact_claim(claim_index[edge["from"]]),
                "relation": edge["relation"],
                "operation": effect["operation"],
                "effect": effect["statement"],
            }
        )
    paper_anchor = next(
        (
            {
                "canonical_handle": anchor["canonical_handle"],
                "paper": anchor["paper"],
                "anchor_class": anchor["anchor_class"],
            }
            for anchor in paper_anchor_inventory()
            if any(row["id"] == open_id for row in anchor["attached_open_propositions"])
        ),
        None,
    )
    programme_routes = [
        route
        for route in all_entrypoints(claims)
        if route.get("route_kind") == "mathematical_programme"
        and open_id in route.get("remaining_open_proposition_ids", [])
    ]
    route_memory_bindings = []
    for route in programme_routes:
        problem_number = route_memory_problem_number(route)
        if problem_number is None:
            continue
        route_memory_bindings.append(
            {
                "route_id": route["id"],
                "problem_number": problem_number,
                "command": (
                    "python3 scripts/query_route_memory.py --problem "
                    f"{problem_number} --route {route['id']}"
                ),
                "authority_posture": (
                    "derived_resume_handoff_not_claim_or_proof_authority"
                ),
                "identity_contract": (
                    "The route-memory command binds this route to the selected "
                    "problem and current tracked source digests before resume."
                ),
            }
        )
    route_memory = {
        "status": "bound" if route_memory_bindings else "unbound",
        "bindings": route_memory_bindings,
        "authority_posture": "derived_resume_handoff_not_claim_or_proof_authority",
        "boundary": (
            "Route-memory bindings are navigation handoffs only; they do not "
            "promote an open proposition or replace claim authority."
        ),
    }
    if not route_memory_bindings:
        route_memory["unbound_reason"] = (
            "no canonical mathematical programme carries this open proposition; "
            "no resume route was invented"
        )
    return {
        "kind": "open_proposition",
        "authority_posture": "authored_open_boundary_navigation_not_proof_authority",
        "open_proposition": proposition,
        "status": "open",
        "open_target": compact_claim(claim_index[proposition["open_target_claim"]]),
        "linked_claims": linked_claims,
        "advancing_claims": advancing_claims,
        "paper_anchor": paper_anchor,
        "route_memory": route_memory,
        "follow": "python3 scripts/query_corpus.py --claim <claim_id>",
        "source": "docs/claims.json::remaining_open_propositions",
        "validation": "python3 scripts/check_release.py",
    }


def decorate_declaration_rows(
    matches: list[dict[str, Any]], limit: int
) -> list[dict[str, Any]]:
    """Attach claim, paper, and source navigation to exact atlas rows."""
    claims = load("docs/claims.json")
    aliases = load("paper/module-aliases.json")["aliases"]
    claim_index = {row["id"]: row for row in claims["claims"]}
    roles = module_roles(claims)
    label_index = paper_label_index()
    sigil_by_path = {row["path"]: row["sigil"] for row in aliases}
    lean_source_identity = formal_source_identity(claims)
    repository = lean_source_identity["repository"].rstrip("/")
    source_ref = lean_source_identity["ref"]
    paper_anchors = paper_anchor_inventory()
    declarations_by_module = declaration_row_indexes()["by_module"]
    decorated = []
    for match in matches[:limit]:
        attached_claims = []
        for claim_id in match.get("claim_ids", []):
            claim = claim_index[claim_id]
            attached_claims.append(
                {
                    **compact_claim(claim),
                    "paper": paper_coordinate(claim.get("paper_label"), label_index),
                }
            )
        decorated.append(
            {
                **match,
                "qualified_name": qualified_declaration_name(match),
                "externally_addressable": declaration_externally_addressable(
                    match
                ),
                "source_ref": f"{match['module']}:{match['line']}",
                "source_url": f"{repository}/blob/{source_ref}/{match['module']}#L{match['line']}",
                "lean_source_identity": dict(lean_source_identity),
                "paper_sigil": sigil_by_path.get(match["module"]),
                "module_role": roles.get(
                    match["module"].removesuffix(".lean").replace("/", "."),
                    "Unclassified module",
                ),
                "attached_claims": attached_claims,
                "paper_anchors": [
                    {
                        "canonical_handle": anchor["canonical_handle"],
                        "paper": anchor["paper"],
                        "anchor_class": anchor["anchor_class"],
                    }
                    for anchor in paper_anchors
                    if any(
                        link["module"] == match["module"]
                        and (
                            link["declaration"] == match["name"]
                            or (
                                link["declaration"] is None
                                and (
                                    abs(link["line"] - match["line"]) <= SOURCE_LINE_WINDOW
                                    or (
                                        match["line"] <= link["line"]
                                        and link["line"] < next(
                                            (
                                                row["line"]
                                                for row in declarations_by_module[match["module"]]
                                                if row["line"] > match["line"]
                                            ),
                                            10**18,
                                        )
                                    )
                                )
                            )
                        )
                        for link in anchor["source_links"]
                    )
                ],
            }
        )
    return decorated


def declaration_route_memory_rows(
    declarations: list[dict[str, Any]], claims: dict[str, Any]
) -> list[dict[str, Any]]:
    """Attach canonical programme resume bindings to declaration projections."""
    programme_routes = [
        route
        for route in all_entrypoints(claims)
        if route.get("route_kind") == "mathematical_programme"
    ]
    routed_matches = []
    for declaration in declarations:
        bindings = []
        for claim_id in declaration.get("claim_ids", []):
            for route in programme_routes:
                if claim_id not in route.get("core_claim_ids", []):
                    continue
                problem_number = route_memory_problem_number(route)
                if problem_number is None:
                    continue
                binding = {
                    "route_id": route["id"],
                    "problem_number": problem_number,
                    "command": (
                        "python3 scripts/query_route_memory.py --problem "
                        f"{problem_number} --route {route['id']}"
                    ),
                    "authority_posture": (
                        "derived_resume_handoff_not_claim_or_proof_authority"
                    ),
                    "identity_contract": (
                        "The route-memory command binds this route to the selected "
                        "problem and current tracked source digests before resume."
                    ),
                }
                if binding["route_id"] not in {
                    row["route_id"] for row in bindings
                }:
                    bindings.append(binding)
        route_memory = {
            "status": "bound" if bindings else "unbound",
            "bindings": bindings,
            "authority_posture": (
                "derived_resume_handoff_not_claim_or_proof_authority"
            ),
            "boundary": (
                "Route-memory bindings are navigation handoffs only; they do not "
                "promote claims or replace Lean declaration authority."
            ),
        }
        if not bindings:
            route_memory["unbound_reason"] = (
                "declaration claim IDs do not resolve to a canonical mathematical "
                "programme; no resume route was invented"
            )
        routed_matches.append({**declaration, "route_memory": route_memory})
    return routed_matches


def module_route_memory_projection(
    declarations: list[dict[str, Any]],
    claims: dict[str, Any],
    source_problem_routes: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Aggregate exact declaration and source-bound problem handoffs."""
    routed_declarations = declaration_route_memory_rows(declarations, claims)
    bindings = []
    seen_routes: set[str] = set()
    for declaration in routed_declarations:
        for binding in declaration["route_memory"]["bindings"]:
            if binding["route_id"] in seen_routes:
                continue
            seen_routes.add(binding["route_id"])
            bindings.append(binding)
    for route in source_problem_routes or []:
        route_id = route.get("problem_id")
        problem_number = route.get("erdos_number")
        if not isinstance(route_id, str) or problem_number is None:
            continue
        if route_id in seen_routes:
            continue
        seen_routes.add(route_id)
        bindings.append(
            {
                "route_id": route_id,
                "problem_number": problem_number,
                "command": (
                    "python3 scripts/query_route_memory.py --problem "
                    f"{problem_number}"
                ),
                "route_kind": "problem_route",
                "authority_posture": (
                    "derived_resume_handoff_not_claim_or_proof_authority"
                ),
                "identity_contract": (
                    "The route-memory command binds this source-bound module "
                    "to the selected problem and current tracked source "
                    "digests before resume."
                ),
            }
        )
    projection = {
        "status": "bound" if bindings else "unbound",
        "bindings": bindings,
        "declaration_count": len(declarations),
        "bound_declaration_count": sum(
            1
            for declaration in routed_declarations
            if declaration["route_memory"]["bindings"]
        ),
        "authority_posture": "derived_resume_handoff_not_claim_or_proof_authority",
        "boundary": (
            "Module bindings aggregate exact declaration or source-bound problem "
            "route handoffs; they do not promote claims or replace Lean module "
            "authority."
        ),
    }
    if not bindings:
        projection["unbound_reason"] = (
            "module declarations do not resolve to a canonical mathematical "
            "programme; no resume route was invented"
        )
    return projection


def module_problem_routes(
    module_path: str,
    problems: list[dict[str, Any]],
    claims: dict[str, Any],
) -> list[dict[str, Any]]:
    """Bind an indexed or reviewed-family source module to its problem route."""
    routes = []
    for problem in problems:
        modules = problem.get("modules", [])
        if not any(
            isinstance(module, Mapping) and module.get("path") == module_path
            for module in modules
        ):
            continue
        obligations = problem.get("open_obligations", [])
        paper = problem.get("paper") or {}
        paper_source = paper.get("source")
        routes.append(
            {
                "problem_id": problem["problem_id"],
                "erdos_number": problem["erdos_number"],
                "command": (
                    "python3 scripts/query_corpus.py --route "
                    f"{problem['problem_id']}"
                ),
                "paper_source": paper_source,
                "paper_route": {
                    "source": paper_source,
                    "command": (
                        "python3 scripts/query_corpus.py --paper-source "
                        f"{paper_source}"
                    )
                    if paper_source
                    else None,
                    "authority_posture": (
                        "authored_paper_navigation_not_proof_authority"
                    ),
                },
                "open_obligation_ids": [
                    item["id"]
                    for item in obligations
                    if isinstance(item, Mapping) and isinstance(item.get("id"), str)
                ],
            }
        )
    family_routes = reviewed_result_family_module_routes(module_path, claims, problems)
    for family_route in family_routes:
        problem_id = family_route["problem_id"]
        route = next(
            (row for row in routes if row["problem_id"] == problem_id), None
        )
        if route is None:
            problem = next(
                row
                for row in problems
                if row.get("problem_id") == problem_id
            )
            obligations = problem.get("open_obligations", [])
            paper = problem.get("paper") or {}
            paper_source = paper.get("source")
            route = {
                "problem_id": problem_id,
                "erdos_number": problem["erdos_number"],
                "command": (
                    "python3 scripts/query_corpus.py --route "
                    f"{problem_id}"
                ),
                "paper_source": paper_source,
                "paper_route": {
                    "source": paper_source,
                    "command": (
                        "python3 scripts/query_corpus.py --paper-source "
                        f"{paper_source}"
                    )
                    if paper_source
                    else None,
                    "authority_posture": (
                        "authored_paper_navigation_not_proof_authority"
                    ),
                },
                "open_obligation_ids": [
                    item["id"]
                    for item in obligations
                    if isinstance(item, Mapping)
                    and isinstance(item.get("id"), str)
                ],
                "match_kind": "reviewed_result_family_source",
            }
            routes.append(route)
        route.setdefault("reviewed_result_family_ids", []).append(
            family_route["id"]
        )
        route.setdefault("reviewed_result_family_routes", []).append(family_route)

    claim_family_routes = claim_registry_module_family_routes(
        module_path, claims, problems
    )
    reviewed_family_ids = {
        family_route["id"]
        for family_route in reviewed_result_family_module_routes(
            module_path, claims, problems
        )
    }
    for claim_family_route in claim_family_routes:
        if claim_family_route["family_id"] in reviewed_family_ids:
            # The reviewed-family join is the richer canonical route when a
            # claim has already been promoted by Comparator.  Do not emit a
            # second claim-registry route for the same family.
            continue
        problem_id = claim_family_route["problem_id"]
        route = next(
            (row for row in routes if row["problem_id"] == problem_id), None
        )
        if route is None:
            problem = next(
                row
                for row in problems
                if row.get("problem_id") == problem_id
            )
            obligations = problem.get("open_obligations", [])
            paper = problem.get("paper") or {}
            paper_source = paper.get("source")
            route = {
                "problem_id": problem_id,
                "erdos_number": problem["erdos_number"],
                "command": (
                    "python3 scripts/query_corpus.py --route "
                    f"{problem_id}"
                ),
                "paper_source": paper_source,
                "paper_route": {
                    "source": paper_source,
                    "command": (
                        "python3 scripts/query_corpus.py --paper-source "
                        f"{paper_source}"
                    )
                    if paper_source
                    else None,
                    "authority_posture": (
                        "authored_paper_navigation_not_proof_authority"
                    ),
                },
                "open_obligation_ids": [
                    item["id"]
                    for item in obligations
                    if isinstance(item, Mapping)
                    and isinstance(item.get("id"), str)
                ],
                "match_kind": "claim_registry_declaration_programme",
            }
            routes.append(route)
        route.setdefault("claim_family_ids", [])
        if claim_family_route["family_id"] not in route["claim_family_ids"]:
            route["claim_family_ids"].append(claim_family_route["family_id"])
        route.setdefault("claim_family_routes", [])
        if not any(
            row.get("family_id") == claim_family_route["family_id"]
            for row in route["claim_family_routes"]
        ):
            route["claim_family_routes"].append(claim_family_route)
    return routes


def claim_registry_module_family_routes(
    module_path: str,
    claims: dict[str, Any],
    problems: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    """Expose claim-family routes when generated problem modules lag the claim registry.

    A source module can be a current proof-bearing claim source before the
    generated eight-problem module roster is refreshed.  In that interval,
    the claim declaration and its canonical programme route are the only
    source-faithful join available.  This fallback preserves the claim's
    representative declarations and exact open boundary without promoting
    subordinate module helpers or inventing a second family registry.
    """
    problem_by_number = {
        int(problem["erdos_number"]): problem
        for problem in problems
        if isinstance(problem, Mapping)
    }
    open_index = {
        row["id"]: row
        for row in claims.get("remaining_open_propositions", [])
        if isinstance(row, Mapping) and isinstance(row.get("id"), str)
    }
    paper_index = paper_label_index()
    routes: list[dict[str, Any]] = []
    seen: set[tuple[str, int]] = set()
    for claim in claims.get("claims", []):
        if not isinstance(claim, Mapping) or not isinstance(claim.get("id"), str):
            continue
        claim_declarations = [
            declaration
            for declaration in claim.get("declarations", [])
            if isinstance(declaration, Mapping)
            and declaration.get("module") == module_path
        ]
        if not claim_declarations:
            continue
        for programme in all_entrypoints(claims):
            if programme.get("route_kind") != "mathematical_programme":
                continue
            if claim["id"] not in programme.get("core_claim_ids", []):
                continue
            problem_number = route_memory_problem_number(programme)
            problem = problem_by_number.get(problem_number) if problem_number else None
            if problem is None or problem_number is None:
                continue
            identity = (claim["id"], problem_number)
            if identity in seen:
                continue
            seen.add(identity)
            paper = paper_coordinate(claim.get("paper_label"), paper_index)
            review_context = claim_registry_context_for_claim(
                claims, claim["id"]
            )
            claim_open_ids = [
                open_id
                for open_id in claim.get(
                    "remaining_open_proposition_ids", []
                )
                if isinstance(open_id, str)
            ]
            open_ids = claim_open_ids or [
                open_id
                for open_id in programme.get(
                    "remaining_open_proposition_ids", []
                )
                if isinstance(open_id, str)
            ]
            representative_declarations = [
                {
                    "name": declaration["name"],
                    "module": declaration["module"],
                    "line": declaration["line"],
                    "source_ref": (
                        f"{declaration['module']}:{declaration['line']}"
                    ),
                    "command": (
                        "python3 scripts/query_corpus.py --declaration "
                        f"{declaration['name']}"
                    ),
                }
                for declaration in claim_declarations
                if isinstance(declaration.get("name"), str)
                and isinstance(declaration.get("line"), int)
            ]
            routes.append(
                {
                    "id": claim["id"],
                    "family_id": claim["id"],
                    "family_kind": "canonical_claim_family",
                    "claim_id": claim["id"],
                    "label": claim.get("label"),
                    "status": claim.get("status"),
                    "claim_statement": claim.get("statement"),
                    "problem_id": problem["problem_id"],
                    "erdos_number": problem_number,
                    "source_route": module_path,
                    "representative_declarations": representative_declarations,
                    "declaration_routes": [
                        row["command"] for row in representative_declarations
                    ],
                    "paper_route": {
                        "label": claim.get("paper_label"),
                        "source": paper.get("source") if paper else None,
                        "source_ref": paper.get("source_ref") if paper else None,
                        "command": (
                            "python3 scripts/query_corpus.py --paper-anchor "
                            f"{claim['paper_label']}"
                        )
                        if claim.get("paper_label")
                        else None,
                        "authority_posture": (
                            "authored_paper_navigation_not_proof_authority"
                        ),
                        "unbound_reason": (
                            "claim has no registered paper label; no paper "
                            "anchor was invented"
                        )
                        if not claim.get("paper_label")
                        else None,
                    },
                    "problem_route": (
                        "python3 scripts/query_corpus.py --route "
                        f"{problem['problem_id']}"
                    ),
                    "open_boundary": {
                        "claim_statement": claim.get("statement"),
                        "remaining_open_propositions": [
                            {
                                "id": open_id,
                                "command": (
                                    "python3 scripts/query_corpus.py --open "
                                    f"{open_id}"
                                ),
                                "statement": open_index[open_id].get("statement"),
                            }
                            for open_id in open_ids
                            if open_id in open_index
                        ],
                        "authority_posture": (
                            "claim_registry_boundary_navigation_not_proof_authority"
                        ),
                    },
                    "programme_route": {
                        "id": programme["id"],
                        "command": (
                            "python3 scripts/query_corpus.py --route "
                            f"{programme['id']}"
                        ),
                        "claim_ceiling": programme.get("claim_ceiling"),
                    },
                    "claim_registry_context": review_context,
                    "subordinate_declaration_contract": {
                        "source": "docs/declaration_atlas.json::modules",
                        "representative_declarations": [
                            row["name"] for row in representative_declarations
                        ],
                        "boundary": (
                            "Other declarations in this module remain subordinate "
                            "module/declaration drilldowns; they are not promoted "
                            "into additional canonical families."
                        ),
                    },
                }
            )
    return routes


def reviewed_result_family_module_routes(
    module_path: str,
    claims: dict[str, Any],
    problems: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    """Expose reviewed families whose governed source record names this module."""
    routes = []
    claim_index = {
        claim["id"]: claim
        for claim in claims.get("claims", [])
        if isinstance(claim, Mapping) and isinstance(claim.get("id"), str)
    }
    paper_index = paper_label_index()
    for problem in problems:
        paper = problem.get("paper") or {}
        paper_source = paper.get("source")
        for family in reviewed_result_family_rows(claims, problem["erdos_number"]):
            source_rows = reviewed_result_family_source_rows(
                claims, problem["erdos_number"], family["id"]
            )
            matching_source_rows = [
                row
                for row in source_rows
                if str(row.get("original_source", "")).removeprefix("./")
                == module_path
            ]
            if not matching_source_rows:
                matching_source_rows = reviewed_result_family_atlas_source_rows(
                    family, module_path
                )
            if not matching_source_rows:
                continue
            representative_source_row = next(
                (
                    row
                    for row in matching_source_rows
                    if row.get("id") == family["id"]
                ),
                matching_source_rows[0],
            )
            declarations = [
                str(declaration)
                for declaration in family.get("declarations", [])
            ]
            if not declarations:
                declarations = reviewed_result_family_source_declarations(
                    claims, problem["erdos_number"], family["id"]
                )
            claim_paper_routes = []
            for source_row in matching_source_rows:
                claim = claim_index.get(source_row.get("claim_id"))
                if claim is None or not claim.get("paper_label"):
                    continue
                coordinate = paper_coordinate(
                    claim["paper_label"], paper_index
                )
                claim_paper_routes.append(
                    {
                        "label": claim["paper_label"],
                        "source": coordinate.get("source") if coordinate else None,
                        "source_ref": (
                            coordinate.get("source_ref") if coordinate else None
                        ),
                        "command": (
                            "python3 scripts/query_corpus.py --paper-anchor "
                            f"{claim['paper_label']}"
                        ),
                        "authority_posture": (
                            "authored_paper_navigation_not_proof_authority"
                        ),
                    }
                )
            routes.append(
                {
                    "id": family["id"],
                    "problem_id": problem["problem_id"],
                    "erdos_number": problem["erdos_number"],
                    "source_route": module_path,
                    "representative": representative_source_row.get(
                        "original_declaration"
                    ),
                    "wrapper_declaration": representative_source_row.get(
                        "wrapper_declaration"
                    ),
                    "contribution_class": family.get("contribution_class"),
                    "summary": family.get("summary"),
                    "evidence_mode": family.get("evidence_mode"),
                    "comparator_disposition": family.get(
                        "comparator_disposition"
                    ),
                    "declarations": declarations,
                    "declaration_routes": [
                        "python3 scripts/query_corpus.py --declaration "
                        f"{declaration}"
                        for declaration in declarations
                    ],
                    "paper_route": {
                        "source": paper_source,
                        "command": (
                            "python3 scripts/query_corpus.py --paper-source "
                            f"{paper_source}"
                        )
                        if paper_source
                        else None,
                        "matching_anchors": paper_anchor_routes_for_declarations(
                            paper_source, declarations
                        ),
                        "authority_posture": (
                            "authored_paper_navigation_not_proof_authority"
                        ),
                    },
                    "claim_paper_routes": claim_paper_routes,
                    "open_boundary": {
                        "boundary": family.get("boundary"),
                        "problem_route": (
                            "python3 scripts/query_corpus.py --route "
                            f"{problem['problem_id']}"
                        ),
                        "problem_open_obligation_ids": [
                            item["id"]
                            for item in problem.get("open_obligations", [])
                            if isinstance(item, Mapping)
                            and isinstance(item.get("id"), str)
                        ],
                        "authority_posture": (
                            "claim_registry_boundary_navigation_not_proof_authority"
                        ),
                    },
                }
            )
    return routes


def declaration_packet(name: str, limit: int) -> dict[str, Any]:
    matches = declaration_rows_for_handle(name)
    if not matches:
        raise KeyError(f"unknown declaration name: {name}")
    decorated = decorate_declaration_rows(matches, limit)
    routed_matches = declaration_route_memory_rows(decorated, load("docs/claims.json"))
    return {
        "kind": "declaration",
        "authority_posture": "atlas_navigation_projection_not_proof_authority",
        "matches": routed_matches,
        "match_count": len(matches),
        "omitted_match_count": max(0, len(matches) - limit),
        "follow": {
            "claim": "python3 scripts/query_corpus.py --claim <claim_id>",
            "module": "python3 scripts/query_corpus.py --module <module_or_sigil>",
        },
        "validation": "python3 scripts/build_declaration_atlas.py --check",
    }


def source_coordinate_packet(source_ref: str, limit: int) -> dict[str, Any]:
    match = re.fullmatch(r"(.+\.lean):(\d+)", source_ref.strip())
    if match is None:
        raise ValueError("source coordinate must have the form <module.lean>:<positive_line>")
    module_path = match.group(1).removeprefix("./")
    line = int(match.group(2))
    if line < 1:
        raise ValueError("source coordinate line must be positive")

    atlas = load("docs/declaration_atlas.json")
    claims = load("docs/claims.json")
    aliases = load("paper/module-aliases.json")["aliases"]
    module = next((row for row in atlas["modules"] if row["path"] == module_path), None)
    if module is None:
        raise KeyError(f"unknown Lean source module: {module_path}")
    source_lines = (ROOT / module_path).read_text(encoding="utf-8").splitlines()
    if line > len(source_lines):
        raise ValueError(
            f"source coordinate line {line} exceeds {module_path} length {len(source_lines)}"
        )

    module_declarations = declaration_row_indexes()["by_module"].get(
        module_path, []
    )
    window_declarations = sorted(
        (
            row
            for row in module_declarations
            if abs(row["line"] - line) <= SOURCE_LINE_WINDOW
        ),
        key=lambda row: (abs(row["line"] - line), row["line"], row["name"]),
    )
    containing = next(
        (row for row in reversed(module_declarations) if row["line"] <= line),
        None,
    )
    candidates = list(window_declarations)
    if containing is not None and containing not in candidates:
        candidates.append(containing)
    candidates.sort(key=lambda row: (abs(row["line"] - line), row["line"], row["name"]))
    decorated = decorate_declaration_rows(candidates, limit)
    decorated = declaration_route_memory_rows(decorated, claims)

    before = [row for row in module_declarations if row["line"] < line]
    after = [row for row in module_declarations if row["line"] > line]
    roles = module_roles(claims)
    lean_source_identity = formal_source_identity(claims)
    repository = lean_source_identity["repository"].rstrip("/")
    source_ref = lean_source_identity["ref"]
    return {
        "kind": "source_coordinate",
        "authority_posture": "source_coordinate_navigation_not_proof_authority",
        "source": {
            "module": module_path,
            "line": line,
            "source_ref": f"{module_path}:{line}",
            "source_url": f"{repository}/blob/{source_ref}/{module_path}#L{line}",
            "lean_source_identity": lean_source_identity,
            "module_id": module["id"],
            "module_role": roles.get(module["id"], "Unclassified module"),
            "paper_sigil": next(
                (row["sigil"] for row in aliases if row["path"] == module_path), None
            ),
        },
        "nearby_declarations": decorated,
        "coordinate_receipt": {
            "line_exists": True,
            "declaration_window": SOURCE_LINE_WINDOW,
            "source_span_posture": (
                "nearest_preceding_atlas_declaration_until_next_declaration_lexical_projection"
            ),
            "containing_declaration": (
                compact_declaration(containing) if containing is not None else None
            ),
            "nearby_total": len(candidates),
            "nearby_emitted": min(len(candidates), limit),
            "nearby_omitted": max(0, len(candidates) - limit),
            "exact_declaration_count": sum(row["line"] == line for row in candidates),
            "nearest_before": compact_declaration(before[-1]) if before else None,
            "nearest_after": compact_declaration(after[0]) if after else None,
            "exhaustive_owner": "docs/declaration_atlas.json",
        },
        "follow": {
            "declaration": "python3 scripts/query_corpus.py --declaration <nearby_declaration.name>",
            "module": f"python3 scripts/query_corpus.py --module {module_path}",
            "paper_anchor": "python3 scripts/query_corpus.py --paper-anchor <nearby_declaration.paper_anchor>",
        },
        "validation": "python3 scripts/build_declaration_atlas.py --check",
    }


def declaration_externally_addressable(row: dict[str, Any]) -> bool:
    """Whether a declaration can be named from an external scratch module."""
    signature = str(row.get("signature") or "")
    return re.match(
        r"^\s*(?:@\[[^\]\n]*\]\s*)*(?:private|local)\b",
        signature,
    ) is None


def compact_declaration(row: dict[str, Any]) -> dict[str, Any]:
    return {
        "name": row["name"],
        "qualified_name": qualified_declaration_name(row),
        "externally_addressable": declaration_externally_addressable(row),
        "declaration_kind": row["kind"],
        "module": row["module"],
        "line": row["line"],
        "source_ref": f"{row['module']}:{row['line']}",
        "claim_ids": row.get("claim_ids", []),
        "generated_certificate": bool(row.get("generated_certificate")),
    }


@lru_cache(maxsize=1024)
def module_namespace_events(rel: str) -> tuple[tuple[int, str], ...]:
    """Return namespace-prefix changes, respecting intervening section blocks."""
    path = ROOT / rel
    if not path.is_file():
        return ((1, ""),)
    current = ""
    blocks: list[tuple[str, str]] = []
    events: list[tuple[int, str]] = [(1, "")]
    for line_number, raw in enumerate(
        lean_code_projection(path.read_text(encoding="utf-8")).splitlines(),
        start=1,
    ):
        line = raw.strip()
        namespace = re.fullmatch(
            r"namespace\s+([A-Za-z0-9_'.]+)", line
        )
        if namespace:
            name = namespace.group(1)
            previous = current
            if not current or name.startswith(f"{current}."):
                current = name
            else:
                current = f"{current}.{name}"
            blocks.append(("namespace", previous))
            events.append((line_number + 1, current))
            continue
        if re.fullmatch(
            r"(?:(?:noncomputable|private)\s+)?section(?:\s+[A-Za-z0-9_']+)?",
            line,
        ):
            blocks.append(("section", current))
            continue
        if re.fullmatch(r"end(?:\s+[A-Za-z0-9_'.]+)?", line) and blocks:
            _, previous = blocks.pop()
            if current != previous:
                current = previous
                events.append((line_number + 1, current))
    return tuple(events)


def qualified_declaration_name(row: dict[str, Any]) -> str:
    events = module_namespace_events(row["module"])
    starts = [event[0] for event in events]
    prefix = events[bisect.bisect_right(starts, row["line"]) - 1][1]
    name = row["name"]
    if not prefix or name.startswith(f"{prefix}."):
        return name
    return f"{prefix}.{name}"


def module_roles(claims: dict[str, Any]) -> dict[str, str]:
    nodes = claims["machine_readable_paper"]["module_graph"]["nodes"]
    roles = {row["id"]: row["role"] for row in nodes}
    roles["Erdos249257"] = "Supported package root import"
    return roles


def compact_module(row: dict[str, Any], roles: dict[str, str]) -> dict[str, Any]:
    return {
        "id": row["id"],
        "path": row["path"],
        "role": roles.get(row["id"], "Unclassified module"),
        "declaration_count": row["declaration_count"],
    }


def file_digest(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def identifier_counts(text: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    for name in re.findall(r"[A-Za-z_][A-Za-z0-9_']*", text):
        counts[name] = counts.get(name, 0) + 1
    return counts


def connection_card(handle: str, limit: int, query: str = "") -> dict[str, Any]:
    """Project one source-current public module relationship card.

    This is the public-corpus projection of the same disclosure-aware card
    contract used by private claim-local mathematical working memory.  The
    shared shape makes prerequisite and consumer directions portable without
    pretending that a public navigation projection has private claim authority.
    """
    atlas = load("docs/declaration_atlas.json")
    claims = load("docs/claims.json")
    aliases = load("paper/module-aliases.json")["aliases"]
    alias = next((row for row in aliases if row["sigil"].casefold() == handle.casefold()), None)
    resolved_handle = alias["path"] if alias is not None else handle
    normalized = (
        resolved_handle.replace(".", "/") + ".lean"
        if "/" not in resolved_handle and not resolved_handle.endswith(".lean")
        else resolved_handle
    ).removeprefix("./")
    declaration_matches = [
        row
        for row in atlas_declarations(atlas)
        if row["name"] == resolved_handle
    ]
    module = next(
        (
            row
            for row in atlas["modules"]
            if resolved_handle in (row["id"], row["path"])
            or normalized == row["path"]
        ),
        None,
    )
    if module is None and declaration_matches:
        module = next(
            row for row in atlas["modules"] if row["path"] == declaration_matches[0]["module"]
        )
    if module is None:
        raise KeyError(f"unknown connection handle: {handle}")

    roles = module_roles(claims)
    by_module = {row["id"]: row for row in atlas["modules"]}
    declarations_by_path: dict[str, list[dict[str, Any]]] = {}
    for row in atlas_declarations(atlas):
        declarations_by_path.setdefault(row["module"], []).append(row)
    for rows in declarations_by_path.values():
        rows.sort(key=lambda row: (row["line"], row["name"]))

    source_path = ROOT / module["path"]
    source_text = source_path.read_text(encoding="utf-8")
    source_counts = identifier_counts(source_text)
    anchor_names = {row["name"] for row in declaration_matches}
    module_declarations = declarations_by_path.get(module["path"], [])
    declaration_relevance: dict[str, dict[str, Any]] = {}
    if query:
        query_terms = semantic_content_terms(query) or search_terms(query)
        source_lines = source_text.splitlines()
        span_identifiers: dict[str, set[str]] = {}
        for index, row in enumerate(module_declarations):
            span_end = (
                module_declarations[index + 1]["line"] - 1
                if index + 1 < len(module_declarations)
                else len(source_lines)
            )
            span = "\n".join(source_lines[row["line"] - 1 : span_end])
            span_identifiers[row["id"]] = set(identifier_counts(span))
        anchor_references = set().union(
            *(
                span_identifiers[row["id"]]
                for row in declaration_matches
                if row["id"] in span_identifiers
            ),
            set(),
        )
        ranked_rows: list[tuple[tuple[int, int, int, int], dict[str, Any]]] = []
        for row in module_declarations:
            row_terms = search_terms(
                " ".join(
                    str(value)
                    for value in (
                        row["name"],
                        row.get("signature"),
                        row.get("docstring"),
                    )
                    if value
                )
            )
            overlap = sorted(query_terms & row_terms)
            relations = []
            if row["name"] in anchor_references:
                relations.append("used_by_anchor_source_span")
            if anchor_names & span_identifiers[row["id"]]:
                relations.append("uses_anchor_in_source_span")
            is_anchor = row["name"] in anchor_names
            if not is_anchor and not overlap and not relations:
                continue
            lexical_rank = search_rank(
                query,
                row["name"],
                " ".join(
                    str(value)
                    for value in (row.get("signature"), row.get("docstring"))
                    if value
                ),
            )
            selection_tier = (
                "anchor"
                if is_anchor
                else "query_and_anchor_relation"
                if overlap and relations
                else "query_lexical"
                if overlap
                else "anchor_relation"
            )
            declaration_relevance[row["id"]] = {
                "selection_tier": selection_tier,
                "query_term_overlap": overlap,
                "anchor_relations": relations,
            }
            ranked_rows.append(
                (
                    (
                        0 if is_anchor else 1,
                        -len(overlap),
                        lexical_rank if lexical_rank is not None else 10**6,
                        row["line"],
                    ),
                    row,
                )
            )
        ranked_rows.sort(key=lambda item: item[0])
        ranked_declarations = [row for _, row in ranked_rows]
    else:
        query_terms = set()
        ranked_declarations = sorted(
            module_declarations,
            key=lambda row: (
                0 if row["name"] in anchor_names else 1,
                row["line"],
            ),
        )

    dependency_capsules = []
    for imported_id in module.get("imports", [])[: min(6, limit)]:
        imported = by_module.get(imported_id)
        if imported is None:
            continue
        rows = declarations_by_path.get(imported["path"], [])
        enriched = [
            {
                **compact_declaration(row),
                "statement_head": row.get("signature"),
                "usage_count_in_anchor_source": source_counts.get(row["name"], 0),
            }
            for row in rows
        ]
        used = [row for row in enriched if row["usage_count_in_anchor_source"] > 0]
        pool = used or enriched
        propositions = [row for row in pool if row["declaration_kind"] in {"theorem", "lemma"}]
        data = [row for row in pool if row["declaration_kind"] not in {"theorem", "lemma"}]
        retained = propositions[:8] + data[:4]
        dependency_capsules.append(
            {
                "module_id": imported_id,
                "file": imported["path"],
                "source_digest": file_digest(ROOT / imported["path"]),
                "relationship_to_anchor_module": "prerequisite_import",
                "selection_basis": (
                    "referenced_declarations_in_anchor_source"
                    if used
                    else "bounded_public_interface"
                ),
                "facts": retained,
                "fact_count": len(rows),
                "omitted_fact_count": max(0, len(rows) - len(retained)),
            }
        )

    producer_names = {row["name"] for row in module_declarations}
    importer_rows = [row for row in atlas["modules"] if module["id"] in row.get("imports", [])]
    consumer_capsules = []
    for importer in importer_rows[: min(6, limit)]:
        importer_path = ROOT / importer["path"]
        importer_lines = importer_path.read_text(encoding="utf-8").splitlines()
        importer_declarations = declarations_by_path.get(importer["path"], [])
        consumers = []
        for index, row in enumerate(importer_declarations):
            end = (
                importer_declarations[index + 1]["line"] - 1
                if index + 1 < len(importer_declarations)
                else len(importer_lines)
            )
            span = "\n".join(importer_lines[row["line"] - 1 : end])
            uses = sorted(name for name in producer_names if re.search(rf"\b{re.escape(name)}\b", span))
            if uses:
                consumers.append(
                    {
                        **compact_declaration(row),
                        "statement_head": row.get("signature"),
                        "uses_anchor_declarations": uses,
                    }
                )
        consumer_capsules.append(
            {
                "module_id": importer["id"],
                "file": importer["path"],
                "source_digest": file_digest(importer_path),
                "producer_source_digest": file_digest(source_path),
                "relationship_to_anchor_module": "consumer_importer",
                "selection_basis": (
                    "consumer_declarations_referencing_anchor_declarations"
                    if consumers
                    else "exact_import_without_named_declaration_reference"
                ),
                "consumers": consumers[:8],
                "consumer_count": len(consumers),
                "omitted_consumer_count": max(0, len(consumers) - 8),
            }
        )

    return {
        "kind": "connection_card",
        "schema_version": CONNECTION_CARD_SCHEMA,
        "status": "source_current",
        "surface_contract": {
            "contract_id": "lean_connection_card",
            "projection_scope": "public_corpus",
            "disclosure_posture": "public_only",
            "equivalent_private_projection": "private_claim_local",
            "equivalence_boundary": (
                "same directional navigation grammar; independent source, claim, and proof authority"
            ),
        },
        "anchor": {
            "handle": handle,
            "handle_kind": "declaration" if declaration_matches else "module",
            "module_id": module["id"],
            "file": module["path"],
            "source_digest": file_digest(source_path),
            "lean_source_identity": formal_source_identity(claims),
        },
        "module_id": module["id"],
        "relationship_direction": {
            "prerequisite_imports": list(module.get("imports", []))[:16],
            "consumer_importers": [
                {"module_id": row["id"], "file": row["path"], "relation": "consumer_importer"}
                for row in importer_rows[:limit]
            ],
        },
        "declarations": [
            {
                **compact_declaration(row),
                "statement_head": row.get("signature"),
                **(
                    {"connection_relevance": declaration_relevance[row["id"]]}
                    if row["id"] in declaration_relevance
                    else {}
                ),
            }
            for row in ranked_declarations[: min(limit, 12)]
        ],
        "declaration_count": len(module_declarations),
        "declaration_selection_receipt": {
            "query": query or None,
            "query_terms": sorted(query_terms),
            "selection_policy": (
                "anchor_then_query_overlap_then_exact_source_span_relation"
                if query
                else "anchor_then_source_order"
            ),
            "eligible_count": len(ranked_declarations),
            "excluded_module_broad_count": (
                len(module_declarations) - len(ranked_declarations)
                if query
                else 0
            ),
            "emitted_count": min(len(ranked_declarations), min(limit, 12)),
        },
        "dependency_capsules": dependency_capsules,
        "consumer_capsules": consumer_capsules,
        "required_consumption": {
            "trigger": "after_public_module_selection_before_proof_or_claim_reasoning",
            "action": (
                "Check prerequisite interfaces, named downstream consumers, attached claim status, "
                "and exact Lean source before introducing a parallel result or public claim."
            ),
        },
        "refresh_contract": {
            "triggers": [
                "after_context_compaction",
                "after_target_declaration_or_strategy_changes",
                "after_import_or_source_changes",
                "when_any_source_digest_changes",
            ],
            "action": f"python3 scripts/query_corpus.py --connections {handle}",
        },
        "exact_drilldown": f"python3 scripts/query_corpus.py --connections {handle}",
        "authority_boundary": (
            "This source-current public relationship card is generated navigation. The pinned Lean "
            "source is proof authority and docs/claims.json owns public claim status."
        ),
        "validation": "python3 scripts/build_declaration_atlas.py --check",
    }


def module_packet(handle: str, limit: int) -> dict[str, Any]:
    packet_limit = min(limit, MODULE_PACKET_LIMIT)
    requested_handle = handle
    atlas = load("docs/declaration_atlas.json")
    claims = load("docs/claims.json")
    aliases = load("paper/module-aliases.json")["aliases"]
    alias = next((row for row in aliases if row["sigil"].casefold() == handle.casefold()), None)
    resolution = "exact_module_handle"
    if alias is not None:
        handle = alias["path"]
        resolution = "paper_sigil"
    normalized = handle.replace(".", "/") + ".lean" if "/" not in handle else handle
    normalized = normalized.removeprefix("./")
    module = next(
        (
            row
            for row in atlas["modules"]
            if handle in (row["id"], row["path"]) or normalized == row["path"]
        ),
        None,
    )
    if module is None and alias is None:
        requested_stem = Path(handle).name.removesuffix(".lean").casefold()
        stem_matches = [
            row
            for row in atlas["modules"]
            if Path(row["path"]).stem.casefold() == requested_stem
        ]
        if len(stem_matches) > 1:
            candidates = ", ".join(row["path"] for row in stem_matches[:8])
            raise KeyError(
                f"ambiguous module shorthand: {requested_handle}; candidates: "
                f"{candidates}"
            )
        if len(stem_matches) == 1:
            module = stem_matches[0]
            handle = module["path"]
            resolution = "unique_module_stem"
    if module is None:
        raise KeyError(f"unknown module handle: {handle}")
    roles = module_roles(claims)
    module_view = {
        **module,
        "role": roles.get(module["id"], "Unclassified module"),
        "authored_synopsis": module_synopsis(module["path"]),
        "synopsis_authority_posture": (
            "source_current_authored_digestion_not_proof_or_claim_status_authority"
        ),
    }
    imported_rows = [row for row in atlas["modules"] if row["id"] in module["imports"]]
    importer_rows = [row for row in atlas["modules"] if module["id"] in row["imports"]]
    declarations = [
        row
        for row in atlas_declarations(atlas)
        if row["module"] == module["path"]
    ]
    attached_claim_ids = sorted(
        {
            claim_id
            for row in declarations
            for claim_id in row.get("claim_ids", [])
        }
    )
    claim_rows = [compact_claim(row) for row in claims["claims"] if row["id"] in attached_claim_ids]
    declaration_preview = declaration_route_memory_rows(
        [compact_declaration(row) for row in declarations[:packet_limit]],
        claims,
    )
    problems = load("docs/problems.json").get("problems", [])
    problem_routes = module_problem_routes(
        module["path"], problems, claims
    )
    reviewed_family_routes = reviewed_result_family_module_routes(
        module["path"], claims, problems
    )
    claim_family_routes = [
        family_route
        for route in problem_routes
        for family_route in route.get("claim_family_routes", [])
    ]
    module_route_memory = module_route_memory_projection(
        declarations,
        claims,
        [
            route
            for route in problem_routes
            if route.get("reviewed_result_family_ids")
            or route.get("claim_family_ids")
        ],
    )
    return {
        "kind": "module",
        "authority_posture": "atlas_navigation_projection_not_proof_authority",
        "lean_source_identity": formal_source_identity(claims),
        "module_handle_resolution": {
            "requested": requested_handle,
            "resolved": module["path"],
            "method": resolution,
            "authority": "docs/declaration_atlas.json::modules",
        },
        "module": module_view,
        "paper_sigil": next(
            (row["sigil"] for row in aliases if row["path"] == module["path"]), None
        ),
        "attached_claims": claim_rows,
        "reviewed_result_families": reviewed_family_routes,
        "claim_family_routes": claim_family_routes,
        "declaration_preview": declaration_preview,
        "problem_routes": problem_routes,
        "problem_route_contract": {
            "source": "docs/problems.json::problems[].modules",
            "matching": (
                "exact indexed module path or docs/claims.json::external_"
                "verification_packet.main_results.original_source, or "
                "docs/claims.json::claims[].declarations plus a canonical "
                "mathematical programme route"
            ),
            "boundary": (
                "Problem routes are navigation context; they expand the paper, "
                "reviewed families, declarations, sources, and exact open "
                "obligations without promoting a claim or replacing Lean "
                "authority."
            ),
        },
        "claim_family_route_contract": {
            "source": (
                "docs/claims.json::claims[].declarations and "
                "machine_readable_paper.entrypoints"
            ),
            "matching": (
                "exact source module declaration claim plus its canonical "
                "mathematical programme route"
            ),
            "claim_registry_context": (
                "When the canonical claims review matrix or publication-assembly "
                "contribution-family record explicitly names the claim, its grouped "
                "significance and method boundary are returned as context, not as a "
                "new family."
            ),
            "boundary": (
                "Claim-family routes expose the registered claim, representative "
                "declarations, paper anchor, problem route, and exact open "
                "propositions. They do not promote subordinate declarations or "
                "replace claim or Lean authority."
            ),
        },
        "route_memory": module_route_memory,
        "declaration_preview_receipt": {
            "total": len(declarations),
            "emitted": min(len(declarations), packet_limit),
            "omitted": max(0, len(declarations) - packet_limit),
            "requested_limit": limit,
            "effective_limit": packet_limit,
            "expand": f"python3 scripts/query_corpus.py --search {module['path']} --limit {MAX_LIMIT}",
            "exhaustive": "docs/declaration_atlas.json",
        },
        "dependency_neighbourhood": {
            "imports": [
                compact_module(row, roles)
                for row in imported_rows[:packet_limit]
            ],
            "importers": [
                compact_module(row, roles)
                for row in importer_rows[:packet_limit]
            ],
            "receipt": {
                "imports_total": len(imported_rows),
                "imports_emitted": min(len(imported_rows), packet_limit),
                "imports_omitted": max(0, len(imported_rows) - packet_limit),
                "importers_total": len(importer_rows),
                "importers_emitted": min(len(importer_rows), packet_limit),
                "importers_omitted": max(0, len(importer_rows) - packet_limit),
                "requested_limit": limit,
                "effective_limit": packet_limit,
                "exhaustive": "docs/claims.json::machine_readable_paper.module_graph",
            },
        },
        "validation": "python3 scripts/build_declaration_atlas.py --check",
    }


SEARCH_STOP_WORDS = frozenset(
    {
        "a",
        "an",
        "and",
        "are",
        "as",
        "at",
        "be",
        "been",
        "close",
        "for",
        "from",
        "how",
        "has",
        "in",
        "is",
        "it",
        "of",
        "on",
        "or",
        "the",
        "to",
        "what",
        "why",
        "with",
    }
)

SEARCH_TERM_ALIASES = {
    "adjacency": "adjunction",
    "cert": "certificate",
    "certified": "certificate",
    "certificate": "certificate",
    "denominator": "den",
    "divides": "dvd",
    "divisibility": "dvd",
    "divisible": "dvd",
    "fail": "obstruction",
    "failed": "obstruction",
    "failure": "obstruction",
    "int": "integrality",
    "integer": "integrality",
    "integral": "integrality",
    "integrality": "integrality",
    "member": "mem",
    "membership": "mem",
    "nonintegral": "integrality",
    "nonintegrality": "integrality",
    "open": "resolution_status",
    "prove": "resolution_status",
    "proved": "resolution_status",
    "resolve": "resolution_status",
    "resolved": "resolution_status",
    "settle": "resolution_status",
    "settled": "resolution_status",
    "solution": "resolution_status",
    "solve": "resolution_status",
    "solved": "resolution_status",
    "unresolved": "resolution_status",
}


@lru_cache(maxsize=32_768)
def search_terms(value: str) -> set[str]:
    """Return stable lexical terms for bounded natural-language fallback."""
    terms: set[str] = set()
    value = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", " ", value)
    folded = "".join(
        character
        for character in unicodedata.normalize("NFKD", value.casefold())
        if not unicodedata.combining(character)
    )
    folded = re.sub(r"\bno[\s-]+go\b", " obstruction ", folded)
    for token in re.findall(r"[a-z0-9]+", folded):
        if token in SEARCH_STOP_WORDS:
            continue
        if token.endswith("ing") and len(token) > 6:
            token = token[:-3]
        elif token.endswith("s") and len(token) > 4 and not token.endswith("ss"):
            token = token[:-1]
        terms.add(SEARCH_TERM_ALIASES.get(token, token))
    return terms


@lru_cache(maxsize=256)
def semantic_content_terms(query: str) -> set[str]:
    """Remove question-operator scaffolding before matching mathematical content."""
    operator = semantic_query_operator(query)
    cue_terms = set().union(
        *(search_terms(cue) for cue in operator["cues"])
    )
    conversational_terms = {
        "after",
        "can",
        "could",
        "do",
        "does",
        "either",
        "exact",
        "expression",
        "get",
        "give",
        "have",
        "i",
        "into",
        "lemma",
        "let",
        "lets",
        "me",
        "route",
        "should",
        "show",
        "still",
        "tell",
        "theorem",
        "turn",
        "whether",
        "which",
        "would",
    }
    return search_terms(query) - cue_terms - conversational_terms


@lru_cache(maxsize=4_096)
def normalized_search_text(value: str) -> str:
    folded = "".join(
        character
        for character in unicodedata.normalize("NFKD", value.casefold())
        if not unicodedata.combining(character)
    )
    return " ".join(re.findall(r"[a-z0-9]+", folded))


def is_repository_overview_query(query: str) -> bool:
    """Recognise ordinary whole-repository orientation questions."""
    text = normalized_search_text(query)
    if re.search(r"\b(?:erdos|problem)\s*\d+\b", text) or "theorem " in text:
        return False
    exact_cues = (
        "what is in this repository",
        "what s in this repo",
        "what does this repo contain",
        "complete repository overview",
        "tell me what is here",
        "lay of the land",
        "walk me through this codebase",
        "what are the interesting and non trivial results",
        "explain this project to me",
        "what has been formalized",
        "comprehensive tour",
        "what is plectis lean",
        "everything interesting and non trivial in this repo",
    )
    return any(cue in text for cue in exact_cues)


def is_paper_reading_query(query: str) -> bool:
    """Recognise requests for the complete question-first paper guide."""
    text = normalized_search_text(query)
    if "paper" not in text and "manuscript" not in text:
        return False
    return any(
        cue in text
        for cue in (
            "which",
            "what does",
            "where",
            "read",
            "reading order",
            "start",
        )
    )


@lru_cache(maxsize=256)
def matched_semantic_vocabulary(query: str) -> list[dict[str, Any]]:
    """Return the small authored translation rows activated by one question."""
    query_text = normalized_search_text(query)
    query_term_set = search_terms(query)
    matches: list[dict[str, Any]] = []
    for row in SEMANTIC_VOCABULARY:
        labels = (row["pref_label"], *row["alt_labels"])
        if any(
            (
                (label_text := normalized_search_text(label)) in query_text
                or (
                    len(label_terms := search_terms(label)) >= 2
                    and label_terms <= query_term_set
                )
            )
            for label in labels
        ):
            matches.append(dict(row))
    return matches


@lru_cache(maxsize=256)
def semantic_query_operator(query: str) -> dict[str, Any]:
    """Classify the question-shaped operator independently of result ranking."""
    query_text = normalized_search_text(query)
    query_terms = search_terms(query)
    if (
        "resolution_status" in query_terms
        and query_terms & {"claim", "public", "release", "status"}
    ) or (
        "what should i try next" in query_text
        or "what blocks" in query_text
        or "what remains" in query_text
        or "missing" in query_text
    ):
        operator_id = "frontier"
    elif re.search(r"\bcan\b.+\bsolve\b", query_text) or any(
        cue in query_text
        for cue in (
            "cannot",
            "counterexample",
            "dead end",
            "does not",
            "failed",
            "worth pursuing",
        )
    ):
        operator_id = "falsify"
    elif any(cue in query_text for cue in ("analog", "analogy", "compare", "transfer")):
        operator_id = "analogy"
    elif any(
        cue in query_text
        for cue in (
            "need",
            "premise",
            "need to prove",
            "support",
            "approach",
            "proof socket",
            "socket",
        )
    ) or re.search(
        r"\bcan\b.+\b(?:provide|yield|imply|establish)\b", query_text
    ) or re.search(
        r"\b(?:theorem|lemma)\b.+\b(?:turns?|takes?)\b.+\binto\b",
        query_text,
    ):
        operator_id = "support"
    elif any(cue in query_text for cue in ("why", "depends on", "builds on", "trace")):
        operator_id = "trace"
    elif any(cue in query_text for cue in ("explain", "understand", "overview", "story")):
        operator_id = "digest"
    else:
        operator_id = "locate"
    return next(
        dict(row) for row in SEMANTIC_QUERY_OPERATORS if row["id"] == operator_id
    )


@lru_cache(maxsize=256)
def semantic_query_interpretation(query: str) -> dict[str, Any]:
    matched_rows = matched_semantic_vocabulary(query)
    routed_rows = (
        [row for row in matched_rows if row["vocabulary_kind"] == "entity"]
        or matched_rows
    )
    expansions = list(
        dict.fromkeys(
            expansion
            for row in matched_rows
            for expansion in row["query_expansions"]
        )
    )
    semantic_node_hints = list(
        dict.fromkeys(
            node_id
            for row in matched_rows
            for node_id in row.get("semantic_node_hints", ())
        )
    )
    return {
        "operator": semantic_query_operator(query),
        "matched_vocabulary": [
            {
                "id": row["id"],
                "pref_label": row["pref_label"],
                "query_expansions": list(row["query_expansions"]),
                "route_hints": list(row["route_hints"]),
            }
            for row in matched_rows
        ],
        "expanded_queries": expansions,
        "prioritized_route_hints": list(
            dict.fromkeys(
                hint for row in routed_rows for hint in row["route_hints"]
            )
        ),
        "authored_semantic_followups": [
            {
                "node_id": node_id,
                "command": (
                    "python3 scripts/query_semantic.py node "
                    f"{node_id}"
                ),
            }
            for node_id in semantic_node_hints
        ],
        "authority_posture": (
            "authored_navigation_translation_not_proof_or_claim_status_authority"
        ),
    }


def semantic_dictionary_packet() -> dict[str, Any]:
    claims = load("docs/claims.json")
    problems = load("docs/problems.json").get("problems", [])
    return {
        "kind": "semantic_dictionary",
        "schema_version": SEMANTIC_DICTIONARY_SCHEMA,
        "authority_posture": (
            "authored_navigation_translation_not_proof_or_claim_status_authority"
        ),
        "operators": [
            {
                **dict(row),
                "cues": list(row["cues"]),
            }
            for row in SEMANTIC_QUERY_OPERATORS
        ],
        "vocabulary": [
            {
                **dict(row),
                "alt_labels": list(row["alt_labels"]),
                "query_expansions": list(row["query_expansions"]),
                "route_hints": list(row["route_hints"]),
            }
            for row in SEMANTIC_VOCABULARY
        ],
        "route_discovery_contract": {
            "source": (
                "docs/claims.json::machine_readable_paper.entrypoints[]."
                "discovery_terms plus docs/publication_contract.json::"
                "entrypoints[].discovery_terms"
            ),
            "matching": (
                "A unique exact normalized authored term may bypass the exhaustive "
                "declaration scan; ambiguous or non-exact language falls through "
                "to transparent vocabulary expansion and ranked corpus search."
            ),
            "routes": [
                {
                    "route_id": row["id"],
                    "discovery_terms": list(row.get("discovery_terms", [])),
                }
                for row in all_entrypoints(claims)
                if row.get("discovery_terms")
            ],
        },
        "problem_registry_contract": {
            "source": "docs/problems.json",
            "matching": (
                "Exact accent-insensitive problem phrases, ids, short titles, and "
                "indexed questions route without an atlas scan. Navigation grants "
                "neither reviewed claim status nor Lean proof authority."
            ),
            "problems": [
                {
                    "problem_id": row["problem_id"],
                    "erdos_number": row["erdos_number"],
                    "short_title": row["short_title"],
                    "examples": [
                        f"Erdős problem {row['erdos_number']}",
                        f"Erdos problem {row['erdos_number']}",
                        f"problem {row['erdos_number']}",
                        row["problem_id"],
                    ],
                    "follow": (
                        "python3 scripts/query_semantic.py problem-registry "
                        f"--problem {row['erdos_number']}"
                    ),
                }
                for row in problems
            ],
        },
        "consumer_action": (
            "Load this packet first; follow a typed route hint or inspect the "
            "transparent --search interpretation."
        ),
        "proof_authority": "Lean source checked by the pinned Lean kernel",
    }


@lru_cache(maxsize=256)
def semantic_query_variants(query: str) -> list[set[str]]:
    return [
        terms
        for expansion in semantic_query_interpretation(query)["expanded_queries"]
        if (terms := search_terms(expansion))
    ]


@lru_cache(maxsize=256)
def semantic_hint_targets(query: str) -> dict[tuple[str, str], int]:
    flag_to_kind = {
        "--claim": "claim",
        "--declaration": "declaration",
        "--open": "open_proposition",
        "--route": "reading_route",
    }
    targets: dict[tuple[str, str], int] = {}
    for index, hint in enumerate(
        semantic_query_interpretation(query)["prioritized_route_hints"]
    ):
        parts = hint.split(maxsplit=1)
        if len(parts) != 2 or parts[0] not in flag_to_kind:
            continue
        targets[(flag_to_kind[parts[0]], parts[1])] = index
    return targets


def status_question_target(query: str) -> tuple[str, str, str] | None:
    """Return the target claim, problem number, and principal open proposition."""
    terms = search_terms(query)
    if "resolution_status" not in terms:
        return None
    if "249" in terms:
        return (
            "erdos_249",
            "249",
            "remaining_open.erdos_249_irrationality",
        )
    if "257" in terms:
        return (
            "universal_257",
            "257",
            "remaining_open.universal_257_all_infinite_supports",
        )
    return None


def is_generic_claim_status_query(
    query: str, status_taxonomy: dict[str, str]
) -> bool:
    """Recognise corpus-wide status questions independently of route copy."""
    terms = search_terms(query)
    if "resolution_status" in terms and terms & {
        "claim",
        "list",
        "result",
        "status",
    }:
        return True
    return any(
        status_terms - {"resolution_status"} and status_terms <= terms
        for status in status_taxonomy
        if (status_terms := search_terms(status))
    )


def search_rank(query: str, primary: str, haystack: str) -> int | None:
    needle = query.casefold()
    key = primary.casefold()
    body = haystack.casefold()
    if needle == key:
        return 0
    if key.startswith(needle):
        return 1
    if needle in key:
        return 2
    if needle in body:
        return 3
    query_terms = semantic_content_terms(query)
    if not query_terms:
        return None
    key_terms = search_terms(primary)
    body_terms = search_terms(haystack)
    if query_terms <= key_terms:
        return 4
    if query_terms <= body_terms:
        return 5
    for index, variant_terms in enumerate(semantic_query_variants(query)):
        if variant_terms <= key_terms:
            return 6 + index
        if variant_terms <= body_terms:
            return 8 + index
        matched_variant = len(variant_terms & (key_terms | body_terms))
        required_variant = max(2, (2 * len(variant_terms) + 2) // 3)
        if matched_variant >= required_variant:
            return 12 + index + len(variant_terms) - matched_variant
    matched = len(query_terms & (key_terms | body_terms))
    required = max(2, (2 * len(query_terms) + 2) // 3)
    if matched >= required:
        return 10 + len(query_terms) - matched
    return None


def search_result_sort_key(
    item: tuple[int, str, dict[str, Any]]
) -> tuple[int, int, int, str]:
    """Keep typed-handle lookup exact while preferring routes for semantic ties."""
    rank, stable_key, result = item
    if rank <= 2:
        return (rank, 0, 0, stable_key)
    semantic_kind_priority = {
        "reading_route": 0,
        "publication_family": 1,
        "reviewed_result_family": 1,
        "open_proposition": 2,
        "claim": 3,
        "paper_anchor": 4,
        "declaration": 5,
        "module": 6,
        "artifact": 7,
    }
    addressability_priority = (
        1
        if result["kind"] == "declaration"
        and not result.get("externally_addressable", True)
        else 0
    )
    return (
        rank,
        addressability_priority,
        semantic_kind_priority.get(result["kind"], 99),
        stable_key,
    )


def exact_discovery_route(
    query: str, claims: dict[str, Any]
) -> dict[str, Any] | None:
    """Resolve an authored first-contact phrase without scanning 151k declarations.

    Discovery terms are an explicit routing contract, not fuzzy corpus content.
    An exact normalized match may therefore take the fast path while all other
    phrasing still receives the exhaustive ranked search below.
    """
    normalized_query = normalized_search_text(query)
    matches: list[dict[str, Any]] = []
    for row in all_entrypoints(claims):
        candidates = (row["id"], *row.get("discovery_terms", []))
        if normalized_query not in {
            normalized_search_text(str(candidate))
            for candidate in candidates
        }:
            continue
        matches.append(row)
    if len(matches) != 1:
        return None
    row = matches[0]
    return {
        "kind": "reading_route",
        "id": row["id"],
        "route_kind": row.get("route_kind", "reading_route"),
        "title": row.get("title"),
        "intent": row["intent"],
        "problem_target_claim_ids": row.get("problem_target_claim_ids", []),
    }


def has_exact_discovery_term(query: str, claims: dict[str, Any]) -> bool:
    """Distinguish an ambiguous authored phrase from an unseen paraphrase."""
    normalized_query = normalized_search_text(query)
    return any(
        normalized_query
        in {
            normalized_search_text(str(candidate))
            for candidate in (row["id"], *row.get("discovery_terms", []))
        }
        for row in all_entrypoints(claims)
    )


def _source_current_research_corpus(
    row: Mapping[str, Any]
) -> dict[str, Any] | None:
    """Attach a research route only while its public files are source-current."""
    research = row.get("research_corpus")
    if research is None:
        return None
    if not isinstance(research, Mapping):
        raise ValueError("research corpus route must be an object")
    indexed_files = research.get("files")
    if not isinstance(indexed_files, Mapping):
        raise ValueError("research corpus route files are missing")
    files: dict[str, dict[str, str]] = {}
    file_digests: dict[str, str] = {}
    for key in ("frontier", "strongest_results", "manifest", "checkpoint"):
        indexed = indexed_files.get(key)
        if not isinstance(indexed, Mapping):
            raise ValueError(f"research corpus route file is missing: {key}")
        raw_path = indexed.get("path")
        if not isinstance(raw_path, str) or not raw_path:
            raise ValueError(f"research corpus route file path is invalid: {key}")
        relative = Path(raw_path)
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError(f"research corpus route path escapes root: {raw_path}")
        path = ROOT / relative
        if not path.is_file() or path.is_symlink():
            raise ValueError(f"research corpus route file is unavailable: {raw_path}")
        digest = "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()
        if indexed.get("content_digest") != digest:
            raise ValueError(f"research corpus route digest drift: {raw_path}")
        files[key] = {"path": raw_path, "content_digest": digest}
        file_digests[key] = digest
    return {
        **dict(research),
        "files": files,
        "source_fingerprint": {
            "problem_index": {
                "path": "docs/problems.json",
                "content_digest": "sha256:"
                + hashlib.sha256(
                    (ROOT / "docs" / "problems.json").read_bytes()
                ).hexdigest(),
            },
            "files": file_digests,
        },
    }


def problem_registry_route(query: str) -> dict[str, Any] | None:
    """Resolve one exact public Erdős-problem phrase without an atlas scan."""
    normalized_query = normalized_search_text(query)
    matches = []
    for row in load("docs/problems.json").get("problems", []):
        problem = str(row["erdos_number"])
        candidates = {
            normalized_search_text(f"Erdős problem {problem}"),
            normalized_search_text(f"Erdos problem {problem}"),
            normalized_search_text(f"problem {problem}"),
            normalized_search_text(str(row["problem_id"])),
            normalized_search_text(str(row["short_title"])),
            normalized_search_text(str(row["question"])),
        }
        if normalized_query in candidates:
            matches.append(row)
    if len(matches) != 1:
        return None
    row = matches[0]
    problem = str(row["erdos_number"])
    claims = load("docs/claims.json")
    paper = row.get("paper") or {}
    paper_source = paper.get("source")
    result_families = []
    for rank, family in enumerate(
        reviewed_result_family_rows(claims, row["erdos_number"]), 1
    ):
        declarations = [
            str(declaration) for declaration in family.get("declarations", [])
        ]
        if not declarations:
            declarations = reviewed_result_family_source_declarations(
                claims, row["erdos_number"], family["id"]
            )
        matching_paper_anchors = paper_anchor_routes_for_declarations(
            paper_source, declarations
        )
        result_families.append(
            {
                "rank": rank,
                "id": family["id"],
                "contribution_class": family.get("contribution_class"),
                "summary": family.get("summary"),
                "evidence_mode": family.get("evidence_mode"),
                "comparator_disposition": family.get(
                    "comparator_disposition"
                ),
                "declarations": declarations,
                "declaration_routes": [
                    "python3 scripts/query_corpus.py --declaration "
                    f"{declaration}"
                    for declaration in declarations
                ],
                "paper_route": {
                    "source": paper_source,
                    "command": (
                        "python3 scripts/query_corpus.py --paper-source "
                        f"{paper_source}"
                    )
                    if paper_source
                    else None,
                    "matching_anchors": matching_paper_anchors,
                    "authority_posture": (
                        "authored_paper_navigation_not_proof_authority"
                    ),
                },
                "boundary": family.get("boundary"),
            }
        )
    route = {
        "kind": "problem",
        "id": row["problem_id"],
        "erdos_number": row["erdos_number"],
        "title": row["short_title"],
        "status": row["status"],
        "question": row["question"],
        "directory": row["directory"],
        "module_count": len(row.get("modules", [])),
        "declaration_count": sum(
            int(module.get("declaration_count", 0))
            for module in row.get("modules", [])
        ),
        "open_obligation_ids": [
            obligation["id"] for obligation in row.get("open_obligations", [])
        ],
        "open_obligations": row.get("open_obligations", []),
        "note": row.get("note"),
        "paper": paper,
        "result_family_contract": {
            "source": "docs/claims.json::external_verification_packet.review_matrix",
            "meaning": (
                "Each row is an authored contribution family for this problem. "
                "The family summary, evidence mode, declaration handles, and "
                "boundary are navigation context; they do not promote an "
                "expansion result into a reviewed claim or close the problem."
            ),
            "ordering": (
                "Claim-registry review-matrix order; all families are retained, "
                "and no theorem or declaration count is used as a significance "
                "proxy."
            ),
        },
        "result_families": result_families,
        "follow": {
            "semantic_problem_registry": (
                "python3 scripts/query_semantic.py problem-registry "
                f"--problem {problem}"
            ),
            "semantic_inventory": (
                "python3 scripts/query_semantic.py inventory "
                f"--problem {problem}"
            ),
            "authored_population": (
                "python3 scripts/query_semantic.py structural-backlog "
                f"--problem {problem}"
            ),
            "route_memory": (
                "python3 scripts/query_route_memory.py --problem "
                f"{problem}"
            ),
        },
        "authority_posture": (
            "generated_problem_index_route_not_claim_status_or_Lean_proof_authority"
        ),
    }
    research = _source_current_research_corpus(row)
    if research is not None:
        route["research_corpus"] = research
    return route


def corpus_scope_boundary_packet(query: str) -> dict[str, Any] | None:
    """Reject explicit problem numbers absent from the live public registry."""
    normalized_query = normalized_search_text(query)
    requested_numbers = {
        int(match)
        for pattern in (
            r"\berdos(?:\s+problem)?\s*#?\s*(\d+)\b",
            r"\bproblem\s*#?\s*(\d+)\b(?!\s*/)",
        )
        for match in re.findall(pattern, normalized_query)
    }
    if not requested_numbers:
        return None

    indexed_numbers = {
        int(row["erdos_number"])
        for row in load("docs/problems.json").get("problems", [])
    }
    outside_numbers = sorted(requested_numbers - indexed_numbers)
    if not outside_numbers:
        return None

    covered_numbers = sorted(requested_numbers & indexed_numbers)
    return {
        "kind": "corpus_scope_boundary",
        "authority_posture": (
            "public_corpus_coverage_receipt_not_claim_status_or_Lean_proof_authority"
        ),
        "query": query,
        "status": (
            "explicit_problem_partially_out_of_scope"
            if covered_numbers
            else "explicit_problem_not_indexed"
        ),
        "requested_problem_numbers": sorted(requested_numbers),
        "out_of_scope_problem_numbers": outside_numbers,
        "covered_problem_numbers": covered_numbers,
        "indexed_problem_numbers": sorted(indexed_numbers),
        "scope_source": "docs/problems.json",
        "match_count": 0,
        "claim_effect": "none",
        "private_state_disclosure": "none",
        "next": (
            "Use a public corpus whose live problem registry includes the "
            "requested problem; this corpus will not substitute ranked results "
            "from other problems."
        ),
    }


def direct_route_search_packet(
    query: str,
    limit: int,
    route: dict[str, Any],
    *,
    selection: str,
    remaining_open_proposition_ids: tuple[str, ...] = (),
) -> dict[str, Any]:
    """Return one source-grounded route without paying the declaration scan."""
    missing_registered_artifacts = [
        row["artifact_handle"]
        for row in artifact_inventory()
        if row.get("availability") == "missing"
    ]
    interpretation = semantic_query_interpretation(query)
    routed_route = dict(route)
    if route.get("route_kind") == "mathematical_programme":
        routed_route["route_memory"] = route_packet(route["id"]).get(
            "route_memory"
        )
    routed_results = [routed_route]
    if (
        interpretation["operator"]["id"] == "frontier"
        and remaining_open_proposition_ids
    ):
        claims = load("docs/claims.json")
        open_index = {
            row["id"]: row
            for row in claims["remaining_open_propositions"]
        }
        routed_results.extend(
            {
                "kind": "open_proposition",
                **open_index[open_id],
                "route_memory": open_proposition_packet(open_id)[
                    "route_memory"
                ],
            }
            for open_id in remaining_open_proposition_ids
            if open_id in open_index
        )
    visible_results = routed_results[:limit]
    return {
        "kind": "search",
        "authority_posture": "navigation_projection_not_proof_authority",
        "query": query,
        "query_interpretation": interpretation,
        "match_count": len(routed_results),
        "results": visible_results,
        "omitted_match_count": len(routed_results) - len(visible_results),
        "limit": limit,
        "routing_receipt": {
            "selection": selection,
            "declaration_scan_required": False,
        },
        "artifact_availability_receipt": {
            "status": (
                "partial_optional_artifacts_missing"
                if missing_registered_artifacts
                else "all_registered_artifacts_present"
            ),
            "missing_registered_artifacts": missing_registered_artifacts,
            "effect_on_search": (
                "missing authored artifacts are omitted from paper-anchor "
                "indexing; claims, routes, open propositions, declarations, "
                "modules, and present papers remain searchable"
            ),
        },
        "next": "Use --route on this handle, then follow its bounded query and action steps.",
    }


def search_packet(query: str, limit: int) -> dict[str, Any]:
    query = query.strip()
    if not query:
        raise ValueError("search query must not be empty")
    scope_boundary = corpus_scope_boundary_packet(query)
    if scope_boundary is not None:
        return scope_boundary
    claims = load("docs/claims.json")
    hint_targets = semantic_hint_targets(query)
    problem_route = problem_registry_route(query)
    if problem_route is not None:
        return direct_route_search_packet(
            query,
            limit,
            problem_route,
            selection="exact_problem_registry_term",
            remaining_open_proposition_ids=tuple(
                problem_route.get("remaining_open_proposition_ids", [])
            ),
        )
    exact_route = exact_discovery_route(query, claims)
    if exact_route is not None:
        return direct_route_search_packet(
            query,
            limit,
            exact_route,
            selection="exact_authored_discovery_term",
            remaining_open_proposition_ids=tuple(
                exact_route.get("remaining_open_proposition_ids", [])
            ),
        )
    hinted_route_ids = [
        handle
        for (kind, handle), _priority in sorted(
            hint_targets.items(), key=lambda item: item[1]
        )
        if kind == "reading_route"
    ]
    if (
        len(hinted_route_ids) == 1
        and not has_exact_discovery_term(query, claims)
    ):
        hinted_row = next(
            (
                row
                for row in all_entrypoints(claims)
                if row["id"] == hinted_route_ids[0]
            ),
            None,
        )
        if hinted_row is not None:
            return direct_route_search_packet(
                query,
                limit,
                {
                    "kind": "reading_route",
                    "id": hinted_row["id"],
                    "route_kind": hinted_row.get(
                        "route_kind", "reading_route"
                    ),
                    "title": hinted_row.get("title"),
                    "intent": hinted_row["intent"],
                    "problem_target_claim_ids": hinted_row.get(
                        "problem_target_claim_ids", []
                    ),
                },
                selection="controlled_vocabulary_route",
                remaining_open_proposition_ids=tuple(
                    hinted_row.get("remaining_open_proposition_ids", [])
                ),
            )
    claims_by_id = {row["id"]: row for row in claims["claims"]}
    atlas = load("docs/declaration_atlas.json")
    aliases = load("paper/module-aliases.json")["aliases"]
    sigil_by_path = {row["path"]: row["sigil"] for row in aliases}
    roles = module_roles(claims)
    status_target = status_question_target(query)
    generic_claim_status_query = (
        status_target is None
        and is_generic_claim_status_query(query, claims["status_taxonomy"])
    )
    ranked: list[tuple[int, str, dict[str, Any]]] = []

    for artifact in artifact_inventory():
        rank = search_rank(
            query,
            artifact["artifact_handle"],
            " ".join(
                str(value)
                for value in (
                    artifact["artifact_id"],
                    artifact["artifact_kind"],
                    artifact["artifact_role"],
                    artifact["content_digest"],
                )
            ),
        )
        if rank is not None:
            ranked.append(
                (
                    rank,
                    f"artifact:{artifact['artifact_handle']}:{artifact['artifact_id']}",
                    {
                        "kind": "artifact",
                        "artifact_id": artifact["artifact_id"],
                        "artifact_handle": artifact["artifact_handle"],
                        "artifact_kind": artifact["artifact_kind"],
                        "content_digest": artifact["content_digest"],
                    },
                )
            )

    for anchor in paper_anchor_inventory():
        primary = anchor["label"] or anchor["canonical_handle"]
        rank = search_rank(
            query,
            primary,
            " ".join(
                str(value)
                for value in (
                    anchor["title"],
                    anchor["environment"],
                    anchor["anchor_class"],
                    anchor["paper"]["source_ref"],
                )
                if value
            ),
        )
        if rank is not None:
            ranked.append(
                (
                    rank,
                    f"paper_anchor:{anchor['canonical_handle']}",
                    {
                        "kind": "paper_anchor",
                        "canonical_handle": anchor["canonical_handle"],
                        "label": anchor["label"],
                        "title": anchor["title"],
                        "anchor_class": anchor["anchor_class"],
                        "source_ref": anchor["paper"]["source_ref"],
                        "route_memory": paper_anchor_packet(
                            anchor["canonical_handle"]
                        )["route_memory"],
                    },
                )
            )

    for proposition in claims["remaining_open_propositions"]:
        target = claims_by_id.get(proposition["open_target_claim"], {})
        rank = search_rank(
            query,
            proposition["id"],
            " ".join(
                str(value)
                for value in (
                    proposition["statement"],
                    proposition["open_target_claim"],
                    target.get("label"),
                    target.get("statement"),
                    target.get("status"),
                    proposition.get("paper_anchor", {}).get("title"),
                    "open unresolved not solved",
                )
                if value
            ),
        )
        if status_target and proposition["open_target_claim"] == status_target[0]:
            rank = -1 if proposition["id"] == status_target[2] else 0
        if (
            hint_priority := hint_targets.get(
                ("open_proposition", proposition["id"])
            )
        ) is not None:
            rank = -10 + hint_priority
        if rank is not None:
            ranked.append(
                (
                    rank,
                    f"open_proposition:{proposition['id']}",
                    {
                        "kind": "open_proposition",
                        **proposition,
                        "route_memory": open_proposition_packet(
                            proposition["id"]
                        )["route_memory"],
                    },
                )
            )

    for claim in claims["claims"]:
        rank = search_rank(
            query,
            claim["id"],
            " ".join(
                str(value)
                for value in (claim["label"], claim["statement"], claim["status"], claim.get("paper_label"))
                if value
            ),
        )
        if (
            hint_priority := hint_targets.get(("claim", claim["id"]))
        ) is not None:
            rank = -10 + hint_priority
        if rank is not None:
            ranked.append(
                (
                    rank,
                    f"claim:{claim['id']}",
                    {
                        "kind": "claim",
                        **compact_claim(claim),
                        # A search hit is a resumable handoff, not just a
                        # status row. Keep its complete canonical route
                        # bindings so readers do not lose the selected
                        # problem at this bounded fan-in boundary.
                        "route_memory": claim_route_memory_projection(
                            claim["id"], claims
                        ),
                    },
                )
            )

    for row in atlas_declarations(atlas):
        rank = search_rank(
            query,
            row["name"],
            " ".join(str(value) for value in (row["signature"], row.get("docstring"), row["module"]) if value),
        )
        if (
            hint_priority := hint_targets.get(
                ("declaration", row["name"])
            )
        ) is not None:
            rank = -10 + hint_priority
        if rank is not None:
            result = {"kind": "declaration", **compact_declaration(row)}
            if row.get("signature"):
                result["signature_excerpt"] = str(row["signature"])[:240]
            result["route_memory"] = declaration_route_memory_rows(
                [row], claims
            )[0]["route_memory"]
            ranked.append((rank, f"declaration:{row['module']}:{row['line']}:{row['name']}", result))

    for row in atlas["modules"]:
        sigil = sigil_by_path.get(row["path"])
        synopsis = module_synopsis(row["path"])
        ranks = [
            search_rank(
                query,
                row["id"],
                " ".join(value for value in (row["path"], synopsis) if value),
            )
        ]
        if sigil:
            ranks.append(search_rank(query, sigil, row["id"] + " " + row["path"]))
        rank = min((value for value in ranks if value is not None), default=None)
        if rank is not None:
            ranked.append(
                (
                    rank,
                    f"module:{row['id']}",
                    {
                        "kind": "module",
                        "id": row["id"],
                        "path": row["path"],
                        "authored_synopsis_excerpt": (
                            synopsis[:480] if synopsis else None
                        ),
                        "paper_sigil": sigil,
                        "role": roles.get(row["id"], "Unclassified module"),
                        "declaration_count": row["declaration_count"],
                        "import_count": len(row["imports"]),
                        "route_memory": module_route_memory_projection(
                            [
                                declaration
                                for declaration in atlas_declarations(atlas)
                                if declaration["module"] == row["path"]
                            ],
                            claims,
                        ),
                    },
                )
            )

    publication_assembly = claims["machine_readable_paper"]["publication_assembly"]
    for row in publication_assembly["contribution_families"]:
        rank = search_rank(
            query,
            row["id"],
            " ".join(
                str(value)
                for value in (
                    row["status_summary"],
                    row["prior_art_posture"],
                    row["primary_narrative_owner"],
                    row["consumer_or_open_obligation"],
                    row["view_decision"],
                    *row["claim_ids"],
                )
            ),
        )
        if rank is not None:
            ranked.append(
                (
                    rank,
                    f"publication_family:{row['id']}",
                    {
                        "kind": "publication_family",
                        "id": row["id"],
                        "status_summary": row["status_summary"],
                        "primary_narrative_owner": row["primary_narrative_owner"],
                        "view_decision": row["view_decision"],
                        # Search is a bounded reader entry point too: preserve
                        # the same canonical resume identity as the dedicated
                        # family packet instead of dropping the route binding
                        # at the fan-in boundary.
                        "route_memory": publication_family_packet(row["id"])[
                            "route_memory"
                        ],
                    },
                )
            )

    problem_papers = {
        str(row["erdos_number"]): (row.get("paper") or {})
        for row in load("docs/problems.json").get("problems", [])
    }
    for census_row in reviewed_result_family_census(claims):
        paper = problem_papers.get(str(census_row["erdos_number"]), {})
        for rank, family in enumerate(
            reviewed_result_family_rows(claims, census_row["erdos_number"]), 1
        ):
            rank_value = search_rank(
                query,
                family["id"],
                " ".join(
                    str(value)
                    for value in (
                        family.get("summary"),
                        family.get("contribution_class"),
                        family.get("evidence_mode"),
                        family.get("comparator_disposition"),
                        census_row["erdos_number"],
                    )
                    if value
                ),
            )
            if rank_value is not None:
                ranked.append(
                    (
                        rank_value,
                        f"reviewed_result_family:{census_row['erdos_number']}:{family['id']}",
                        {
                            "kind": "reviewed_result_family",
                            "id": family["id"],
                            "erdos_number": census_row["erdos_number"],
                            "rank": rank,
                            "contribution_class": family.get(
                                "contribution_class"
                            ),
                            "summary": family.get("summary"),
                            "evidence_mode": family.get("evidence_mode"),
                            "comparator_disposition": family.get(
                                "comparator_disposition"
                            ),
                            "boundary": family.get("boundary"),
                            "problem_route": (
                                "python3 scripts/query_corpus.py --route erdos_"
                                f"{census_row['erdos_number']}"
                            ),
                            "paper_source": paper.get("source"),
                            "paper_source_route": (
                                "python3 scripts/query_corpus.py --paper-source "
                                f"{paper['source']}"
                                if paper.get("source")
                                else None
                            ),
                        },
                    )
                )

    for artifact in publication_contract()["artifacts"]:
        rank = search_rank(
            query,
            artifact["id"],
            " ".join(
                str(value)
                for value in (
                    artifact["title"],
                    artifact["artifact_class"],
                    artifact["claim_scope"],
                    artifact["source_path"],
                    artifact["rendered_path"],
                    artifact.get("evidence_boundary"),
                )
                if value
            ),
        )
        if rank is not None:
            ranked.append(
                (
                    rank,
                    f"publication_artifact:{artifact['id']}",
                    {
                        "kind": "publication_artifact",
                        "id": artifact["id"],
                        "title": artifact["title"],
                        "artifact_class": artifact["artifact_class"],
                        "source_path": artifact["source_path"],
                        "rendered_path": artifact["rendered_path"],
                    },
                )
            )

    for mutation in publication_evidence()["evaluation"]["mutations"]:
        rank = search_rank(
            query,
            f"mutation {mutation['id']}",
            " ".join(
                str(value)
                for value in (
                    mutation["description"],
                    mutation["outcome"],
                    mutation.get("first_detector"),
                    *mutation.get("additional_detectors", []),
                )
                if value
            ),
        )
        if rank is not None:
            ranked.append(
                (
                    rank,
                    f"publication_evidence:{mutation['id']}",
                    {
                        "kind": "publication_evidence",
                        "id": mutation["id"],
                        "outcome": mutation["outcome"],
                        "first_detector": mutation.get("first_detector"),
                        "description": mutation["description"],
                    },
                )
            )

    for row in all_entrypoints(claims):
        route_haystack = " ".join(
            str(value)
            for value in (
                row.get("title"),
                row["intent"],
                *row.get("discovery_terms", []),
                row.get("mathematical_focus"),
                row.get("claim_ceiling"),
                *row["read"],
                *row["query_steps"],
                *row["authority_owners"],
                *row["adjacent_handle_classes"],
                *row.get("core_claim_ids", []),
                *row.get("remaining_open_proposition_ids", []),
            )
            if value
        )
        ranks = [search_rank(query, row["id"], route_haystack)]
        ranks.extend(
            search_rank(query, discovery_term, route_haystack)
            for discovery_term in row.get("discovery_terms", [])
        )
        rank = min((value for value in ranks if value is not None), default=None)
        if (
            status_target
            and status_target[0] in row.get("problem_target_claim_ids", [])
            and {
                "resolution_status",
                status_target[1],
            }
            <= search_terms(" ".join(row.get("discovery_terms", [])))
        ):
            rank = -2
        elif generic_claim_status_query and row["id"] == "browse_claim_status":
            rank = -2
        if (
            hint_priority := hint_targets.get(("reading_route", row["id"]))
        ) is not None:
            rank = -10 + hint_priority
        if rank is not None:
            route_result = {
                "kind": "reading_route",
                "id": row["id"],
                "route_kind": row.get("route_kind", "reading_route"),
                "title": row.get("title"),
                "intent": row["intent"],
                "problem_target_claim_ids": row.get(
                    "problem_target_claim_ids", []
                ),
            }
            if row.get("route_kind") == "mathematical_programme":
                # Generic search is a reader-facing fan-in just like an exact
                # route lookup. Preserve the canonical route-memory handoff so
                # the selected problem and current source-digest contract are
                # not lost at this boundary.
                route_result["route_memory"] = route_packet(row["id"]).get(
                    "route_memory"
                )
            ranked.append(
                (
                    rank,
                    f"route:{row['id']}",
                    route_result,
                )
            )

    ranked = [
        (
            (
                -10 + hint_targets[(result["kind"], str(handle))]
                if handle is not None
                and (result["kind"], str(handle)) in hint_targets
                else rank
            ),
            stable_key,
            result,
        )
        for rank, stable_key, result in ranked
        for handle in (result.get("id") or result.get("name"),)
    ]
    ranked.sort(key=search_result_sort_key)
    results = [item[2] for item in ranked]
    missing_registered_artifacts = [
        row["artifact_handle"]
        for row in artifact_inventory()
        if row.get("availability") == "missing"
    ]
    return {
        "kind": "search",
        "authority_posture": "navigation_projection_not_proof_authority",
        "query": query,
        "query_interpretation": semantic_query_interpretation(query),
        "match_count": len(results),
        "results": results[:limit],
        "omitted_match_count": max(0, len(results) - limit),
        "limit": limit,
        "artifact_availability_receipt": {
            "status": (
                "partial_optional_artifacts_missing"
                if missing_registered_artifacts
                else "all_registered_artifacts_present"
            ),
            "missing_registered_artifacts": missing_registered_artifacts,
            "effect_on_search": (
                "missing authored artifacts are omitted from paper-anchor "
                "indexing; claims, routes, open propositions, declarations, "
                "modules, and present papers remain searchable"
            ),
        },
        "next": "Inspect --vocabulary when phrasing is uncertain, then use the typed handle with --claim, --status, --paper-source, --paper-anchor, --open, --declaration, --source, --module, --connections, --artifact, --publication-artifact, --publication-evidence, --route, or --publication-family.",
    }


def semantic_result_handle(result: dict[str, Any]) -> str:
    return str(
        result.get("id")
        or result.get("name")
        or result.get("canonical_handle")
        or result.get("artifact_handle")
        or result.get("source_ref")
        or "unresolved"
    )


def semantic_result_key(result: dict[str, Any]) -> str:
    """Return an unambiguous result key while retaining short display handles."""
    if result["kind"] == "declaration":
        return str(result.get("qualified_name") or result.get("name"))
    return semantic_result_handle(result)


def claim_formal_witnesses(claim: dict[str, Any]) -> list[dict[str, Any]]:
    """Resolve authored claim handles to exact atlas signatures and source lines."""
    atlas = load("docs/declaration_atlas.json")
    declarations = {
        (row["name"], row["module"], row["line"]): row
        for row in atlas_declarations(atlas)
    }
    claims = load("docs/claims.json")
    identity = formal_source_identity(claims)
    repository = identity["repository"].rstrip("/")
    source_ref = identity["ref"]
    witnesses = []
    for handle in claim.get("declarations", []):
        key = (handle["name"], handle["module"], handle["line"])
        declaration = declarations.get(key)
        if declaration is None:
            continue
        witnesses.append(
            {
                "name": declaration["name"],
                "qualified_name": qualified_declaration_name(declaration),
                "externally_addressable": declaration_externally_addressable(
                    declaration
                ),
                "declaration_kind": declaration["kind"],
                "signature": declaration.get("signature"),
                "source_ref": (
                    f"{declaration['module']}:{declaration['line']}"
                ),
                "source_url": (
                    f"{repository}/blob/{source_ref}/{declaration['module']}"
                    f"#L{declaration['line']}"
                ),
                "docstring": declaration.get("docstring"),
                "lean_source_identity": dict(identity),
            }
        )
    return witnesses


@lru_cache(maxsize=512)
def declaration_source_dependency_candidates(
    name: str, limit: int = 6
) -> list[dict[str, Any]]:
    """Return exact declarations named in one declaration's source span.

    This is source-current lexical evidence, not an elaborator dependency
    trace. The distinction is retained in every emitted row.
    """
    atlas = load("docs/declaration_atlas.json")
    matches = [
        row
        for row in atlas_declarations(atlas)
        if row["name"] == name or qualified_declaration_name(row) == name
    ]
    if len(matches) != 1:
        return []
    declaration = matches[0]
    module = next(
        row
        for row in atlas["modules"]
        if row["path"] == declaration["module"]
    )
    module_declarations = sorted(
        (
            row
            for row in atlas_declarations(atlas)
            if row["module"] == declaration["module"]
        ),
        key=lambda row: (row["line"], row["name"]),
    )
    declaration_index = module_declarations.index(declaration)
    source_lines = (ROOT / declaration["module"]).read_text(
        encoding="utf-8"
    ).splitlines()
    span_end = (
        module_declarations[declaration_index + 1]["line"] - 1
        if declaration_index + 1 < len(module_declarations)
        else len(source_lines)
    )
    span = "\n".join(
        source_lines[declaration["line"] - 1 : span_end]
    )
    span = re.split(r"(?m)^\s*#print\b", span, maxsplit=1)[0]
    visible_paths = {
        declaration["module"],
        *(
            row["path"]
            for row in atlas["modules"]
            if row["id"] in module.get("imports", [])
        ),
    }
    candidates = []
    for row in atlas_declarations(atlas):
        candidate_name = row["name"]
        if (
            row["module"] not in visible_paths
            or row["id"] == declaration["id"]
            or len(candidate_name) < 3
            or row["kind"] not in ("theorem", "lemma")
        ):
            continue
        occurrences = list(
            re.finditer(rf"\b{re.escape(candidate_name)}\b", span)
        )
        if not occurrences:
            continue
        candidates.append(
            (
                occurrences[0].start(),
                -len(candidate_name),
                {
                    "name": candidate_name,
                    "qualified_name": qualified_declaration_name(row),
                    "declaration_kind": row["kind"],
                    "signature": row.get("signature"),
                    "source_ref": f"{row['module']}:{row['line']}",
                    "use_count_in_declaration_span": len(occurrences),
                    "evidence_posture": (
                        "source_lexical_dependency_candidate_not_elaborator_dependency_proof"
                    ),
                },
            )
        )
    candidates.sort(key=lambda item: (item[0], item[1], item[2]["name"]))
    return [item[2] for item in candidates[:limit]]


def semantic_cell(
    query: str, result: dict[str, Any], selection_reason: str
) -> dict[str, Any]:
    """Expand one ranked handle without collapsing its authority planes."""
    kind = result["kind"]
    handle = semantic_result_handle(result)
    canonical_handle = semantic_result_key(result)
    operator_id = semantic_query_operator(query)["id"]
    expansion_command: str
    witness_edges: list[dict[str, str]] = [
        {
            "from": "query",
            "relation": "retrieved_as",
            "to": f"{kind}:{canonical_handle}",
            "authority": "navigation",
        }
    ]

    if kind == "declaration":
        packet = declaration_packet(canonical_handle, 1)
        declaration = packet["matches"][0]
        canonical_handle = declaration.get("qualified_name") or handle
        content = {
            "formal_witness": {
                key: declaration.get(key)
                for key in (
                    "name",
                    "qualified_name",
                    "externally_addressable",
                    "kind",
                    "signature",
                    "module",
                    "line",
                    "source_ref",
                    "source_url",
                    "lean_source_identity",
                )
            },
            "authored_digest": {
                "text": declaration.get("docstring"),
                "authority_posture": (
                    "authored_explanation_not_kernel_or_claim_status_authority"
                ),
            },
            "claim_status_links": declaration.get("attached_claims", []),
            "route_memory": declaration.get("route_memory"),
            "module_role": declaration.get("module_role"),
        }
        if operator_id in ("support", "trace"):
            formal_dependencies = formal_dependency_neighbourhood(
                canonical_handle,
                3 if operator_id == "trace" else 2,
            )
            content["formal_dependency_neighbourhood"] = (
                formal_dependencies
            )
            content["source_dependency_candidates"] = (
                declaration_source_dependency_candidates(canonical_handle)
            )
            if formal_dependencies["availability"] == "available":
                witness_edges.extend(
                    {
                        "from": f"declaration:{canonical_handle}",
                        "relation": "uses_elaborated_constant",
                        "to": f"declaration:{dependency['handle']}",
                        "authority": "kernel_elaborated_environment",
                    }
                    for dependency in formal_dependencies[
                        "direct_dependencies"
                    ]
                )
        expansion_command = (
            "python3 scripts/query_corpus.py --declaration "
            f"{canonical_handle}"
        )
        witness_edges.append(
            {
                "from": f"declaration:{canonical_handle}",
                "relation": "elaborated_at",
                "to": declaration["source_ref"],
                "authority": "kernel",
            }
        )
    elif kind == "claim":
        packet = claim_packet(handle)
        claim = packet["claim"]
        content = {
            "claim_record": claim,
            "formal_witnesses": claim_formal_witnesses(claim),
            "argument_neighbourhood": packet["argument_neighbourhood"],
            "remaining_open_propositions": packet[
                "remaining_open_propositions"
            ],
            "programme_contexts": packet["programme_contexts"],
            "route_memory": claim_route_memory_projection(
                handle, load("docs/claims.json")
            ),
            "paper_coordinate": packet["paper"],
            "lean_source_identity": packet["lean_source_identity"],
        }
        expansion_command = f"python3 scripts/query_corpus.py --claim {handle}"
        if operator_id in ("locate", "support", "trace", "digest"):
            witness_edges.extend(
                {
                    "from": f"claim:{handle}",
                    "relation": "has_formal_handle",
                    "to": f"declaration:{declaration['name']}",
                    "authority": "status_to_kernel_bridge",
                }
                for declaration in claim.get("declarations", [])
            )
        if operator_id in ("frontier", "falsify", "trace", "digest"):
            witness_edges.extend(
                {
                    "from": f"claim:{handle}",
                    "relation": "bounded_by",
                    "to": f"open_proposition:{proposition['id']}",
                    "authority": "status",
                }
                for proposition in packet["remaining_open_propositions"]
            )
        if operator_id == "trace":
            for direction in ("incoming", "outgoing"):
                witness_edges.extend(
                    {
                        "from": (
                            f"claim:{edge['neighbour']['id']}"
                            if direction == "incoming"
                            else f"claim:{handle}"
                        ),
                        "relation": edge["relation"],
                        "to": (
                            f"claim:{handle}"
                            if direction == "incoming"
                            else f"claim:{edge['neighbour']['id']}"
                        ),
                        "authority": "status_argument_graph",
                    }
                    for edge in packet["argument_neighbourhood"][direction]
                )
    elif kind == "open_proposition":
        packet = open_proposition_packet(handle)
        proposition = packet["open_proposition"]
        content = {
            "open_record": proposition,
            "open_target": packet["open_target"],
            "nearest_advances": packet["advancing_claims"],
            "linked_claims": packet["linked_claims"],
            "paper_anchor": packet["paper_anchor"],
            "route_memory": packet["route_memory"],
        }
        expansion_command = f"python3 scripts/query_corpus.py --open {handle}"
        witness_edges.append(
            {
                "from": f"open_proposition:{handle}",
                "relation": "keeps_open",
                "to": f"claim:{packet['open_target']['id']}",
                "authority": "status",
            }
        )
        if operator_id in ("frontier", "trace", "digest"):
            witness_edges.extend(
                {
                    "from": f"claim:{advance['claim']['id']}",
                    "relation": advance["operation"],
                    "to": f"open_proposition:{handle}",
                    "authority": "status",
                }
                for advance in packet["advancing_claims"]
            )
    elif kind == "reading_route":
        packet = route_packet(handle)
        route = packet["route"]
        programme = packet.get("programme")
        content = {
            "route": route,
            "programme": programme,
            "route_memory": packet.get("route_memory"),
        }
        expansion_command = f"python3 scripts/query_corpus.py --route {handle}"
        if programme and operator_id in ("trace", "digest"):
            witness_edges.extend(
                {
                    "from": f"reading_route:{handle}",
                    "relation": "organises",
                    "to": f"claim:{claim['id']}",
                    "authority": "navigation",
                }
                for claim in programme["core_claims"]
            )
        if programme and operator_id in (
            "frontier",
            "falsify",
            "analogy",
            "trace",
            "digest",
        ):
            witness_edges.extend(
                {
                    "from": f"reading_route:{handle}",
                    "relation": "bounded_by",
                    "to": f"open_proposition:{proposition['id']}",
                    "authority": "status",
                }
                for proposition in programme["remaining_open_propositions"]
            )
    elif kind == "module":
        packet = module_packet(handle, 6)
        content = {
            "module": packet["module"],
            "attached_claims": packet["attached_claims"],
            "declaration_preview": packet["declaration_preview"],
            "dependency_neighbourhood": packet["dependency_neighbourhood"],
            "route_memory": packet["route_memory"],
        }
        expansion_command = f"python3 scripts/query_corpus.py --module {handle}"
        witness_edges.append(
            {
                "from": f"module:{handle}",
                "relation": "authored_in",
                "to": packet["module"]["path"],
                "authority": "digestion_to_kernel_source",
            }
        )
    else:
        content = {
            "ranked_result": result,
            "notice": (
                "This handle is retained as navigation context; use its typed "
                "query command for the full owner packet."
            ),
        }
        if kind in {"paper_anchor", "publication_family"}:
            content["route_memory"] = result.get("route_memory")
        flag_by_kind = {
            "paper_anchor": "--paper-anchor",
            "module": "--module",
            "publication_family": "--publication-family",
            "artifact": "--artifact",
            "publication_artifact": "--publication-artifact",
            "publication_evidence": "--publication-evidence",
        }
        expansion_command = (
            "python3 scripts/query_corpus.py "
            f"{flag_by_kind.get(kind, '--search')} {handle}"
        )

    return {
        "cell_id": f"{kind}:{canonical_handle}",
        "kind": kind,
        "handle": handle,
        "canonical_handle": canonical_handle,
        "selection_reason": selection_reason,
        "witness_selection": {
            "operator": operator_id,
            "posture": (
                "operator_specific_decisive_edges; full typed content remains "
                "available inside the cell and through expansion_command"
            ),
        },
        "content": content,
        "witness_edges": witness_edges,
        "typed_provenance": [
            {
                "plane": "kernel",
                "owner": "pinned Lean source and Lean kernel",
                "meaning": (
                    "Only elaborated declarations and their exact source "
                    "coordinates carry proof authority."
                ),
            },
            {
                "plane": "status",
                "owner": "docs/claims.json",
                "meaning": (
                    "Claim labels, statuses, remaining-open boundaries, and "
                    "argument relations are authored registry authority."
                ),
            },
            {
                "plane": "digestion",
                "owner": "declaration docstrings and authored paper coordinates",
                "meaning": (
                    "Explanation aids comprehension but does not replace proof "
                    "or claim-status authority."
                ),
            },
            {
                "plane": "navigation",
                "owner": "scripts/query_corpus.py",
                "meaning": (
                    "Selection, vocabulary translation, and route ordering are "
                    "query-relative navigation projections."
                ),
            },
        ],
        "authority_invariant": (
            "kernel,status,digestion,navigation_are_typed_and_non_substitutable"
        ),
        "expansion_command": expansion_command,
    }


def operator_synthesis(
    operator_id: str, cells: list[dict[str, Any]]
) -> dict[str, Any]:
    """Assemble operator-specific relations without upgrading their authority."""
    if operator_id == "support":
        formal_consumers = []
        formal_dependency_neighbourhoods = []
        source_dependency_candidates = []
        unproved_requirements = []
        for cell in cells:
            if cell["kind"] == "claim":
                formal_consumers.extend(cell["content"]["formal_witnesses"])
                unproved_requirements.extend(
                    cell["content"]["remaining_open_propositions"]
                )
            elif cell["kind"] == "declaration":
                formal_consumers.append(cell["content"]["formal_witness"])
                formal_dependency_neighbourhoods.append(
                    cell["content"].get(
                        "formal_dependency_neighbourhood", {}
                    )
                )
                source_dependency_candidates.extend(
                    cell["content"].get(
                        "source_dependency_candidates", []
                    )
                )
            elif cell["kind"] == "open_proposition":
                unproved_requirements.append(cell["content"]["open_record"])
            elif cell["kind"] == "reading_route":
                programme = cell["content"].get("programme")
                if programme:
                    unproved_requirements.extend(
                        programme["remaining_open_propositions"]
                    )
        checked_consumers = list(
            {
                row.get("qualified_name") or row["name"]: row
                for row in formal_consumers
                if row.get("name")
                and (
                    row.get("kind")
                    or row.get("declaration_kind")
                )
                in {"theorem", "lemma", "corollary", "proposition"}
                and row.get("externally_addressable", True)
            }.values()
        )
        return {
            "kind": "support_synthesis",
            "checked_consumer_signatures": checked_consumers,
            "lean_application_candidates": [
                {
                    "declaration": row["name"],
                    "qualified_declaration": row.get("qualified_name"),
                    "signature": row.get("signature"),
                    "tactic": (
                        f"apply {row.get('qualified_name') or row['name']}"
                    ),
                    "authority_posture": (
                        "query_derived_tactic_candidate_requires_Lean_elaboration"
                    ),
                }
                for row in checked_consumers
            ],
            "source_dependency_candidates": list(
                {
                    (row["name"], row["source_ref"]): row
                    for row in source_dependency_candidates
                }.values()
            ),
            "formal_dependency_neighbourhoods": [
                row
                for row in formal_dependency_neighbourhoods
                if row.get("availability") == "available"
            ],
            "unproved_requirements": list(
                {
                    row["id"]: row
                    for row in unproved_requirements
                    if row.get("id")
                }.values()
            ),
            "sufficiency_posture": (
                "Only an emitted theorem signature can certify that its named "
                "hypothesis implies its conclusion; relevance alone is not "
                "joint sufficiency."
            ),
        }
    if operator_id == "analogy":
        subjects: dict[str, dict[str, Any]] = {}
        for side in ("left", "right"):
            side_cells = [
                cell
                for cell in cells
                if cell["selection_reason"] == f"analogy_{side}_subject"
            ]
            claim_ids: set[str] = set()
            open_ids: set[str] = set()
            ceilings = []
            for cell in side_cells:
                if cell["kind"] == "reading_route":
                    programme = cell["content"].get("programme")
                    if programme:
                        claim_ids.update(
                            row["id"] for row in programme["core_claims"]
                        )
                        open_ids.update(
                            row["id"]
                            for row in programme[
                                "remaining_open_propositions"
                            ]
                        )
                        ceilings.append(programme["claim_ceiling"])
                elif cell["kind"] == "claim":
                    claim_ids.add(cell["handle"])
                    open_ids.update(
                        row["id"]
                        for row in cell["content"][
                            "remaining_open_propositions"
                        ]
                    )
            subjects[side] = {
                "cell_ids": [cell["cell_id"] for cell in side_cells],
                "claim_ids": sorted(claim_ids),
                "open_proposition_ids": sorted(open_ids),
                "claim_ceilings": ceilings,
            }
        left_claims = set(subjects["left"]["claim_ids"])
        right_claims = set(subjects["right"]["claim_ids"])
        left_opens = set(subjects["left"]["open_proposition_ids"])
        right_opens = set(subjects["right"]["open_proposition_ids"])
        return {
            "kind": "analogy_synthesis",
            "subjects": subjects,
            "shared_claim_ids": sorted(left_claims & right_claims),
            "shared_open_proposition_ids": sorted(left_opens & right_opens),
            "formal_bridge_status": "not_inferred",
            "formal_bridge_requirement": (
                "A transported conclusion requires an emitted Lean theorem "
                "whose signature connects the two subjects."
            ),
        }
    if operator_id == "frontier":
        directly_selected_open_records = []
        contextual_open_records = []
        advances = []
        for cell in cells:
            if cell["kind"] == "open_proposition":
                directly_selected_open_records.append(
                    cell["content"]["open_record"]
                )
                advances.extend(cell["content"]["nearest_advances"])
            elif cell["kind"] == "reading_route":
                programme = cell["content"].get("programme")
                if programme:
                    contextual_open_records.extend(
                        programme["remaining_open_propositions"]
                    )
            elif cell["kind"] == "claim":
                contextual_open_records.extend(
                    cell["content"]["remaining_open_propositions"]
                )
        exact_open_records = (
            directly_selected_open_records or contextual_open_records
        )
        exact_open_ids = {
            row["id"] for row in exact_open_records if row.get("id")
        }
        return {
            "kind": "frontier_synthesis",
            "exact_open_records": list(
                {
                    row["id"]: row
                    for row in exact_open_records
                    if row.get("id")
                }.values()
            ),
            "adjacent_open_records": list(
                {
                    row["id"]: row
                    for row in contextual_open_records
                    if row.get("id") and row["id"] not in exact_open_ids
                }.values()
            ),
            "nearest_advances": advances,
            "boundary": (
                "Every emitted open record remains open; narrowing and "
                "re-expression operations do not discharge it."
            ),
        }
    if operator_id == "falsify":
        verdicts = []
        claim_ceilings = []
        open_requirements = []
        for cell in cells:
            if cell["kind"] == "declaration":
                digest = cell["content"]["authored_digest"]
                if digest.get("text"):
                    verdicts.append(
                        {
                            "declaration": cell["handle"],
                            "authored_digest": digest,
                            "formal_witness": cell["content"][
                                "formal_witness"
                            ],
                        }
                    )
            elif cell["kind"] == "claim":
                open_requirements.extend(
                    cell["content"]["remaining_open_propositions"]
                )
                claim_ceilings.extend(
                    row["claim_ceiling"]
                    for row in cell["content"]["programme_contexts"]
                )
            elif cell["kind"] == "reading_route":
                programme = cell["content"].get("programme")
                if programme:
                    claim_ceilings.append(programme["claim_ceiling"])
                    open_requirements.extend(
                        programme["remaining_open_propositions"]
                    )
        return {
            "kind": "falsification_synthesis",
            "authored_verdicts": verdicts,
            "claim_ceilings": list(dict.fromkeys(claim_ceilings)),
            "open_requirements": list(
                {
                    row["id"]: row
                    for row in open_requirements
                    if row.get("id")
                }.values()
            ),
            "boundary": (
                "A measured negative verdict is scoped to its stated fixture "
                "or probe; an open producer blocks promotion to a solved claim."
            ),
        }
    if operator_id == "trace":
        argument_edges = []
        formal_dependency_neighbourhoods = []
        source_dependency_candidates = []
        for cell in cells:
            if cell["kind"] == "claim":
                neighbourhood = cell["content"]["argument_neighbourhood"]
                argument_edges.extend(neighbourhood["incoming"])
                argument_edges.extend(neighbourhood["outgoing"])
            elif cell["kind"] == "declaration":
                formal_dependency_neighbourhoods.append(
                    cell["content"].get(
                        "formal_dependency_neighbourhood", {}
                    )
                )
                source_dependency_candidates.extend(
                    cell["content"].get(
                        "source_dependency_candidates", []
                    )
                )
        return {
            "kind": "trace_synthesis",
            "argument_edges": argument_edges,
            "formal_dependency_neighbourhoods": [
                row
                for row in formal_dependency_neighbourhoods
                if row.get("availability") == "available"
            ],
            "source_dependency_candidates": list(
                {
                    (row["name"], row["source_ref"]): row
                    for row in source_dependency_candidates
                }.values()
            ),
            "boundary": (
                "Authored argument relations explain dependency posture; "
                "formal source witnesses remain proof authority."
            ),
        }
    if operator_id == "digest":
        return {
            "kind": "digest_synthesis",
            "ordered_cell_ids": [cell["cell_id"] for cell in cells],
            "boundedness": (
                "The digest is an ordered witness slice, not a complete "
                "summary of every declaration matching the question."
            ),
        }
    return {
        "kind": "location_synthesis",
        "exact_handles": [cell["cell_id"] for cell in cells],
        "source_witnesses": [
            edge
            for cell in cells
            for edge in cell["witness_edges"]
            if edge["authority"]
            in ("kernel", "digestion_to_kernel_source")
        ],
    }


def semantic_slice_rejections(operator_id: str) -> list[str]:
    common = [
        "A navigation match is not evidence that a theorem proves the query.",
        "A conditional reduction, finite instance, or open target is not promoted to a solved claim.",
    ]
    operator_specific = {
        "frontier": (
            "Nearby proved reductions do not discharge the exact remaining-open proposition.",
        ),
        "falsify": (
            "A promising formal interface is not treated as a producer when its supply hypothesis remains open.",
            "Authored experimental verdicts are reported as measured scope, not universal impossibility.",
        ),
        "analogy": (
            "Structural similarity is not transported as a proof without an exact formal bridge.",
        ),
        "support": (
            "Individually relevant premises are not asserted jointly sufficient without a checked consumer.",
        ),
        "trace": (
            "Argument-graph edges explain authored dependency posture; Lean source remains proof authority.",
        ),
        "digest": (
            "The bounded digest omits material by handle rather than silently claiming corpus completeness.",
        ),
        "locate": (
            "A lexical or vocabulary match is not treated as identity unless its typed handle is expanded.",
        ),
    }
    return [*common, *operator_specific.get(operator_id, ())]


def analogy_subject_queries(query: str) -> list[str]:
    """Recover the compared subjects so intersection matching does not erase either."""
    stripped = re.sub(
        r"^\s*(?:compare|contrast)\s+",
        "",
        query,
        flags=re.IGNORECASE,
    )
    parts = re.split(
        r"\s+(?:with|versus|vs\.?|and)\s+",
        stripped,
        maxsplit=1,
        flags=re.IGNORECASE,
    )
    return [part.strip() for part in parts if part.strip()] if len(parts) == 2 else []


def support_alternative_queries(query: str) -> list[str]:
    """Split `either X or Y proves Z` into two premise-selection questions."""
    match = re.search(
        r"\beither\s+(.+?)\s+or\s+(.+?)\s+"
        r"(?:prove|proves|imply|implies|establish|establishes)\s+(.+)",
        query,
        flags=re.IGNORECASE,
    )
    if match is None:
        return []
    left, right, conclusion = (part.strip() for part in match.groups())
    return [f"{left} {conclusion}", f"{right} {conclusion}"]


def trace_endpoint_queries(query: str) -> list[str]:
    """Split an explicitly relational trace question into two subjects."""
    patterns = (
        r"\bfrom\s+(.+?)\s+(?:to|through|into)\s+(.+?)\s*[?.!]*$",
        (
            r"^\s*(?:trace\s+)?(?:why\s+)?(?:does\s+)?(.+?)\s+"
            r"(?:ultimately\s+)?(?:use|uses|depend(?:s)?\s+on|"
            r"build(?:s)?\s+on)\s+(.+?)\s*[?.!]*$"
        ),
    )
    for pattern in patterns:
        match = re.search(pattern, query, flags=re.IGNORECASE)
        if match is not None:
            subjects = [part.strip() for part in match.groups()]
            if all(subjects):
                return subjects
    return []


def trace_dependency_resolution(
    query: str, candidate_limit: int = 24
) -> dict[str, Any]:
    """Resolve two natural-language endpoints through exact Lean paths."""
    subjects = trace_endpoint_queries(query)
    if len(subjects) != 2:
        return {"availability": "no_explicit_endpoint_pair"}
    theorem_kinds = {"theorem", "lemma", "corollary", "proposition"}

    def candidates(subject: str) -> list[dict[str, Any]]:
        results = search_packet(subject, min(MAX_LIMIT, 40))["results"]
        return [
            result
            for result in results
            if result["kind"] == "declaration"
            and result.get("declaration_kind") in theorem_kinds
            and result.get("externally_addressable", True)
        ][:candidate_limit]

    source_candidates = candidates(subjects[0])
    target_candidates = candidates(subjects[1])
    tested_pair_count = 0
    ranked_paths = []
    for source_index, source in enumerate(source_candidates):
        for target_index, target in enumerate(target_candidates):
            tested_pair_count += 1
            path = formal_dependency_path(
                semantic_result_key(source),
                semantic_result_key(target),
                8,
            )
            if path["availability"] != "available" or not path["hop_count"]:
                continue
            ranked_paths.append(
                (
                    path["hop_count"],
                    source_index + target_index,
                    source_index,
                    target_index,
                    source,
                    target,
                    path,
                )
            )
    if not ranked_paths:
        return {
            "availability": "no_path_between_bounded_candidates",
            "endpoint_queries": subjects,
            "source_candidate_count": len(source_candidates),
            "target_candidate_count": len(target_candidates),
            "tested_pair_count": tested_pair_count,
            "source_candidate_handles": [
                semantic_result_key(row)
                for row in source_candidates[:8]
            ],
            "target_candidate_handles": [
                semantic_result_key(row)
                for row in target_candidates[:8]
            ],
            "authority_posture": (
                "bounded_negative_navigation_result_not_global_dependency_"
                "absence"
            ),
        }
    (
        _,
        _,
        source_index,
        target_index,
        source,
        target,
        path,
    ) = min(ranked_paths, key=lambda row: row[:4])
    return {
        "availability": "available",
        "endpoint_queries": subjects,
        "source_result": source,
        "target_result": target,
        "formal_dependency_path": path,
        "receipt": {
            "source_candidate_count": len(source_candidates),
            "target_candidate_count": len(target_candidates),
            "tested_pair_count": tested_pair_count,
            "path_bearing_pair_count": len(ranked_paths),
            "selected_source_rank": source_index,
            "selected_target_rank": target_index,
            "selection_policy": (
                "shortest_exact_path_then_combined_endpoint_rank_then_"
                "source_rank_then_target_rank"
            ),
            "omitted_source_candidate_count": max(
                0, len(source_candidates) - 8
            ),
            "omitted_target_candidate_count": max(
                0, len(target_candidates) - 8
            ),
            "alternative_source_handles": [
                semantic_result_key(row)
                for row in source_candidates[:8]
                if semantic_result_key(row)
                != semantic_result_key(source)
            ],
            "alternative_target_handles": [
                semantic_result_key(row)
                for row in target_candidates[:8]
                if semantic_result_key(row)
                != semantic_result_key(target)
            ],
        },
        "authority_posture": (
            "lexical_endpoint_resolution_plus_exact_kernel_elaborated_path_"
            "not_proof_that_the_selected_endpoints_match_user_intent"
        ),
    }


def semantic_context_residual_terms(query: str) -> set[str]:
    """Return mathematical terms not already explained by a vocabulary route."""
    consumed: set[str] = set()
    for row in matched_semantic_vocabulary(query):
        for phrase in (
            row["pref_label"],
            *row["alt_labels"],
            *row["query_expansions"],
        ):
            consumed.update(search_terms(phrase))
    return {
        term
        for term in semantic_content_terms(query)
        - consumed
        - {"problem", "erdo"}
        if not term.isdigit()
    }


def module_local_declaration_results(
    query: str, module_result: dict[str, Any], limit: int = 2
) -> list[dict[str, Any]]:
    """Rank exact declarations after authored module digestion finds the organ."""
    query_terms = semantic_content_terms(query)
    if not query_terms:
        return []
    atlas = load("docs/declaration_atlas.json")
    theorem_requested = (
        semantic_query_operator(query)["id"] == "support"
        or bool(
            {"theorem", "lemma", "proof"}
            & search_terms(query)
        )
    )
    ranked = []
    for row in atlas_declarations(atlas):
        if row["module"] != module_result["path"]:
            continue
        candidate_terms = search_terms(
            " ".join(
                str(value)
                for value in (
                    row["name"],
                    row.get("signature"),
                    row.get("docstring"),
                )
                if value
            )
        )
        matched = len(query_terms & candidate_terms)
        if matched < min(2, len(query_terms)):
            continue
        theorem_like = row["kind"] in {
            "theorem",
            "lemma",
            "corollary",
            "proposition",
        }
        if theorem_requested and (
            not theorem_like
            or not declaration_externally_addressable(row)
        ):
            continue
        ranked.append(
            (
                -matched,
                0 if theorem_requested and theorem_like else 1,
                len(candidate_terms - query_terms),
                row["line"],
                row,
            )
        )
    results = []
    for _, _, _, _, row in sorted(ranked)[:limit]:
        result = {"kind": "declaration", **compact_declaration(row)}
        if row.get("signature"):
            result["signature_excerpt"] = str(row["signature"])[:240]
        results.append(result)
    return results


def best_reading_route_result(query: str) -> dict[str, Any] | None:
    """Rank routes as a handle class so declaration volume cannot erase them."""
    claims = load("docs/claims.json")
    ranked = []
    for route in all_entrypoints(claims):
        haystack = " ".join(
            str(value)
            for value in (
                route.get("title"),
                route.get("intent"),
                route.get("mathematical_focus"),
                route.get("claim_ceiling"),
                *route.get("discovery_terms", []),
                *route.get("core_claim_ids", []),
                *route.get("remaining_open_proposition_ids", []),
            )
            if value
        )
        ranks = [search_rank(query, route["id"], haystack)]
        ranks.extend(
            search_rank(query, term, haystack)
            for term in route.get("discovery_terms", [])
        )
        rank = min((value for value in ranks if value is not None), default=None)
        if rank is not None:
            ranked.append((rank, route["id"], route))
    if not ranked:
        return None
    _, _, route = min(ranked, key=lambda row: (row[0], row[1]))
    return {
        "kind": "reading_route",
        "id": route["id"],
        "route_kind": route.get("route_kind", "reading_route"),
        "title": route.get("title"),
        "intent": route["intent"],
        "problem_target_claim_ids": route.get(
            "problem_target_claim_ids", []
        ),
    }


def semantic_slice_packet(query: str, limit: int) -> dict[str, Any]:
    """Compile a question into a bounded, witness-carrying semantic subgraph."""
    scope_boundary = corpus_scope_boundary_packet(query)
    if scope_boundary is not None:
        return scope_boundary
    if is_repository_overview_query(query):
        return repository_overview_packet(query)
    if is_paper_reading_query(query):
        return paper_reading_guide_packet()
    search = search_packet(query, max(12, min(MAX_LIMIT, limit)))
    interpretation = search["query_interpretation"]
    operator_id = interpretation["operator"]["id"]
    hint_targets = set(semantic_hint_targets(query))
    directly_routed = [
        result
        for result in search["results"]
        if (result["kind"], semantic_result_handle(result)) in hint_targets
    ]
    analogy_subjects = (
        analogy_subject_queries(query) if operator_id == "analogy" else []
    )
    support_alternatives = (
        support_alternative_queries(query) if operator_id == "support" else []
    )
    trace_resolution = (
        trace_dependency_resolution(query)
        if operator_id == "trace"
        else {"availability": "not_a_trace_query"}
    )
    goal_support = (
        formal_goal_support_packet(query, 3)
        if operator_id == "support"
        and support_goal_request(query) is not None
        else {
            "kind": "formal_goal_support",
            "availability": "no_goal_expression",
        }
    )
    if (
        goal_support["availability"] == "available"
        and goal_support["candidates"]
    ):
        goal_adjacency = lean_dependency_adjacency()
        goal_handle = goal_support["candidates"][0]["qualified_name"]
        if (
            goal_adjacency is not None
            and goal_handle
            in goal_adjacency["formal_type_affordances"]
        ):
            goal_support = {
                **goal_support,
                "application": formal_application_obligations(
                    query,
                    goal_support["goal_request"],
                    goal_adjacency["formal_type_affordances"][
                        goal_handle
                    ],
                ),
            }
    if trace_resolution["availability"] not in (
        "available",
        "no_explicit_endpoint_pair",
        "not_a_trace_query",
    ):
        interpretation = {
            **interpretation,
            "trace_endpoint_resolution": trace_resolution,
        }
    selected_with_reasons: list[tuple[dict[str, Any], str]]
    if trace_resolution["availability"] == "available":
        interpretation = {
            **interpretation,
            "trace_endpoint_resolution": {
                "availability": "available",
                "endpoint_queries": trace_resolution[
                    "endpoint_queries"
                ],
                "resolved_source": semantic_result_key(
                    trace_resolution["source_result"]
                ),
                "resolved_target": semantic_result_key(
                    trace_resolution["target_result"]
                ),
                "receipt": trace_resolution["receipt"],
                "authority_posture": trace_resolution[
                    "authority_posture"
                ],
            },
        }
        selected_with_reasons = [
            (
                trace_resolution["source_result"],
                "trace_source_endpoint",
            ),
            (
                trace_resolution["target_result"],
                "trace_target_endpoint",
            ),
        ][: min(limit, MAX_SEMANTIC_CELLS)]
    elif len(support_alternatives) == 2:
        interpretation = {
            **interpretation,
            "support_alternative_queries": support_alternatives,
        }
        selected_with_reasons = []
        for side, subject in zip(("left", "right"), support_alternatives):
            subject_results = search_packet(subject, max(8, limit))["results"]
            declaration = next(
                (
                    result
                    for result in subject_results
                    if result["kind"] == "declaration"
                ),
                None,
            )
            claim = next(
                (
                    result
                    for result in subject_results
                    if result["kind"] == "claim"
                ),
                None,
            )
            candidates = [
                result for result in (declaration, claim) if result is not None
            ]
            selected_with_reasons.extend(
                (result, f"support_alternative_{side}")
                for result in candidates[:2]
            )
        selected_with_reasons = selected_with_reasons[
            : min(limit, MAX_SEMANTIC_CELLS)
        ]
    elif (
        goal_support["availability"] == "available"
        and goal_support["candidates"]
    ):
        interpretation = {
            **interpretation,
            "formal_goal_support": {
                "availability": "available",
                "goal_request": goal_support["goal_request"],
                "goal_shape_cues": goal_support[
                    "goal_shape_cues"
                ],
                "candidate_count": goal_support["candidate_count"],
                "selected_declaration": semantic_result_key(
                    goal_support["candidates"][0]
                ),
                "authority_posture": goal_support[
                    "authority_posture"
                ],
            },
        }
        selected_with_reasons = [
            (
                goal_support["candidates"][0],
                "formal_goal_shape_candidate",
            )
        ]
    elif len(analogy_subjects) == 2:
        interpretation = {
            **interpretation,
            "analogy_subject_queries": analogy_subjects,
        }
        selected_with_reasons = []
        for side, subject in zip(("left", "right"), analogy_subjects):
            subject_results = search_packet(subject, max(8, limit))["results"]
            route = best_reading_route_result(subject)
            candidates = [
                *([route] if route else []),
                *[
                    result
                    for result in subject_results
                    if result is not route
                    and result["kind"]
                    in ("claim", "declaration", "publication_family")
                ],
            ]
            selected_with_reasons.extend(
                (result, f"analogy_{side}_subject")
                for result in candidates[:2]
            )
        selected_with_reasons = selected_with_reasons[
            : min(limit, MAX_SEMANTIC_CELLS)
        ]
    elif directly_routed:
        selected_with_reasons = [
            (result, "controlled_vocabulary_route")
            for result in directly_routed[
                : min(limit, MAX_SEMANTIC_CELLS)
            ]
        ]
        residual_terms = semantic_context_residual_terms(query)
        if len(residual_terms) >= 2:
            contextual_search = search_packet(
                " ".join(sorted(residual_terms)),
                max(12, min(MAX_LIMIT, limit * 4)),
            )
            routed_keys = {
                (result["kind"], semantic_result_key(result))
                for result, _ in selected_with_reasons
            }
            contextual = [
                result
                for result in contextual_search["results"]
                if (
                    result["kind"],
                    semantic_result_key(result),
                )
                not in routed_keys
                and result["kind"]
                in ("declaration", "claim", "module", "reading_route")
            ]
            selected_with_reasons.extend(
                (result, "ranked_context_beyond_controlled_vocabulary")
                for result in contextual[
                    : max(
                        0,
                        min(limit, MAX_SEMANTIC_CELLS)
                        - len(selected_with_reasons),
                    )
                ]
            )
    else:
        selected_with_reasons = [
            (result, "ranked_query_relative_match")
            for result in search["results"][
                : min(limit, MAX_SEMANTIC_CELLS)
            ]
        ]

    if operator_id == "frontier":
        claims = load("docs/claims.json")
        claim_index = {row["id"]: row for row in claims["claims"]}
        route_index = {row["id"]: row for row in all_entrypoints(claims)}
        open_index = {
            row["id"]: row
            for row in claims["remaining_open_propositions"]
        }
        boundary_ids: list[str] = []
        for result, _ in selected_with_reasons[:3]:
            if result["kind"] == "claim":
                boundary_ids.extend(
                    claim_index[result["id"]].get(
                        "remaining_open_proposition_ids", []
                    )
                )
            elif result["kind"] == "reading_route":
                boundary_ids.extend(
                    route_index[result["id"]].get(
                        "remaining_open_proposition_ids", []
                    )
                )
        existing_open_ids = {
            result["id"]
            for result, _ in selected_with_reasons
            if result["kind"] == "open_proposition"
        }
        directly_routed_frontier = (
            bool(selected_with_reasons)
            and selected_with_reasons[0][1]
            == "controlled_vocabulary_route"
        )
        boundary_rows = [
            (
                {"kind": "open_proposition", **open_index[open_id]},
                "frontier_boundary_from_ranked_context",
            )
            for open_id in dict.fromkeys(boundary_ids)
            if open_id in open_index and open_id not in existing_open_ids
        ]
        if directly_routed_frontier and existing_open_ids:
            boundary_rows = []
        if boundary_rows:
            insertion_index = (
                1
                if directly_routed_frontier
                else min(2, len(selected_with_reasons))
            )
            selected_with_reasons = [
                *selected_with_reasons[:insertion_index],
                *boundary_rows,
                *selected_with_reasons[insertion_index:],
            ][: min(limit, MAX_SEMANTIC_CELLS)]

    if (
        operator_id == "trace"
        and not any(
            result["kind"] == "declaration"
            for result, _ in selected_with_reasons
        )
    ):
        formal_witness = next(
            (
                result
                for result in search["results"]
                if result["kind"] == "declaration"
            ),
            None,
        )
        if formal_witness is not None:
            selected_with_reasons = [
                *selected_with_reasons[
                    : max(0, min(limit, MAX_SEMANTIC_CELLS) - 1)
                ],
                (formal_witness, "trace_formal_declaration_witness"),
            ]

    wants_local_theorem = (
        operator_id == "support"
        or bool({"theorem", "lemma"} & search_terms(query))
    ) and "module" not in search_terms(query)
    if wants_local_theorem:
        local_results = [
            result
            for result, _ in selected_with_reasons
            if result["kind"] == "module"
        ]
        enriched = [
            (
                declaration,
                "module_local_declaration_witness",
            )
            for module in local_results
            for declaration in module_local_declaration_results(
                query, module, 1
            )
        ]
        if enriched:
            merged = [*enriched, *selected_with_reasons]
            selected_with_reasons = []
            seen_keys: set[tuple[str, str]] = set()
            for result, reason in merged:
                key = (result["kind"], semantic_result_key(result))
                if key in seen_keys:
                    continue
                seen_keys.add(key)
                selected_with_reasons.append((result, reason))
                if len(selected_with_reasons) >= min(
                    limit, MAX_SEMANTIC_CELLS
                ):
                    break
    selected = [result for result, _ in selected_with_reasons]
    if not selected:
        return {
            "kind": "semantic_slice",
            "schema_version": SEMANTIC_SLICE_SCHEMA,
            "query": query,
            "query_interpretation": interpretation,
            "semantic_cells": [],
            "operator_synthesis": operator_synthesis(operator_id, []),
            "minimal_witness_subgraph": {"nodes": ["query"], "edges": []},
            "rejected_overinterpretations": semantic_slice_rejections(operator_id),
            "omission_receipt": {
                "status": "no_matching_handles",
                "refine_with": "python3 scripts/query_corpus.py --vocabulary",
            },
            "authority_posture": "bounded_navigation_projection_not_proof_authority",
        }

    selected_keys = {
        (result["kind"], semantic_result_key(result)) for result in selected
    }
    cells = [
        semantic_cell(query, result, reason)
        for result, reason in selected_with_reasons
    ]
    near_misses = [
        {
            "kind": result["kind"],
            "handle": semantic_result_handle(result),
            "canonical_handle": semantic_result_key(result),
            "reason": "lower_ranked_outside_bounded_witness_slice",
            **(
                {"route_memory": result["route_memory"]}
                if result.get("route_memory") is not None
                else {}
            ),
        }
        for result in search["results"]
        if (result["kind"], semantic_result_key(result)) not in selected_keys
    ][:5]
    witness_edges: list[dict[str, str]] = [
        edge for cell in cells for edge in cell["witness_edges"]
    ]
    synthesis = operator_synthesis(operator_id, cells)
    if goal_support["availability"] == "available":
        synthesis = {
            **synthesis,
            "formal_goal_support": goal_support,
        }
    if trace_resolution["availability"] == "available":
        formal_path = trace_resolution["formal_dependency_path"]
        synthesis = {
            **synthesis,
            "endpoint_resolution_receipt": trace_resolution["receipt"],
            "formal_dependency_path": formal_path,
        }
        witness_edges.extend(
            {
                "from": f"declaration:{edge['from']}",
                "relation": "uses_in_elaborated_value",
                "to": f"declaration:{edge['to']}",
                "authority": "kernel_elaborated_environment",
            }
            for edge in formal_path["edges"]
        )
    witness_nodes = list(
        dict.fromkeys(
            [
                "query",
                *(cell["cell_id"] for cell in cells),
                *(edge["from"] for edge in witness_edges),
                *(edge["to"] for edge in witness_edges),
            ]
        )
    )
    digest_source = {
        "query": query,
        "operator": operator_id,
        "cells": [cell["cell_id"] for cell in cells],
        "edges": witness_edges,
    }
    slice_digest = hashlib.sha256(
        json.dumps(
            digest_source, ensure_ascii=False, sort_keys=True, separators=(",", ":")
        ).encode("utf-8")
    ).hexdigest()
    return {
        "kind": "semantic_slice",
        "schema_version": SEMANTIC_SLICE_SCHEMA,
        "slice_id": f"sha256:{slice_digest}",
        "query": query,
        "query_interpretation": interpretation,
        "semantic_cells": cells,
        "operator_synthesis": synthesis,
        "minimal_witness_subgraph": {
            "nodes": witness_nodes,
            "edges": witness_edges,
            "minimality_posture": (
                "query_relative_operator_specific_decisive_edges_with_typed_omission_handles"
            ),
        },
        "rejected_overinterpretations": semantic_slice_rejections(operator_id),
        "near_misses": near_misses,
        "omission_receipt": {
            "search_match_count": search["match_count"],
            "selected_cell_count": len(cells),
            "omitted_match_count": max(0, search["match_count"] - len(cells)),
            "additional_match_handles": near_misses,
            "refine_with": (
                f"python3 scripts/query_corpus.py --search {json.dumps(query)} "
                f"--limit {min(MAX_LIMIT, max(limit * 2, 12))}"
            ),
        },
        "artifact_availability_receipt": search[
            "artifact_availability_receipt"
        ],
        "authority_posture": (
            "witness_carrying_navigation_projection_with_non_substitutable_authority_planes"
        ),
        "proof_authority": "Lean source checked by the pinned Lean kernel",
    }


def claim_status_packet(status: str, limit: int) -> dict[str, Any]:
    claims = load("docs/claims.json")
    taxonomy = claims["status_taxonomy"]
    status_by_folded = {key.casefold(): key for key in taxonomy}
    canonical_status = status_by_folded.get(status.strip().casefold())
    if canonical_status is None:
        expected = ", ".join(taxonomy)
        raise KeyError(f"unknown claim status: {status}; expected one of: {expected}")
    matching_claims = [
        claim for claim in claims["claims"] if claim["status"] == canonical_status
    ]
    remaining_open = (
        claims["remaining_open_propositions"] if canonical_status == "open" else []
    )
    emitted_claims = matching_claims[:limit]
    route_memory_by_claim = {}
    for claim in emitted_claims:
        route_memory_by_claim[claim["id"]] = claim_route_memory_projection(
            claim["id"], claims
        )
    return {
        "kind": "claim_status",
        "authority_posture": "claim_registry_status_navigation_not_proof_authority",
        "status": canonical_status,
        "meaning": taxonomy[canonical_status],
        "claim_count": len(matching_claims),
        "claims": [
            compact_status_claim(claim) for claim in emitted_claims
        ],
        "omitted_claim_count": max(0, len(matching_claims) - limit),
        "limit": limit,
        "remaining_open_propositions": remaining_open,
        "route_memory": {
            "by_claim": route_memory_by_claim,
            "authority_posture": (
                "derived_resume_handoff_not_claim_or_proof_authority"
            ),
            "identity_contract": (
                "Bindings are complete canonical programme options for each "
                "emitted claim; they are not ranked and resolve current source "
                "digests when queried."
            ),
        },
        "proof_authority": "Lean source checked by the pinned Lean kernel",
        "expansion": {
            "claim": "python3 scripts/query_corpus.py --claim <claim_id>",
            "open_proposition": (
                "python3 scripts/query_corpus.py --open <remaining_open.id>"
            ),
        },
        "validation": "python3 scripts/check_release.py",
    }


def route_memory_problem_number(route: Mapping[str, Any]) -> int | None:
    """Derive a problem selector from an authored programme target claim."""
    for claim_id in route.get("problem_target_claim_ids", []):
        match = re.fullmatch(r"(?:erdos|universal)_(\d+)", str(claim_id))
        if match:
            return int(match.group(1))
    return None


def claim_route_memory_projection(
    claim_id: str, claims: Mapping[str, Any]
) -> dict[str, Any]:
    """Project every canonical programme route that can resume a claim."""
    programme_routes = [
        route
        for route in all_entrypoints(claims)
        if route.get("route_kind") == "mathematical_programme"
    ]
    bindings = []
    for route in programme_routes:
        if (
            claim_id not in route.get("core_claim_ids", [])
            and claim_id not in route.get("problem_target_claim_ids", [])
        ):
            continue
        problem_number = route_memory_problem_number(route)
        if problem_number is None:
            continue
        bindings.append(
            {
                "route_id": route["id"],
                "problem_number": problem_number,
                "command": (
                    "python3 scripts/query_route_memory.py --problem "
                    f"{problem_number} --route {route['id']}"
                ),
            }
        )
    projection = {
        "status": "bound" if bindings else "unbound",
        "bindings": bindings,
        "authority_posture": "derived_resume_handoff_not_claim_or_proof_authority",
        "identity_contract": (
            "Bindings are complete canonical programme options for the claim; "
            "they are not ranked and resolve current source digests when queried."
        ),
    }
    if not bindings:
        projection["unbound_reason"] = (
            "claim does not resolve to a canonical mathematical programme; "
            "no resume route was invented"
        )
    return projection


def bounded_programme_signal_projection(spine: Mapping[str, Any]) -> dict[str, Any]:
    """Keep every signal identity while routing verbose judgement to detail.

    Programme routes are first-contact packets.  Palomar's complete per-family
    prose remains available through the problem route, but repeating it inside
    every overlapping programme made those packets grow with the corpus.  This
    projection keeps ordering, source, declaration, family, and relation-edge
    identities; only descriptive prose is omitted.
    """
    problem = int(spine["problem"])
    retained_fields = (
        "tier_order",
        "tier_id",
        "within_tier_order",
        "global_rank",
        "programme_order",
        "family_id",
        "signal_family_id",
        "source_disposition",
        "screening_disposition",
        "source_kind",
        "declaration",
        "source_declaration",
        "source_file",
    )
    relation_fields = (
        "from_family_id",
        "relation",
        "to_family_id",
        "direction",
    )
    result_fields = (*retained_fields, "relations")
    results = []
    omitted_fields: set[str] = set()
    relation_reason_count = 0
    for result in spine["results"]:
        relations = []
        for relation in result.get("relations", []):
            relations.append([relation.get(key) for key in relation_fields])
            if "reason" in relation:
                relation_reason_count += 1
        omitted_fields.update(set(result) - set(result_fields))
        results.append([result.get(key) for key in retained_fields] + [relations])
    if relation_reason_count:
        omitted_fields.add("relations[].reason")
    detail_route = f"python3 scripts/query_corpus.py --route erdos_{problem}"
    return {
        "problem": problem,
        "ordering_contract": spine["ordering_contract"],
        "result_fields": list(result_fields),
        "relation_fields": list(relation_fields),
        "results": results,
        "projection_receipt": {
            "projection": "bounded_identity_projection",
            "result_count": len(results),
            "identity_contract": (
                "Columnar result_fields and relation_fields preserve every family, "
                "declaration, source, ordering, disposition, and relation-edge "
                "identity without repeating field names per row."
            ),
            "omitted_fields": sorted(omitted_fields),
            "omitted_relation_reason_count": relation_reason_count,
            "detail_handles": {
                "complete_problem_signal": detail_route,
                "exact_declaration": (
                    "python3 scripts/query_corpus.py --declaration "
                    "<source_declaration>"
                ),
                "publication_family": (
                    "python3 scripts/query_corpus.py --publication-family <family_id>"
                ),
            },
            "authority_posture": (
                "bounded_navigation_projection_not_mathematical_judgement_or_"
                "proof_authority"
            ),
        },
    }


def route_packet(route_id: str) -> dict[str, Any]:
    claims = load("docs/claims.json")
    route = next(
        (
            row
            for row in all_entrypoints(claims)
            if row["id"] == route_id
        ),
        None,
    )
    if route is None:
        problem_route = problem_registry_route(route_id)
        if problem_route is None:
            raise KeyError(f"unknown route id: {route_id}")
        problem_number = int(problem_route["erdos_number"])
        signal = mathematical_signal_spine(claims, include_programme_detail=True)
        programme_signal = next(
            (
                row
                for row in signal["programme_spines"]
                if row["problem"] == problem_number
            ),
            None,
        )
        if programme_signal is None:
            raise ValueError(f"Palomar signal authority lacks programme #{problem_number}")
        return {
            "kind": "problem_route",
            "authority_posture": problem_route["authority_posture"],
            "route": problem_route,
            "mathematical_signal_spine": programme_signal,
            "proof_authority": "Lean source checked by the pinned Lean kernel",
            "release_provenance": claims["release"]["public_projection"],
            "validation": "python3 scripts/check_release.py",
        }
    claim_index = {row["id"]: row for row in claims["claims"]}
    open_index = {
        row["id"]: row for row in claims["remaining_open_propositions"]
    }
    route_index = {
        row["id"]: row for row in all_entrypoints(claims)
    }
    packet = {
        "kind": "reading_route",
        "authority_posture": route.get(
            "authority_posture", "authored_navigation_route_not_proof_authority"
        ),
        "route": route,
        "proof_authority": "Lean source checked by the pinned Lean kernel",
        "release_provenance": claims["release"]["public_projection"],
        "validation": "python3 scripts/check_release.py",
    }
    if route_id == "instant_orientation":
        packet["mathematical_signal_spine"] = mathematical_signal_spine(claims)
    if route.get("route_kind") == "mathematical_programme":
        core_claims = [claim_index[claim_id] for claim_id in route["core_claim_ids"]]
        packet["programme"] = {
            "title": route["title"],
            "mathematical_focus": route["mathematical_focus"],
            "claim_ceiling": route["claim_ceiling"],
            "problem_targets": [
                compact_claim(claim_index[claim_id])
                for claim_id in route["problem_target_claim_ids"]
            ],
            "core_claims": [compact_claim(claim) for claim in core_claims],
            "status_counts": dict(
                sorted(
                    {
                        status: sum(
                            claim["status"] == status for claim in core_claims
                        )
                        for status in {claim["status"] for claim in core_claims}
                    }.items()
                )
            ),
            "remaining_open_propositions": [
                open_index[open_id]
                for open_id in route["remaining_open_proposition_ids"]
            ],
            "related_programmes": [
                {
                    "id": related_id,
                    "title": route_index[related_id]["title"],
                    "intent": route_index[related_id]["intent"],
                }
                for related_id in route["related_route_ids"]
            ],
        }
        problem_number = route_memory_problem_number(route)
        if problem_number is not None:
            signal = mathematical_signal_spine(claims, include_programme_detail=True)
            programme_signal = next(
                (
                    row
                    for row in signal["programme_spines"]
                    if row["problem"] == problem_number
                ),
                None,
            )
            if programme_signal is None:
                raise ValueError(
                    f"Palomar signal authority lacks programme #{problem_number}"
                )
            packet["programme"]["mathematical_signal_spine"] = (
                bounded_programme_signal_projection(programme_signal)
            )
            packet["route_memory"] = {
                "problem_number": problem_number,
                "command": (
                    "python3 scripts/query_route_memory.py --problem "
                    f"{problem_number} --route {route_id}"
                ),
                "authority_posture": (
                    "derived_resume_handoff_not_claim_or_proof_authority"
                ),
                "identity_contract": (
                    "The route-memory command binds this route to the selected "
                    "problem and current tracked source digests before resume."
                ),
            }
    return packet


def publication_family_packet(family_id: str) -> dict[str, Any]:
    claims = load("docs/claims.json")
    assembly = claims["machine_readable_paper"]["publication_assembly"]
    family = next(
        (
            row
            for row in assembly["contribution_families"]
            if row["id"] == family_id
        ),
        None,
    )
    if family is None:
        raise KeyError(f"unknown publication family id: {family_id}")
    claim_index = {row["id"]: row for row in claims["claims"]}
    family_claims = [claim_index[claim_id] for claim_id in family["claim_ids"]]
    source_route = str(family.get("source_route", ""))
    route_index = {row["id"]: row for row in all_entrypoints(claims)}
    candidate_routes = []
    route_match = re.fullmatch(
        r"\s*python3 scripts/query_corpus\.py --route ([^\s]+)\s*",
        source_route,
    )
    claim_match = re.fullmatch(
        r"\s*python3 scripts/query_corpus\.py --claim ([^\s]+)\s*",
        source_route,
    )
    if route_match:
        route = route_index.get(route_match.group(1))
        if route and route.get("route_kind") == "mathematical_programme":
            candidate_routes = [route]
    elif claim_match:
        claim_source = claim_match.group(1)
        candidate_routes = [
            route
            for route in route_index.values()
            if route.get("route_kind") == "mathematical_programme"
            and claim_source in route.get("core_claim_ids", [])
        ]
    route_memory_bindings = []
    for route in candidate_routes:
        problem_number = route_memory_problem_number(route)
        if problem_number is None:
            continue
        route_memory_bindings.append(
            {
                "route_id": route["id"],
                "problem_number": problem_number,
                "command": (
                    "python3 scripts/query_route_memory.py --problem "
                    f"{problem_number} --route {route['id']}"
                ),
                "authority_posture": (
                    "derived_resume_handoff_not_claim_or_proof_authority"
                ),
                "identity_contract": (
                    "The route-memory command binds this route to the selected "
                    "problem and current tracked source digests before resume."
                ),
            }
        )
    route_memory = {
        "status": "bound" if route_memory_bindings else "unbound",
        "source_route": source_route,
        "bindings": route_memory_bindings,
        "authority_posture": "derived_resume_handoff_not_claim_or_proof_authority",
        "boundary": (
            "Route-memory bindings are navigation handoffs only; they do not "
            "promote claims, prove mathematics, or replace the family source route."
        ),
    }
    if not route_memory_bindings:
        route_memory["unbound_reason"] = (
            "source_route does not resolve to a canonical mathematical programme "
            "with a problem selector; no resume route was invented"
        )
    return {
        "kind": "publication_family",
        "authority_posture": "publication_assembly_navigation_not_proof_authority",
        "family": family,
        "claims": [compact_claim(claim) for claim in family_claims],
        "route_memory": route_memory,
        "status_counts": dict(
            sorted(
                {
                    status: sum(claim["status"] == status for claim in family_claims)
                    for status in {claim["status"] for claim in family_claims}
                }.items()
            )
        ),
        "publication_architecture": assembly["publication_architecture"],
        "proof_authority": "Lean source checked by the pinned Lean kernel",
        "validation": "python3 scripts/check_release.py",
    }


def publication_architecture_packet() -> dict[str, Any]:
    claims = load("docs/claims.json")
    assembly = claims["machine_readable_paper"]["publication_assembly"]
    family_index = []
    for row in assembly["contribution_families"]:
        family_route_memory = publication_family_packet(row["id"])["route_memory"]
        family_index.append(
            {
                "id": row["id"],
                "status_summary": row["status_summary"],
                "primary_narrative_owner": row["primary_narrative_owner"],
                "view_decision": row["view_decision"],
                "claim_count": len(row["claim_ids"]),
                "route_memory": family_route_memory,
            }
        )
    return {
        "kind": "publication_architecture",
        "authority_posture": "authored_editorial_topology_not_proof_authority",
        "architecture": assembly["publication_architecture"],
        "family_index": family_index,
        "coverage_rule": assembly["coverage_rule"],
        "validation": "python3 scripts/check_release.py",
    }


def _signal_reader_tier(candidate: Mapping[str, Any]) -> str:
    """Project an authored rank into a reader role without changing the rank."""
    if candidate.get("selection_status") == "subordinate":
        return "exact_reduction_or_structural_result"
    conditional_text = " ".join(
        str(candidate.get(key, ""))
        for key in (
            "consequence_and_endpoint_proximity",
            "mechanism_depth_and_natural_friction",
            "overclaim_risk",
            "why_not_ranked_first",
        )
    ).casefold()
    if any(
        marker in conditional_text
        for marker in (
            "conditional",
            "unresolved",
            "missing producer",
            "not constructed",
        )
    ):
        return "conditional_endpoint_route"
    return "completed_direct_result"


def _signal_presentation_contract(
    showcase: Mapping[str, Any],
) -> tuple[dict[str, Mapping[str, Any]], dict[str, Mapping[str, Any]]]:
    """Validate the one Palomar tier contract consumed by query projections."""
    contract = showcase.get("selection_contract")
    screening = showcase.get("candidate_screening")
    if not isinstance(contract, Mapping):
        raise ValueError("Palomar showcase lacks selection_contract")
    tiers = contract.get("presentation_tiers")
    if not isinstance(tiers, list) or not tiers:
        raise ValueError("Palomar selection contract lacks presentation_tiers")
    if not isinstance(screening, list):
        raise ValueError("Palomar showcase lacks candidate_screening")
    orders = [tier.get("order") for tier in tiers]
    if sorted(orders) != list(range(1, len(tiers) + 1)):
        raise ValueError("Palomar presentation tiers must be unique and contiguous")

    tier_by_id = {tier["tier_id"]: tier for tier in tiers}
    if len(tier_by_id) != len(tiers):
        raise ValueError("Palomar presentation tier ids must be unique")
    tier_by_disposition: dict[str, Mapping[str, Any]] = {}
    for tier in tiers:
        for disposition in tier.get("candidate_screening_dispositions", []):
            if disposition in tier_by_disposition:
                raise ValueError(
                    f"Palomar screening disposition occurs in two tiers: {disposition}"
                )
            tier_by_disposition[disposition] = tier
    actual_dispositions = {row.get("disposition") for row in screening}
    missing = sorted(actual_dispositions - set(tier_by_disposition))
    if missing:
        raise ValueError(
            "Palomar presentation tiers must cover candidate_screening dispositions: "
            f"missing={missing!r}"
        )

    placements = contract.get("relational_placements")
    if not isinstance(placements, list):
        raise ValueError("Palomar selection contract lacks relational_placements")
    placement_by_family: dict[str, Mapping[str, Any]] = {}
    for placement in placements:
        family_id = placement["family_id"]
        if family_id in placement_by_family:
            raise ValueError(f"duplicate Palomar relational placement: {family_id}")
        if placement["tier_id"] not in tier_by_id:
            raise ValueError(
                f"Palomar relational placement has unknown tier: {family_id}"
            )
        placement_by_family[family_id] = placement
    return tier_by_disposition, placement_by_family


def _signal_programme_spines(
    packet: Mapping[str, Any],
    showcase: Mapping[str, Any],
    result_by_declaration: Mapping[str, Mapping[str, Any]],
    family_by_id: Mapping[str, tuple[int, Mapping[str, Any]]],
) -> list[dict[str, Any]]:
    """Return programme-local reader order without using any source array order."""
    tier_by_disposition, placement_by_family = _signal_presentation_contract(showcase)
    universe = showcase["candidate_universe"]
    source_dispositions = universe["source_family_dispositions"]
    if set(source_dispositions) != set(family_by_id):
        raise ValueError(
            "Palomar source-family dispositions must cover the complete review matrix"
        )
    ranked_tier = next(
        tier
        for tier in showcase["selection_contract"]["presentation_tiers"]
        if tier["tier_id"] == "source_ranked_frontier"
    )

    rows_by_key: dict[tuple[int, str], dict[str, Any]] = {}
    ranked_keys: set[tuple[int, str]] = set()
    matched_placements: set[str] = set()
    for candidate in sorted(showcase["candidate_ranking"], key=lambda row: row["rank"]):
        result = result_by_declaration[candidate["declaration"]]
        family_id = result["review_family"]
        problem, family = family_by_id[family_id]
        key = (problem, family_id)
        rows_by_key[key] = {
            "tier_order": ranked_tier["order"],
            "tier_id": ranked_tier["tier_id"],
            "tier_label": ranked_tier["label"],
            "within_tier_order": candidate["rank"],
            "global_rank": candidate["rank"],
            "family_id": family_id,
            "signal_family_id": candidate["family_id"],
            "source_disposition": source_dispositions[family_id],
            "declaration": candidate["declaration"],
            "source_declaration": result["original_declaration"],
            "source_file": result["original_source"],
            "why_here": candidate["consequence_and_endpoint_proximity"],
            "boundary": result["boundary"],
        }
        ranked_keys.add(key)

    for screening_row in showcase["candidate_screening"]:
        declaration = screening_row["declaration"]
        result = result_by_declaration.get(declaration)
        family_owner = family_by_id.get(screening_row["family_id"])
        if result is None and family_owner is None:
            raise ValueError(
                "Palomar candidate_screening row lacks a Comparator result and review "
                f"family owner: {declaration}"
            )
        if result is not None:
            family_id = result["review_family"]
            problem, family = family_by_id[family_id]
        else:
            problem, family = family_owner
            family_id = family["id"]
        key = (problem, family_id)
        if key in ranked_keys:
            continue
        tier = tier_by_disposition[screening_row["disposition"]]
        placement = placement_by_family.get(family_id)
        if placement is not None and placement["tier_id"] != tier["tier_id"]:
            placement = None
        if placement is not None:
            matched_placements.add(family_id)
        within_tier_order = (
            placement["within_tier_order"] if placement is not None else 1_000_000
        )
        candidate_row = {
            "tier_order": tier["order"],
            "tier_id": tier["tier_id"],
            "tier_label": tier["label"],
            "within_tier_order": within_tier_order,
            "global_rank": None,
            "family_id": family_id,
            "signal_family_id": screening_row["family_id"],
            "source_disposition": source_dispositions[family_id],
            "screening_disposition": screening_row["disposition"],
            "declaration": declaration,
            "source_declaration": (
                result["original_declaration"] if result is not None else declaration
            ),
            "source_file": (
                result["original_source"]
                if result is not None
                else "ExternalVerification/Statements.lean"
            ),
            "why_here": (
                placement["relative_judgement"]
                if placement is not None
                else screening_row["reason"]
            ),
            "boundary": family["boundary"],
        }
        previous = rows_by_key.get(key)
        candidate_key = (
            candidate_row["tier_order"],
            candidate_row["within_tier_order"],
            candidate_row["declaration"],
        )
        previous_key = (
            previous["tier_order"],
            previous["within_tier_order"],
            previous["declaration"],
        ) if previous is not None else None
        if previous is None or candidate_key < previous_key:
            rows_by_key[key] = candidate_row

    tiers_by_id = {
        tier["tier_id"]: tier
        for tier in showcase["selection_contract"]["presentation_tiers"]
    }
    represented_placements = showcase["selection_contract"].get(
        "represented_family_placements"
    )
    if not isinstance(represented_placements, list):
        raise ValueError("Palomar selection contract lacks represented-family placements")
    for placement in represented_placements:
        family_id = placement["family_id"]
        owner = family_by_id.get(family_id)
        if owner is None:
            raise ValueError(
                f"Palomar represented-family placement lacks review owner: {family_id}"
            )
        problem, family = owner
        key = (problem, family_id)
        if key in rows_by_key:
            raise ValueError(
                f"Palomar represented-family placement duplicates a ranked/screened row: {family_id}"
            )
        if source_dispositions[family_id] != "represented":
            raise ValueError(
                f"Palomar represented-family placement is not represented: {family_id}"
            )
        tier = tiers_by_id.get(placement["tier_id"])
        if tier is None:
            raise ValueError(
                f"Palomar represented-family placement has unknown tier: {family_id}"
            )
        rows_by_key[key] = {
            "tier_order": tier["order"],
            "tier_id": tier["tier_id"],
            "tier_label": tier["label"],
            "within_tier_order": 1_000_000,
            "global_rank": None,
            "family_id": family_id,
            "signal_family_id": family_id,
            "source_disposition": source_dispositions[family_id],
            "declaration": f"review_family:{family_id}",
            "source_declaration": f"review_family:{family_id}",
            "source_kind": "canonical_review_family",
            "source_file": "docs/claims.json",
            "why_here": placement["relative_judgement"],
            "boundary": family["boundary"],
        }

    missing_placements = sorted(set(placement_by_family) - matched_placements)
    if missing_placements:
        raise ValueError(
            "Palomar relational placements lack a matching screening tier: "
            f"{missing_placements!r}"
        )

    relations = showcase["selection_contract"].get("family_relations")
    if not isinstance(relations, list):
        raise ValueError("Palomar selection contract lacks family relations")
    relation_rows_by_family: dict[str, list[dict[str, Any]]] = {}
    for relation in relations:
        source_family = relation["from_family_id"]
        target_family = relation["to_family_id"]
        if source_family not in family_by_id or target_family not in family_by_id:
            raise ValueError("Palomar family relation names an unknown review family")
        relation_rows_by_family.setdefault(source_family, []).append(
            {**relation, "direction": "outgoing"}
        )
        relation_rows_by_family.setdefault(target_family, []).append(
            {**relation, "direction": "incoming"}
        )
    for row in rows_by_key.values():
        row["relations"] = relation_rows_by_family.get(row["family_id"], [])

    rows_by_problem: dict[int, list[dict[str, Any]]] = {}
    for (problem, _), row in rows_by_key.items():
        rows_by_problem.setdefault(problem, []).append(row)
    programme_order = showcase["selection_contract"].get("programme_family_order")
    if not isinstance(programme_order, list):
        raise ValueError("Palomar selection contract lacks programme-family order")
    order_by_problem = {
        int(row["problem"]): row["family_ids"] for row in programme_order
    }
    if len(order_by_problem) != len(programme_order):
        raise ValueError("Palomar programme-family order repeats a problem")
    if set(order_by_problem) != set(rows_by_problem):
        raise ValueError("Palomar programme-family order does not cover every dossier")
    programme_spines = []
    for problem, rows in sorted(rows_by_problem.items()):
        authored_order = order_by_problem[problem]
        if len(authored_order) != len(set(authored_order)):
            raise ValueError(
                f"Palomar programme-family order repeats a family for #{problem}"
            )
        emitted_ids = {row["family_id"] for row in rows}
        if set(authored_order) != emitted_ids:
            raise ValueError(
                f"Palomar programme-family order is not signal-complete for #{problem}"
            )
        order_index = {family_id: index for index, family_id in enumerate(authored_order)}
        rows.sort(key=lambda row: order_index[row["family_id"]])
        for programme_order, row in enumerate(rows, start=1):
            row["programme_order"] = programme_order
        programme_spines.append(
            {
                "problem": problem,
                "ordering_contract": (
                    "Palomar ranked frontier, then authored presentation tiers and "
                    "relational placements; never roster or review-matrix order."
                ),
                "results": rows,
            }
        )
    return programme_spines


def mathematical_signal_spine(
    claims: Mapping[str, Any],
    showcase: Mapping[str, Any] | None = None,
    *,
    include_programme_detail: bool = False,
) -> dict[str, Any]:
    """Project Palomar's judgement before exhaustive query inventory."""
    if showcase is None:
        showcase = load("docs/PALOMAR_RESULT_SHOWCASE.json")
    ranking = showcase.get("candidate_ranking")
    contract = showcase.get("selection_contract")
    dispositions = showcase.get("candidate_value_dispositions")
    if not isinstance(ranking, list) or not ranking:
        raise ValueError("Palomar showcase lacks candidate_ranking")
    if not isinstance(contract, Mapping) or not contract.get("ranking_axes"):
        raise ValueError("Palomar showcase lacks selection_contract.ranking_axes")
    if not isinstance(dispositions, Mapping):
        raise ValueError("Palomar showcase lacks candidate_value_dispositions")
    ranks = [row.get("rank") for row in ranking]
    if sorted(ranks) != list(range(1, len(ranking) + 1)):
        raise ValueError("Palomar candidate ranks must be unique and contiguous")

    packet = claims["external_verification_packet"]
    result_by_declaration = {
        row["wrapper_declaration"]: row for row in packet["main_results"]
    }
    ranked_frontier = []
    for candidate in sorted(ranking, key=lambda row: row["rank"]):
        declaration = candidate["declaration"]
        result = result_by_declaration.get(declaration)
        if result is None:
            raise ValueError(
                "Palomar ranked declaration lacks an exact Comparator result: "
                f"{declaration}"
            )
        tier = _signal_reader_tier(candidate)
        row = {
            "rank": candidate["rank"],
            "reader_tier": tier,
            "problem": result["problem"],
            "family_id": candidate["family_id"],
            "declaration": declaration,
            "source_declaration": result["original_declaration"],
            "selection_status": candidate["selection_status"],
            "consequence": candidate["consequence_and_endpoint_proximity"],
            "evidence_class": result["contribution_class"],
            "source_file": result["original_source"],
            "exact_boundary": result["boundary"],
        }
        if tier != "exact_reduction_or_structural_result":
            row.update(
                {
                    "load_bearing_mechanism": candidate[
                        "mechanism_depth_and_natural_friction"
                    ],
                    "evidence_certainty": candidate["evidence_certainty"],
                    "overclaim_risk": candidate["overclaim_risk"],
                }
            )
        ranked_frontier.append(row)

    family_by_id = {
        family["id"]: (problem["problem"], family)
        for problem in packet["review_matrix"]
        for family in problem["families"]
    }
    friction_rows = []
    for candidate in dispositions.get("source_landscape_candidates", []):
        search_text = " ".join(
            str(candidate.get(key, ""))
            for key in (
                "candidate_id",
                "family_id",
                "ranking_status",
                "reason",
            )
        ).casefold()
        identifiers = " ".join(
            str(candidate.get(key, ""))
            for key in ("candidate_id", "family_id")
        ).casefold()
        is_natural_friction = (
            "no_go" in identifiers
            or "negative method" in search_text
            or "negative-method" in search_text
            or (
                "high-signal model-specific" in search_text
                and "no-go" in search_text
            )
        )
        if candidate.get("disposition") != "represented" or not is_natural_friction:
            continue
        family_id = candidate["family_id"]
        family_owner = family_by_id.get(family_id)
        if family_owner is None:
            raise ValueError(
                f"Palomar natural-friction family lacks review-matrix owner: {family_id}"
            )
        problem, family = family_owner
        declaration = candidate.get("comparator_declaration")
        friction_rows.append(
            {
                "family_id": family_id,
                "problem": problem,
                "disposition": candidate["disposition"],
                "load_bearing_mechanism": candidate["hard_mechanism"],
                "evidence_mode": family["evidence_mode"],
                "source_file": candidate["source_file"],
                "source_anchor": candidate["source_anchor"],
                "boundary": family["boundary"],
                "declaration": declaration,
            }
        )
    friction_rows.sort(key=lambda row: row["family_id"])
    if not friction_rows:
        raise ValueError("Palomar showcase lacks represented natural-friction rows")

    long_tail_group = next(
        (
            row
            for row in dispositions.get("eligible_groups", [])
            if row.get("disposition") == "long_tail"
        ),
        None,
    )
    if long_tail_group is None:
        raise ValueError("Palomar showcase lacks a long-tail disposition")

    programme_spines = _signal_programme_spines(
        packet, showcase, result_by_declaration, family_by_id
    )
    universe = showcase["candidate_universe"]
    source_dispositions = universe["source_family_dispositions"]
    disposition_order = contract.get("source_family_disposition_order")
    if not isinstance(disposition_order, list):
        raise ValueError("Palomar selection contract lacks source disposition order")
    unknown_dispositions = sorted(set(source_dispositions.values()) - set(disposition_order))
    if unknown_dispositions:
        raise ValueError(
            "Palomar source family has an unordered disposition: "
            f"{unknown_dispositions!r}"
        )
    disposition_groups = []
    for disposition in disposition_order:
        families = []
        for family_id in sorted(
            family_id
            for family_id, value in source_dispositions.items()
            if value == disposition
        ):
            problem, family = family_by_id[family_id]
            families.append(
                {
                    "family_id": family_id,
                    "problem": problem,
                    "trace_route": (
                        "python3 scripts/query_corpus.py --route "
                        f"erdos_{problem}"
                    ),
                }
            )
        if families:
            disposition_groups.append(
                {
                    "disposition": disposition,
                    "family_count": len(families),
                    "families": families,
                }
            )
    if include_programme_detail:
        programme_projection: dict[str, Any] = {
            "programme_spines": programme_spines,
        }
        universe_groups = disposition_groups
    else:
        programme_projection = {
            "programme_spine_index": [
                {
                    "problem": row["problem"],
                    "ordered_family_ids": [
                        result["family_id"] for result in row["results"]
                    ],
                    "tier_ids": [result["tier_id"] for result in row["results"]],
                    "trace_route": (
                        "python3 scripts/query_corpus.py --route "
                        f"erdos_{row['problem']}"
                    ),
                }
                for row in programme_spines
            ]
        }
        universe_groups = [
            {
                "disposition": group["disposition"],
                "family_count": group["family_count"],
            }
            for group in disposition_groups
        ]
    return {
        "authority": "docs/PALOMAR_RESULT_SHOWCASE.json::candidate_ranking",
        "ordering_contract": (
            "Explicit mathematical rank, never Comparator roster order, problem "
            "number, insertion order, theorem count, or qualification ease."
        ),
        "ranking_axes": [row["axis"] for row in contract["ranking_axes"]],
        "anti_hype_boundary": contract["anti_hype_boundary"],
        "trace_contract": {
            "proof_authority": "Lean source checked by the pinned kernel",
            "exact_hypotheses_route": (
                "python3 scripts/query_corpus.py --declaration <source_declaration>"
            ),
            "attribution_and_novelty_ceiling": "unassessed_no_priority_claim",
            "rule": (
                "Every ranked declaration keeps its exact source and boundary; "
                "the declaration route returns its formal hypothesis surface."
            ),
        },
        "ranked_frontier": ranked_frontier,
        **programme_projection,
        "candidate_universe": {
            "authority": universe["authority"],
            "selection_scope": universe["selection_scope"],
            "source_family_count": len(source_dispositions),
            "disposition_order": disposition_order,
            "disposition_groups": universe_groups,
            "complete_inventory_routes": [
                "docs/EXTERNAL_VERIFICATION.md#complete-serious-result-universe",
                "python3 scripts/query_corpus.py --route erdos_<problem_number>",
            ],
            "boundary": (
                "Complete source-family accounting remains subordinate to the ranked "
                "frontier; every family retains its source summary and open boundary."
            ),
        },
        "natural_friction": {
            "ordering": "alphabetical_unranked",
            "source_route": "Open each result's source_file at source_anchor.",
            "results": friction_rows,
        },
        "long_tail": {
            "disposition": "long_tail",
            "declaration_count": len(long_tail_group["declarations"]),
            "complete_inventory_routes": [
                "python3 scripts/query_corpus.py --route erdos_<problem_number>",
                "python3 scripts/query_corpus.py --publication-architecture",
                "docs/EXTERNAL_VERIFICATION.md#comparator-interface-appendix",
            ],
            "boundary": (
                "Subordination preserves exact declarations, evidence, and boundaries; "
                "it is not deletion or an adverse mathematical judgement."
            ),
        },
    }


def companion_repository_packet() -> dict[str, Any]:
    return {
        "name": "plectis",
        "repository": "https://github.com/wcook04/plectis",
        "relationship": (
            "Public systems and software companion, not dependency; this "
            "mathematical checkout remains self-contained."
        ),
    }


def paper_reading_guide_packet() -> dict[str, Any]:
    """Return the complete bounded reading guide for shipped manuscripts."""
    corpus = load("docs/papers/corpus.json")
    contract = load("docs/publication_contract.json")
    claims = load("docs/claims.json")
    problems = load("docs/problems.json")["problems"]
    artifacts = []
    for row in contract["artifacts"]:
        source = ROOT / row["source_path"]
        rendered = ROOT / row["rendered_path"]
        artifacts.append(
            {
                "id": row["id"],
                "artifact_class": row["artifact_class"],
                "source_path": row["source_path"],
                "rendered_path": row["rendered_path"],
                "source_available_in_checkout": source.is_file(),
                "rendered_available_in_checkout": rendered.is_file(),
            }
        )
    artifact_index = {row["id"]: row for row in artifacts}
    papers = []
    for row in corpus["papers"]:
        full_text_available = (ROOT / row["local_full_text"]).is_file()
        local_pdf = row.get("local_pdf")
        pdf_available = bool(local_pdf) and (ROOT / local_pdf).is_file()
        preferred_read_path = (
            row["local_full_text"]
            if full_text_available
            else local_pdf or row.get("local_source")
        )
        papers.append(
            {
                "paper_id": row["paper_id"],
                "title": row["title"],
                "question_this_paper_answers": row[
                    "question_this_paper_answers"
                ],
                "publication_class": row["publication_class"],
                "publication_state": row["publication_state"],
                "manuscript_status": row["manuscript_status"],
                "peer_review_state": row["peer_review_state"],
                "preferred_read_path": preferred_read_path,
                "full_text_available_in_checkout": full_text_available,
                "pdf_available_in_checkout": pdf_available,
                "local_source": row.get("local_source"),
                "first_pass": row.get("first_pass", []),
                "not_authority_for": row["not_authority_for"],
            }
        )
    default_gateway = artifact_index["human_exposition"]
    paper_index = {row["paper_id"]: row for row in papers}
    paper_by_problem = {
        int(row["erdos_number"]): row["paper"]["paper_id"] for row in problems
    }
    signal = mathematical_signal_spine(claims)

    def bind_paper(result: Mapping[str, Any]) -> dict[str, Any]:
        problem = int(result["problem"])
        paper_id = paper_by_problem.get(problem)
        if paper_id is None or paper_id not in paper_index:
            raise ValueError(
                f"Mathematical signal row lacks an active problem paper: #{problem}"
            )
        paper = paper_index[paper_id]
        return {
            **result,
            "paper_id": paper_id,
            "paper_title": paper["title"],
            "preferred_read_path": paper["preferred_read_path"],
        }

    signal["ranked_frontier"] = [
        bind_paper(row) for row in signal["ranked_frontier"]
    ]
    signal["natural_friction"] = {
        **signal["natural_friction"],
        "results": [
            bind_paper(row) for row in signal["natural_friction"]["results"]
        ],
    }
    signal["paper_route_contract"] = (
        "Ranked mathematical families and natural friction lead; the complete "
        "manuscript shelf follows without becoming a significance order."
    )
    mathematical_default_gateway = {
        key: signal["ranked_frontier"][0][key]
        for key in (
            "rank",
            "problem",
            "family_id",
            "reader_tier",
            "paper_id",
            "paper_title",
            "preferred_read_path",
            "exact_boundary",
        )
    }
    return {
        "kind": "paper_reading_guide",
        "schema_version": "erdos249257-paper-reading-guide/1",
        "authority_posture": (
            "generated_paper_navigation_not_Lean_proof_or_claim_status_authority"
        ),
        "paper_count": len(papers),
        "mathematical_signal_spine": signal,
        "papers": papers,
        "default_gateway": default_gateway,
        "mathematical_default_gateway": mathematical_default_gateway,
        "recommended_routes": {
            "understand_the_mathematics": [
                {
                    "path": mathematical_default_gateway["preferred_read_path"],
                    "reason": (
                        "Start with the active paper carrying the highest-ranked "
                        "source-current mathematical family."
                    ),
                },
                {
                    "artifact_id": "human_exposition",
                    "reason": (
                        "Use the retained combined manuscript for provenance and "
                        "cross-problem synthesis, not as the signal-first paper."
                    ),
                },
                {
                    "path": "docs/RESULTS.md",
                    "reason": "Read the strongest checked result and limit per problem.",
                },
                {
                    "path": "docs/papers/README.md",
                    "reason": "Choose a problem-owned note by the question it answers.",
                },
            ],
            "audit_public_claims": [
                {
                    "artifact_id": "repository_architecture_guide",
                    "reason": "Inspect the proof, claim, exposition, and release boundary.",
                },
                {
                    "path": "docs/EXTERNAL_VERIFICATION.md",
                    "reason": "Inspect the Comparator interface and axiom boundary.",
                },
            ],
            "work_from_a_cold_clone": [
                {
                    "artifact_id": "agent_native_navigation_guide",
                    "reason": "Cross from bounded navigation to a Lean proof receipt.",
                }
            ],
        },
        "registered_publication_artifacts": artifacts,
        "clone_local_paper_index": "docs/papers/README.md",
        "machine_inventory": "docs/papers/corpus.json",
        "companion_repository": companion_repository_packet(),
        "authority_order": corpus["authority_order"],
        "verification_boundary": corpus["verification_boundary"],
        "next": (
            "Choose the question first; then follow the selected paper's "
            "claim, open-proposition, declaration, or source handles."
        ),
    }


def repository_overview_packet(query: str | None = None) -> dict[str, Any]:
    """Return complete bounded coverage for an unfamiliar public reader."""
    orientation = load("docs/orientation.json")
    claims = load("docs/claims.json")
    problems = load("docs/problems.json").get("problems", [])
    assembly = claims["machine_readable_paper"]["publication_assembly"]
    programmes = orientation["mathematical_programmes"]
    open_rows = orientation["remaining_open_propositions"]
    families = assembly["contribution_families"]
    statuses = orientation["status_taxonomy"]
    principal_claims = orientation["principal_claims"]
    reviewed_family_census = reviewed_result_family_census(claims)
    reviewed_family_by_problem = {
        str(row["erdos_number"]): row for row in reviewed_family_census
    }
    packet = {
        "kind": "repository_overview",
        "schema_version": "erdos249257-repository-overview/2",
        "authority_posture": "bounded_public_orientation_not_proof_authority",
        "mathematical_signal_spine": mathematical_signal_spine(claims),
        "coverage_receipt": {
            "mathematical_programme_count": len(programmes),
            "mathematical_programme_ids": [row["id"] for row in programmes],
            "claim_status_class_count": len(statuses),
            "claim_status_classes": list(statuses),
            "remaining_open_proposition_count": len(open_rows),
            "remaining_open_proposition_ids": [row["id"] for row in open_rows],
            "publication_family_count": len(families),
            "publication_family_ids": [row["id"] for row in families],
            "reviewed_result_family_count": sum(
                row["family_count"] for row in reviewed_family_census
            ),
            "reviewed_result_family_count_by_problem": {
                str(row["erdos_number"]): row["family_count"]
                for row in reviewed_family_census
            },
            "reviewed_result_family_source": (
                "docs/claims.json::external_verification_packet.review_matrix"
            ),
            "curated_claim_count": len(claims["claims"]),
            "principal_claim_count": len(principal_claims),
            "indexed_problem_count": len(problems),
        },
        "problem_fleet": [
            {
                "erdos_number": row["erdos_number"],
                "title": row["short_title"],
                "status": row["status"],
                "note": row.get("note"),
                "open_obligation_ids": [
                    item["id"] for item in row.get("open_obligations", [])
                ],
                "result_family_count": reviewed_family_by_problem.get(
                    str(row["erdos_number"]), {}
                ).get("family_count", 0),
                "result_family_ids": reviewed_family_by_problem.get(
                    str(row["erdos_number"]), {}
                ).get("family_ids", []),
                "result_family_source": (
                    "docs/claims.json::external_verification_packet.review_matrix"
                ),
                "result_route": (
                    "python3 scripts/query_corpus.py --route "
                    f"{row['problem_id']}"
                ),
                "route_memory": (
                    "python3 scripts/query_route_memory.py --problem "
                    f"{row['erdos_number']}"
                ),
            }
            for row in problems
        ],
        "mathematical_programmes": [
            {
                "id": row["id"],
                "title": row["title"],
                "mathematical_focus": row["mathematical_focus"],
                "claim_ceiling": row["claim_ceiling"],
                "remaining_open_proposition_ids": row[
                    "remaining_open_proposition_ids"
                ],
            }
            for row in programmes
        ],
        "claim_status_taxonomy": statuses,
        "principal_claims": principal_claims,
        "remaining_open_propositions": open_rows,
        "publication_family_index": [
            {
                "id": row["id"],
                "primary_narrative_owner": row["primary_narrative_owner"],
                "view_decision": row["view_decision"],
                "claim_count": len(row["claim_ids"]),
                "source_route": row["source_route"],
            }
            for row in families
        ],
        "publication_family_index_contract": {
            "coverage": "complete_family_id_owner_disposition_count_and_route",
            "detail": (
                "python3 scripts/query_corpus.py --publication-family <family_id>"
            ),
            "boundary": (
                "Detailed status prose is routed, not duplicated ahead of the "
                "mathematical signal spine."
            ),
        },
        "problem_result_family_contract": {
            "source": "docs/claims.json::external_verification_packet.review_matrix",
            "route": "python3 scripts/query_corpus.py --route <problem_id>",
            "ordering": (
                "Each problem route preserves claim-registry review-matrix order "
                "across all distinct families; theorem and declaration counts "
                "are not used as a significance proxy."
            ),
            "boundary": (
                "Family rows are navigation context. Their evidence mode and "
                "declaration handles do not promote expansion material into "
                "reviewed claims or close an Erdős problem."
            ),
        },
        "repository_map": [
            {"layer": "proof", "owner": "Lean source and pinned kernel"},
            {"layer": "public_status", "owner": "docs/claims.json"},
            {"layer": "methodology", "owner": "docs/methodology.json"},
            {"layer": "papers", "owner": "docs/papers/corpus.json"},
            {"layer": "navigation", "owner": "generated docs projections"},
            {"layer": "verification", "owner": "release checks and Comparator CI"},
        ],
        "answer_contract": {
            "required_coverage": [
                "all mathematical programmes",
                "all claim-status classes",
                "every exact remaining-open proposition",
                "the complete publication-family index",
                "the companion Plectis boundary",
            ],
            "weighting": (
                "Weight reductions, reusable interfaces, and honest "
                "obstructions above raw theorem or file volume."
            ),
        },
        "companion_repository": companion_repository_packet(),
        "next": {
            "papers": "python3 scripts/query_corpus.py --papers",
            "problem": "python3 scripts/query_corpus.py --search 'Erdős problem <n>'",
            "claim": "python3 scripts/verify_claims.py --claim <claim_id>",
            "route_memory": (
                "python3 scripts/query_route_memory.py --problem <problem_number>"
            ),
        },
    }
    if query is not None:
        packet["query_interpretation"] = {
            "query": query,
            "routed_by": "ordinary_cold_reader_phrase",
        }
    return packet


def agent_tour_packet() -> dict[str, Any]:
    """Return a signal-first, corpus-derived tour for an unfamiliar agent.

    The tour is intentionally assembled from committed projections rather than
    paper-specific module names. It exposes the same intent classes that recur
    in a large Lean development: understand the mathematical map, locate exact
    source, inspect formal dependencies, begin a checked change, and audit the
    agent/release system.
    """
    orientation = load("docs/orientation.json")
    claims = load("docs/claims.json")
    problems = load("docs/problems.json").get("problems", [])
    dependency = load("docs/lean_dependency_index.json")
    assembly = claims["machine_readable_paper"]["publication_assembly"]
    status_counts = Counter(row["status"] for row in claims["claims"])
    coverage = dependency["coverage"]
    programmes = orientation["mathematical_programmes"]
    open_rows = orientation["remaining_open_propositions"]
    indexed_open_problem_count = sum(
        row.get("status") == "open" for row in problems
    )
    reviewed_family_census = reviewed_result_family_census(claims)
    reviewed_family_by_problem = {
        str(row["erdos_number"]): row for row in reviewed_family_census
    }
    mathematical_signal = mathematical_signal_spine(claims)
    return {
        "kind": "agent_corpus_tour",
        "schema_version": "agent-corpus-tour/2",
        "authority_posture": "computed_navigation_tour_not_proof_authority",
        "mathematical_signal_spine": mathematical_signal,
        "budget_contract": {
            "maximum_encoded_bytes": agent_tour_budget_bytes(len(problems)),
            "policy": (
                "18000 base bytes plus 5100 bytes per canonically indexed "
                "problem; eight problems currently yield a 58800-byte ceiling"
            ),
            "reason": (
                "The registry map is material first-contact context. Its budget "
                "scales with registry breadth instead of inheriting the generic "
                "single-packet cap."
            ),
        },
        "scale": {
            **orientation["scale"],
            "curated_claim_count": len(claims["claims"]),
            "mathematical_programme_count": len(programmes),
            "contribution_family_count": len(
                assembly["contribution_families"]
            ),
            "remaining_open_proposition_count": len(open_rows),
            "reviewed_remaining_open_proposition_count": len(open_rows),
            "reviewed_result_family_count": sum(
                row["family_count"] for row in reviewed_family_census
            ),
            "indexed_problem_count": len(problems),
            "indexed_open_problem_count": indexed_open_problem_count,
        },
        "formal_dependency_graph": {
            "loaded_library_roots": coverage["loaded_library_roots"],
            "source_resolved_node_count": coverage[
                "source_resolved_node_count"
            ],
            "source_resolved_direct_edge_count": coverage[
                "source_resolved_direct_edge_count"
            ],
            "unresolved_atlas_declaration_count": coverage[
                "unresolved_atlas_declaration_count"
            ],
            "unresolved_public_edge_count": coverage[
                "unresolved_public_edge_count"
            ],
            "edge_policy": "elaborated direct value references",
        },
        "claim_status_counts": {
            status: status_counts.get(status, 0)
            for status in orientation["status_taxonomy"]
        },
        "problem_map": [
            {
                "problem_id": row["problem_id"],
                "erdos_number": row["erdos_number"],
                "title": row["short_title"],
                "status": row["status"],
                "module_count": len(row.get("modules", [])),
                "note": row.get("note"),
                "result_family_count": reviewed_family_by_problem.get(
                    str(row["erdos_number"]), {}
                ).get("family_count", 0),
                "result_family_ids": reviewed_family_by_problem.get(
                    str(row["erdos_number"]), {}
                ).get("family_ids", []),
                "result_family_source": (
                    "docs/claims.json::external_verification_packet.review_matrix"
                ),
                "follow": (
                    "python3 scripts/query_corpus.py --route "
                    f"{row['problem_id']}"
                ),
                "route_memory": (
                    "python3 scripts/query_route_memory.py --problem "
                    f"{row['erdos_number']}"
                ),
            }
            for row in problems
        ],
        "route_memory_contract": {
            "start": (
                "python3 scripts/query_route_memory.py --problem "
                "<problem_map.erdos_number> [--route <mathematical_map.id>]"
            ),
            "validate": (
                "python3 scripts/query_route_memory.py --validate <packet.json>"
            ),
            "selector_source": "problem_map[].erdos_number from docs/problems.json",
            "coverage": {
                "indexed_problem_count": len(problems),
                "indexed_problem_numbers": [row["erdos_number"] for row in problems],
            },
            "authority_posture": (
                "derived_resume_handoff_not_claim_or_proof_authority"
            ),
            "rejections": [
                "stale_source_snapshot",
                "invented_route_or_reference",
                "cross_problem_route_or_declaration",
            ],
        },
        "problem_result_family_contract": {
            "source": "docs/claims.json::external_verification_packet.review_matrix",
            "route": "python3 scripts/query_corpus.py --route <problem_id>",
            "meaning": (
                "The problem map names every distinct review-matrix family; "
                "expand the problem route for its summary, evidence mode, "
                "declarations, paper, and exact open obligations."
            ),
        },
        "open_frontier_contract": {
            "indexed_open_problem_count": indexed_open_problem_count,
            "reviewed_remaining_open_proposition_count": len(open_rows),
            "reviewed_scope": "all eight indexed problem programmes",
            "distinction": (
                "Open-proposition rows describe exact surviving endpoints and "
                "selected subfrontiers across all eight programmes; their count "
                "is not the count of indexed open Erdős problems."
            ),
        },
        "mathematical_map": [
            {
                "id": row["id"],
                "title": row["title"],
                "mathematical_focus": row["mathematical_focus"],
                "claim_ceiling": row["claim_ceiling"],
                "core_claim_count": row["core_claim_count"],
                "remaining_open_proposition_ids": row[
                    "remaining_open_proposition_ids"
                ],
                "follow": (
                    "python3 scripts/query_corpus.py --route "
                    f"{row['id']}"
                ),
            }
            for row in programmes
        ],
        "frontier": [
            {
                "id": row["id"],
                "statement": row["statement"],
                "follow": (
                    "python3 scripts/query_corpus.py --open "
                    f"{row['id']}"
                ),
            }
            for row in open_rows
        ],
        "intent_lenses": [
            {
                "intent": "understand_the_mathematics",
                "start": "python3 scripts/query_corpus.py --route <mathematical_map.id>",
                "then": "python3 scripts/query_corpus.py --claim <claim.id>",
            },
            {
                "intent": "locate_any_formal_object",
                "start": (
                    "python3 scripts/query_corpus.py --search "
                    "<ordinary-language-query>"
                ),
                "then": (
                    "python3 scripts/query_semantic.py inventory "
                    "<candidate-name-or-source-term> --module <path-fragment> "
                    "--role <role> --zone <zone>"
                ),
                "expand": (
                    "python3 scripts/query_corpus.py --declaration <Lean_name>"
                ),
            },
            {
                "intent": "inspect_exact_formal_dependencies",
                "start": (
                    "python3 scripts/query_corpus.py --proof-cone "
                    "<Lean_name> --depth 2"
                ),
                "then": (
                    "python3 scripts/query_corpus.py --dependency-path "
                    "<source> <target>"
                ),
            },
            {
                "intent": "begin_a_checked_change",
                "start": "python3 scripts/proof_workbench.py open --help",
                "then": (
                    "python3 scripts/lean_fast_build.py --jobs 2 "
                    "--lake-staleness <selected-target>"
                ),
            },
            {
                "intent": "audit_the_agent_and_release_system",
                "start": "python3 scripts/query_corpus.py --publication-architecture",
                "then": "python3 scripts/check_release.py",
            },
        ],
        "cold_reader_contracts": {
            "research_mathematician": {
                "questions_answered": [
                    "What mathematical programmes are present?",
                    "Which claims are proved, conditional, finite, cited, or open?",
                    "What exact propositions remain open?",
                ],
                "use": [
                    "mathematical_map",
                    "claim_status_counts",
                    "frontier",
                ],
            },
            "formalisation_engineer": {
                "questions_answered": [
                    "Where is a declaration defined?",
                    "Which exact formal values does it reference?",
                    "How do I make and replay a kernel-checked change?",
                ],
                "use": [
                    "locate_any_formal_object",
                    "inspect_exact_formal_dependencies",
                    "begin_a_checked_change",
                ],
            },
            "ai_lab_researcher": {
                "questions_answered": [
                    "Which layers are exhaustive and which are selective?",
                    "What is exact graph data versus authored interpretation?",
                    "Which agent actions receive replayable authority receipts?",
                ],
                "use": [
                    "scale",
                    "formal_dependency_graph",
                    "authority_boundary",
                ],
            },
            "independent_contributor": {
                "questions_answered": [
                    "Can I orient before compiling?",
                    "Can I build only the selected or stale dependency cone?",
                    "Which release check establishes the public handoff?",
                ],
                "use": [
                    "authority_boundary.navigation",
                    "begin_a_checked_change",
                    "audit_the_agent_and_release_system",
                ],
            },
        },
        "authority_boundary": {
            "navigation": "committed JSON projections; no Lean build required",
            "proof": orientation["proof_authority"],
            "public_meaning": (
                "maintainer-reviewed claims and authored mathematical "
                "interpretation"
            ),
            "release": (
                "automated checks preserve recorded relationships but do not "
                "judge unrestricted prose"
            ),
        },
        "omission_receipt": {
            "omitted": (
                "the exhaustive declaration rows, proof edges, full claim "
                "records, and per-family review records"
            ),
            "reason": (
                "first-contact tour gives ranked mathematics unequal depth and "
                "routes exhaustive family detail through each problem"
            ),
            "expand": (
                "python3 scripts/query_corpus.py --route "
                "agent_native_corpus_navigation"
            ),
        },
    }


def summary_packet() -> dict[str, Any]:
    orientation = load("docs/orientation.json")
    claims = load("docs/claims.json")
    atlas = load("docs/declaration_atlas.json")
    raw_declaration_count = len(atlas["declarations"])
    effective_declaration_count = len(atlas_declarations(atlas))
    assembly = claims["machine_readable_paper"]["publication_assembly"]
    bounded_omissions = (
        "checks",
        "editorial_architecture",
        "editorial_state",
        "external_registration",
        "source_provenance",
    )
    summary_orientation = {
        key: value
        for key, value in orientation.items()
        if key not in bounded_omissions
    }
    summary_orientation["principal_claims"] = [
        {
            key: value
            for key, value in row.items()
            if key != "declarations"
        }
        for row in orientation["principal_claims"]
    ]
    return {
        "kind": "corpus_summary",
        **summary_orientation,
        "curated_claim_count": len(claims["claims"]),
        "publication_family_count": len(assembly["contribution_families"]),
        "declaration_projection_filter_receipt": {
            "raw_atlas_declaration_count": raw_declaration_count,
            "effective_query_declaration_count": effective_declaration_count,
            "suppressed_comment_false_positive_count": (
                raw_declaration_count - effective_declaration_count
            ),
            "validation": "python3 scripts/audit_semantic_corpus.py",
        },
        "bounded_summary_omission_receipt": {
            "omitted_sections": list(bounded_omissions),
            "omitted_fields": ["principal_claims[].declarations"],
            "drilldown": "docs/orientation.json",
            "claim_drilldown": "python3 scripts/query_corpus.py --claim <claim_id>",
            "reason": "non_mathematical_owner_metadata_kept_out_of_bounded_agent_summary",
        },
    }


def _route_memory_resume_commands(route_memory: Any) -> list[str]:
    """Return canonical resume commands carried by a route-memory projection.

    Semantic cells may expose a direct command (reading-route bindings) or a
    bound projection whose commands live inside its binding rows.  Card output
    is a reader-facing continuation surface, so preserve both shapes without
    inventing commands for unbound route memory.
    """
    if isinstance(route_memory, str):
        return (
            [route_memory]
            if route_memory.startswith("python3 scripts/query_route_memory.py")
            else []
        )
    if not isinstance(route_memory, dict):
        return []
    commands: list[str] = []
    direct = route_memory.get("command")
    if isinstance(direct, str) and direct:
        commands.append(direct)
    for binding in route_memory.get("bindings", []):
        if not isinstance(binding, dict):
            continue
        command = binding.get("command")
        if isinstance(command, str) and command and command not in commands:
            commands.append(command)
    return commands


def _append_route_memory_resumes(card: str, route_memory: Any) -> str:
    """Append every bound continuation command to a human-readable card."""
    for command in _route_memory_resume_commands(route_memory):
        card += f" | resume={command}"
    return card


def render_card(packet: dict[str, Any]) -> str:
    kind = packet["kind"]
    if kind == "claim":
        claim = packet["claim"]
        decls = ", ".join(row["name"] for row in claim["declarations"]) or "none"
        neighbourhood = packet["argument_neighbourhood"]
        card = (
            f"claim {claim['id']} | {claim['status']} | paper={claim.get('paper_label')} "
            f"| incoming={len(neighbourhood['incoming'])} | outgoing={len(neighbourhood['outgoing'])} "
            f"| declarations={decls}"
        )
        return _append_route_memory_resumes(card, packet.get("route_memory"))
    if kind == "paper_label":
        paper = packet["paper"]
        claim_ids = ",".join(row["id"] for row in packet["attached_claims"]) or "none"
        source = paper.get("source_ref") or paper.get(
            "availability", "unavailable"
        )
        card = (
            f"paper {paper['label']} | {source} | rendered={paper.get('rendered')} "
            f"| claims={claim_ids}"
        )
        return _append_route_memory_resumes(card, packet.get("route_memory"))
    if kind == "paper_anchor":
        paper = packet["paper"]
        card = (
            f"paper anchor {packet['canonical_handle']} | {packet['anchor_class']} "
            f"| {paper['source_ref']} | title={packet.get('title') or 'none'}"
        )
        return _append_route_memory_resumes(card, packet.get("route_memory"))
    if kind == "paper_source":
        paper = packet["paper"]
        rows = [
            (
                f"paper source {paper['source']} | anchors="
                f"{packet['coverage_receipt']['anchor_count']}"
            )
        ]
        rows.extend(
            f"paper anchor | {anchor['canonical_handle']} | {anchor['source_ref']}"
            for anchor in packet["anchors"]
        )
        return "\n".join(rows)
    if kind == "reviewed_result_family":
        return (
            f"result family #{packet['erdos_number']} rank={packet['rank']} "
            f"| {packet['id']} | {packet.get('comparator_disposition')} "
            f"| {packet.get('summary')} | problem={packet['problem_route']} "
            f"| paper={packet.get('paper_source_route') or 'none'}"
        )
    if kind == "declaration":
        rows = []
        for row in packet["matches"]:
            card = (
                f"declaration {row['name']} | {row['kind']} | {row['module']}:{row['line']} "
                f"| claims={','.join(row['claim_ids']) or 'none'}"
            )
            rows.append(_append_route_memory_resumes(card, row.get("route_memory")))
        return "\n".join(rows)
    if kind == "formal_dependency_proof_cone":
        return (
            f"proof cone {packet.get('resolved_handle', packet['requested'])} "
            f"| {packet['availability']} | nodes={len(packet.get('nodes', []))} "
            f"| edges={len(packet.get('edges', []))} "
            f"| depth={packet.get('max_depth', 'n/a')}"
        )
    if kind == "formal_dependency_path":
        return (
            f"dependency path {packet.get('source', packet.get('requested_source'))} "
            f"-> {packet.get('target', packet.get('requested_target'))} "
            f"| {packet['availability']} "
            f"| hops={packet.get('hop_count', 'n/a')}"
        )
    if kind == "formal_goal_support":
        return (
            f"formal goal support | {packet['availability']} "
            f"| goal={packet.get('goal_request', {}).get('goal', 'unresolved')} "
            f"| candidates={len(packet.get('candidates', []))}/"
            f"{packet.get('candidate_count', 0)}"
        )
    if kind == "formal_proof_plan":
        application = packet.get("application", {})
        return (
            f"formal proof plan | {packet['availability']} "
            f"| terminal={packet.get('terminal_candidate', {}).get('name', 'unresolved')} "
            f"| status={packet.get('plan_status', 'unresolved')} "
            f"| obligations={application.get('obligation_count', 0)} "
            f"| unmatched={application.get('unmatched_proposition_count', 0)} "
            f"| spine={len(packet.get('exact_dependency_spine', {}).get('steps', []))}"
        )
    if kind == "source_coordinate":
        source = packet["source"]
        card = (
            f"source {source['source_ref']} | module={source['module_id']} "
            f"| nearby_declarations={len(packet['nearby_declarations'])}"
        )
        for declaration in packet["nearby_declarations"]:
            card = _append_route_memory_resumes(
                card, declaration.get("route_memory")
            )
        return card
    if kind == "artifact":
        match = packet["matches"][0]
        return (
            f"artifact {match['artifact_handle']} | {match['artifact_kind']} "
            f"| digest={match['content_digest']} | matches={len(packet['matches'])}"
        )
    if kind == "publication_artifact":
        artifact = packet["artifact"]
        return (
            f"publication artifact {artifact['id']} | {artifact['artifact_class']} "
            f"| identity={packet['content_identity_status']} "
            f"| source={artifact['source_path']} | rendered={artifact['rendered_path']}"
        )
    if kind == "publication_evidence":
        mutation = packet["mutation"]
        if mutation is None:
            summary = packet["summary"]
            return (
                f"publication evidence {packet['record_id']} "
                f"| checkpoint={packet['checkpoint'][:7]} "
                f"| snapshot_claims={packet['corpus_snapshot']['curated_claim_count']} "
                f"| snapshot_families={packet['corpus_snapshot']['contribution_family_count']} "
                f"| current_claims={packet['current_corpus_census']['curated_claim_count']} "
                f"| current_families={packet['current_corpus_census']['contribution_family_count']} "
                f"| same_snapshot={packet['time_axis']['same_as_evaluation_snapshot']} "
                f"| mutations={summary['authored_mutation_count']} "
                f"| rejected={summary['rejected_mutation_count']} "
                f"| escaped={','.join(summary['escaped_mutation_ids'])}"
            )
        return (
            f"publication mutation {mutation['id']} | {mutation['outcome']} "
            f"| first_detector={mutation.get('first_detector') or 'none'} "
            f"| time={mutation['wall_time_seconds']}s "
            f"| checkpoint={packet['checkpoint'][:7]}"
        )
    if kind == "open_proposition":
        proposition = packet["open_proposition"]
        card = (
            f"open {proposition['id']} | target={packet['open_target']['id']} "
            f"| linked_claims={len(packet['linked_claims'])} "
            f"| advancing_claims={len(packet['advancing_claims'])}"
        )
        return _append_route_memory_resumes(card, packet.get("route_memory"))
    if kind == "module":
        module = packet["module"]
        dependency = packet["dependency_neighbourhood"]["receipt"]
        card = (
            f"module {module['id']} | {module['path']} | declarations={module['declaration_count']} "
            f"| imports={dependency['imports_total']} | importers={dependency['importers_total']} "
            f"| claims={len(packet['attached_claims'])} | paper_sigil={packet.get('paper_sigil') or 'none'} "
            f"| role={module['role']}"
        )
        return _append_route_memory_resumes(card, packet.get("route_memory"))
    if kind == "connection_card":
        anchor = packet["anchor"]
        return (
            f"connections {anchor['module_id']} | declarations={packet['declaration_count']} "
            f"| imports={len(packet['relationship_direction']['prerequisite_imports'])} "
            f"| importers={len(packet['relationship_direction']['consumer_importers'])} "
            f"| disclosure={packet['surface_contract']['disclosure_posture']}"
        )
    if kind == "search":
        rows = [
            f"search {packet['query']!r} "
            f"| operator={packet['query_interpretation']['operator']['id']} "
            f"| matches={packet['match_count']} | emitted={len(packet['results'])}"
        ]
        for result in packet["results"]:
            handle = result.get("id") or result.get("name")
            line = f"{result['kind']} | {handle}"
            for command in _route_memory_resume_commands(result.get("route_memory")):
                line += f" | resume={command}"
            rows.append(line)
        return "\n".join(rows)
    if kind == "semantic_dictionary":
        return (
            f"semantic dictionary {packet['schema_version']} "
            f"| operators={len(packet['operators'])} "
            f"| vocabulary={len(packet['vocabulary'])}"
        )
    if kind == "semantic_slice":
        rows = [
            f"semantic slice {packet['query']!r} "
            f"| operator={packet['query_interpretation']['operator']['id']} "
            f"| cells={len(packet['semantic_cells'])}"
        ]
        for cell in packet["semantic_cells"]:
            line = f"{cell['kind']} | {cell['handle']} | {cell['selection_reason']}"
            content = cell.get("content")
            route_memory = content.get("route_memory") if isinstance(content, dict) else None
            for command in _route_memory_resume_commands(route_memory):
                line += f" | resume={command}"
            rows.append(line)
        rows.extend(
            f"semantic_node | {row['node_id']} | authored_semantic_followup"
            for row in packet["query_interpretation"].get(
                "authored_semantic_followups", []
            )
        )
        rows.append(
            f"witness_edges={len(packet['minimal_witness_subgraph']['edges'])} "
            f"| omitted={packet['omission_receipt'].get('omitted_match_count', 0)}"
        )
        return "\n".join(rows)
    if kind == "corpus_scope_boundary":
        requested = ",".join(
            f"#{number}" for number in packet["requested_problem_numbers"]
        )
        outside = ",".join(
            f"#{number}" for number in packet["out_of_scope_problem_numbers"]
        )
        indexed = ",".join(
            f"#{number}" for number in packet["indexed_problem_numbers"]
        )
        return (
            f"corpus scope boundary | status={packet['status']} "
            f"| requested={requested} | out_of_scope={outside} "
            f"| indexed={indexed} | source={packet['scope_source']} "
            "| claim_effect=none"
        )
    if kind == "claim_status":
        card = (
            f"status {packet['status']} | claims={packet['claim_count']} "
            f"| emitted={len(packet['claims'])} "
            f"| remaining_open_propositions={len(packet['remaining_open_propositions'])}"
        )
        route_memory_by_claim = packet.get("route_memory", {}).get("by_claim", {})
        rows = [card]
        for claim in packet["claims"]:
            commands = _route_memory_resume_commands(
                route_memory_by_claim.get(claim.get("id"))
            )
            if not commands:
                continue
            row = f"claim_route | {claim['id']}"
            for command in commands:
                row += f" | resume={command}"
            rows.append(row)
        return "\n".join(rows)
    if kind == "reading_route":
        route = packet["route"]
        if route.get("route_kind") == "mathematical_programme":
            programme = packet["programme"]
            claims = ",".join(
                row["id"] for row in programme["core_claims"]
            )
            open_ids = ",".join(
                row["id"]
                for row in programme["remaining_open_propositions"]
            )
            card = (
                f"programme {route['id']} | {programme['title']} "
                f"| claims={claims} | open={open_ids}"
            )
            rows = [
                _append_route_memory_resumes(card, packet.get("route_memory"))
            ]
            signal = programme["mathematical_signal_spine"]
            signal_rows = [
                dict(zip(signal["result_fields"], row, strict=True))
                for row in signal["results"]
            ]
            rows.extend(
                (
                    f"programme_signal #{row['programme_order']} "
                    f"| tier={row['tier_id']} | family={row['family_id']} "
                    f"| source_disposition={row['source_disposition']} "
                    f"| declaration={row['declaration']}"
                )
                for row in signal_rows
            )
            return "\n".join(rows)
        card = (
            f"route {route['id']} | {route['intent']} | read={' -> '.join(route['read'])} "
            f"| next={route['query_steps'][0]}"
        )
        signal = packet.get("mathematical_signal_spine")
        if not isinstance(signal, Mapping):
            return card
        rows = [card]
        rows.extend(
            (
                f"global_signal #{row['rank']} | problem=#{row['problem']} "
                f"| tier={row['reader_tier']} | family={row['family_id']} "
                f"| boundary={row['exact_boundary']}"
            )
            for row in signal["ranked_frontier"]
        )
        return "\n".join(rows)
    if kind == "problem_route":
        route = packet["route"]
        research = route.get("research_corpus")
        research_summary = ""
        if isinstance(research, dict):
            strongest = research.get("strongest_result_summary", {})
            research_summary = (
                f" | research_results={strongest.get('result_count', 0)}"
                f" | research_frontier={research['files']['frontier']['path']}"
            )
        paper = route.get("paper") or {}
        paper_summary = paper.get("source") or paper.get("resolution", "")
        card = (
            f"problem {route['id']} | #{route['erdos_number']} | {route['status']}"
            f" | modules={route['module_count']} | note={route['note']['artifact_id']}"
            f" | families={len(route.get('result_families', []))}"
            f" | paper={paper_summary}"
            f" | open={len(route.get('open_obligations', []))}"
            f"{research_summary}"
        )
        rows = [
            _append_route_memory_resumes(
                card, route.get("follow", {}).get("route_memory")
            )
        ]
        rows.extend(
            (
                f"programme_signal #{row['programme_order']} "
                f"| tier={row['tier_id']} | family={row['family_id']} "
                f"| source_disposition={row['source_disposition']} "
                f"| declaration={row['declaration']}"
            )
            for row in packet["mathematical_signal_spine"]["results"]
        )
        return "\n".join(rows)
    if kind == "publication_family":
        family = packet["family"]
        card = (
            f"publication family {family['id']} | claims={len(packet['claims'])} "
            f"| owner={family['primary_narrative_owner']} "
            f"| view={family['view_decision']} "
            f"| obligation={family['consumer_or_open_obligation']}"
        )
        return _append_route_memory_resumes(card, packet.get("route_memory"))
    if kind == "publication_architecture":
        architecture = packet["architecture"]
        card = (
            f"publication architecture | gateway="
            f"{architecture['canonical_gateway']['source']} "
            f"| retained_companions={len(architecture['retained_companions'])} "
            f"| families={len(packet['family_index'])}"
        )
        rows = [card]
        for family in packet.get("family_index", []):
            commands = _route_memory_resume_commands(family.get("route_memory"))
            if not commands:
                continue
            row = f"family_route | {family['id']}"
            for command in commands:
                row += f" | resume={command}"
            rows.append(row)
        return "\n".join(rows)
    if kind == "repository_overview":
        coverage = packet["coverage_receipt"]
        signal = packet["mathematical_signal_spine"]
        rows = [
            (
                "repository overview | "
                f"problems={coverage['indexed_problem_count']} "
                f"| programmes={coverage['mathematical_programme_count']} "
                f"| claims={coverage['curated_claim_count']} "
                f"| exact_open={coverage['remaining_open_proposition_count']}"
            ),
            (
                "signal rule | explicit Palomar mathematical rank before exhaustive "
                "inventory; Comparator roster order is not significance"
            ),
        ]
        rows.extend(
            (
                f"signal #{candidate['rank']} | {candidate['reader_tier']} "
                f"| problem=#{candidate['problem']} | family={candidate['family_id']} "
                f"| declaration={candidate['declaration']}"
            )
            for candidate in signal["ranked_frontier"]
        )
        rows.extend(
            (
                f"natural_friction | problem=#{candidate['problem']} "
                f"| family={candidate['family_id']} | disposition="
                f"{candidate['disposition']}"
            )
            for candidate in signal["natural_friction"]["results"]
        )
        rows.extend(
            [
                (
                    "long_tail | subordinate_not_deleted "
                    f"| declarations={signal['long_tail']['declaration_count']}"
                ),
                "papers | command=python3 scripts/query_corpus.py --papers",
            ]
        )
        for problem in packet.get("problem_fleet", []):
            command = problem.get("route_memory")
            if not isinstance(command, str) or not command:
                continue
            rows.append(
                f"problem_route | #{problem['erdos_number']} | resume={command}"
            )
        return "\n".join(rows)
    if kind == "paper_reading_guide":
        signal = packet["mathematical_signal_spine"]
        rows = [
            f"paper reading guide | papers={packet['paper_count']} "
            f"| index={packet['clone_local_paper_index']}",
            (
                "authority | papers are exposition; Lean source proves, "
                "docs/claims.json declares public status"
            ),
            (
                "signal rule | Palomar mathematical rank before the complete "
                "manuscript shelf; paper inventory order is not significance"
            ),
        ]
        rows.extend(
            f"paper_signal #{row['rank']} | problem=#{row['problem']} "
            f"| tier={row['reader_tier']} | family={row['family_id']} "
            f"| paper={row['paper_id']} | read={row['preferred_read_path']} "
            f"| boundary={row['exact_boundary']}"
            for row in signal["ranked_frontier"]
        )
        rows.extend(
            f"paper_friction | problem=#{row['problem']} "
            f"| family={row['family_id']} | paper={row['paper_id']} "
            f"| read={row['preferred_read_path']} | boundary={row['boundary']}"
            for row in signal["natural_friction"]["results"]
        )
        rows.extend(
            [
                (
                    "paper_long_tail | subordinate_not_deleted "
                    f"| declarations={signal['long_tail']['declaration_count']}"
                ),
                "paper_inventory | exhaustive_not_ranked",
            ]
        )
        rows.extend(
            f"paper_inventory | {row['paper_id']} | {row['publication_state']} "
            f"| {row['title']} | read={row['preferred_read_path']}"
            for row in packet["papers"]
        )
        return "\n".join(rows)
    if kind == "agent_corpus_tour":
        scale = packet["scale"]
        graph = packet["formal_dependency_graph"]
        signal = packet["mathematical_signal_spine"]
        frontier = ",".join(row["id"] for row in packet["frontier"])
        problem_ids = ",".join(
            f"#{row['erdos_number']}" for row in packet["problem_map"]
        )
        rows = [
            (
                "corpus tour | signal_source=Palomar "
                "| mathematical_rank_before_scale_and_inventory"
            ),
        ]
        rows.extend(
            f"tour_signal #{row['rank']} | problem=#{row['problem']} "
            f"| tier={row['reader_tier']} | family={row['family_id']} "
            f"| declaration={row['declaration']} "
            f"| boundary={row['exact_boundary']}"
            for row in signal["ranked_frontier"]
        )
        rows.extend(
            f"tour_friction | problem=#{row['problem']} "
            f"| family={row['family_id']} | boundary={row['boundary']}"
            for row in signal["natural_friction"]["results"]
        )
        rows.extend(
            [
                (
                    "tour_long_tail | subordinate_not_deleted "
                    f"| declarations={signal['long_tail']['declaration_count']}"
                ),
                (
                    f"scale | modules={scale['module_count']} "
                f"| theorem_like={scale['theorem_like_count']} "
                f"| curated_claims={scale['curated_claim_count']} "
                f"| programmes={scale['mathematical_programme_count']} "
                f"| contribution_families={scale['contribution_family_count']} "
                f"| reviewed_open_propositions="
                    f"{scale['reviewed_remaining_open_proposition_count']} "
                    "| counts=descriptive_not_ranked"
                ),
                (
                    f"problem map | indexed={scale['indexed_problem_count']} "
                f"| open={scale['indexed_open_problem_count']} "
                f"| ids={problem_ids} "
                "| route=python3 scripts/query_semantic.py problem-registry"
                ),
            ]
        )
        for problem in packet.get("problem_map", []):
            route_memory = problem.get("route_memory")
            if not isinstance(route_memory, str) or not route_memory:
                continue
            rows.append(
                f"problem_route | #{problem['erdos_number']} | resume={route_memory}"
            )
        rows.extend(
            (
                (
                    f"formal graph | roots={','.join(graph['loaded_library_roots'])} "
                    f"| nodes={graph['source_resolved_node_count']} "
                    f"| direct_edges={graph['source_resolved_direct_edge_count']} "
                    f"| unresolved_atlas={graph['unresolved_atlas_declaration_count']} "
                    f"| unresolved_edges={graph['unresolved_public_edge_count']}"
                ),
                (
                    "authority | navigation=committed projections/no build "
                    "| proof=pinned Lean kernel | public meaning=maintainer review"
                ),
                (
                    "open frontier | scope=all-eight "
                    f"| propositions={scale['reviewed_remaining_open_proposition_count']} "
                    f"| ids={frontier}"
                ),
                (
                    "next | command=python3 scripts/query_corpus.py --route "
                    "agent_native_corpus_navigation | requires_lean_build=false"
                ),
            )
        )
        return "\n".join(rows)
    scale = packet["scale"]
    return (
        f"corpus {packet['release']['tag']} | modules={scale['module_count']} "
        f"| theorem_like={scale['theorem_like_count']} "
        f"| curated_claims={packet['curated_claim_count']} "
        f"| programmes={len(packet['mathematical_programmes'])} "
        f"| contribution_families={packet['publication_family_count']} "
        f"| claim_links={scale['principal_claim_link_count']} "
        f"| open={len(packet['remaining_open_propositions'])}"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--claim", metavar="ID")
    group.add_argument("--paper-label", metavar="LABEL")
    group.add_argument("--paper-source", metavar="SOURCE_PATH")
    group.add_argument("--paper-anchor", metavar="LABEL_OR_SOURCE_REF")
    group.add_argument("--open", metavar="ID")
    group.add_argument("--declaration", metavar="NAME")
    group.add_argument("--goal-support", metavar="LEAN_OR_MATHEMATICAL_GOAL")
    group.add_argument("--proof-plan", metavar="LEAN_OR_MATHEMATICAL_GOAL")
    group.add_argument("--proof-cone", metavar="DECLARATION")
    group.add_argument(
        "--dependency-path",
        nargs=2,
        metavar=("SOURCE_DECLARATION", "TARGET_DECLARATION"),
    )
    group.add_argument("--source", metavar="MODULE_DOT_LEAN:LINE")
    group.add_argument("--artifact", metavar="PATH_OR_SHA256")
    group.add_argument("--publication-artifact", metavar="ID")
    group.add_argument(
        "--publication-evidence",
        nargs="?",
        const="summary",
        metavar="MUTATION_ID",
    )
    group.add_argument("--module", metavar="PATH_OR_ID")
    group.add_argument("--connections", metavar="MODULE_OR_DECLARATION")
    group.add_argument("--route", metavar="ID")
    group.add_argument("--status", metavar="CLAIM_STATUS")
    group.add_argument("--publication-family", metavar="ID")
    group.add_argument("--publication-architecture", action="store_true")
    group.add_argument("--overview", action="store_true")
    group.add_argument("--papers", action="store_true")
    group.add_argument("--tour", action="store_true")
    group.add_argument("--vocabulary", action="store_true")
    group.add_argument("--search", metavar="TEXT")
    group.add_argument("--ask", metavar="QUESTION")
    parser.add_argument("--limit", type=int, default=DEFAULT_LIMIT)
    parser.add_argument(
        "--depth",
        type=int,
        default=4,
        help=(
            "maximum dependency depth for --proof-plan/--proof-cone/"
            "--dependency-path"
        ),
    )
    parser.add_argument("--query", default="", help="rank a connection card toward one task")
    parser.add_argument(
        "--format",
        choices=("json", "card"),
        default=None,
        help=(
            "output encoding; bare --ask defaults to a bounded card except for "
            "overview and paper-reading questions, whose complete packets default "
            "to JSON; all explicit routes also default to JSON"
        ),
    )
    args = parser.parse_args()
    if args.format:
        output_format = args.format
    elif args.ask and not (
        is_repository_overview_query(args.ask)
        or is_paper_reading_query(args.ask)
    ):
        output_format = "card"
    else:
        output_format = "json"
    if not 1 <= args.limit <= MAX_LIMIT:
        parser.error(f"--limit must be between 1 and {MAX_LIMIT}")
    if not 1 <= args.depth <= 8:
        parser.error("--depth must be between 1 and 8")
    try:
        if args.claim:
            packet = claim_packet(args.claim)
        elif args.paper_label:
            packet = paper_label_packet(args.paper_label)
        elif args.paper_source:
            packet = paper_source_packet(args.paper_source)
        elif args.paper_anchor:
            packet = paper_anchor_packet(args.paper_anchor)
        elif args.open:
            packet = open_proposition_packet(args.open)
        elif args.declaration:
            packet = declaration_packet(args.declaration, args.limit)
        elif args.goal_support:
            packet = formal_goal_support_packet(
                args.goal_support,
                args.limit,
                explicit_goal=True,
            )
        elif args.proof_plan:
            packet = formal_proof_plan_packet(
                args.proof_plan,
                args.limit,
                args.depth,
                explicit_goal=True,
            )
        elif args.proof_cone:
            packet = formal_dependency_proof_cone(
                args.proof_cone, args.depth, args.limit
            )
        elif args.dependency_path:
            packet = formal_dependency_path(
                args.dependency_path[0],
                args.dependency_path[1],
                args.depth,
            )
        elif args.source:
            packet = source_coordinate_packet(args.source, args.limit)
        elif args.artifact:
            packet = artifact_packet(args.artifact)
        elif args.publication_artifact:
            packet = publication_artifact_packet(args.publication_artifact)
        elif args.publication_evidence:
            packet = publication_evidence_packet(args.publication_evidence)
        elif args.module:
            packet = module_packet(args.module, args.limit)
        elif args.connections:
            packet = connection_card(args.connections, args.limit, args.query)
        elif args.route:
            packet = route_packet(args.route)
        elif args.status:
            packet = claim_status_packet(args.status, args.limit)
        elif args.publication_family:
            packet = publication_family_packet(args.publication_family)
        elif args.publication_architecture:
            packet = publication_architecture_packet()
        elif args.overview:
            packet = repository_overview_packet()
        elif args.papers:
            packet = paper_reading_guide_packet()
        elif args.tour:
            packet = agent_tour_packet()
        elif args.vocabulary:
            packet = semantic_dictionary_packet()
        elif args.search:
            packet = search_packet(args.search, args.limit)
        elif args.ask:
            packet = semantic_slice_packet(args.ask, args.limit)
        else:
            packet = summary_packet()
    except (KeyError, ValueError, json.JSONDecodeError, OSError) as exc:
        print(f"query_corpus: {exc}", file=sys.stderr)
        return 2
    if output_format == "card":
        print(render_card(packet))
    else:
        encoded = json.dumps(packet, ensure_ascii=False, indent=2) + "\n"
        if len(encoded.encode("utf-8")) > OUTPUT_BUDGET_BYTES:
            print(
                f"query_corpus: response exceeds {OUTPUT_BUDGET_BYTES} bytes; lower --limit or use --format card",
                file=sys.stderr,
            )
            return 2
        print(encoded, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
