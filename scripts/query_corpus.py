#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Query the public mathematical corpus without loading its exhaustive files.

This is a read-only navigation projection. It does not elaborate Lean and does
not acquire proof authority. Run from any directory; output is JSON by default.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import unicodedata
from functools import lru_cache
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_LIMIT = 20
MAX_LIMIT = 100
MAX_SEMANTIC_CELLS = 4
OUTPUT_BUDGET_BYTES = 64_000
SOURCE_LINE_WINDOW = 3
CONNECTION_CARD_SCHEMA = "lean-connection-card/2"
SEMANTIC_DICTIONARY_SCHEMA = "erdos249257-semantic-dictionary/1"
SEMANTIC_SLICE_SCHEMA = "erdos249257-semantic-slice/1"

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
            "premise",
            "support",
            "approach",
            "proof socket",
            "socket",
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
)


@lru_cache(maxsize=None)
def load(rel: str) -> dict[str, Any]:
    return json.loads((ROOT / rel).read_text(encoding="utf-8"))


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
    if packet.get("source_fingerprint") != atlas.get("source_fingerprint"):
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


def publication_contract() -> dict[str, Any]:
    return load("docs/publication_contract.json")


def publication_evidence() -> dict[str, Any]:
    return load("docs/publication_evidence.json")


def current_corpus_census() -> dict[str, Any]:
    claims = load("docs/claims.json")
    atlas_summary = load("docs/declaration_atlas.json")["summary"]
    assembly = claims["machine_readable_paper"]["publication_assembly"]
    return {
        "snapshot_kind": "current_worktree_navigation_state",
        "claims_source": "docs/claims.json",
        "declaration_atlas_source": "docs/declaration_atlas.json",
        "module_count": atlas_summary["module_count"],
        "declaration_count": atlas_summary["declaration_count"],
        "theorem_like_count": atlas_summary["theorem_like_count"],
        "generated_certificate_declaration_count": atlas_summary[
            "generated_certificate_declaration_count"
        ],
        "curated_claim_count": len(claims["claims"]),
        "contribution_family_count": len(assembly["contribution_families"]),
        "status_count": len(claims["status_taxonomy"]),
        "remaining_open_proposition_count": len(
            claims["remaining_open_propositions"]
        ),
    }


def all_entrypoints(claims: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        *claims["machine_readable_paper"]["entrypoints"],
        *publication_contract().get("entrypoints", []),
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
    paper = claims["machine_readable_paper"]["paper"]
    paper_rows = [paper, *paper.get("companion_sources", [])]
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
        environments = set(re.findall(r"\\newtheorem\*?\{([^}]+)\}", text))
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

        starts.sort(key=lambda row: row["offset"])
        for index, start in enumerate(starts):
            region_end = starts[index + 1]["offset"] if index + 1 < len(starts) else len(text)
            region = text[start["offset"]:region_end]
            line = text.count("\n", 0, start["offset"]) + 1
            label = start["label"]
            source_ref = f"{relative}:{line}"
            attached_claims = sorted(claims_by_label.get(label, []), key=lambda row: row["id"])
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
            for link in re.finditer(
                r"\\(?P<macro>lref|lrefx|lword|lloc)"
                r"\{(?P<file>[^}]+)\}\{(?P<line>\d+)\}"
                r"(?:\{(?P<name>[^}]*)\})?"
                r"(?:\{(?P<label>[^}]*)\})?",
                region,
            ):
                module = f"Erdos249257/{link.group('file')}"
                source_links.append(
                    {
                        "edge_kind": "authored_source_link",
                        "macro": link.group("macro"),
                        "module": module,
                        "line": int(link.group("line")),
                        "source_ref": f"{module}:{link.group('line')}",
                        "source_identity": dict(lean_source_identity),
                        "declaration": link.group("name") or None,
                        "display_label": link.group("label") or None,
                    }
                )

            inventory.append(
                {
                    "canonical_handle": label or source_ref,
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


@lru_cache(maxsize=1)
def paper_label_index() -> dict[str, dict[str, Any]]:
    index: dict[str, dict[str, Any]] = {}
    for anchor in paper_anchor_inventory():
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
    return {
        "kind": "claim",
        "authority_posture": "navigation_projection_not_proof_authority",
        "lean_source_identity": lean_source_identity_for_paper(
            claims, claim_paper and claim_paper.get("source")
        ),
        "claim": claim,
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
        "programme_contexts": [
            {
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
            for route in programme_routes
        ],
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
    return {
        "kind": "open_proposition",
        "authority_posture": "authored_open_boundary_navigation_not_proof_authority",
        "open_proposition": proposition,
        "status": "open",
        "open_target": compact_claim(claim_index[proposition["open_target_claim"]]),
        "linked_claims": linked_claims,
        "advancing_claims": advancing_claims,
        "paper_anchor": paper_anchor,
        "follow": "python3 scripts/query_corpus.py --claim <claim_id>",
        "source": "docs/claims.json::remaining_open_propositions",
        "validation": "python3 scripts/check_release.py",
    }


def declaration_packet(name: str, limit: int) -> dict[str, Any]:
    atlas = load("docs/declaration_atlas.json")
    claims = load("docs/claims.json")
    aliases = load("paper/module-aliases.json")["aliases"]
    matches = [row for row in atlas["declarations"] if row["name"] == name]
    if not matches:
        raise KeyError(f"unknown declaration name: {name}")
    claim_index = {row["id"]: row for row in claims["claims"]}
    roles = module_roles(claims)
    label_index = paper_label_index()
    sigil_by_path = {row["path"]: row["sigil"] for row in aliases}
    lean_source_identity = formal_source_identity(claims)
    repository = lean_source_identity["repository"].rstrip("/")
    source_ref = lean_source_identity["ref"]
    paper_anchors = paper_anchor_inventory()
    declarations_by_module: dict[str, list[dict[str, Any]]] = {}
    for row in atlas["declarations"]:
        declarations_by_module.setdefault(row["module"], []).append(row)
    for rows in declarations_by_module.values():
        rows.sort(key=lambda row: (row["line"], row["name"]))
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
    return {
        "kind": "declaration",
        "authority_posture": "atlas_navigation_projection_not_proof_authority",
        "matches": decorated,
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

    module_declarations = sorted(
        (row for row in atlas["declarations"] if row["module"] == module_path),
        key=lambda row: (row["line"], row["name"]),
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
    decorated = []
    for row in candidates[:limit]:
        declaration = declaration_packet(row["name"], MAX_LIMIT)
        decorated.append(
            next(
                candidate
                for candidate in declaration["matches"]
                if candidate["module"] == module_path and candidate["line"] == row["line"]
            )
        )

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


def compact_declaration(row: dict[str, Any]) -> dict[str, Any]:
    return {
        "name": row["name"],
        "declaration_kind": row["kind"],
        "module": row["module"],
        "line": row["line"],
        "source_ref": f"{row['module']}:{row['line']}",
        "claim_ids": row.get("claim_ids", []),
        "generated_certificate": bool(row.get("generated_certificate")),
    }


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
        row for row in atlas["declarations"] if row["name"] == resolved_handle
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
    for row in atlas["declarations"]:
        declarations_by_path.setdefault(row["module"], []).append(row)
    for rows in declarations_by_path.values():
        rows.sort(key=lambda row: (row["line"], row["name"]))

    source_path = ROOT / module["path"]
    source_text = source_path.read_text(encoding="utf-8")
    source_counts = identifier_counts(source_text)
    anchor_names = {row["name"] for row in declaration_matches}
    module_declarations = declarations_by_path.get(module["path"], [])
    ranked_declarations = sorted(
        module_declarations,
        key=lambda row: (
            0 if row["name"] in anchor_names else 1,
            search_rank(query, row["name"], str(row.get("signature") or ""))
            if query and search_rank(query, row["name"], str(row.get("signature") or "")) is not None
            else 9,
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
            {**compact_declaration(row), "statement_head": row.get("signature")}
            for row in ranked_declarations[: min(limit, 12)]
        ],
        "declaration_count": len(module_declarations),
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
    atlas = load("docs/declaration_atlas.json")
    claims = load("docs/claims.json")
    aliases = load("paper/module-aliases.json")["aliases"]
    alias = next((row for row in aliases if row["sigil"].casefold() == handle.casefold()), None)
    if alias is not None:
        handle = alias["path"]
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
        row for row in atlas["declarations"] if row["module"] == module["path"]
    ]
    attached_claim_ids = sorted(
        {
            claim_id
            for row in declarations
            for claim_id in row.get("claim_ids", [])
        }
    )
    claim_rows = [compact_claim(row) for row in claims["claims"] if row["id"] in attached_claim_ids]
    return {
        "kind": "module",
        "authority_posture": "atlas_navigation_projection_not_proof_authority",
        "lean_source_identity": formal_source_identity(claims),
        "module": module_view,
        "paper_sigil": next(
            (row["sigil"] for row in aliases if row["path"] == module["path"]), None
        ),
        "attached_claims": claim_rows,
        "declaration_preview": [compact_declaration(row) for row in declarations[:limit]],
        "declaration_preview_receipt": {
            "total": len(declarations),
            "emitted": min(len(declarations), limit),
            "omitted": max(0, len(declarations) - limit),
            "expand": f"python3 scripts/query_corpus.py --search {module['path']} --limit {MAX_LIMIT}",
            "exhaustive": "docs/declaration_atlas.json",
        },
        "dependency_neighbourhood": {
            "imports": [compact_module(row, roles) for row in imported_rows[:limit]],
            "importers": [compact_module(row, roles) for row in importer_rows[:limit]],
            "receipt": {
                "imports_total": len(imported_rows),
                "imports_emitted": min(len(imported_rows), limit),
                "imports_omitted": max(0, len(imported_rows) - limit),
                "importers_total": len(importer_rows),
                "importers_emitted": min(len(importer_rows), limit),
                "importers_omitted": max(0, len(importer_rows) - limit),
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
    "fail": "obstruction",
    "failed": "obstruction",
    "failure": "obstruction",
    "member": "mem",
    "membership": "mem",
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
        "get",
        "give",
        "i",
        "let",
        "lets",
        "me",
        "route",
        "should",
        "show",
        "still",
        "tell",
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
    if (
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
            "premise",
            "need to prove",
            "support",
            "approach",
            "proof socket",
            "socket",
        )
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
        "authority_posture": (
            "authored_navigation_translation_not_proof_or_claim_status_authority"
        ),
    }


def semantic_dictionary_packet() -> dict[str, Any]:
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
        "consumer_action": (
            "Load this bounded packet before free-text search, then follow one "
            "typed route hint or inspect the transparent query interpretation "
            "returned by --search."
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


def status_question_target(query: str) -> tuple[str, str] | None:
    """Return the open-target claim and problem number for a status question."""
    terms = search_terms(query)
    if "resolution_status" not in terms:
        return None
    if "249" in terms:
        return ("erdos_249", "249")
    if "257" in terms:
        return ("universal_257", "257")
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
) -> tuple[int, int, str]:
    """Keep typed-handle lookup exact while preferring routes for semantic ties."""
    rank, stable_key, result = item
    if rank <= 2:
        return (rank, 0, stable_key)
    semantic_kind_priority = {
        "reading_route": 0,
        "publication_family": 1,
        "open_proposition": 2,
        "claim": 3,
        "paper_anchor": 4,
        "declaration": 5,
        "module": 6,
        "artifact": 7,
    }
    return (rank, semantic_kind_priority.get(result["kind"], 99), stable_key)


def search_packet(query: str, limit: int) -> dict[str, Any]:
    query = query.strip()
    if not query:
        raise ValueError("search query must not be empty")
    claims = load("docs/claims.json")
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
            rank = -1
        if rank is not None:
            ranked.append(
                (
                    rank,
                    f"open_proposition:{proposition['id']}",
                    {"kind": "open_proposition", **proposition},
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
        if rank is not None:
            ranked.append((rank, f"claim:{claim['id']}", {"kind": "claim", **compact_claim(claim)}))

    for row in atlas["declarations"]:
        rank = search_rank(
            query,
            row["name"],
            " ".join(str(value) for value in (row["signature"], row.get("docstring"), row["module"]) if value),
        )
        if rank is not None:
            result = {"kind": "declaration", **compact_declaration(row)}
            if row.get("signature"):
                result["signature_excerpt"] = str(row["signature"])[:240]
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
                        "authored_synopsis": synopsis,
                        "paper_sigil": sigil,
                        "role": roles.get(row["id"], "Unclassified module"),
                        "declaration_count": row["declaration_count"],
                        "import_count": len(row["imports"]),
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
        if rank is not None:
            ranked.append(
                (
                    rank,
                    f"route:{row['id']}",
                    {
                        "kind": "reading_route",
                        "id": row["id"],
                        "route_kind": row.get("route_kind", "reading_route"),
                        "title": row.get("title"),
                        "intent": row["intent"],
                        "problem_target_claim_ids": row.get(
                            "problem_target_claim_ids", []
                        ),
                    },
                )
            )

    hint_targets = semantic_hint_targets(query)
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
        "next": "Inspect --vocabulary when phrasing is uncertain, then use the typed handle with --claim, --status, --paper-anchor, --open, --declaration, --source, --module, --connections, --artifact, --publication-artifact, --publication-evidence, --route, or --publication-family.",
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


def claim_formal_witnesses(claim: dict[str, Any]) -> list[dict[str, Any]]:
    """Resolve authored claim handles to exact atlas signatures and source lines."""
    atlas = load("docs/declaration_atlas.json")
    declarations = {
        (row["name"], row["module"], row["line"]): row
        for row in atlas["declarations"]
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
    matches = [row for row in atlas["declarations"] if row["name"] == name]
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
            for row in atlas["declarations"]
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
    for row in atlas["declarations"]:
        candidate_name = row["name"]
        if (
            row["module"] not in visible_paths
            or candidate_name == name
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
    operator_id = semantic_query_operator(query)["id"]
    expansion_command: str
    witness_edges: list[dict[str, str]] = [
        {
            "from": "query",
            "relation": "retrieved_as",
            "to": f"{kind}:{handle}",
            "authority": "navigation",
        }
    ]

    if kind == "declaration":
        packet = declaration_packet(handle, 1)
        declaration = packet["matches"][0]
        content = {
            "formal_witness": {
                key: declaration.get(key)
                for key in (
                    "name",
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
            "module_role": declaration.get("module_role"),
        }
        if operator_id in ("support", "trace"):
            content["source_dependency_candidates"] = (
                declaration_source_dependency_candidates(handle)
            )
        expansion_command = (
            f"python3 scripts/query_corpus.py --declaration {handle}"
        )
        witness_edges.append(
            {
                "from": f"declaration:{handle}",
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
        "cell_id": f"{kind}:{handle}",
        "kind": kind,
        "handle": handle,
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
                source_dependency_candidates.extend(
                    cell["content"].get(
                        "source_dependency_candidates", []
                    )
                )
            elif cell["kind"] == "reading_route":
                programme = cell["content"].get("programme")
                if programme:
                    unproved_requirements.extend(
                        programme["remaining_open_propositions"]
                    )
        return {
            "kind": "support_synthesis",
            "checked_consumer_signatures": list(
                {
                    row["name"]: row
                    for row in formal_consumers
                    if row.get("name")
                }.values()
            ),
            "source_dependency_candidates": list(
                {
                    (row["name"], row["source_ref"]): row
                    for row in source_dependency_candidates
                }.values()
            ),
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
        open_records = []
        advances = []
        for cell in cells:
            if cell["kind"] == "open_proposition":
                open_records.append(cell["content"]["open_record"])
                advances.extend(cell["content"]["nearest_advances"])
            elif cell["kind"] == "reading_route":
                programme = cell["content"].get("programme")
                if programme:
                    open_records.extend(
                        programme["remaining_open_propositions"]
                    )
            elif cell["kind"] == "claim":
                open_records.extend(
                    cell["content"]["remaining_open_propositions"]
                )
        return {
            "kind": "frontier_synthesis",
            "exact_open_records": list(
                {
                    row["id"]: row for row in open_records if row.get("id")
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
        source_dependency_candidates = []
        for cell in cells:
            if cell["kind"] == "claim":
                neighbourhood = cell["content"]["argument_neighbourhood"]
                argument_edges.extend(neighbourhood["incoming"])
                argument_edges.extend(neighbourhood["outgoing"])
            elif cell["kind"] == "declaration":
                source_dependency_candidates.extend(
                    cell["content"].get(
                        "source_dependency_candidates", []
                    )
                )
        return {
            "kind": "trace_synthesis",
            "argument_edges": argument_edges,
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
    selected_with_reasons: list[tuple[dict[str, Any], str]]
    if len(support_alternatives) == 2:
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
            boundary_rows = [
                (
                    {"kind": "open_proposition", **open_index[open_id]},
                    "frontier_boundary_from_ranked_context",
                )
                for open_id in dict.fromkeys(boundary_ids)
                if open_id in open_index
            ]
            if boundary_rows:
                selected_with_reasons = [
                    *selected_with_reasons[:2],
                    *boundary_rows,
                    *selected_with_reasons[2:],
                ][: min(limit, MAX_SEMANTIC_CELLS)]
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
        (result["kind"], semantic_result_handle(result)) for result in selected
    }
    cells = [
        semantic_cell(query, result, reason)
        for result, reason in selected_with_reasons
    ]
    near_misses = [
        {
            "kind": result["kind"],
            "handle": semantic_result_handle(result),
            "reason": "lower_ranked_outside_bounded_witness_slice",
        }
        for result in search["results"]
        if (result["kind"], semantic_result_handle(result)) not in selected_keys
    ][:5]
    witness_edges = [
        edge for cell in cells for edge in cell["witness_edges"]
    ]
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
        "operator_synthesis": operator_synthesis(operator_id, cells),
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
    return {
        "kind": "claim_status",
        "authority_posture": "claim_registry_status_navigation_not_proof_authority",
        "status": canonical_status,
        "meaning": taxonomy[canonical_status],
        "claim_count": len(matching_claims),
        "claims": [
            compact_status_claim(claim) for claim in matching_claims[:limit]
        ],
        "omitted_claim_count": max(0, len(matching_claims) - limit),
        "limit": limit,
        "remaining_open_propositions": remaining_open,
        "proof_authority": "Lean source checked by the pinned Lean kernel",
        "expansion": {
            "claim": "python3 scripts/query_corpus.py --claim <claim_id>",
            "open_proposition": (
                "python3 scripts/query_corpus.py --open <remaining_open.id>"
            ),
        },
        "validation": "python3 scripts/check_release.py",
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
        raise KeyError(f"unknown route id: {route_id}")
    claim_index = {row["id"]: row for row in claims["claims"]}
    open_index = {
        row["id"]: row for row in claims["remaining_open_propositions"]
    }
    route_index = {
        row["id"]: row for row in all_entrypoints(claims)
    }
    packet = {
        "kind": "reading_route",
        "authority_posture": "authored_navigation_route_not_proof_authority",
        "route": route,
        "proof_authority": "Lean source checked by the pinned Lean kernel",
        "release_provenance": claims["release"]["public_projection"],
        "validation": "python3 scripts/check_release.py",
    }
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
    return {
        "kind": "publication_family",
        "authority_posture": "publication_assembly_navigation_not_proof_authority",
        "family": family,
        "claims": [compact_claim(claim) for claim in family_claims],
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
    return {
        "kind": "publication_architecture",
        "authority_posture": "authored_editorial_topology_not_proof_authority",
        "architecture": assembly["publication_architecture"],
        "family_index": [
            {
                "id": row["id"],
                "status_summary": row["status_summary"],
                "primary_narrative_owner": row["primary_narrative_owner"],
                "view_decision": row["view_decision"],
                "claim_count": len(row["claim_ids"]),
            }
            for row in assembly["contribution_families"]
        ],
        "coverage_rule": assembly["coverage_rule"],
        "validation": "python3 scripts/check_release.py",
    }


def summary_packet() -> dict[str, Any]:
    orientation = load("docs/orientation.json")
    claims = load("docs/claims.json")
    assembly = claims["machine_readable_paper"]["publication_assembly"]
    bounded_omissions = (
        "editorial_architecture",
        "editorial_state",
        "external_registration",
        "source_revision",
    )
    return {
        "kind": "corpus_summary",
        **{
            key: value
            for key, value in orientation.items()
            if key not in bounded_omissions
        },
        "curated_claim_count": len(claims["claims"]),
        "publication_family_count": len(assembly["contribution_families"]),
        "bounded_summary_omission_receipt": {
            "omitted_sections": list(bounded_omissions),
            "drilldown": "docs/orientation.json",
            "reason": "non_mathematical_owner_metadata_kept_out_of_bounded_agent_summary",
        },
    }


def render_card(packet: dict[str, Any]) -> str:
    kind = packet["kind"]
    if kind == "claim":
        claim = packet["claim"]
        decls = ", ".join(row["name"] for row in claim["declarations"]) or "none"
        neighbourhood = packet["argument_neighbourhood"]
        return (
            f"claim {claim['id']} | {claim['status']} | paper={claim.get('paper_label')} "
            f"| incoming={len(neighbourhood['incoming'])} | outgoing={len(neighbourhood['outgoing'])} "
            f"| declarations={decls}"
        )
    if kind == "paper_label":
        paper = packet["paper"]
        claim_ids = ",".join(row["id"] for row in packet["attached_claims"]) or "none"
        source = paper.get("source_ref") or paper.get(
            "availability", "unavailable"
        )
        return (
            f"paper {paper['label']} | {source} | rendered={paper.get('rendered')} "
            f"| claims={claim_ids}"
        )
    if kind == "paper_anchor":
        paper = packet["paper"]
        return (
            f"paper anchor {packet['canonical_handle']} | {packet['anchor_class']} "
            f"| {paper['source_ref']} | title={packet.get('title') or 'none'}"
        )
    if kind == "declaration":
        return "\n".join(
            f"declaration {row['name']} | {row['kind']} | {row['module']}:{row['line']} | claims={','.join(row['claim_ids']) or 'none'}"
            for row in packet["matches"]
        )
    if kind == "source_coordinate":
        source = packet["source"]
        return (
            f"source {source['source_ref']} | module={source['module_id']} "
            f"| nearby_declarations={len(packet['nearby_declarations'])}"
        )
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
        return (
            f"open {proposition['id']} | target={packet['open_target']['id']} "
            f"| linked_claims={len(packet['linked_claims'])} "
            f"| advancing_claims={len(packet['advancing_claims'])}"
        )
    if kind == "module":
        module = packet["module"]
        dependency = packet["dependency_neighbourhood"]["receipt"]
        return (
            f"module {module['id']} | {module['path']} | declarations={module['declaration_count']} "
            f"| imports={dependency['imports_total']} | importers={dependency['importers_total']} "
            f"| claims={len(packet['attached_claims'])} | paper_sigil={packet.get('paper_sigil') or 'none'} "
            f"| role={module['role']}"
        )
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
            rows.append(f"{result['kind']} | {handle}")
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
        rows.extend(
            f"{cell['kind']} | {cell['handle']} | {cell['selection_reason']}"
            for cell in packet["semantic_cells"]
        )
        rows.append(
            f"witness_edges={len(packet['minimal_witness_subgraph']['edges'])} "
            f"| omitted={packet['omission_receipt'].get('omitted_match_count', 0)}"
        )
        return "\n".join(rows)
    if kind == "claim_status":
        return (
            f"status {packet['status']} | claims={packet['claim_count']} "
            f"| emitted={len(packet['claims'])} "
            f"| remaining_open_propositions={len(packet['remaining_open_propositions'])}"
        )
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
            return (
                f"programme {route['id']} | {programme['title']} "
                f"| claims={claims} | open={open_ids}"
            )
        return (
            f"route {route['id']} | {route['intent']} | read={' -> '.join(route['read'])} "
            f"| next={route['query_steps'][0]}"
        )
    if kind == "publication_family":
        family = packet["family"]
        return (
            f"publication family {family['id']} | claims={len(packet['claims'])} "
            f"| owner={family['primary_narrative_owner']} "
            f"| view={family['view_decision']} "
            f"| obligation={family['consumer_or_open_obligation']}"
        )
    if kind == "publication_architecture":
        architecture = packet["architecture"]
        return (
            f"publication architecture | gateway="
            f"{architecture['canonical_gateway']['source']} "
            f"| retained_companions={len(architecture['retained_companions'])} "
            f"| families={len(packet['family_index'])}"
        )
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
    group.add_argument("--paper-anchor", metavar="LABEL_OR_SOURCE_REF")
    group.add_argument("--open", metavar="ID")
    group.add_argument("--declaration", metavar="NAME")
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
    group.add_argument("--vocabulary", action="store_true")
    group.add_argument("--search", metavar="TEXT")
    group.add_argument("--ask", metavar="QUESTION")
    parser.add_argument("--limit", type=int, default=DEFAULT_LIMIT)
    parser.add_argument("--query", default="", help="rank a connection card toward one task")
    parser.add_argument("--format", choices=("json", "card"), default="json")
    args = parser.parse_args()
    if not 1 <= args.limit <= MAX_LIMIT:
        parser.error(f"--limit must be between 1 and {MAX_LIMIT}")
    try:
        if args.claim:
            packet = claim_packet(args.claim)
        elif args.paper_label:
            packet = paper_label_packet(args.paper_label)
        elif args.paper_anchor:
            packet = paper_anchor_packet(args.paper_anchor)
        elif args.open:
            packet = open_proposition_packet(args.open)
        elif args.declaration:
            packet = declaration_packet(args.declaration, args.limit)
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
    if args.format == "card":
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
