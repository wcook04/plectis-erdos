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
OUTPUT_BUDGET_BYTES = 64_000
SOURCE_LINE_WINDOW = 3
CONNECTION_CARD_SCHEMA = "lean-connection-card/2"


@lru_cache(maxsize=None)
def load(rel: str) -> dict[str, Any]:
    return json.loads((ROOT / rel).read_text(encoding="utf-8"))


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
            inventory.append(
                {
                    **common,
                    "artifact_kind": "json_fragment" if "::" in path else "registered_file",
                    "artifact_handle": path,
                    "file_path": file_path,
                    "fragment": path.split("::", 1)[1] if "::" in path else None,
                    "content_digest": row["content_digest"],
                    "size_bytes": (ROOT / file_path).stat().st_size,
                }
            )
        for variant in ("source", "rendered"):
            path = row.get(f"{variant}_path")
            digest = row.get(f"{variant}_content_digest")
            if path and digest:
                inventory.append(
                    {
                        **common,
                        "artifact_kind": f"authored_paper_{variant}",
                        "artifact_handle": path,
                        "file_path": path,
                        "fragment": None,
                        "content_digest": digest,
                        "size_bytes": (ROOT / path).stat().st_size,
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
        raise ValueError(f"unknown paper label: {label}")
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
    return {
        "kind": "claim",
        "authority_posture": "navigation_projection_not_proof_authority",
        "lean_source_identity": lean_source_identity_for_paper(
            claims, claim.get("paper_label") and label_index[claim["paper_label"]]["source"]
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
        "paper": paper_coordinate(claim.get("paper_label"), label_index),
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
        raise ValueError(f"unknown paper label: {label}")
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
    module_view = {**module, "role": roles.get(module["id"], "Unclassified module")}
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


def search_terms(value: str) -> set[str]:
    """Return stable lexical terms for bounded natural-language fallback."""
    terms: set[str] = set()
    folded = "".join(
        character
        for character in unicodedata.normalize("NFKD", value.casefold())
        if not unicodedata.combining(character)
    )
    for token in re.findall(r"[a-z0-9]+", folded):
        if token in SEARCH_STOP_WORDS:
            continue
        if token.endswith("ing") and len(token) > 6:
            token = token[:-3]
        elif token.endswith("s") and len(token) > 4 and not token.endswith("ss"):
            token = token[:-1]
        terms.add(SEARCH_TERM_ALIASES.get(token, token))
    return terms


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
    query_terms = search_terms(query)
    if not query_terms:
        return None
    key_terms = search_terms(primary)
    body_terms = search_terms(haystack)
    if query_terms <= key_terms:
        return 4
    if query_terms <= body_terms:
        return 5
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
        ranks = [search_rank(query, row["id"], row["path"])]
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

    ranked.sort(key=search_result_sort_key)
    results = [item[2] for item in ranked]
    return {
        "kind": "search",
        "authority_posture": "navigation_projection_not_proof_authority",
        "query": query,
        "match_count": len(results),
        "results": results[:limit],
        "omitted_match_count": max(0, len(results) - limit),
        "limit": limit,
        "next": "Use the typed handle with --claim, --status, --paper-anchor, --open, --declaration, --source, --module, --connections, --artifact, --publication-artifact, --publication-evidence, --route, or --publication-family.",
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
        "checks",
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
        return (
            f"paper {paper['label']} | {paper['source_ref']} | rendered={paper['rendered']} "
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
            f"search {packet['query']!r} | matches={packet['match_count']} | emitted={len(packet['results'])}"
        ]
        for result in packet["results"]:
            handle = result.get("id") or result.get("name")
            rows.append(f"{result['kind']} | {handle}")
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
    group.add_argument("--search", metavar="TEXT")
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
        elif args.search:
            packet = search_packet(args.search, args.limit)
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
