#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Audit whole-corpus coverage of the semantic query and witness surfaces."""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path
from typing import Any, Callable

import build_declaration_atlas
import query_corpus


AUDIT_SCHEMA = "erdos249257-semantic-corpus-audit/1"


def packet_size(packet: dict[str, Any]) -> int:
    return len(
        json.dumps(
            packet, ensure_ascii=False, sort_keys=True, separators=(",", ":")
        ).encode("utf-8")
    )


def audit_packet() -> dict[str, Any]:
    claims_document = query_corpus.load("docs/claims.json")
    atlas = query_corpus.load("docs/declaration_atlas.json")
    claims = claims_document["claims"]
    opens = claims_document["remaining_open_propositions"]
    routes = query_corpus.all_entrypoints(claims_document)
    programmes = [
        row for row in routes if row.get("route_kind") == "mathematical_programme"
    ]
    raw_declarations = atlas["declarations"]
    declarations = query_corpus.atlas_declarations(atlas)
    errors: list[dict[str, str]] = []

    def error(check: str, handle: str, detail: str) -> None:
        errors.append({"check": check, "handle": handle, "detail": detail})

    claim_index = {row["id"]: row for row in claims}
    open_index = {row["id"]: row for row in opens}
    route_index = {row["id"]: row for row in routes}
    declaration_coordinates = {
        (row["name"], row["module"], row["line"]) for row in declarations
    }

    for label, rows, index in (
        ("claim", claims, claim_index),
        ("open", opens, open_index),
        ("route", routes, route_index),
    ):
        if len(index) != len(rows):
            error("unique_handle", label, f"{len(rows) - len(index)} duplicates")

    graph = claims_document["machine_readable_paper"]["argument_graph"]
    for edge in graph["edges"]:
        for endpoint in ("from", "to"):
            if edge[endpoint] not in claim_index:
                error(
                    "argument_graph_endpoint",
                    str(edge[endpoint]),
                    f"missing {endpoint} claim",
                )

    for proposition in opens:
        if proposition["open_target_claim"] not in claim_index:
            error(
                "open_target",
                proposition["id"],
                f"missing claim {proposition['open_target_claim']}",
            )

    for claim in claims:
        for open_id in claim.get("remaining_open_proposition_ids", []):
            if open_id not in open_index:
                error("claim_open_link", claim["id"], f"missing {open_id}")
        for declaration in claim.get("declarations", []):
            coordinate = (
                declaration["name"],
                declaration["module"],
                declaration["line"],
            )
            if coordinate not in declaration_coordinates:
                error(
                    "claim_declaration_coordinate",
                    claim["id"],
                    ":".join(map(str, coordinate)),
                )

    for route in routes:
        for claim_id in (
            *route.get("core_claim_ids", []),
            *route.get("problem_target_claim_ids", []),
        ):
            if claim_id not in claim_index:
                error("route_claim_link", route["id"], f"missing {claim_id}")
        for open_id in route.get("remaining_open_proposition_ids", []):
            if open_id not in open_index:
                error("route_open_link", route["id"], f"missing {open_id}")
        for related_id in route.get("related_route_ids", []):
            if related_id not in route_index:
                error("related_route_link", route["id"], f"missing {related_id}")

    module_lines: dict[str, int] = {}
    module_code_lines: dict[str, list[str]] = {}
    source_missing_count = 0
    coordinate_error_count = 0
    for declaration in raw_declarations:
        module = declaration["module"]
        if module not in module_lines:
            source = query_corpus.ROOT / module
            if not source.is_file():
                module_lines[module] = -1
                module_code_lines[module] = []
                source_missing_count += 1
                error("declaration_source", module, "source file missing")
            else:
                source_text = source.read_text(encoding="utf-8")
                module_lines[module] = len(source_text.splitlines())
                module_code_lines[module] = query_corpus.lean_code_projection(
                    source_text
                ).splitlines()
        if not 1 <= declaration["line"] <= module_lines[module]:
            coordinate_error_count += 1
            error(
                "declaration_source_coordinate",
                declaration["name"],
                f"{module}:{declaration['line']} outside 1..{module_lines[module]}",
            )

    actual_comment_false_positive_ids = set()
    for declaration in raw_declarations:
        module = declaration["module"]
        line_number = declaration["line"]
        code_lines = module_code_lines.get(module, [])
        if not 1 <= line_number <= len(code_lines):
            continue
        match = build_declaration_atlas.DECL_RE.match(
            code_lines[line_number - 1]
        )
        if match is None or match.group(2) != declaration["name"]:
            actual_comment_false_positive_ids.add(declaration["id"])
    configured_suppression_ids = query_corpus.SUPPRESSED_DECLARATION_ATLAS_ROWS
    if actual_comment_false_positive_ids != configured_suppression_ids:
        error(
            "declaration_projection_suppression_contract",
            "docs/declaration_atlas.json",
            "missing="
            f"{sorted(actual_comment_false_positive_ids - configured_suppression_ids)} "
            "stale="
            f"{sorted(configured_suppression_ids - actual_comment_false_positive_ids)}",
        )

    packet_specs: tuple[
        tuple[str, list[dict[str, Any]], Callable[[dict[str, Any]], dict[str, Any]]],
        ...,
    ] = (
        ("claim", claims, lambda row: query_corpus.claim_packet(row["id"])),
        (
            "open",
            opens,
            lambda row: query_corpus.open_proposition_packet(row["id"]),
        ),
        ("route", routes, lambda row: query_corpus.route_packet(row["id"])),
    )
    expanded_packet_count = 0
    maximum_packet: tuple[int, str] = (0, "")
    for kind, rows, expand in packet_specs:
        for row in rows:
            handle = row["id"]
            try:
                size = packet_size(expand(row))
            except Exception as exc:  # audit must retain the failing handle
                error("typed_packet_expansion", f"{kind}:{handle}", repr(exc))
                continue
            expanded_packet_count += 1
            maximum_packet = max(maximum_packet, (size, f"{kind}:{handle}"))
            if size > query_corpus.OUTPUT_BUDGET_BYTES:
                error(
                    "typed_packet_budget",
                    f"{kind}:{handle}",
                    f"{size} bytes",
                )

    hint_targets = {
        "--claim": set(claim_index),
        "--open": set(open_index),
        "--route": set(route_index),
        "--declaration": {row["name"] for row in declarations},
    }
    checked_hint_count = 0
    for vocabulary in query_corpus.SEMANTIC_VOCABULARY:
        for hint in vocabulary["route_hints"]:
            flag, _, handle = hint.partition(" ")
            if "<" in handle:
                continue
            checked_hint_count += 1
            if flag == "--search" and handle:
                continue
            if flag not in hint_targets or handle not in hint_targets[flag]:
                error(
                    "semantic_vocabulary_hint",
                    vocabulary["id"],
                    f"unresolved {hint}",
                )

    programme_question_results = []
    for programme in programmes:
        question = f"explain {programme['title']}"
        packet = query_corpus.semantic_slice_packet(question, 4)
        recovered = {
            (cell["kind"], cell["handle"])
            for cell in packet["semantic_cells"]
        }
        expected = ("reading_route", programme["id"])
        passed = expected in recovered
        programme_question_results.append(
            {
                "route_id": programme["id"],
                "query": question,
                "passed": passed,
                "packet_bytes": packet_size(packet),
            }
        )
        if not passed:
            error(
                "programme_natural_language_discovery",
                programme["id"],
                question,
            )

    theorem_like = [
        row
        for row in declarations
        if row["kind"] in {"theorem", "lemma", "corollary", "proposition"}
    ]
    theorem_like_with_docstrings = sum(
        bool(row.get("docstring")) for row in theorem_like
    )
    module_synopsis_count = sum(
        bool(query_corpus.module_synopsis(module["path"]))
        for module in atlas["modules"]
    )
    synopsis_index_paths = set(query_corpus.module_synopsis_index())
    atlas_module_paths = {module["path"] for module in atlas["modules"]}
    if synopsis_index_paths != atlas_module_paths:
        error(
            "module_synopsis_index_inventory",
            "docs/module_synopsis_index.json",
            f"missing={len(atlas_module_paths - synopsis_index_paths)} "
            f"extra={len(synopsis_index_paths - atlas_module_paths)}",
        )
    artifacts = query_corpus.artifact_inventory()
    artifact_availability = Counter(
        row.get("availability", "unknown") for row in artifacts
    )
    unresolved_paper_coordinates = sum(
        bool(
            coordinate
            and coordinate.get("availability")
            == "authored_source_unavailable_in_worktree"
        )
        for claim in claims
        if (
            coordinate := query_corpus.paper_coordinate(
                claim.get("paper_label"), query_corpus.paper_label_index()
            )
        )
    )
    return {
        "kind": "semantic_corpus_audit",
        "schema_version": AUDIT_SCHEMA,
        "passed": not errors,
        "authority_posture": (
            "whole_corpus_navigation_and_referential_integrity_audit_not_a_proof_of_open_claims"
        ),
        "corpus_scale": {
            "raw_atlas_declaration_count": len(raw_declarations),
            "declaration_count": len(declarations),
            "suppressed_comment_false_positive_count": (
                len(raw_declarations) - len(declarations)
            ),
            "theorem_like_count": len(theorem_like),
            "claim_count": len(claims),
            "open_proposition_count": len(opens),
            "route_count": len(routes),
            "mathematical_programme_count": len(programmes),
        },
        "coverage": {
            "typed_packet_expansion_count": expanded_packet_count,
            "expected_typed_packet_expansion_count": (
                len(claims) + len(opens) + len(routes)
            ),
            "programme_question_pass_count": sum(
                row["passed"] for row in programme_question_results
            ),
            "programme_question_count": len(programme_question_results),
            "checked_semantic_vocabulary_hint_count": checked_hint_count,
            "declaration_source_module_count": len(module_lines),
            "authored_module_synopsis_count": module_synopsis_count,
            "authored_module_synopsis_ratio": (
                module_synopsis_count / len(atlas["modules"])
                if atlas["modules"]
                else 1.0
            ),
            "missing_declaration_source_count": source_missing_count,
            "invalid_declaration_coordinate_count": coordinate_error_count,
            "verified_comment_false_positive_count": len(
                actual_comment_false_positive_ids
            ),
            "theorem_like_docstring_count": theorem_like_with_docstrings,
            "theorem_like_docstring_ratio": (
                theorem_like_with_docstrings / len(theorem_like)
                if theorem_like
                else 1.0
            ),
        },
        "boundedness": {
            "maximum_typed_packet_bytes": maximum_packet[0],
            "maximum_typed_packet_handle": maximum_packet[1],
            "output_budget_bytes": query_corpus.OUTPUT_BUDGET_BYTES,
        },
        "partial_artifact_receipt": {
            "availability_counts": dict(sorted(artifact_availability.items())),
            "unresolved_paper_coordinate_count": unresolved_paper_coordinates,
            "meaning": (
                "Missing optional authored artifacts remain typed; they do not "
                "erase Lean, claim, open, route, or declaration witnesses."
            ),
        },
        "programme_questions": programme_question_results,
        "errors": errors,
        "error_count": len(errors),
    }


def render_card(packet: dict[str, Any]) -> str:
    scale = packet["corpus_scale"]
    coverage = packet["coverage"]
    boundedness = packet["boundedness"]
    return (
        f"semantic corpus audit {packet['schema_version']} "
        f"| {'PASS' if packet['passed'] else 'FAIL'} "
        f"| declarations={scale['declaration_count']} "
        f"| claims={scale['claim_count']} | open={scale['open_proposition_count']} "
        f"| programmes={coverage['programme_question_pass_count']}/"
        f"{coverage['programme_question_count']} "
        f"| packets={coverage['typed_packet_expansion_count']}/"
        f"{coverage['expected_typed_packet_expansion_count']} "
        f"| module_synopses={coverage['authored_module_synopsis_ratio']:.3f} "
        f"| docstrings={coverage['theorem_like_docstring_ratio']:.3f} "
        f"| max_packet={boundedness['maximum_typed_packet_bytes']}B "
        f"| errors={packet['error_count']}"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--format", choices=("json", "card"), default="card")
    args = parser.parse_args()
    packet = audit_packet()
    if args.format == "json":
        print(json.dumps(packet, ensure_ascii=False, indent=2))
    else:
        print(render_card(packet))
        for row in packet["errors"][:20]:
            print(
                f"FAIL {row['check']} | {row['handle']} | {row['detail']}"
            )
    return 0 if packet["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
