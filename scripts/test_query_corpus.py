#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Focused tests for the bounded public corpus query surface."""

from __future__ import annotations

import json
import copy
import re
import subprocess
import sys
from pathlib import Path

import query_corpus
from query_corpus import (
    agent_tour_packet,
    all_entrypoints,
    artifact_inventory,
    artifact_packet,
    claim_status_packet,
    claim_packet,
    declaration_packet,
    lean_source_identity_for_paper,
    load,
    open_proposition_packet,
    paper_anchor_inventory,
    paper_anchor_packet,
    route_packet,
    route_memory_problem_number,
    source_coordinate_packet,
)

ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts" / "query_corpus.py"
SEMANTIC_SCRIPT = ROOT / "scripts" / "query_semantic.py"
PROGRAMME_EXPECTATIONS = {
    "erdos257_half_story": {
        "title": "Achievement-set geometry and the rational-target seams",
        "open_ids": {
            "remaining_open.half_value_membership",
            "remaining_open.twenty_one_permanent_affine_supercapacity",
            "remaining_open.universal_257_all_infinite_supports",
        },
    },
    "erdos249_certificate_story": {
        "title": "#249 certificate and harmonic interface",
        "open_ids": {
            "remaining_open.erdos_249_irrationality",
            "remaining_open.unbounded_certificate_supply",
        },
    },
    "structured_support_families": {
        "title": "Classical and structured support irrationality",
        "open_ids": {"remaining_open.universal_257_all_infinite_supports"},
    },
    "erdos249_diagonal_arithmetic": {
        "title": "#249 diagonal arithmetic and fresh-loss interfaces",
        "open_ids": {"remaining_open.unbounded_certificate_supply"},
    },
    "boolean_mobius_constraints": {
        "title": "Boolean Möbius carry and global rationality constraints",
        "open_ids": {"remaining_open.universal_257_all_infinite_supports"},
    },
    "transport_curvature_programme": {
        "title": "Transport, curvature, phase separation, and no-go results",
        "open_ids": {"remaining_open.unbounded_certificate_supply"},
    },
    "lambert_obstruction_interfaces": {
        "title": "Mersenne–Lambert identities and obstruction interfaces",
        "open_ids": {"remaining_open.unbounded_certificate_supply"},
    },
    "probabilistic_gcd_geometry": {
        "title": "Coprimality probability, gcd moments, and Stern–Brocot geometry",
        "open_ids": {"remaining_open.erdos_249_irrationality"},
    },
    "half_carry_compactness_programme": {
        "title": "Half-carry compactness, windows, seams, and finite propagation",
        "open_ids": {
            "remaining_open.half_value_membership",
            "remaining_open.universal_257_all_infinite_supports",
        },
    },
    "arithmetic_obstruction_interfaces": {
        "title": "Denominator, CRT, moment, and gauge obstructions",
        "open_ids": {
            "remaining_open.erdos_249_irrationality",
            "remaining_open.unbounded_certificate_supply",
        },
    },
}


def query(*args: str) -> dict[str, object]:
    completed = subprocess.run(
        [sys.executable, str(SCRIPT), *args],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return json.loads(completed.stdout)


def run(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(SCRIPT), *args],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )


def semantic_query(*args: str) -> dict[str, object]:
    completed = subprocess.run(
        [sys.executable, str(SEMANTIC_SCRIPT), *args],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return json.loads(completed.stdout)


def validate_programme_routes() -> None:
    for route_id, expected in PROGRAMME_EXPECTATIONS.items():
        packet = query("--route", route_id)
        route = packet["route"]
        programme = packet["programme"]
        assert route["route_kind"] == "mathematical_programme"
        assert programme["title"] == expected["title"]
        assert programme["core_claims"]
        assert programme["problem_targets"]
        assert all(row["status"] == "open" for row in programme["problem_targets"])
        assert {
            row["id"] for row in programme["remaining_open_propositions"]
        } == expected["open_ids"]
        assert {
            step.rsplit(" ", 1)[-1]
            for step in route["query_steps"]
            if " --claim " in step
        } == {row["id"] for row in programme["core_claims"]}
        assert {
            step.rsplit(" ", 1)[-1]
            for step in route["query_steps"]
            if " --open " in step
        } == expected["open_ids"]
        route_memory = packet["route_memory"]
        target_claim_ids = {row["id"] for row in programme["problem_targets"]}
        expected_problem = 257 if "universal_257" in target_claim_ids else 249
        assert route_memory["problem_number"] == expected_problem
        assert route_memory["command"] == (
            "python3 scripts/query_route_memory.py --problem "
            f"{expected_problem} --route {route_id}"
        )
        assert route_memory["authority_posture"] == (
            "derived_resume_handoff_not_claim_or_proof_authority"
        )
        claim_view = query("--claim", route["core_claim_ids"][0])
        context = next(
            row
            for row in claim_view["programme_contexts"]
            if row["id"] == route_id
        )
        assert context["route_memory"]["problem_number"] == expected_problem
        assert context["route_memory"]["command"] == route_memory["command"]
        assert context["route_memory"]["authority_posture"] == (
            "derived_resume_handoff_not_claim_or_proof_authority"
        )
        assert "current tracked source digests" in context["route_memory"][
            "identity_contract"
        ]
        assert any(
            token in programme["claim_ceiling"].casefold()
            for token in (
                "remain open",
                "not proved",
                "does not",
                "do not",
                "neither",
                "no ",
            )
        )
        encoded = json.dumps(packet, ensure_ascii=False).encode("utf-8")
        assert len(encoded) <= 16_384
        card = run("--route", route_id, "--format", "card")
        assert card.returncode == 0
        assert card.stdout.startswith(f"programme {route_id} |")
        assert "| resume=python3 scripts/query_route_memory.py --problem " in card.stdout


def validate_indexed_problem_routes() -> None:
    """Canonical problem ids in the public source map must be executable routes."""
    problems = load("docs/problems.json")["problems"]
    for problem in problems:
        route_id = problem["problem_id"]
        packet = query("--route", route_id)
        assert packet["kind"] == "problem_route"
        route = packet["route"]
        assert route["id"] == route_id
        assert route["erdos_number"] == problem["erdos_number"]
        assert route["authority_posture"] == (
            "generated_problem_index_route_not_claim_status_or_Lean_proof_authority"
        )
        if route_id == "erdos_1041":
            research = route["research_corpus"]
            assert research["strongest_result_summary"]["result_count"] == 35
            assert research["files"]["frontier"]["path"] == (
                "research_corpus/Erdos1041/FRONTIER.md"
            )
            assert "not_reviewed_claim_registry" in research["authority_posture"]
            assert research["source_fingerprint"]["problem_index"]["path"] == (
                "docs/problems.json"
            )
            assert set(research["source_fingerprint"]["files"]) == {
                "frontier",
                "strongest_results",
                "manifest",
                "checkpoint",
            }
        card = run("--route", route_id, "--format", "card")
        assert card.returncode == 0
        assert card.stdout.startswith(f"problem {route_id} |")


def validate_research_corpus_fingerprint() -> None:
    """A copied index digest must not hide changed public research bytes."""
    problem = next(
        row
        for row in load("docs/problems.json")["problems"]
        if row["problem_id"] == "erdos_1041"
    )
    broken = copy.deepcopy(problem)
    broken["research_corpus"]["files"]["frontier"]["content_digest"] = (
        "sha256:" + "0" * 64
    )
    try:
        query_corpus._source_current_research_corpus(broken)
    except ValueError as error:
        assert "digest drift" in str(error)
    else:
        raise AssertionError("research corpus digest mutation escaped")


def validate_agent_tour() -> None:
    packet = agent_tour_packet()
    assert packet["kind"] == "agent_corpus_tour"
    assert packet["scale"]["declaration_count"] > 100_000
    assert packet["scale"]["mathematical_programme_count"] == len(
        PROGRAMME_EXPECTATIONS
    )
    assert packet["scale"]["indexed_problem_count"] == 8
    assert packet["scale"]["indexed_open_problem_count"] == 8
    assert packet["scale"]["reviewed_remaining_open_proposition_count"] == len(
        packet["frontier"]
    )
    assert packet["open_frontier_contract"] == {
        "indexed_open_problem_count": 8,
        "reviewed_remaining_open_proposition_count": len(packet["frontier"]),
        "reviewed_scope": "reviewed #249/#257 claim registry",
        "distinction": (
            "Open-proposition rows describe the reviewed #249/#257 claim "
            "frontier; they are not a count of the canonically indexed open "
            "Erdős problems."
        ),
    }
    assert packet["budget_contract"]["maximum_encoded_bytes"] == (
        query_corpus.agent_tour_budget_bytes(8)
    )
    assert {row["erdos_number"] for row in packet["problem_map"]} == {
        68,
        243,
        249,
        251,
        257,
        269,
        1041,
        1049,
    }
    route_memory_contract = packet["route_memory_contract"]
    assert route_memory_contract["selector_source"] == (
        "problem_map[].erdos_number from docs/problems.json"
    )
    assert route_memory_contract["coverage"] == {
        "indexed_problem_count": 8,
        "indexed_problem_numbers": [68, 243, 249, 251, 257, 269, 1041, 1049],
    }
    assert route_memory_contract["start"].startswith(
        "python3 scripts/query_route_memory.py --problem"
    )
    assert route_memory_contract["validate"] == (
        "python3 scripts/query_route_memory.py --validate <packet.json>"
    )
    assert "cross_problem_route_or_declaration" in route_memory_contract["rejections"]
    assert packet["formal_dependency_graph"]["source_resolved_node_count"] > 0
    assert packet["formal_dependency_graph"]["source_resolved_direct_edge_count"] > 0
    assert {row["id"] for row in packet["mathematical_map"]} == set(
        PROGRAMME_EXPECTATIONS
    )
    assert all(
        row["follow"] == (
            "python3 scripts/query_corpus.py --route "
            f"{row['problem_id']}"
        )
        for row in packet["problem_map"]
    )
    assert {
        row["intent"] for row in packet["intent_lenses"]
    } >= {
        "understand_the_mathematics",
        "locate_any_formal_object",
        "inspect_exact_formal_dependencies",
        "begin_a_checked_change",
    }
    locate = next(
        row
        for row in packet["intent_lenses"]
        if row["intent"] == "locate_any_formal_object"
    )
    assert "query_corpus.py --search" in locate["start"]
    assert "query_semantic.py inventory" in locate["then"]
    assert "query_corpus.py --declaration" in locate["expand"]
    assert set(packet["cold_reader_contracts"]) == {
        "research_mathematician",
        "formalisation_engineer",
        "ai_lab_researcher",
        "independent_contributor",
    }
    encoded = json.dumps(packet, ensure_ascii=False).encode("utf-8")
    assert len(encoded) <= packet["budget_contract"]["maximum_encoded_bytes"]
    card = run("--tour", "--format", "card")
    assert card.returncode == 0
    lines = card.stdout.strip().splitlines()
    assert len(lines) == 6
    assert lines[0].startswith("corpus tour | modules=")
    assert "reviewed_open_propositions=" in lines[0]
    assert lines[1].startswith("problem map | indexed=8 | open=8")
    assert lines[2].startswith("formal graph | roots=")
    assert lines[3].startswith("authority | navigation=")
    assert lines[4].startswith("reviewed frontier | scope=#249/#257")
    assert lines[5] == (
        "next | command=python3 scripts/query_corpus.py --route "
        "agent_native_corpus_navigation | requires_lean_build=false"
    )


def validate_paper_guide() -> None:
    packet = query("--papers", "--format", "json")
    corpus = load("docs/papers/corpus.json")
    assert packet["kind"] == "paper_reading_guide"
    assert packet["paper_count"] == corpus["paper_count"]
    assert [row["paper_id"] for row in packet["papers"]] == [
        row["paper_id"] for row in corpus["papers"]
    ]
    assert all(row["preferred_read_path"] for row in packet["papers"])
    assert all(
        row["full_text_available_in_checkout"] for row in packet["papers"]
    )
    assert all(row["not_authority_for"] for row in packet["papers"])
    corpus_by_id = {row["paper_id"]: row for row in corpus["papers"]}
    packet_by_id = {row["paper_id"]: row for row in packet["papers"]}
    omitted_pdf_ids = {
        row["paper_id"] for row in corpus["papers"] if "local_pdf" not in row
    }
    assert omitted_pdf_ids == {
        "erdos-68-factorial-denominator-irrationality",
        "erdos-1041-lemniscate-newton-flow",
    }
    for paper_id in omitted_pdf_ids:
        assert packet_by_id[paper_id]["pdf_available_in_checkout"] is False
        assert packet_by_id[paper_id]["preferred_read_path"] == corpus_by_id[
            paper_id
        ]["local_full_text"]

    card = run("--papers", "--format", "card")
    assert card.returncode == 0
    assert card.stdout.startswith(
        f"paper reading guide | papers={corpus['paper_count']} "
    )
    assert "papers are exposition" in card.stdout
    assert len(card.stdout.strip().splitlines()) == corpus["paper_count"] + 2

    natural = query("--ask", "which papers should I read?")
    assert natural["kind"] == "paper_reading_guide"
    assert [row["paper_id"] for row in natural["papers"]] == [
        row["paper_id"] for row in packet["papers"]
    ]


def validate_natural_language_search() -> None:
    assert query_corpus.search_rank("exact_id", "exact_id", "body") == 0
    assert query_corpus.search_rank("exact", "exact_id", "body") == 1
    assert query_corpus.search_rank("act_id", "exact_id", "body") == 2
    assert (
        query_corpus.search_rank(
            "whole phrase", "id", "prefix whole phrase suffix"
        )
        == 3
    )
    assert (
        query_corpus.search_rank(
            "denominator obstruction",
            "id",
            "denominator and gauge obstruction",
        )
        == 5
    )
    assert (
        query_corpus.search_rank(
            "unknown mathematical phrase", "id", "unrelated body"
        )
        is None
    )
    for exact_problem_phrase in ("Erdős problem 243", "Erdos problem 243"):
        problem = query("--search", exact_problem_phrase, "--limit", "1")
        assert problem["results"][0]["kind"] == "problem"
        assert problem["results"][0]["id"] == "erdos_243"
        assert problem["results"][0]["follow"]["route_memory"] == (
            "python3 scripts/query_route_memory.py --problem 243"
        )
        assert problem["routing_receipt"] == {
            "selection": "exact_problem_registry_term",
            "declaration_scan_required": False,
        }
    # Erdős 300 is not in the indexed corpus. This used to name #68, which the
    # eight-problem corpus now answers rather than refuses.
    out_of_scope_question = (
        "For Erdos 300, what does equality of two complementary "
        "leave-one-out projections prove?"
    )
    boundary = query("--ask", out_of_scope_question, "--format", "json")
    assert boundary["kind"] == "corpus_scope_boundary"
    assert boundary["status"] == "explicit_problem_not_indexed"
    assert boundary["requested_problem_numbers"] == [300]
    assert boundary["out_of_scope_problem_numbers"] == [300]
    assert boundary["covered_problem_numbers"] == []
    assert boundary["indexed_problem_numbers"] == [
        row["erdos_number"]
        for row in load("docs/problems.json")["problems"]
    ]
    assert boundary["scope_source"] == "docs/problems.json"
    assert boundary["match_count"] == 0
    assert boundary["claim_effect"] == "none"
    assert boundary["private_state_disclosure"] == "none"
    boundary_card = run(
        "--ask",
        out_of_scope_question,
        "--format",
        "card",
    )
    assert boundary_card.returncode == 0
    assert boundary_card.stdout.startswith(
        "corpus scope boundary | status=explicit_problem_not_indexed "
        "| requested=#300 | out_of_scope=#300 "
    )
    assert "claim_effect=none" in boundary_card.stdout
    dictionary = query("--vocabulary")
    assert dictionary["problem_registry_contract"]["source"] == "docs/problems.json"
    assert len(dictionary["problem_registry_contract"]["problems"]) == 8
    natural_language_routes = {
        "how close is problem 249": "erdos249_certificate_story",
        "what remains open for 257": "erdos257_half_story",
        "achievement set topology": "erdos257_half_story",
        "periodic weighted Lambert series": "structured_support_families",
        "diagonal pincer and fresh loss": "erdos249_diagonal_arithmetic",
        "binary carry rigidity": "boolean_mobius_constraints",
        "why local induction fails": "half_carry_compactness_programme",
        "dyadic prefix compression": "half_carry_compactness_programme",
        "first harmonic pivot decomposition": "transport_curvature_programme",
        "strategy countermodels": "transport_curvature_programme",
        "Mersenne Lambert identities": "lambert_obstruction_interfaces",
        "what probability and gcd identities are formalized": "probabilistic_gcd_geometry",
        "what Stern Brocot or continued fraction geometry is proved": "probabilistic_gcd_geometry",
        "what exact run geometry is proved": "probabilistic_gcd_geometry",
        "formal proof trust": "change_or_verify_release",
        "denominator obstruction": "arithmetic_obstruction_interfaces",
        "how big is the corpus": "instant_orientation",
        "what is formally checked": "instant_orientation",
        "what other exact mathematics is there": "instant_orientation",
        "what else is formally checked besides Erdos 249 and 257": "instant_orientation",
        "what is proved": "browse_claim_status",
        "what is formalised": "browse_claim_status",
        "what is formalized": "browse_claim_status",
        "which results are unconditional progress": "browse_claim_status",
        "what is reduced": "browse_claim_status",
        "what is computed": "browse_claim_status",
        "show verified finite computations": "browse_claim_status",
        "show conditional reductions": "browse_claim_status",
        "which claims are cited only": "browse_claim_status",
        "list open claims": "browse_claim_status",
        "where are the Lean proofs": "follow_one_claim",
        "what is new mathematics": "trace_prior_art",
        "how do I verify this": "change_or_verify_release",
        "which semantic meanings were reviewed": "agent_native_corpus_navigation",
        "what semantic interpretations were checked": "agent_native_corpus_navigation",
        "audit semantic review receipts": "agent_native_corpus_navigation",
        "why does this Lean proof work": "agent_native_corpus_navigation",
        "which proof mechanisms transfer": "agent_native_corpus_navigation",
        "what mathematical routes failed": "agent_native_corpus_navigation",
        "what semantic work remains": "agent_native_corpus_navigation",
        "which paper proofs lack semantic interpretation": "agent_native_corpus_navigation",
        "prioritize semantic population from the papers": "agent_native_corpus_navigation",
        "what is still missing": "understand_methodology_and_open_boundary",
        "what remains open": "understand_methodology_and_open_boundary",
    }
    for search_text, route_id in natural_language_routes.items():
        natural_search = query("--search", search_text, "--limit", "10")
        assert natural_search["results"][0]["kind"] == "reading_route"
        assert natural_search["results"][0]["id"] == route_id
    backlog_route = query(
        "--search",
        "which paper proofs lack semantic interpretation",
        "--limit",
        "1",
    )
    assert backlog_route["routing_receipt"] == {
        "selection": "exact_authored_discovery_term",
        "declaration_scan_required": False,
    }
    paraphrased_backlog = query(
        "--search",
        "where are the semantic coverage gaps in the papers",
        "--limit",
        "3",
    )
    assert paraphrased_backlog["results"][0]["id"] == (
        "agent_native_corpus_navigation"
    )
    assert paraphrased_backlog["routing_receipt"] == {
        "selection": "controlled_vocabulary_route",
        "declaration_scan_required": False,
    }
    portfolio_search = query(
        "--search", "what other exact mathematics is there", "--limit", "10"
    )
    assert portfolio_search["results"][0]["kind"] == "reading_route"
    assert portfolio_search["results"][0]["id"] == "instant_orientation"
    ruled_out = query("--search", "what is ruled out", "--limit", "10")
    assert {
        row["id"]
        for row in ruled_out["results"]
        if row["kind"] == "reading_route"
    } >= {
        "transport_curvature_programme",
        "lambert_obstruction_interfaces",
        "arithmetic_obstruction_interfaces",
    }


def validate_indexed_declaration_lookup() -> None:
    """Keep exact declaration/source lookup off the eager qualified-name scan."""
    query_corpus.declaration_row_indexes.cache_clear()
    query_corpus.declaration_rows_by_qualified_name.cache_clear()
    name = (
        "tsum_totient_div_pow_two_ne_ratCast_of_den_le_"
        "79639646646701375323355774875831053"
    )
    qualified_name = f"Erdos249257.{name}"

    bare = declaration_packet(name, 20)
    qualified = declaration_packet(qualified_name, 20)
    source = source_coordinate_packet(
        "Erdos249257/CertificateKernel.lean:18384", 20
    )

    assert bare == qualified
    assert source["nearby_declarations"][0]["qualified_name"] == qualified_name
    declaration_route_memory = bare["matches"][0]["route_memory"]
    assert declaration_route_memory["status"] == "bound"
    assert declaration_route_memory["bindings"] == [
        {
            "route_id": "erdos249_certificate_story",
            "problem_number": 249,
            "command": (
                "python3 scripts/query_route_memory.py --problem 249 "
                "--route erdos249_certificate_story"
            ),
            "authority_posture": (
                "derived_resume_handoff_not_claim_or_proof_authority"
            ),
            "identity_contract": (
                "The route-memory command binds this route to the selected "
                "problem and current tracked source digests before resume."
            ),
        }
    ]
    index_cache = query_corpus.declaration_row_indexes.cache_info()
    qualified_cache = (
        query_corpus.declaration_rows_by_qualified_name.cache_info()
    )
    assert index_cache.misses == 1
    assert index_cache.hits >= 2
    assert qualified_cache.misses == 0
    assert qualified_cache.currsize == 0


def validate_connection_query_ranking() -> None:
    packet = query_corpus.connection_card(
        "mersenneTail_lt_weight",
        8,
        "achievement set compact closed topology",
    )
    declarations = packet["declarations"]
    names = [row["name"] for row in declarations]

    assert names[0] == "mersenneTail_lt_weight"
    assert names[1:3] == [
        "isCompact_mersenneAchievementSet",
        "isClosed_mersenneAchievementSet",
    ]
    assert "mersenneWeightRat_zero" not in names
    assert all(
        row["connection_relevance"]["query_term_overlap"]
        or row["connection_relevance"]["anchor_relations"]
        for row in declarations[1:]
    )
    receipt = packet["declaration_selection_receipt"]
    assert receipt["selection_policy"] == (
        "anchor_then_query_overlap_then_exact_source_span_relation"
    )
    assert receipt["excluded_module_broad_count"] > 100


def validate_paper_semantic_citation_aliases() -> None:
    """Qualified authored roles must resolve ordinary source-level paper links."""
    packet = semantic_query(
        "paper-coverage",
        "--paper",
        "erdos_243_note",
        "--limit",
        "64",
    )
    by_artifact = {row["artifact"]: row for row in packet["results"]}
    reciprocal = by_artifact["erdos_243_note"]

    assert reciprocal["authored_statement_nodes_reached"] > 0
    assert (
        reciprocal["all_tier_statement_nodes_reached"]
        >= reciprocal["authored_statement_nodes_reached"]
    )
    assert (
        "Erdos243/ReciprocalTailRigidity.lean:no_periodicNegative_orbit"
        in reciprocal["node_routed_citations"]
    )
    assert (
        "Erdos243/ReciprocalTailRigidity.lean:no_periodicNegative_orbit"
        not in reciprocal["atlas_absent_declaration_citations"]
    )

    backlog = semantic_query(
        "population-backlog",
        "--paper",
        "erdos249-totient-reasoning-surface",
        "--limit",
        "12",
    )
    assert backlog["paper_count"] == 1
    assert backlog["authored_statement_backlog_declaration_count"] > 0
    paper = backlog["papers"][0]
    assert paper["authored_statement_backlog_declaration_count"] > 0
    assert paper["authored_statement_backlog_declaration_count"] >= sum(
        group["declaration_count"]
        for group in paper["unlinked_module_groups"]
    )
    assert all(
        group["declaration_count"] >= len(group["candidates"])
        for group in paper["unlinked_module_groups"]
    )
    assert all(
        group["module"].endswith(".lean")
        for group in paper["unlinked_module_groups"]
    )
    assert all(
        candidate["interpretation_tier"] != "authored_statement"
        for group in paper["unlinked_module_groups"]
        for candidate in group["candidates"]
    )

    structural = semantic_query(
        "structural-backlog",
        "--problem",
        "257",
    )
    assert structural.get("truncated") is not True
    assert structural["results"]
    assert structural["returned_module_count"] == len(structural["results"])
    assert structural["omitted_module_count"] == (
        structural["module_backlog_count"]
        - structural["returned_module_count"]
    )
    assert structural["results"][0]["candidate_roles"]
    assert (
        len(
            json.dumps(
                structural,
                indent=1,
                ensure_ascii=False,
            ).encode("utf-8")
        )
        <= structural["budget_contract"]["maximum_encoded_bytes"]
    )


def validate_claim_status_packets() -> None:
    claims_document = load("docs/claims.json")
    taxonomy = claims_document["status_taxonomy"]
    all_claims = claims_document["claims"]
    for status, meaning in taxonomy.items():
        packet = query("--status", status, "--limit", "100")
        expected = [claim for claim in all_claims if claim["status"] == status]
        assert packet["kind"] == "claim_status"
        assert packet["authority_posture"] == (
            "claim_registry_status_navigation_not_proof_authority"
        )
        assert packet["status"] == status
        assert packet["meaning"] == meaning
        assert packet["claim_count"] == len(expected)
        assert packet["omitted_claim_count"] == 0
        assert len(packet["claims"]) == len(expected)
        assert all(row["status"] == status for row in packet["claims"])
        assert all(row["statement_excerpt"] for row in packet["claims"])
        if status == "conditional reduction":
            assert all(
                row["remaining_open_proposition_ids"] for row in packet["claims"]
            )
        if status == "verified finite instance":
            assert all(row["bounded_domain"] for row in packet["claims"])
        if status == "open":
            assert {row["id"] for row in packet["claims"]} == {
                "erdos_249",
                "universal_257",
            }
            assert {
                row["id"] for row in packet["remaining_open_propositions"]
            } == {
                row["id"]
                for row in claims_document["remaining_open_propositions"]
            }
        else:
            assert packet["remaining_open_propositions"] == []
        direct = claim_status_packet(status.upper(), 1)
        assert direct["status"] == status
        assert len(direct["claims"]) == min(1, len(expected))
        card = run("--status", status, "--format", "card")
        assert card.returncode == 0
        assert card.stdout.startswith(f"status {status} | claims={len(expected)}")

    unknown_status = run("--status", "not a registry status")
    assert unknown_status.returncode == 2
    assert "unknown claim status" in unknown_status.stderr


def main() -> int:
    validate_programme_routes()
    validate_indexed_problem_routes()
    validate_research_corpus_fingerprint()
    validate_agent_tour()
    validate_paper_guide()
    validate_natural_language_search()
    validate_indexed_declaration_lookup()
    validate_connection_query_ranking()
    validate_paper_semantic_citation_aliases()
    bare_ask = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--ask",
            "why does this Lean proof work",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert bare_ask.returncode == 0, bare_ask.stderr
    assert len(bare_ask.stdout.encode("utf-8")) <= query_corpus.OUTPUT_BUDGET_BYTES
    assert "semantic slice" in bare_ask.stdout.lower()
    validate_claim_status_packets()
    summary = query()
    assert summary["kind"] == "corpus_summary"
    omission_receipt = summary["bounded_summary_omission_receipt"]
    assert set(omission_receipt["omitted_sections"]) == {
        "checks",
        "editorial_architecture",
        "editorial_state",
        "external_registration",
        "source_provenance",
    }
    assert omission_receipt["drilldown"] == "docs/orientation.json"
    assert all(
        key not in summary for key in omission_receipt["omitted_sections"]
    )
    claims_document = json.loads((ROOT / "docs" / "claims.json").read_text(encoding="utf-8"))
    assert summary["curated_claim_count"] == len(claims_document["claims"])
    assert summary["publication_family_count"] == len(
        claims_document["machine_readable_paper"]["publication_assembly"][
            "contribution_families"
        ]
    )
    module_graph = claims_document["machine_readable_paper"]["module_graph"]
    assert module_graph["root"] == "Erdos249257.lean"
    assert module_graph["additional_roots"] == ["ErdosProblems.lean"]
    assert summary["scale"]["module_count"] == (
        len(module_graph["nodes"])
        + 1
        + len(module_graph["additional_roots"])
    )
    descriptor = json.loads((ROOT / "docs" / "corpus_descriptor.json").read_text(encoding="utf-8"))
    formal_source = claims_document["release"]["formal_source"]
    publication_assembly = claims_document["machine_readable_paper"]["publication_assembly"]
    architecture = query("--publication-architecture")
    assert architecture["kind"] == "publication_architecture"
    assert architecture["architecture"]["canonical_gateway"]["source"] == (
        "paper/erdos249-257-main-paper.tex"
    )
    assert len(architecture["family_index"]) == len(
        publication_assembly["contribution_families"]
    )
    assembled_claim_ids = [
        claim_id
        for family in publication_assembly["contribution_families"]
        for claim_id in family["claim_ids"]
    ]
    assert len(assembled_claim_ids) == len(set(assembled_claim_ids))
    assert set(assembled_claim_ids) == {
        claim["id"] for claim in claims_document["claims"]
    }
    certificate_family = query(
        "--publication-family", "exact_certificate_equivalence_and_deposits"
    )
    assert certificate_family["kind"] == "publication_family"
    assert certificate_family["family"]["primary_narrative_owner"] == (
        "paper/erdos249-257-main-paper.tex"
    )
    assert {claim["id"] for claim in certificate_family["claims"]} == {
        "certificate_reduction",
        "certificate_completeness",
        "certified_kill_instances",
        "diagonal_pincer_t64_primality_closure",
        "diagonal_pincer_t64_endpoint_certificate",
    }
    family_card = run(
        "--publication-family",
        "exact_certificate_equivalence_and_deposits",
        "--format",
        "card",
    )
    assert family_card.returncode == 0
    assert family_card.stdout.startswith(
        "publication family exact_certificate_equivalence_and_deposits |"
    )
    for family in publication_assembly["contribution_families"]:
        family_packet = query("--publication-family", family["id"])
        bindings = family_packet["route_memory"]["bindings"]
        expected_routes = []
        route_match = re.fullmatch(
            r"\s*python3 scripts/query_corpus\.py --route ([^\s]+)\s*",
            family["source_route"],
        )
        claim_match = re.fullmatch(
            r"\s*python3 scripts/query_corpus\.py --claim ([^\s]+)\s*",
            family["source_route"],
        )
        programme_routes = {
            row["id"]: row
            for row in all_entrypoints(claims_document)
            if row.get("route_kind") == "mathematical_programme"
        }
        if route_match and route_match.group(1) in programme_routes:
            expected_routes = [programme_routes[route_match.group(1)]]
        elif claim_match:
            expected_routes = [
                row
                for row in programme_routes.values()
                if claim_match.group(1) in row.get("core_claim_ids", [])
            ]
        expected_bindings = {
            (
                row["id"],
                route_memory_problem_number(row),
            )
            for row in expected_routes
            if route_memory_problem_number(row) is not None
        }
        actual_bindings = {
            (row["route_id"], row["problem_number"]) for row in bindings
        }
        assert actual_bindings == expected_bindings
        assert family_packet["route_memory"]["status"] == (
            "bound" if expected_bindings else "unbound"
        )
        if not expected_bindings:
            assert "no resume route was invented" in family_packet["route_memory"][
                "unbound_reason"
            ]
    architecture_card = run("--publication-architecture", "--format", "card")
    assert architecture_card.returncode == 0
    assert architecture_card.stdout.startswith("publication architecture |")
    assert descriptor["identity"]["formal_source"]["ref"] == formal_source["ref"]
    resolved_formal_source = subprocess.run(
        ["git", "rev-parse", formal_source["ref"]],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()
    assert descriptor["identity"]["formal_source"]["resolved_commit"] == (
        resolved_formal_source
    )
    assert descriptor["identity"]["formal_source"]["publication_state"] == (
        formal_source["publication_state"]
    )
    assert descriptor["identity"]["formal_source"]["public_tag"] == (
        formal_source["public_tag"]
    )
    resolved_public_tag = subprocess.run(
        ["git", "rev-parse", f"{formal_source['public_tag']}^{{}}"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()
    assert resolved_public_tag == formal_source["ref"]

    claim = query("--claim", "denominator_exclusion")
    assert claim["claim"]["status"] == "formalised here"
    assert claim["remaining_open_propositions"][0]["id"] == "remaining_open.erdos_249_irrationality"
    assert claim["argument_neighbourhood"]["outgoing"][0]["neighbour"]["id"] == "erdos_249"
    assert "partial progress" in claim["argument_neighbourhood"]["outgoing"][0]["relation_meaning"]

    reduction = query("--claim", "certificate_reduction")
    incoming_ids = {
        row["neighbour"]["id"] for row in reduction["argument_neighbourhood"]["incoming"]
    }
    assert "certificate_completeness" in incoming_ids
    assert "first_harmonic_certificate_interface" in incoming_ids
    assert reduction["argument_neighbourhood"]["outgoing"][0]["neighbour"]["status"] == "open"
    reduction_claim = next(
        row for row in claims_document["claims"] if row["id"] == "certificate_reduction"
    )
    assert reduction["paper"]["label"] == reduction_claim["paper_label"]

    half_route = query("--route", "erdos257_half_story")["route"]
    assert half_route["query_steps"] == [
        "python3 scripts/query_corpus.py --claim greedy_achievement_geometry",
        "python3 scripts/query_corpus.py --claim half_greedy_two_thirds_band",
        "python3 scripts/query_corpus.py --claim half_membership_seam_classification",
        "python3 scripts/query_corpus.py --claim fatal_gap_right_tail_classification",
        "python3 scripts/query_corpus.py --claim twenty_one_quotient_greedy_frontier",
        "python3 scripts/query_corpus.py --claim final_middle_cell_escape",
        "python3 scripts/query_corpus.py --claim final_middle_neg_two_phase_sieve",
        "python3 scripts/query_corpus.py --claim last_producer_tail_escape_reduction",
        "python3 scripts/query_corpus.py --open remaining_open.half_value_membership",
        "python3 scripts/query_corpus.py --open remaining_open.twenty_one_permanent_affine_supercapacity",
        "python3 scripts/query_corpus.py --open remaining_open.universal_257_all_infinite_supports",
    ]
    band_claim = query("--claim", "half_greedy_two_thirds_band")
    assert {
        row["id"] for row in band_claim["remaining_open_propositions"]
    } == {"remaining_open.half_value_membership"}
    assert ("builds_on", "greedy_achievement_geometry") in {
        (row["relation"], row["neighbour"]["id"])
        for row in band_claim["argument_neighbourhood"]["outgoing"]
    }
    assert (
        "no theorem here says that the actual greedy orbit for 1/2 avoids a band"
        in band_claim["claim"]["statement"]
    )
    half_membership = query("--claim", "half_membership_seam_classification")
    assert {
        (row["relation"], row["neighbour"]["id"])
        for row in half_membership["argument_neighbourhood"]["outgoing"]
    } >= {
        ("builds_on", "greedy_achievement_geometry"),
        ("builds_on", "fatal_gap_right_tail_classification"),
        ("re_expresses_open_branch", "universal_257"),
    }
    assert {
        row["id"] for row in half_membership["remaining_open_propositions"]
    } == {"remaining_open.half_value_membership"}
    last_producer = query("--claim", "last_producer_tail_escape_reduction")
    assert ("builds_on", "fatal_gap_right_tail_classification") in {
        (row["relation"], row["neighbour"]["id"])
        for row in last_producer["argument_neighbourhood"]["outgoing"]
    }
    assert ("advances_open_target", "universal_257") in {
        (row["relation"], row["neighbour"]["id"])
        for row in last_producer["argument_neighbourhood"]["outgoing"]
    }
    assert ("eliminates_case", "final_middle_cell_escape") in {
        (row["relation"], row["neighbour"]["id"])
        for row in last_producer["argument_neighbourhood"]["incoming"]
    }
    phase_sieve = query("--claim", "final_middle_neg_two_phase_sieve")
    assert "Exactly 412 of the 2730 joint residue classes survive" in phase_sieve["claim"]["statement"]
    assert ("builds_on", "fatal_gap_right_tail_classification") in {
        (row["relation"], row["neighbour"]["id"])
        for row in phase_sieve["argument_neighbourhood"]["outgoing"]
    }
    assert ("advances_open_target", "universal_257") in {
        (row["relation"], row["neighbour"]["id"])
        for row in phase_sieve["argument_neighbourhood"]["outgoing"]
    }

    certificate_route = query("--route", "erdos249_certificate_story")["route"]
    assert certificate_route["query_steps"] == [
        "python3 scripts/query_corpus.py --claim denominator_exclusion",
        "python3 scripts/query_corpus.py --claim certificate_reduction",
        "python3 scripts/query_corpus.py --claim certificate_completeness",
        "python3 scripts/query_corpus.py --claim certified_kill_instances",
        "python3 scripts/query_corpus.py --claim first_harmonic_certificate_interface",
        "python3 scripts/query_corpus.py --claim first_harmonic_pivot_decomposition",
        "python3 scripts/query_corpus.py --open remaining_open.erdos_249_irrationality",
        "python3 scripts/query_corpus.py --open remaining_open.unbounded_certificate_supply",
    ]
    certificate_programme = query("--route", "erdos249_certificate_story")
    assert certificate_programme["route"]["route_kind"] == "mathematical_programme"
    assert certificate_programme["programme"]["problem_targets"][0]["id"] == "erdos_249"
    assert {
        row["id"] for row in certificate_programme["programme"]["core_claims"]
    } == {
        "denominator_exclusion",
        "certificate_reduction",
        "certificate_completeness",
        "certified_kill_instances",
        "first_harmonic_certificate_interface",
        "first_harmonic_pivot_decomposition",
    }
    assert {
        row["id"]
        for row in certificate_programme["programme"][
            "remaining_open_propositions"
        ]
    } == {
        "remaining_open.erdos_249_irrationality",
        "remaining_open.unbounded_certificate_supply",
    }
    assert "remain open" in certificate_programme["programme"]["claim_ceiling"]
    diagonal_programme = query("--route", "erdos249_diagonal_arithmetic")
    assert diagonal_programme["programme"]["title"] == (
        "#249 diagonal arithmetic and fresh-loss interfaces"
    )
    assert "diagonal_fresh_loss_reduction" in {
        row["id"] for row in diagonal_programme["programme"]["core_claims"]
    }
    assert {
        row["id"] for row in diagonal_programme["programme"]["related_programmes"]
    } >= {
        "erdos249_certificate_story",
        "transport_curvature_programme",
    }
    programme_card = run(
        "--route", "boolean_mobius_constraints", "--format", "card"
    )
    assert programme_card.returncode == 0
    assert programme_card.stdout.startswith(
        "programme boolean_mobius_constraints |"
    )
    programme_search = query("--search", "fresh-loss interfaces", "--limit", "10")
    assert any(
        row["kind"] == "reading_route"
        and row["id"] == "erdos249_diagonal_arithmetic"
        for row in programme_search["results"]
    )
    first_harmonic = query("--claim", "first_harmonic_certificate_interface")
    assert {
        row["neighbour"]["id"]
        for row in first_harmonic["argument_neighbourhood"]["outgoing"]
        if row["relation"] == "builds_on"
    } >= {"certificate_reduction", "certificate_completeness"}
    harmonic_pivot = query("--claim", "first_harmonic_pivot_decomposition")
    assert harmonic_pivot["claim"]["status"] == "conditional reduction"
    assert "14X/25" in harmonic_pivot["claim"]["statement"]
    assert "9X/10" in harmonic_pivot["claim"]["statement"]
    assert {
        (row["relation"], row["neighbour"]["id"])
        for row in harmonic_pivot["argument_neighbourhood"]["outgoing"]
    } >= {
        ("builds_on", "first_harmonic_certificate_interface"),
        ("advances_open_target", "erdos_249"),
    }

    labelled_claims = [row for row in claims_document["claims"] if row.get("paper_label")]
    for row in labelled_claims:
        packet = query("--claim", row["id"])
        paper = packet["paper"]
        source_lines = (ROOT / paper["source"]).read_text(encoding="utf-8").splitlines()
        anchor_window = "\n".join(source_lines[paper["line"] - 1 : paper["line"] + 1])
        assert re.search(rf"\\label\{{{re.escape(row['paper_label'])}\}}", anchor_window)
    companion = query("--claim", "transport_curvature_reductions")
    assert companion["paper"] is None
    assert companion["lean_source_identity"] == {
        **formal_source,
        "repository": claims_document["release"]["repository"],
    }
    assert query("--claim", "erdos_249")["paper"] is None

    adelic = query("--claim", "adelic_height_obstruction")
    assert adelic["claim"]["status"] == "proved here"
    assert "not an irrationality criterion" in adelic["claim"]["statement"]
    assert adelic["claim"]["declarations"][0]["module"] == (
        "Erdos249257/AdelicHeightObstruction.lean"
    )
    assert adelic["lean_source_identity"] == {
        **formal_source,
        "repository": claims_document["release"]["repository"],
    }

    square_crt_claim = query("--claim", "square_crt_correction_suppression")
    assert square_crt_claim["claim"]["status"] == "proved here"
    assert "neither an unbounded certificate family nor an irrationality criterion" in (
        square_crt_claim["claim"]["statement"]
    )
    assert square_crt_claim["claim"]["declarations"][0] == {
        "name": "exists_squareCRT_clean_totient_family",
        "module": "Erdos249257/SquareCRTCube.lean",
        "line": 297,
    }
    assert square_crt_claim["lean_source_identity"] == adelic["lean_source_identity"]

    signed_moment_claim = query("--claim", "signed_dyadic_moment_substrate")
    assert signed_moment_claim["claim"]["status"] == "proved here"
    assert "neither non-vanishing of the actual totient Hankel determinants" in (
        signed_moment_claim["claim"]["statement"]
    )
    assert signed_moment_claim["claim"]["declarations"][0] == {
        "name": "det_mul_rectangular",
        "module": "Erdos249257/SignedQMomentObstruction.lean",
        # Shifted by one when the module gained its MersenneLambertLadder import.
        "line": 29,
    }
    assert signed_moment_claim["lean_source_identity"] == square_crt_claim["lean_source_identity"]

    dyadic_totient_claim = query("--claim", "dyadic_totient_certificate_interface")
    assert dyadic_totient_claim["claim"]["status"] == "unconditional progress"
    assert "full dyadic kernel span is not finite-dimensional" in (
        dyadic_totient_claim["claim"]["statement"]
    )
    assert dyadic_totient_claim["claim"]["declarations"][0] == {
        "name": "exists_separatedMinorCertificate_totientAffineOddFamily",
        "module": "Erdos249257/TotientMahlerDefect.lean",
        "line": 882,
    }
    assert any(
        row["name"] == "not_finiteDimensional_span_fullTotientKernel"
        for row in dyadic_totient_claim["claim"]["declarations"]
    )
    assert dyadic_totient_claim["lean_source_identity"] == signed_moment_claim["lean_source_identity"]

    residual_gauge_claim = query("--claim", "residual_gauge_obstruction")
    assert residual_gauge_claim["claim"]["status"] == "proved here"
    assert "cannot exclude the target" in residual_gauge_claim["claim"]["statement"]
    assert residual_gauge_claim["claim"]["declarations"][0] == {
        "name": "det_residualMonomialMatrix_ne_zero_iff",
        "module": "Erdos249257/ResidualGaugeObstruction.lean",
        "line": 55,
    }
    assert residual_gauge_claim["lean_source_identity"] == dyadic_totient_claim["lean_source_identity"]
    residual_gauge_paper = query("--paper-label", "res:residualgauge")
    assert residual_gauge_paper["attachment_receipt"]["complete"] is True
    assert [row["declaration"] for row in residual_gauge_paper["source_links"]] == [
        "det_residualMonomialMatrix_ne_zero_iff",
        "locked_reconstruction_preserves_nonzero_minor",
        "rowReconstruction_zero_row_one",
    ]

    paper_label = query("--paper-label", "res:farey")
    assert paper_label["kind"] == "paper_label"
    assert paper_label["paper"] == claim["paper"]
    assert paper_label["attached_claims"][0]["id"] == "denominator_exclusion"
    assert paper_label["anchor_class"] == "registered_claim_anchor"
    assert any(
        row["source_ref"] == "Erdos249257/CertificateKernel.lean:18384"
        for row in paper_label["source_links"]
    )
    assert paper_label["lean_source_identity"] == adelic["lean_source_identity"]
    assert all(
        row["source_identity"] == paper_label["lean_source_identity"]
        for row in paper_label["source_links"]
    )
    shared_paper_label = query("--paper-label", "res:full")
    assert shared_paper_label["attachment_receipt"]["claim_count"] == 2
    assert {row["id"] for row in shared_paper_label["attached_claims"]} == {
        "eb_constant",
        "eb_full_support",
    }
    twenty_one_paper = query("--paper-label", "res:one-over-twenty-one-frontier")
    assert twenty_one_paper["paper"]["source"] == (
        "paper/erdos-257-mersenne-support-subseries.tex"
    )
    assert twenty_one_paper["anchor_class"] == "registered_claim_anchor"
    assert twenty_one_paper["attachment_receipt"] == {
        "claim_count": 1,
        "open_proposition_count": 0,
        "source_link_count": 6,
        "complete": True,
        "owners": [
            "paper/erdos-257-mersenne-support-subseries.tex",
            "docs/claims.json",
        ],
    }
    assert {
        row["declaration"] for row in twenty_one_paper["source_links"]
    } == {
        "twentyOneClosedRow_forces_quotientGreedy",
        "one_div_twenty_one_mem_iff_not_fatalAlignedBranch",
        "twentyOneAlignedSaturatedCrossing_forces_canonical_ancestor_hole",
        "twentyOneAlignedSaturatedCrossing_forces_scaled_greedy_skip",
        "twentyOneCofinalEvenQuotientGreedyDecay_of_closedRows",
        "twentyOneFatalAlignedBranch_eventually_affine_supercapacity",
    }
    local_result = query("--paper-anchor", "res:lift")
    assert local_result["anchor_class"] == "authored_formal_anchor_without_registered_claim"
    assert local_result["attachment_receipt"]["claim_count"] == 0
    assert local_result["source_links"][0]["macro"] == "lword"
    assert local_result["source_links"][0]["declaration"] == (
        "tsum_primWeight_div_two_pow_sub_one_eq_totient_series"
    )
    assert local_result["source_links"][0]["display_label"] == "Lambert representation"
    unlabelled_declaration = query(
        "--declaration", "tsum_moebius_div_two_pow_sub_one_eq_half"
    )["matches"]
    unlabelled_handle = next(
        anchor["canonical_handle"]
        for row in unlabelled_declaration
        if row["module"] == "Erdos249257/MersenneLambertLadder.lean"
        for anchor in row["paper_anchors"]
        if anchor["anchor_class"] == "authored_formal_anchor_without_registered_claim"
    )
    unlabelled_result = query("--paper-anchor", unlabelled_handle)
    assert unlabelled_result["paper"]["label"] is None
    assert unlabelled_result["anchor_class"] == (
        "authored_formal_anchor_without_registered_claim"
    )
    assert unlabelled_result["source_links"][0]["declaration"] == (
        "tsum_moebius_div_two_pow_sub_one_eq_half"
    )
    navigation_anchor = query("--paper-anchor", "sec:intro")
    assert navigation_anchor["anchor_class"] == "section_navigation_anchor"
    assert navigation_anchor["anchor_neighbourhood"]["previous"] is None
    assert query("--paper-anchor", "app:index")["anchor_neighbourhood"]["next"] is None
    unknown_paper_label = run("--paper-label", "prop:not-a-real-label")
    assert unknown_paper_label.returncode == 2
    assert "unknown paper label" in unknown_paper_label.stderr

    original_anchor_inventory = query_corpus.paper_anchor_inventory
    query_corpus.paper_anchor_inventory = lambda: [  # type: ignore[method-assign]
        {
            "canonical_handle": "ambiguous:anchor",
            "label": "ambiguous:anchor",
            "paper": {"source_ref": "paper/a.tex:10"},
        },
        {
            "canonical_handle": "ambiguous:anchor",
            "label": "ambiguous:anchor",
            "paper": {"source_ref": "paper/b.tex:20"},
        },
    ]
    try:
        try:
            paper_anchor_packet("ambiguous:anchor")
        except ValueError as error:
            assert "ambiguous paper anchor" in str(error)
            assert "paper/a.tex:10" in str(error)
            assert "paper/b.tex:20" in str(error)
        else:
            raise AssertionError("ambiguous paper anchor must not select an arbitrary match")
    finally:
        query_corpus.paper_anchor_inventory = original_anchor_inventory  # type: ignore[method-assign]

    open_expectations = {
        "remaining_open.erdos_249_irrationality": ("erdos_249", 1),
        "remaining_open.unbounded_certificate_supply": ("erdos_249", 10),
        "remaining_open.half_value_membership": ("universal_257", 5),
        "remaining_open.twenty_one_permanent_affine_supercapacity": (
            "universal_257",
            1,
        ),
        "remaining_open.universal_257_all_infinite_supports": ("universal_257", 6),
    }
    for open_id, (target, advancing_count) in open_expectations.items():
        open_packet = query("--open", open_id)
        assert open_packet["kind"] == "open_proposition"
        assert open_packet["status"] == "open"
        assert open_packet["open_target"]["id"] == target
        assert len(open_packet["advancing_claims"]) == advancing_count
        assert open_packet["paper_anchor"]["anchor_class"] == (
            "remaining_open_proposition_anchor"
        )
        reverse_open = query(
            "--paper-anchor", open_packet["paper_anchor"]["canonical_handle"]
        )
        assert [row["id"] for row in reverse_open["attached_open_propositions"]] == [
            open_id
        ]

    open_search = query("--search", "remaining_open.unbounded_certificate_supply", "--limit", "1")
    assert open_search["results"][0]["kind"] == "open_proposition"
    assert open_search["results"][0]["id"] == "remaining_open.unbounded_certificate_supply"

    declaration = query(
        "--declaration",
        "tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053",
    )
    assert declaration["match_count"] == 1
    assert declaration["matches"][0]["claim_ids"] == ["denominator_exclusion"]
    assert declaration["matches"][0]["source_ref"] == "Erdos249257/CertificateKernel.lean:18384"
    assert declaration["matches"][0]["source_url"].startswith(
        "https://github.com/wcook04/plectis-lean-erdos249-257/blob/"
        + formal_source["ref"]
        + "/"
    )
    assert declaration["matches"][0]["lean_source_identity"] == adelic["lean_source_identity"]
    assert declaration["matches"][0]["attached_claims"][0]["paper"]["label"] == "res:farey"
    assert "res:farey" in {
        row["canonical_handle"]
        for row in declaration["matches"][0]["paper_anchors"]
    }

    reduction_declaration = query(
        "--declaration", "irrational_totient_series_of_certificate_supply"
    )["matches"][0]
    assert reduction_declaration["source_ref"] == (
        "Erdos249257/TotientTailPeriodKiller.lean:394"
    )
    assert reduction_declaration["paper_sigil"] == "TotTaiPerKil"
    assert reduction_declaration["module_role"] == "Tail-period certificate reduction"
    assert reduction_declaration["attached_claims"][0]["paper"] == reduction["paper"]

    unlinked = query("--declaration", "totientTail_pos")["matches"][0]
    assert unlinked["attached_claims"] == []
    assert unlinked["route_memory"]["status"] == "unbound"
    assert unlinked["route_memory"]["bindings"] == []
    assert "no resume route was invented" in unlinked["route_memory"][
        "unbound_reason"
    ]

    local_declaration = query(
        "--declaration", "tsum_primWeight_div_two_pow_sub_one_eq_totient_series"
    )["matches"][0]
    assert local_declaration["attached_claims"] == []
    assert local_declaration["paper_anchors"][0]["canonical_handle"] == "res:lift"

    source_coordinate = query(
        "--source", "Erdos249257/CertificateKernel.lean:18383"
    )
    assert source_coordinate["kind"] == "source_coordinate"
    assert source_coordinate["source"]["source_url"].endswith(
        "/Erdos249257/CertificateKernel.lean#L18383"
    )
    assert source_coordinate["source"]["lean_source_identity"] == adelic["lean_source_identity"]
    source_declaration = source_coordinate["nearby_declarations"][0]
    assert source_declaration["name"] == (
        "tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053"
    )
    assert source_declaration["attached_claims"][0]["id"] == "denominator_exclusion"
    assert "res:farey" in {
        row["canonical_handle"] for row in source_declaration["paper_anchors"]
    }
    nondeclaration_source = query("--source", "Erdos249257/CertificateKernel.lean:1")
    assert nondeclaration_source["source"]["line"] == 1
    assert nondeclaration_source["coordinate_receipt"]["line_exists"] is True
    assert nondeclaration_source["coordinate_receipt"]["nearest_after"] is not None

    module_run = run("--module", "Erdos249257/CertificateKernel.lean")
    assert module_run.returncode == 0
    assert len(module_run.stdout.encode("utf-8")) <= 64_000
    module = json.loads(module_run.stdout)
    assert module["module"]["declaration_count"] > 400
    assert any(row["id"] == "eb_full_support" for row in module["attached_claims"])
    assert len(module["declaration_preview"]) == 12
    assert module["declaration_preview_receipt"]["omitted"] > 0
    assert module["declaration_preview_receipt"]["requested_limit"] == 20
    assert module["declaration_preview_receipt"]["effective_limit"] == 12
    assert "declaration_kind" in module["declaration_preview"][0]
    assert module["module"]["role"] == "Assembled theorem kernel and headline interfaces"
    neighbourhood = module["dependency_neighbourhood"]
    receipt = neighbourhood["receipt"]
    assert receipt["imports_total"] == len(module["module"]["imports"])
    assert receipt["importers_total"] >= 9
    assert len(neighbourhood["importers"]) == min(receipt["importers_total"], 12)
    assert receipt["importers_omitted"] == max(receipt["importers_total"] - 12, 0)
    assert receipt["requested_limit"] == 20
    assert receipt["effective_limit"] == 12

    certificate_hub = query("--module", "Erdos249257.DiagonalPincerCertificates")
    hub_neighbourhood = certificate_hub["dependency_neighbourhood"]
    hub_receipt = hub_neighbourhood["receipt"]
    assert hub_receipt["importers_total"] >= 483
    assert len(hub_neighbourhood["importers"]) == min(hub_receipt["importers_total"], 12)
    assert hub_receipt["importers_omitted"] == max(hub_receipt["importers_total"] - 12, 0)

    root = query("--module", "Erdos249257.lean", "--limit", "3")
    assert root["module"]["role"] == "Supported package root import"
    assert root["dependency_neighbourhood"]["receipt"]["importers_total"] == 0
    assert root["dependency_neighbourhood"]["receipt"]["imports_total"] > 3

    leaf = query("--module", "Erdos249257.GeneratedCertificates.b10_L6_A11", "--limit", "3")
    assert leaf["module"]["role"] == "Generated finite certificate shard"
    assert leaf["dependency_neighbourhood"]["imports"][0]["id"] == "Erdos249257.CertificateKernel"
    assert any(
        row["id"] == "Erdos249257.GeneratedCertificates"
        for row in leaf["dependency_neighbourhood"]["importers"]
    )

    square_crt = query("--module", "Erdos249257.SquareCRTCube", "--limit", "3")
    assert square_crt["module"]["role"] == (
        "Finite square-CRT correction-suppression mechanism"
    )
    assert square_crt["dependency_neighbourhood"]["receipt"]["imports_total"] == 0
    assert square_crt["dependency_neighbourhood"]["receipt"]["importers_total"] == 1

    signed_moment = query("--module", "Erdos249257.SignedQMomentObstruction", "--limit", "3")
    assert signed_moment["module"]["role"] == (
        "Finite signed-moment determinant and dyadic-parity substrate"
    )
    # This module was a leaf until the Mobius-Mersenne ladder (mobiusMersenneTerm,
    # Theta, the Hankel gap and the log-concavity chain) was published into it; that
    # body genuinely depends on Erdos249257.MersenneLambertLadder, so the single
    # import is a real edge and not a packaging artefact.
    assert signed_moment["dependency_neighbourhood"]["receipt"]["imports_total"] == 1
    assert signed_moment["dependency_neighbourhood"]["receipt"]["importers_total"] >= 1
    assert any(
        row["id"] == "Erdos249257"
        for row in signed_moment["dependency_neighbourhood"]["importers"]
    )

    totient_mahler = query("--module", "Erdos249257.TotientMahlerDefect", "--limit", "3")
    assert totient_mahler["module"]["role"] == (
        "Finite dyadic-totient rank and certificate interface"
    )
    assert totient_mahler["dependency_neighbourhood"]["receipt"]["imports_total"] == 0
    assert totient_mahler["dependency_neighbourhood"]["receipt"]["importers_total"] == 2

    aliases = json.loads((ROOT / "paper" / "module-aliases.json").read_text(encoding="utf-8"))
    assert aliases["alias_count"] == len(aliases["aliases"])
    assert len({row["sigil"] for row in aliases["aliases"]}) == aliases["alias_count"]
    for row in aliases["aliases"]:
        resolved = query("--module", row["sigil"], "--limit", "1")
        assert resolved["module"]["path"] == row["path"]
        assert resolved["paper_sigil"] == row["sigil"]

    sigil_search = query("--search", "CerKer", "--limit", "1")
    assert sigil_search["results"][0]["kind"] == "module"
    assert sigil_search["results"][0]["path"] == "Erdos249257/CertificateKernel.lean"

    anchor_search = query("--search", "Lambert representation", "--limit", "5")
    assert any(
        row["kind"] == "paper_anchor" and row["canonical_handle"] == "res:lift"
        for row in anchor_search["results"]
    )

    search = query("--search", " denominator_exclusion ", "--limit", "5")
    assert search["match_count"] >= 1
    assert search["results"][0]["kind"] == "claim"
    assert search["results"][0]["id"] == "denominator_exclusion"
    assert len(search["results"]) <= 5

    declaration_search = query("--search", "totientTail", "--limit", "1")
    assert declaration_search["results"][0]["kind"] == "declaration"
    assert declaration_search["results"][0]["declaration_kind"] in {
        "abbrev", "class", "def", "example", "instance", "lemma", "structure", "theorem"
    }

    connections = query(
        "--connections",
        "Erdos249257.GreedyAchievementSet",
        "--query",
        "reuse the greedy achievement interface downstream",
        "--limit",
        "6",
    )
    assert connections["kind"] == "connection_card"
    assert connections["schema_version"] == "lean-connection-card/2"
    assert connections["status"] == "source_current"
    assert connections["surface_contract"] == {
        "contract_id": "lean_connection_card",
        "projection_scope": "public_corpus",
        "disclosure_posture": "public_only",
        "equivalent_private_projection": "private_claim_local",
        "equivalence_boundary": (
            "same directional navigation grammar; independent source, claim, and proof authority"
        ),
    }
    assert connections["anchor"]["source_digest"].startswith("sha256:")
    assert "Erdos249257.CertificateKernel" in connections["relationship_direction"][
        "prerequisite_imports"
    ]
    assert any(
        row["module_id"] == "Erdos249257.DyadicPrefixCompression"
        for row in connections["relationship_direction"]["consumer_importers"]
    )
    assert connections["dependency_capsules"][0]["source_digest"].startswith("sha256:")
    assert all(
        row["source_digest"].startswith("sha256:")
        for row in connections["consumer_capsules"]
    )
    declaration_connections = query(
        "--connections", "mersenneWeightRat", "--limit", "4"
    )
    assert declaration_connections["anchor"]["handle_kind"] == "declaration"
    assert declaration_connections["declarations"][0]["name"] == (
        "mersenneWeightRat"
    )

    route = query("--route", "instant_orientation")
    assert route["route"]["read"][0] == "docs/orientation.json"
    assert "docs/claims.json" not in route["route"]["read"]
    assert route["route"]["query_steps"]
    assert route["route"]["authority_owners"]
    assert route["route"]["adjacent_handle_classes"]

    agent_route = query("--route", "agent_native_corpus_navigation")["route"]
    assert all(
        step.startswith("python3 scripts/query_corpus.py --")
        for step in agent_route["query_steps"]
    )
    assert {
        "scripts/query_semantic.py",
        "scripts/proof_workbench.py",
        "scripts/lean_fast_build.py",
    } == {
        step.split()[1] for step in agent_route["action_steps"]
    }
    assert any(
        "query_semantic.py population-backlog" in step
        for step in agent_route["action_steps"]
    )
    assert {"lean-toolchain", "lakefile.toml"}.issubset(
        agent_route["authority_owners"]
    )

    unknown = run("--claim", "does_not_exist")
    assert unknown.returncode == 2
    assert "unknown claim id" in unknown.stderr

    unknown_open = run("--open", "remaining_open.does_not_exist")
    assert unknown_open.returncode == 2
    assert "unknown remaining-open proposition id" in unknown_open.stderr

    unknown_source = run("--source", "Erdos249257/NotAModule.lean:1")
    assert unknown_source.returncode == 2
    assert "unknown Lean source module" in unknown_source.stderr

    invalid_source_line = run("--source", "Erdos249257/CertificateKernel.lean:999999")
    assert invalid_source_line.returncode == 2
    assert "exceeds" in invalid_source_line.stderr

    source_link_count = 0
    for anchor in paper_anchor_inventory():
        for link in anchor["source_links"]:
            source_link_count += 1
            packet = source_coordinate_packet(link["source_ref"], 20)
            assert packet["coordinate_receipt"]["line_exists"] is True
            names = {row["name"] for row in packet["nearby_declarations"]}
            if link["declaration"]:
                assert link["declaration"] in names
            reverse_anchors = {
                paper_anchor["canonical_handle"]
                for row in packet["nearby_declarations"]
                for paper_anchor in row["paper_anchors"]
            }
            assert anchor["canonical_handle"] in reverse_anchors
    assert source_link_count > 100

    descriptor = json.loads(
        (ROOT / "docs" / "corpus_descriptor.json").read_text(encoding="utf-8")
    )
    claims_identity = descriptor["identity"]["content"]["claims_document"]
    claims_artifact = query("--artifact", "docs/claims.json")
    assert claims_artifact["matches"][0]["artifact_id"] == "claims_document"
    assert claims_artifact["matches"][0]["content_digest"] == claims_identity["content_digest"]
    claims_by_digest = query("--artifact", claims_identity["content_digest"])
    assert claims_by_digest["matches"][0]["artifact_handle"] == "docs/claims.json"
    machine_paper_artifact = query(
        "--artifact", "docs/claims.json::machine_readable_paper"
    )
    assert machine_paper_artifact["matches"][0]["artifact_kind"] == "json_fragment"
    exposition_artifact = query("--artifact", "erdos249-257-main-paper.pdf")
    assert exposition_artifact["matches"][0]["artifact_kind"] == (
        "authored_paper_rendered"
    )
    artifact_search = query("--search", claims_identity["content_digest"], "--limit", "1")
    assert artifact_search["results"][0]["kind"] == "artifact"

    unknown_artifact = run("--artifact", "sha256:" + "0" * 64)
    assert unknown_artifact.returncode == 2
    assert "unknown registered artifact" in unknown_artifact.stderr

    # Exhaustive populated-owner closure matrix. These assertions are derived
    # from the current owners, so corpus growth creates a failing orphan instead
    # of requiring a hand-maintained count or specimen list.
    closure_checks = 0
    for claim_row in claims_document["claims"]:
        claim_view = claim_packet(claim_row["id"])
        closure_checks += 1
        assert claim_view["claim"]["id"] == claim_row["id"]
        assert claim_view["lean_source_identity"] == lean_source_identity_for_paper(
            claims_document,
            claim_view["paper"]["source"] if claim_view["paper"] else None,
        )
        if claim_row.get("paper_label"):
            paper_view = paper_anchor_packet(claim_row["paper_label"])
            closure_checks += 1
            assert claim_row["id"] in {
                row["id"] for row in paper_view["attached_claims"]
            }
        for declaration_row in claim_row["declarations"]:
            declaration_view = declaration_packet(declaration_row["name"], 100)
            closure_checks += 1
            exact_rows = [
                row
                for row in declaration_view["matches"]
                if row["module"] == declaration_row["module"]
                and row["line"] == declaration_row["line"]
            ]
            assert len(exact_rows) == 1
            assert claim_row["id"] in exact_rows[0]["claim_ids"]

    for open_row in claims_document["remaining_open_propositions"]:
        open_view = open_proposition_packet(open_row["id"])
        closure_checks += 1
        assert open_view["paper_anchor"] is not None
        assert open_view["paper_anchor"]["anchor_class"] == (
            "remaining_open_proposition_anchor"
        )

    for anchor_row in paper_anchor_inventory():
        anchor_view = paper_anchor_packet(anchor_row["canonical_handle"])
        closure_checks += 1
        assert anchor_view["anchor_class"] == anchor_row["anchor_class"]
        assert anchor_view["lean_source_identity"] == anchor_row["paper"]["lean_source_identity"]
        assert all(
            link["source_identity"] == anchor_view["lean_source_identity"]
            for link in anchor_view["source_links"]
        )

    for artifact_row in artifact_inventory():
        for handle in (artifact_row["artifact_handle"], artifact_row["content_digest"]):
            artifact_view = artifact_packet(handle)
            closure_checks += 1
            assert artifact_row["artifact_handle"] in {
                row["artifact_handle"] for row in artifact_view["matches"]
            }

    orientation_document = load("docs/orientation.json")
    for route_row in orientation_document["reading_routes"]:
        route_view = route_packet(route_row["id"])
        closure_checks += 1
        assert route_view["route"]["id"] == route_row["id"]
        assert sum((ROOT / path).stat().st_size for path in route_row["read"]) <= 48_000

    assert closure_checks > 150

    invalid_limit = run("--search", "totient", "--limit", "101")
    assert invalid_limit.returncode == 2
    assert "--limit must be between 1 and 100" in invalid_limit.stderr

    print(
        "test_query_corpus: bounded lookup and exhaustive populated-owner closure "
        f"passed ({closure_checks} closure checks)"
    )
    return 0


if __name__ == "__main__":
    if sys.argv[1:] == ["--programme-routes-only"]:
        validate_programme_routes()
        validate_agent_tour()
        validate_paper_guide()
        validate_natural_language_search()
        print(
            "test_query_corpus: "
            f"{len(PROGRAMME_EXPECTATIONS)} mathematical programme routes and "
            "natural-language discovery queries passed"
        )
        raise SystemExit(0)
    if sys.argv[1:]:
        raise SystemExit(
            "usage: python3 scripts/test_query_corpus.py "
            "[--programme-routes-only]"
        )
    raise SystemExit(main())
