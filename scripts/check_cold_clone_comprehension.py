#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Verify bounded first-contact comprehension in a fresh public checkout.

This evaluator deliberately does *not* concatenate the exhaustive claim,
methodology, or declaration owners.  A cold reader starts from the compact
human surfaces; a coding agent starts from the bounded corpus query and then
follows typed packets.  The authoritative owners remain available as explicit
expansions, but are not evidence for first-contact comprehension.

This checks navigation semantics and response budgets, not Lean proof
correctness.  The pinned Lean source checked by the kernel remains proof
authority.
"""

from __future__ import annotations

import argparse
import copy
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
QUERY = ROOT / "scripts" / "query_corpus.py"
HUMAN_SURFACES = ("README.md", "SCOPE.md", "docs/ORIENTATION.md")
HUMAN_SURFACE_BUDGET_BYTES = {
    "README.md": 12_000,
    "SCOPE.md": 4_000,
    "docs/ORIENTATION.md": 16_000,
}
README_FIRST_CONTACT_BUDGET_BYTES = 12_000
SUMMARY_PACKET_BUDGET_BYTES = 32_256
PACKET_BUDGET_BYTES = 16_384
PROOF_AUTHORITY = "Lean source checked by the pinned Lean kernel"
SELF_APPRAISAL_PHRASES = (
    "ambitious",
    "crazy good",
    "exceptional",
    "extraordinary",
    "groundbreaking",
    "impressive",
    "insane",
    "major achievement",
    "research-grade",
    "unprecedented",
)
GATEWAY_PAPER = "paper/erdos249-257-main-paper.tex"
# The slice includes the introduction and both exact proof spines through page 3.
GATEWAY_OPENING_BUDGET_BYTES = 12_000
CLAUDE_ENTRY_BUDGET_BYTES = 1_500
STORY_ROUTES = (
    "erdos257_half_story",
    "erdos249_certificate_story",
    "structured_support_families",
    "erdos249_diagonal_arithmetic",
    "boolean_mobius_constraints",
    "transport_curvature_programme",
    "lambert_obstruction_interfaces",
    "probabilistic_gcd_geometry",
    "half_carry_compactness_programme",
    "arithmetic_obstruction_interfaces",
)
STORY_CLAIMS = (
    "greedy_achievement_geometry",
    "half_greedy_two_thirds_band",
    "half_membership_seam_classification",
    "fatal_gap_right_tail_classification",
    "final_middle_cell_escape",
    "final_middle_neg_two_phase_sieve",
    "last_producer_tail_escape_reduction",
    "certificate_reduction",
    "certificate_completeness",
    "first_harmonic_certificate_interface",
    "first_harmonic_pivot_decomposition",
)
DISCOVERY_ROUTE_QUERIES = {
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
    "what is still missing": "understand_methodology_and_open_boundary",
    "what remains open": "understand_methodology_and_open_boundary",
}
DISCOVERY_MULTI_ROUTE_QUERIES = {
    "what is ruled out": {
        "transport_curvature_programme",
        "lambert_obstruction_interfaces",
        "arithmetic_obstruction_interfaces",
    }
}
PROOF_PLAN_QUERIES = {
    "blocked_integer_tail": (
        "I need to prove totientTail (N + h) - totientTail N is an integer "
        "from a rational totient series; which theorem applies?"
    ),
    "context_ready_curvature": (
        "I need to prove Irrational (∑' n : ℕ, "
        "(Nat.totient n : ℝ) / 2 ^ n) from a SharpCurvatureSupply"
    ),
}


def read(rel: str) -> str:
    return (ROOT / rel).read_text(encoding="utf-8")


def quick_summary() -> dict[str, Any]:
    """Load the committed bounded projection without spawning corpus queries."""
    orientation = json.loads(read("docs/orientation.json"))
    return {
        "remaining_open_propositions": orientation["remaining_open_propositions"],
        "status_taxonomy": orientation["status_taxonomy"],
        "mathematical_programmes": orientation["mathematical_programmes"],
    }


def encoded_bytes(value: Any) -> int:
    return len(json.dumps(value, ensure_ascii=False, sort_keys=True).encode("utf-8"))


def query_packet(*args: str, budget_bytes: int = PACKET_BUDGET_BYTES) -> dict[str, Any]:
    """Run the public CLI exactly as a cold coding agent would."""
    completed = subprocess.run(
        [sys.executable, str(QUERY), *args],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        raise AssertionError(completed.stdout.strip() or completed.stderr.strip())
    raw = completed.stdout.encode("utf-8")
    assert len(raw) <= budget_bytes, (
        f"query {' '.join(args) or '<summary>'} emitted {len(raw)} bytes "
        f"(budget {budget_bytes})"
    )
    return json.loads(completed.stdout)


def human_tasks(summary: dict[str, Any]) -> dict[str, list[list[str]]]:
    """Facts a reader must recover from the bounded README first contact.

    Each task contains conjunctions of semantic anchor groups.  Alternatives
    within one group permit harmless wording changes; satisfying one task with
    tokens scattered across three documents is deliberately impossible.
    """
    open_rows = {row["id"]: row for row in summary["remaining_open_propositions"]}
    return {
        "identity_and_public_boundary": [
            ["self-contained public"],
            ["Plectis"],
            ["not an entrypoint into any private development system"],
        ],
        "state_both_problems": [
            ["Erdős #249 asks whether"],
            ["S = ∑ φ(n)/2ⁿ"],
            ["Erdős #257 asks whether"],
            ["∑_{n∈A} 1/(2ⁿ - 1)"],
            ["every infinite", "for every infinite"],
        ],
        "distinguish_release_source_and_authority": [
            ["latest tagged release and citation anchor"],
            ["formal-source checkpoint"],
            ["not a new tagged release"],
            [PROOF_AUTHORITY],
        ],
        "recover_headline_statuses": [
            ["formalised here"],
            ["unconditional progress"],
            ["conditional reduction"],
            ["verified finite instance"],
            ["does not show that the actual orbit avoids", "does not show the actual orbit avoids"],
            ["does not prove successful cases beyond every fixed cutoff"],
        ],
        "recover_breadth_beyond_headlines": [
            ["eventually-periodic nonnegative weighted irrationality"],
            ["signed irrational-or-base-terminating dichotomy"],
            [
                "five binary-carry criteria/consequences",
                "five binary-carry criteria or consequences",
            ],
            ["two scoped #249 no-go countermodels"],
        ],
        "recover_independent_exact_packages": [
            ["fair-coin coprimality", "P(gcd(X,Y)=1)"],
            ["squared-Lambert gcd moments"],
            ["Stern–Brocot cylinder law"],
            ["(2/3)^d"],
            ["Fibonacci/continuant run stability"],
            ["F_{r+3}"],
            ["tempered binary tail rigidity"],
            ["exact Möbius-shadow denominator"],
            ["scalar-localisation height obstruction"],
        ],
        "recover_scale_and_assembly": [
            ["Lean modules"],
            ["Formal results and supporting lemmas"],
            ["Curated claim records"],
            ["Contribution families"],
            ["navigation counts, not novelty claims"],
        ],
        "name_exact_open_frontier": [
            [open_rows["remaining_open.erdos_249_irrationality"]["statement"],
             "Prove that `S = ∑ φ(n)/2ⁿ` is irrational"],
            [open_rows["remaining_open.unbounded_certificate_supply"]["statement"],
             "Produce the unbounded certificate supply"],
            [open_rows["remaining_open.universal_257_all_infinite_supports"]["statement"],
             "Prove irrationality of `∑_{n∈A} 1/(2ⁿ - 1)` for every infinite"],
        ],
        "choose_a_next_read": [
            ["Exposition PDF"],
            ["AGENTS.md"],
            ["docs/orientation.json"],
            ["docs/SOURCE_MAP.md"],
        ],
    }


def first_bytes(text: str, limit: int) -> str:
    return text.encode("utf-8")[:limit].decode("utf-8", errors="ignore")


def normalized(text: str) -> str:
    return " ".join(text.split())


def contains_any(text: str, alternatives: list[str]) -> bool:
    compact = normalized(text).casefold()
    return any(normalized(token).casefold() in compact for token in alternatives)


def validate_human_first_contact(
    summary: dict[str, Any], surfaces: dict[str, str]
) -> None:
    assert set(surfaces) == set(HUMAN_SURFACES)
    for path, budget in HUMAN_SURFACE_BUDGET_BYTES.items():
        size = len(surfaces[path].encode("utf-8"))
        assert size <= budget, f"{path} is {size} bytes (budget {budget})"
        lowered = normalized(surfaces[path]).casefold()
        for phrase in SELF_APPRAISAL_PHRASES:
            assert phrase not in lowered, (
                f"{path} uses self-appraisal phrase {phrase!r}; expose objective "
                "mathematical and formal facts instead"
            )

    readme_prefix = first_bytes(surfaces["README.md"], README_FIRST_CONTACT_BUDGET_BYTES)
    section_order = (
        "## The two problems",
        "## What the formal source establishes",
        "## What remains open",
        "## Read or run it",
    )
    positions = [readme_prefix.find(heading) for heading in section_order]
    assert all(position >= 0 for position in positions), (
        f"README first-contact surface lost section sequence {section_order}"
    )
    assert positions == sorted(positions), "README first-contact sections are out of order"

    for task_id, requirements in human_tasks(summary).items():
        for alternatives in requirements:
            assert contains_any(readme_prefix, alternatives), (
                f"README first-contact task {task_id!r} lost semantic anchor group "
                f"{alternatives}"
            )

    scope = surfaces["SCOPE.md"]
    assert contains_any(scope, ["does not prove"])
    assert contains_any(scope, ["formal-source checkpoint"])
    orientation = surfaces["docs/ORIENTATION.md"]
    for status in (
        "formalised here",
        "unconditional progress",
        "conditional reduction",
        "verified finite instance",
    ):
        assert contains_any(orientation, [summary["status_taxonomy"][status]])
    for row in summary["remaining_open_propositions"]:
        assert row["id"] in orientation and contains_any(orientation, [row["statement"]])
    for programme in summary["mathematical_programmes"]:
        assert programme["id"] in orientation
        assert contains_any(orientation, [programme["title"]])
        assert contains_any(orientation, [programme["claim_ceiling"]])


def validate_gateway_opening(paper: str) -> None:
    """Check that the authored introduction works without source inventory."""
    start = paper.index(r"\section{Introduction}")
    end = paper.index(r"\section{The Mersenne--Lambert ladder}")
    opening = paper[start:end]
    visible_opening = re.sub(
        r"\\lword\{[^{}]*\}\{[^{}]*\}\{[^{}]*\}\{([^{}]*)\}",
        r"\1",
        opening,
    )
    visible_opening = re.sub(
        r"\\(?:lref|lrefx)\{[^{}]*\}\{[^{}]*\}\{([^{}]*)\}",
        lambda match: re.sub(
            r"(?<=[a-z0-9])(?=[A-Z])",
            " ",
            match.group(1).replace("_", " "),
        ).lower(),
        visible_opening,
    )
    visible_opening = re.sub(
        r"\\lloc\{[^{}]*\}\{[^{}]*\}",
        "Lean source",
        visible_opening,
    )
    size = len(visible_opening.encode("utf-8"))
    assert size <= GATEWAY_OPENING_BUDGET_BYTES, (
        f"visible gateway introduction is {size} bytes "
        f"(budget {GATEWAY_OPENING_BUDGET_BYTES})"
    )
    requirements = {
        "both_problem_statements": [
            [r"is irrational (\#249)"],
            [r"for every infinite $A\subseteq\Npos$ (\#257)"],
        ],
        "status_table": [
            [r"Irrationality in \#249 & Open"],
            [r"Denominator exclusion & Proved"],
            [r"q>\Qzero"],
            ["28 diagonal certificates"],
            [r"Universal assertion in \#257 & Open"],
            ["Classical/formalised"],
            ["Open; exact reductions"],
        ],
        "exact_residuals": [
            ["An unbounded certificate supply"],
            ["cofinal terminal zeros"],
            ["two final-skip obligations"],
        ],
        "common_architecture": [
            ["tail and carry identities separate exact finite arithmetic"],
            ["one analytic or combinatorial cofinality statement"],
        ],
        "reading_map": [
            [r"\paragraph{Reading map.}"],
            [r"Section~\ref{sec:spines}"],
            [r"Section~\ref{sec:ladder}"],
            [r"Sections~\ref{sec:eb}"],
            [r"and~\ref{sec:249}"],
        ],
    }
    for task_id, groups in requirements.items():
        for alternatives in groups:
            assert contains_any(opening, alternatives), (
                f"gateway opening task {task_id!r} lost {alternatives}"
            )
    for source_inventory_token in (r"\idn", "module inventory"):
        assert source_inventory_token not in opening, (
            f"gateway opening exposes source-inventory token {source_inventory_token!r}"
        )


def validate_cross_agent_entry(agents: str, claude: str) -> None:
    """Keep one shared semantic core with a small Claude-native adapter."""
    assert len(claude.encode("utf-8")) <= CLAUDE_ENTRY_BUDGET_BYTES
    for path, text in (("AGENTS.md", agents), ("CLAUDE.md", claude)):
        lowered = normalized(text).casefold()
        for phrase in SELF_APPRAISAL_PHRASES:
            assert phrase not in lowered, (
                f"{path} uses self-appraisal phrase {phrase!r}; route to objective "
                "claims, scale, and verification receipts instead"
            )
    for token in (
        "docs/orientation.json",
        "docs/claims.json",
        "Lean source checked by the pinned Lean kernel",
        "not an entrypoint into any private development system",
    ):
        assert contains_any(agents, [token]), f"AGENTS.md lost shared invariant {token!r}"
    for token in (
        "@AGENTS.md",
        "Claude-specific deltas only",
        "docs/orientation.json",
        "mathematical programme",
        "larger ongoing formal-mathematics workflow",
        "not an entrypoint into any private development system",
    ):
        assert contains_any(claude, [token]), f"CLAUDE.md lost native adapter token {token!r}"
    assert "## First read" not in claude, "CLAUDE.md duplicated the shared first-read manual"


def collect_proof_plan_packets() -> dict[str, Any]:
    """Exercise the bounded hypothesis-aware path used by a cold coding agent."""
    return {
        "blocked_integer_tail": query_packet(
            "--proof-plan",
            PROOF_PLAN_QUERIES["blocked_integer_tail"],
            "--depth",
            "2",
            "--limit",
            "8",
        ),
        "context_ready_curvature": query_packet(
            "--proof-plan",
            PROOF_PLAN_QUERIES["context_ready_curvature"],
            "--depth",
            "1",
            "--limit",
            "8",
        ),
    }


def collect_agent_packets() -> dict[str, Any]:
    """Collect only bounded query replies needed to walk the public graph."""
    summary = query_packet(budget_bytes=SUMMARY_PACKET_BUDGET_BYTES)
    publication_architecture = query_packet("--publication-architecture")
    packets: dict[str, Any] = {
        "summary": summary,
        "opens": {},
        "claims": {},
        "papers": {},
        "declarations": {},
        "sources": {},
        "modules": {},
        "sigil_modules": {},
        "route": query_packet("--route", "instant_orientation"),
        "publication_architecture": publication_architecture,
        "publication_families": {
            row["id"]: query_packet("--publication-family", row["id"])
            for row in publication_architecture["family_index"]
        },
        "claim_statuses": {
            status: query_packet("--status", status, "--limit", "12")
            for status in summary["status_taxonomy"]
        },
        "story_routes": {
            route_id: query_packet("--route", route_id) for route_id in STORY_ROUTES
        },
        "discovery_searches": {
            search_text: query_packet("--search", search_text, "--limit", "10")
            for search_text in DISCOVERY_ROUTE_QUERIES
        },
        "discovery_multi_searches": {
            search_text: query_packet("--search", search_text, "--limit", "10")
            for search_text in DISCOVERY_MULTI_ROUTE_QUERIES
        },
        "proof_plans": collect_proof_plan_packets(),
        "story_claims": {
            claim_id: query_packet("--claim", claim_id) for claim_id in STORY_CLAIMS
        },
    }
    for row in summary["remaining_open_propositions"]:
        packets["opens"][row["id"]] = query_packet("--open", row["id"])
    for row in summary["principal_claims"]:
        claim_id = row["id"]
        claim = query_packet("--claim", claim_id)
        packets["claims"][claim_id] = claim
        paper_label = claim["claim"].get("paper_label")
        if paper_label:
            packets["papers"][paper_label] = query_packet("--paper-label", paper_label)
        for declaration in claim["claim"]["declarations"][:1]:
            key = f"{declaration['module']}:{declaration['line']}"
            packets["declarations"][key] = query_packet(
                "--declaration", declaration["name"]
            )
            packets["sources"][key] = query_packet("--source", key)
            module = query_packet("--module", declaration["module"])
            packets["modules"][declaration["module"]] = module
            sigil = module.get("paper_sigil")
            if sigil:
                packets["sigil_modules"][sigil] = query_packet("--module", sigil)
    artifact = query_packet("--artifact", "docs/orientation.json")
    packets["artifact"] = artifact
    digest = artifact["matches"][0]["content_digest"]
    packets["artifact_digest"] = query_packet("--artifact", digest)
    return packets


def validate_proof_plan_packets(proof_plans: dict[str, Any]) -> None:
    """Validate application boundaries and exact spines independently."""
    blocked = proof_plans["blocked_integer_tail"]
    assert blocked["kind"] == "formal_proof_plan"
    assert blocked["availability"] == "available"
    assert blocked["terminal_candidate"]["name"] == "tail_diff_int_of_den_dvd"
    assert blocked["plan_status"] == (
        "blocked_by_unmatched_proposition_obligations"
    )
    assert {
        row["name"]
        for row in blocked["application"]["obligations"]
        if row["status"] == "unmatched_proposition_obligation"
    } == {"hdvd"}
    assert blocked["application"]["authority_posture"] == (
        "binder_roles_and_type_shapes_from_elaborated_Lean_context_"
        "matching_is_lexical_navigation_not_local_context_unification"
    )
    assert encoded_bytes(blocked) <= PACKET_BUDGET_BYTES

    ready = proof_plans["context_ready_curvature"]
    assert ready["kind"] == "formal_proof_plan"
    assert ready["availability"] == "available"
    assert ready["terminal_candidate"]["name"] == (
        "irrational_totientSeries_of_sharpCurvatureSupply"
    )
    assert ready["plan_status"] == (
        "all_proposition_obligations_have_context_matches"
    )
    assert ready["application"]["unmatched_proposition_count"] == 0
    assert {
        row["name"] for row in ready["exact_dependency_spine"]["steps"]
    } >= {
        "curvature_notMem_int_of_sharpCurvatureCert",
        "periodLcm_pos",
        "rational_totient_series_forces_lcm_cone_flatness",
    }
    assert ready["exact_dependency_spine"]["edge_policy"] == (
        "elaborated_value_references_only"
    )
    assert encoded_bytes(ready) <= PACKET_BUDGET_BYTES


def validate_agent_packets(packets: dict[str, Any]) -> None:
    summary = packets["summary"]
    assert summary["kind"] == "corpus_summary"
    assert summary["authority_posture"] == "navigation_projection_not_proof_authority"
    assert summary["proof_authority"] == PROOF_AUTHORITY
    assert summary["release_provenance"]["posture"] == (
        "self_contained_public_projection_from_a_larger_ongoing_research_workflow"
    )
    assert "does not imply hidden proof authority" in (
        summary["release_provenance"]["boundary"]
    )
    assert encoded_bytes(summary) <= SUMMARY_PACKET_BUDGET_BYTES
    assert summary["remaining_open_propositions"]
    assert summary["scale"]["theorem_like_count"] > (
        summary["scale"]["generated_certificate_declaration_count"]
    )
    assert summary["curated_claim_count"] >= len(summary["principal_claims"])
    assert summary["publication_family_count"] > 0
    assert len(summary["mathematical_programmes"]) == len(STORY_ROUTES)

    validate_proof_plan_packets(packets["proof_plans"])

    architecture = packets["publication_architecture"]
    assert architecture["kind"] == "publication_architecture"
    assert architecture["authority_posture"] == (
        "authored_editorial_topology_not_proof_authority"
    )
    assert len(architecture["family_index"]) == summary["publication_family_count"]
    assert set(packets["publication_families"]) == {
        row["id"] for row in architecture["family_index"]
    }
    for family_id, packet in packets["publication_families"].items():
        assert packet["kind"] == "publication_family"
        assert packet["family"]["id"] == family_id
        assert packet["claims"]
        assert packet["status_counts"]
        assert packet["family"]["primary_narrative_owner"]
        assert packet["family"]["consumer_or_open_obligation"]
        assert packet["family"]["view_decision"]
        assert encoded_bytes(packet) <= PACKET_BUDGET_BYTES

    assert set(packets["claim_statuses"]) == set(summary["status_taxonomy"])
    for status, packet in packets["claim_statuses"].items():
        assert packet["kind"] == "claim_status"
        assert packet["authority_posture"] == (
            "claim_registry_status_navigation_not_proof_authority"
        )
        assert packet["status"] == status
        assert packet["meaning"] == summary["status_taxonomy"][status]
        assert packet["claim_count"] >= len(packet["claims"]) > 0
        assert packet["omitted_claim_count"] == (
            packet["claim_count"] - len(packet["claims"])
        )
        assert all(row["status"] == status for row in packet["claims"])
        assert all(row["statement_excerpt"] for row in packet["claims"])
        if status == "conditional reduction":
            assert all(
                row.get("remaining_open_proposition_ids")
                for row in packet["claims"]
            )
        if status == "verified finite instance":
            assert all(row.get("bounded_domain") for row in packet["claims"])
        if status == "open":
            assert {row["id"] for row in packet["claims"]} == {
                "erdos_249",
                "universal_257",
            }
            assert {
                row["id"] for row in packet["remaining_open_propositions"]
            } == {
                row["id"] for row in summary["remaining_open_propositions"]
            }
        else:
            assert packet["remaining_open_propositions"] == []
        assert encoded_bytes(packet) <= PACKET_BUDGET_BYTES

    principal = {row["id"]: row for row in summary["principal_claims"]}
    assert any(row["status"] == "conditional reduction" for row in principal.values())
    assert any(row["status"] == "verified finite instance" for row in principal.values())

    for open_id, packet in packets["opens"].items():
        proposition = packet["open_proposition"]
        assert proposition["id"] == open_id
        assert packet["authority_posture"] == "authored_open_boundary_navigation_not_proof_authority"
        assert proposition["paper_anchor"] is not None
        assert packet["open_target"]["status"] == "open"

    for claim_id, packet in packets["claims"].items():
        claim = packet["claim"]
        assert claim["id"] == claim_id
        assert claim["status"] == principal[claim_id]["status"]
        assert packet["authority_posture"] == "navigation_projection_not_proof_authority"
        if claim["status"] == "conditional reduction":
            assert claim["remaining_open_proposition_ids"]
        if claim["status"] == "verified finite instance":
            assert claim.get("bounded_domain")
        paper_label = claim.get("paper_label")
        if paper_label:
            assert paper_label in packets["papers"]
            assert packets["papers"][paper_label]["paper"]["label"] == paper_label
        for declaration in claim["declarations"][:1]:
            key = f"{declaration['module']}:{declaration['line']}"
            exact = [
                row
                for row in packets["declarations"][key]["matches"]
                if row["module"] == declaration["module"] and row["line"] == declaration["line"]
            ]
            assert len(exact) == 1
            source = packets["sources"][key]["source"]
            assert source["source_ref"] == key
            module = packets["modules"][declaration["module"]]
            assert module["module"]["path"] == declaration["module"]
            sigil = module.get("paper_sigil")
            if sigil:
                assert packets["sigil_modules"][sigil]["module"]["path"] == declaration["module"]

    artifact = packets["artifact"]["matches"]
    digest_matches = packets["artifact_digest"]["matches"]
    assert artifact and digest_matches
    assert artifact[0]["artifact_handle"] in {
        row["artifact_handle"] for row in digest_matches
    }
    assert packets["route"]["route"]["id"] == "instant_orientation"
    assert packets["route"]["proof_authority"] == PROOF_AUTHORITY
    route = packets["route"]["route"]
    assert "docs/claims.json" not in route["read"]
    assert route["query_steps"]
    assert "python3 scripts/query_corpus.py --publication-architecture" in (
        route["query_steps"]
    )
    assert route["authority_owners"]
    assert route["adjacent_handle_classes"]

    story_routes = packets["story_routes"]
    assert tuple(story_routes) == STORY_ROUTES
    summary_programmes = {
        row["id"]: row for row in summary["mathematical_programmes"]
    }
    assert set(summary_programmes) == set(STORY_ROUTES)
    for route_id, packet in story_routes.items():
        route = packet["route"]
        programme = packet["programme"]
        assert route["route_kind"] == "mathematical_programme"
        assert route["id"] == route_id
        assert programme["title"] == summary_programmes[route_id]["title"]
        assert programme["core_claims"]
        assert summary_programmes[route_id]["core_claim_count"] == len(
            programme["core_claims"]
        )
        assert set(summary_programmes[route_id]["representative_claim_ids"]).issubset(
            {row["id"] for row in programme["core_claims"]}
        )
        assert programme["problem_targets"]
        assert all(row["status"] == "open" for row in programme["problem_targets"])
        assert programme["remaining_open_propositions"]
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
        assert {
            step.rsplit(" ", 1)[-1]
            for step in route["query_steps"]
            if " --claim " in step
        } == {row["id"] for row in programme["core_claims"]}
        assert {
            step.rsplit(" ", 1)[-1]
            for step in route["query_steps"]
            if " --open " in step
        } == {
            row["id"] for row in programme["remaining_open_propositions"]
        }
        assert packet["release_provenance"] == summary["release_provenance"]
    for search_text, expected_route_id in DISCOVERY_ROUTE_QUERIES.items():
        search_packet = packets["discovery_searches"][search_text]
        assert search_packet["kind"] == "search"
        assert search_packet["query"] == search_text
        assert search_packet["results"]
        assert search_packet["results"][0]["kind"] == "reading_route"
        assert search_packet["results"][0]["id"] == expected_route_id
    for search_text, expected_route_ids in DISCOVERY_MULTI_ROUTE_QUERIES.items():
        search_packet = packets["discovery_multi_searches"][search_text]
        assert search_packet["kind"] == "search"
        assert search_packet["query"] == search_text
        assert {
            row["id"]
            for row in search_packet["results"]
            if row["kind"] == "reading_route"
        } >= expected_route_ids
    portfolio_results = packets["discovery_searches"][
        "what other exact mathematics is there"
    ]["results"]
    assert portfolio_results[0]["kind"] == "reading_route"
    assert portfolio_results[0]["id"] == "instant_orientation"
    assert [
        step.rsplit(" ", 1)[-1]
        for step in story_routes["erdos257_half_story"]["route"]["query_steps"]
    ] == [
        *STORY_CLAIMS[:7],
        "remaining_open.half_value_membership",
        "remaining_open.universal_257_all_infinite_supports",
    ]
    assert [
        step.rsplit(" ", 1)[-1]
        for step in story_routes["erdos249_certificate_story"]["route"]["query_steps"]
    ] == [
        "denominator_exclusion",
        "certificate_reduction",
        "certificate_completeness",
        "certified_kill_instances",
        "first_harmonic_certificate_interface",
        "first_harmonic_pivot_decomposition",
        "remaining_open.erdos_249_irrationality",
        "remaining_open.unbounded_certificate_supply",
    ]

    story_claims = packets["story_claims"]
    band_claim = story_claims["half_greedy_two_thirds_band"]
    assert ("builds_on", "greedy_achievement_geometry") in {
        (row["relation"], row["neighbour"]["id"])
        for row in band_claim["argument_neighbourhood"]["outgoing"]
    }
    assert (
        "no theorem here says that the actual greedy orbit for 1/2 avoids a band"
        in band_claim["claim"]["statement"]
    )
    half_membership = story_claims["half_membership_seam_classification"]
    assert {
        (row["relation"], row["neighbour"]["id"])
        for row in half_membership["argument_neighbourhood"]["outgoing"]
    } >= {
        ("builds_on", "greedy_achievement_geometry"),
        ("builds_on", "fatal_gap_right_tail_classification"),
    }
    last_producer = story_claims["last_producer_tail_escape_reduction"]
    assert ("eliminates_case", "final_middle_cell_escape") in {
        (row["relation"], row["neighbour"]["id"])
        for row in last_producer["argument_neighbourhood"]["incoming"]
    }
    assert ("builds_on", "fatal_gap_right_tail_classification") in {
        (row["relation"], row["neighbour"]["id"])
        for row in last_producer["argument_neighbourhood"]["outgoing"]
    }
    phase_sieve = story_claims["final_middle_neg_two_phase_sieve"]
    assert "Exactly 412 of the 2730 joint residue classes survive" in phase_sieve["claim"]["statement"]
    assert ("advances_open_target", "universal_257") in {
        (row["relation"], row["neighbour"]["id"])
        for row in phase_sieve["argument_neighbourhood"]["outgoing"]
    }
    first_harmonic = story_claims["first_harmonic_certificate_interface"]
    assert {
        row["neighbour"]["id"]
        for row in first_harmonic["argument_neighbourhood"]["outgoing"]
        if row["relation"] == "builds_on"
    } >= {"certificate_reduction", "certificate_completeness"}
    harmonic_pivot = story_claims["first_harmonic_pivot_decomposition"]
    assert "14X/25" in harmonic_pivot["claim"]["statement"]
    assert "9X/10" in harmonic_pivot["claim"]["statement"]
    assert {
        (row["relation"], row["neighbour"]["id"])
        for row in harmonic_pivot["argument_neighbourhood"]["outgoing"]
    } >= {
        ("builds_on", "first_harmonic_certificate_interface"),
        ("advances_open_target", "erdos_249"),
    }


def run_quick_check() -> int:
    """Verify the zero-build first-contact path from committed projections."""
    summary = quick_summary()
    human_surfaces = {path: read(path) for path in HUMAN_SURFACES}
    validate_human_first_contact(summary, human_surfaces)
    validate_gateway_opening(read(GATEWAY_PAPER))
    validate_cross_agent_entry(read("AGENTS.md"), read("CLAUDE.md"))
    print(
        "cold-clone quick check: committed human and agent first-contact "
        "projections verified; no Lean build or corpus-query sweep run"
    )
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Verify bounded cold-clone comprehension."
    )
    parser.add_argument(
        "--quick",
        action="store_true",
        help=(
            "check committed first-contact projections only; performs no Lean "
            "build and no exhaustive typed-query sweep"
        ),
    )
    parser.add_argument(
        "--proof-plans-only",
        action="store_true",
        help=(
            "exercise the two bounded semantic proof plans without the wider "
            "claim, paper, and route projection sweep"
        ),
    )
    args = parser.parse_args(argv)
    if args.quick:
        return run_quick_check()
    if args.proof_plans_only:
        validate_proof_plan_packets(collect_proof_plan_packets())
        print(
            "cold-clone proof plans: blocked and context-ready application "
            "boundaries verified"
        )
        return 0

    packets = collect_agent_packets()
    summary = packets["summary"]
    human_surfaces = {path: read(path) for path in HUMAN_SURFACES}
    validate_human_first_contact(summary, human_surfaces)
    validate_gateway_opening(read(GATEWAY_PAPER))
    validate_cross_agent_entry(read("AGENTS.md"), read("CLAUDE.md"))
    validate_agent_packets(packets)
    query_count = (
        1
        + len(packets["opens"])
        + len(packets["claims"])
        + len(packets["papers"])
        + len(packets["declarations"])
        + len(packets["sources"])
        + len(packets["modules"])
        + len(packets["sigil_modules"])
        + 1
        + len(packets["publication_families"])
        + len(packets["claim_statuses"])
        + len(packets["story_routes"])
        + len(packets["discovery_searches"])
        + len(packets["discovery_multi_searches"])
        + len(packets["proof_plans"])
        + len(packets["story_claims"])
        + 3
    )
    print(
        "cold-clone comprehension: bounded human first contact and "
        f"{query_count} typed query packets verified"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
