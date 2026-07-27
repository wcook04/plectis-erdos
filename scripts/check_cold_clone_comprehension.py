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
from collections import Counter
import copy
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
QUERY = ROOT / "scripts" / "query_corpus.py"
SEMANTIC_QUERY = ROOT / "scripts" / "query_semantic.py"
EXPERT_HANDOFF_QUERY = ROOT / "scripts" / "query_expert_handoffs.py"
SYSTEMS_EXPERT_QUESTION_ID = "XQSYS-ten-minute-hostile-reader"
HUMAN_SURFACES = ("README.md", "SCOPE.md", "docs/ORIENTATION.md")
CENSUS_SURFACES = ("README.md", "docs/RESULTS.md", "docs/TRUTH_AUDIT.md")
# Whole-file ceilings are intentionally looser than the fixed first-contact
# prefix below. They prevent accidental bloat without making the next honest
# sentence a release failure.
HUMAN_SURFACE_BUDGET_BYTES = {
    "README.md": 14_000,
    "SCOPE.md": 4_000,
    "docs/ORIENTATION.md": 18_000,
}
# This prefix window is the actual newcomer contract: later growth cannot move
# the problem statements, authority boundary, or semantic routes off the first
# screen.
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


def semantic_query_packet(
    *args: str, budget_bytes: int = PACKET_BUDGET_BYTES
) -> dict[str, Any]:
    """Run the public semantic CLI exactly as a cold coding agent would."""
    completed = subprocess.run(
        [sys.executable, str(SEMANTIC_QUERY), *args],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        raise AssertionError(completed.stdout.strip() or completed.stderr.strip())
    raw = completed.stdout.encode("utf-8")
    assert len(raw) <= budget_bytes, (
        f"semantic query {' '.join(args)} emitted {len(raw)} bytes "
        f"(budget {budget_bytes})"
    )
    return json.loads(completed.stdout)


def expert_handoff_packet(
    *args: str, budget_bytes: int = PACKET_BUDGET_BYTES
) -> dict[str, Any]:
    """Run the cross-domain expert-handoff query from a cold clone."""
    completed = subprocess.run(
        [sys.executable, str(EXPERT_HANDOFF_QUERY), *args],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        raise AssertionError(completed.stdout.strip() or completed.stderr.strip())
    raw = completed.stdout.encode("utf-8")
    assert len(raw) <= budget_bytes, (
        f"expert-handoff query {' '.join(args) or '<default>'} emitted "
        f"{len(raw)} bytes (budget {budget_bytes})"
    )
    return json.loads(completed.stdout)


def check_expert_handoff_protocol() -> str:
    """Run the cross-domain protocol's own structural self-check."""
    completed = subprocess.run(
        [sys.executable, str(EXPERT_HANDOFF_QUERY), "--check"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        raise AssertionError(completed.stdout.strip() or completed.stderr.strip())
    return completed.stdout.strip()


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
            ["conditional reduction"],
            ["verified finite instance"],
            ["does not show that the actual orbit avoids", "does not show the actual orbit avoids"],
            ["does not prove successful cases beyond every fixed cutoff"],
        ],
        "recover_farey_boundary": [
            ["classical Farey/mediant bound"],
            ["Farey's method supplies the number directly"],
            ["numerical delta `0`", "numerical delta 0"],
            ["exactly the Farey bound, not an improvement"],
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
        "route_exact_expert_handoffs": [
            ["exact expert handoffs"],
            ["what input is requested"],
            ["current guess"],
            ["alternatives"],
            ["discriminating evidence"],
            ["checked consumer"],
            ["endpoint-or-counterexample boundary"],
            ["python3 scripts/query_expert_handoffs.py"],
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


def semantic_census() -> dict[str, Any]:
    """Recompute the public diagnostic census from the generated graph."""
    corpus = json.loads(read("docs/semantic_corpus.json"))
    nodes = corpus["statement_nodes"]
    frontier = corpus["frontier"]
    nonrecurring_ids = set(corpus["views"]["nonrecurring"]["nodes"])
    nonrecurring = [node for node in nodes if node["id"] in nonrecurring_ids]
    bare = [
        node
        for node in nodes
        if node.get("logical_class") == "equivalence_or_classification"
        and node.get("is_restatement_of_open_problem")
    ]
    classical = [
        node
        for node in nodes
        if node.get("logical_class") == "classical_formalised"
        or node.get("prior_art_state") in ("known_classical", "prior_art_found")
    ]
    open_antecedents = frontier["open_antecedents"]
    demand_lattice = frontier["demand_lattice"]
    demand_classes = demand_lattice["classes"]
    demand_equivalent_classes = [
        row for row in demand_classes if row.get("equivalent_to_problem")
    ]

    def problem_counts(rows: list[dict[str, Any]]) -> Counter[str]:
        return Counter(row["problem"] for row in rows)

    return {
        "nonrecurring_total": len(nonrecurring),
        "nonrecurring_by_problem": problem_counts(nonrecurring),
        "nonrecurring_by_class": Counter(
            row["logical_class"] for row in nonrecurring
        ),
        "nonrecurring_not_assessed": sum(
            row.get("prior_art_state") == "not_assessed"
            for row in nonrecurring
        ),
        "bare_total": len(bare),
        "bare_by_problem": problem_counts(bare),
        "classical_total": len(classical),
        "classical_by_problem": problem_counts(classical),
        "open_antecedent_cluster_total": len(open_antecedents),
        "open_antecedent_equivalent_total": sum(
            row.get("equivalent_to_the_open_problem") is True
            for row in open_antecedents
        ),
        "demand_lattice_counts": demand_lattice["counts"],
        "demand_equivalent_total": sum(
            len(row["members"]) for row in demand_equivalent_classes
        ),
        "demand_equivalent_by_problem": Counter(
            {
                problem: sum(
                    len(row["members"])
                    for row in demand_equivalent_classes
                    if row["problem"] == problem
                )
                for problem in ("249", "257")
            }
        ),
    }


def validate_public_semantic_census(
    census: dict[str, Any], surfaces: dict[str, str]
) -> None:
    """Keep authored public snapshots synchronized with the live graph."""
    assert set(surfaces) == set(CENSUS_SURFACES)
    nonrecurring = census["nonrecurring_by_problem"]
    classes = census["nonrecurring_by_class"]
    bare = census["bare_by_problem"]
    classical = census["classical_by_problem"]
    total = census["nonrecurring_total"]
    unassessed = census["nonrecurring_not_assessed"]
    demand = census["demand_lattice_counts"]
    demand_equivalent = census["demand_equivalent_total"]
    demand_equivalent_by_problem = census[
        "demand_equivalent_by_problem"
    ]
    open_cluster_total = census["open_antecedent_cluster_total"]
    open_cluster_equivalent = census[
        "open_antecedent_equivalent_total"
    ]

    expectations = {
        "README.md": (
            (
                f"{total} mechanically nonrecurring candidates "
                f"({nonrecurring['257']} #257, {nonrecurring['249']} #249, "
                f"{nonrecurring['shared_substrate']} shared)"
            ),
            f"{census['bare_total']} bare equivalences",
            f"{census['classical_total']} classical/prior-art formalisations",
            f"{unassessed} candidates lack prior-art assessment",
            (
                f"{demand_equivalent} of {demand['substantial']} substantial "
                "hypotheses extracted from conditional theorems are proved "
                "endpoint-equivalent"
            ),
        ),
        "docs/RESULTS.md": (
            (
                "| mechanically nonrecurring candidates | "
                f"{nonrecurring['249']} | {nonrecurring['257']} | "
                f"{nonrecurring['shared_substrate']} | **{total}** |"
            ),
            (
                "| classical/prior-art formalisations | "
                f"{classical['249']} | {classical['257']} | "
                f"{classical['shared_substrate']} | "
                f"**{census['classical_total']}** |"
            ),
            (
                "| bare open-problem equivalences | "
                f"{bare['249']} | {bare['257']} | "
                f"{bare['shared_substrate']} | **{census['bare_total']}** |"
            ),
            (
                f"The nonrecurring view contains "
                f"{classes['unconditional_object_theorem']} unconditional "
                f"object theorems, {classes['barrier_no_go']} scoped "
                f"barriers, and {classes['reduction_or_transport']} "
                "reductions or transports"
            ),
            f"{unassessed} of the {total} candidates have",
            (
                f"Of {demand['substantial']} substantial Lean propositions "
                "extracted from hypotheses of conditional theorems, "
                f"{demand_equivalent} are provably equivalent to an endpoint"
            ),
            (
                f"{demand_equivalent_by_problem['249']} to #249 and "
                f"{demand_equivalent_by_problem['257']} to the `1/2` "
                "membership test for #257"
            ),
            (
                f"`open-antecedents` view currently has {open_cluster_total} "
                f"entries, {open_cluster_equivalent} marked "
                "endpoint-equivalent"
            ),
        ),
        "docs/TRUTH_AUDIT.md": (
            (
                f"{total} mechanically nonrecurring candidates "
                f"({nonrecurring['249']} for #249, "
                f"{nonrecurring['257']} for #257, and "
                f"{nonrecurring['shared_substrate']} shared)"
            ),
            f"{census['bare_total']} bare open-problem equivalences",
            f"{census['classical_total']} classical/prior-art formalisations",
            f"{unassessed} candidates have no completed prior-art assessment",
            (
                f"The `{demand_equivalent}/{demand['substantial']}` count is "
                "a narrower kernel-checked audit"
            ),
            (
                f"starts from {demand['conditional_declarations_walked']} "
                "conditional declarations, extracts "
                f"{demand['closed_props_extracted']} distinct closed "
                "hypothesis Props"
            ),
            (
                f"classifies {demand['substantial']} as substantial; "
                f"{demand_equivalent} of those {demand['substantial']} are "
                "endpoint-equivalent"
            ),
            (
                f"lists {open_cluster_total} entries, "
                f"{open_cluster_equivalent} marked endpoint-equivalent"
            ),
        ),
    }
    for path, phrases in expectations.items():
        compact = normalized(surfaces[path])
        for phrase in phrases:
            assert normalized(phrase) in compact, (
                f"{path} semantic census is stale; missing {phrase!r}"
            )


def validate_gateway_opening(paper: str) -> None:
    """Check that the authored introduction works without source inventory."""
    start = paper.index(r"\section{Introduction}")
    end = paper.index(r"\section{Lambert-series identities and comparison values}")
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
            # Pins the finite-evidence row to the band the claim record carries.
            # The band moved from 28 deposits through t = 64 to every scale
            # t <= 82; anchoring the old count would enforce an understatement
            # of the checked theorem.
            ["diagonal certificate at every scale"],
            [r"Universal assertion in \#257 & Open"],
            ["Prior work/formalised"],
            ["Open; exact reductions"],
        ],
        "exact_residuals": [
            ["An unbounded certificate supply"],
            ["the terminal bit is zero beyond every bound"],
            ["two explicit obligations"],
        ],
        "finite_open_split": [
            ["finite Lean-checkable calculation and one unbounded condition"],
            ["Neither equivalence proves the unbounded behaviour"],
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
    for retired_internal_label in (
        "cofinal terminal zeros",
        "certificate normal form",
    ):
        assert retired_internal_label not in opening, (
            f"gateway opening restored retired internal label {retired_internal_label!r}"
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


def collect_agent_packets() -> dict[str, Any]:
    """Collect only bounded query replies needed to walk the public graph."""
    summary = query_packet(budget_bytes=SUMMARY_PACKET_BUDGET_BYTES)
    publication_architecture = query_packet("--publication-architecture")
    expert_questions = semantic_query_packet("expert-questions")
    expert_handoffs = expert_handoff_packet()
    mathematical_question_ids = [
        row["id"] for row in expert_questions["results"]
    ]
    handoff_ids = [row["id"] for row in expert_handoffs["results"]]
    semantic_corpus = json.loads(read("docs/semantic_corpus.json"))
    inventory_sample = semantic_corpus["declaration_roles"][0]
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
        "story_claims": {
            claim_id: query_packet("--claim", claim_id) for claim_id in STORY_CLAIMS
        },
        "expert_questions": expert_questions,
        "semantic_inventory": semantic_query_packet(
            "inventory", "--limit", "3"
        ),
        "semantic_inventory_lookup": semantic_query_packet(
            "inventory",
            inventory_sample["declaration"],
            "--module",
            inventory_sample["module"],
            "--limit",
            "3",
        ),
        "semantic_inventory_sample": inventory_sample,
        "expert_questions_by_problem": {
            problem: semantic_query_packet(
                "expert-questions", "--problem", problem
            )
            for problem in ("249", "257")
        },
        "expert_question_details": {
            question_id: semantic_query_packet(
                "expert-questions", question_id
            )
            for question_id in mathematical_question_ids
        },
        "expert_handoffs": expert_handoffs,
        "expert_handoff_details": {
            question_id: expert_handoff_packet(
                "--question", question_id
            )
            for question_id in handoff_ids
        },
        "expert_handoff_protocol_check": check_expert_handoff_protocol(),
        "expert_handoff_review_template": expert_handoff_packet(
            "--review-template", SYSTEMS_EXPERT_QUESTION_ID
        ),
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

    inventory = packets["semantic_inventory"]
    assert inventory["authority_posture"] == (
        "exhaustive_inventory_navigation_not_semantic_interpretation"
    )
    assert inventory["total_matches"] == summary["scale"]["declaration_count"]
    assert inventory["returned"] == 3
    assert inventory["omitted"] == inventory["total_matches"] - 3
    assert all(row["module"] and row["declaration"] for row in inventory["results"])
    assert "does not infer a mathematical claim" in inventory["measurement_contract"]

    inventory_sample = packets["semantic_inventory_sample"]
    inventory_lookup = packets["semantic_inventory_lookup"]
    assert inventory_lookup["total_matches"] >= 1
    assert any(
        row["id"] == inventory_sample["id"]
        for row in inventory_lookup["results"]
    )
    assert encoded_bytes(inventory_lookup) <= PACKET_BUDGET_BYTES

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

    def validate_compact_question(row: dict[str, Any]) -> None:
        assert isinstance(row.get("id"), str) and row["id"].strip()
        assert row.get("status") == "OPEN"
        for field in ("exact_ask", "current_hypothesis"):
            assert isinstance(row.get(field), str) and row[field].strip()
        assert row.get("hypothesis_confidence") in {"low", "medium", "high"}
        alternatives = row.get("plausible_alternatives")
        assert isinstance(alternatives, list) and len(alternatives) >= 2
        alternative_ids = [alternative.get("id") for alternative in alternatives]
        assert len(alternative_ids) == len(set(alternative_ids))
        for alternative in alternatives:
            for field in ("id", "statement"):
                assert isinstance(alternative.get(field), str)
                assert alternative[field].strip()
        for field in ("current_evidence", "discriminating_evidence"):
            evidence = row.get(field)
            assert isinstance(evidence, list) and len(evidence) >= 2
            assert len(evidence) == len(set(evidence))
            assert all(
                isinstance(item, str) and item.strip()
                for item in evidence
            )

    def validate_full_question(row: dict[str, Any]) -> None:
        validate_compact_question(row)
        for field in ("payoff", "boundary", "known_obstruction"):
            assert isinstance(row.get(field), str) and row[field].strip()
        for alternative in row["plausible_alternatives"]:
            assert isinstance(alternative.get("consequence"), str)
            assert alternative["consequence"].strip()

    expert_questions = packets["expert_questions"]
    expert_questions_by_problem = packets["expert_questions_by_problem"]
    expert_question_details = packets["expert_question_details"]
    assert expert_questions["packet_kind"] == "compact_index"
    assert expert_questions["count"] == len(expert_questions["results"]) == 5
    assert encoded_bytes(expert_questions) <= PACKET_BUDGET_BYTES
    assert set(expert_questions_by_problem) == {"249", "257"}
    assert {
        problem: packet["count"]
        for problem, packet in expert_questions_by_problem.items()
    } == {"249": 3, "257": 2}
    assert {
        row["classification"] for row in expert_questions["results"]
    } == {
        "endpoint_equivalent",
        "sufficient_for_erdos_249",
        "sufficient_for_counterexample",
    }
    assert set(expert_questions["classification_legend"]) == {
        "endpoint_equivalent",
        "sufficient_for_erdos_249",
        "sufficient_for_counterexample",
    }
    semantic_index_by_id = {
        row["id"]: row for row in expert_questions["results"]
    }
    assert len(semantic_index_by_id) == 5
    for row in semantic_index_by_id.values():
        assert row["problem"] in {"249", "257"}
        validate_compact_question(row)
        assert row["detail_command"] == (
            "python3 scripts/query_semantic.py expert-questions "
            f"{row['id']}"
        )
        assert isinstance(row.get("checked_consumers"), list)
        assert row["checked_consumers"]
        assert all(
            isinstance(consumer, str) and consumer.strip()
            for consumer in row["checked_consumers"]
        )
    default_by_problem = {
        problem: [
            row for row in expert_questions["results"]
            if row["problem"] == problem
        ]
        for problem in ("249", "257")
    }
    for problem, packet in expert_questions_by_problem.items():
        assert packet["packet_kind"] == "compact_index"
        assert packet["results"] == default_by_problem[problem]
        assert all(row["problem"] == problem for row in packet["results"])
        assert packet["classification_legend"] == (
            expert_questions["classification_legend"]
        )
        assert packet["limits"] == expert_questions["limits"]
        assert encoded_bytes(packet) <= PACKET_BUDGET_BYTES
    assert {
        row["classification"]
        for row in expert_questions_by_problem["249"]["results"]
    } == {"endpoint_equivalent", "sufficient_for_erdos_249"}
    assert {
        row["classification"]
        for row in expert_questions_by_problem["257"]["results"]
    } == {"sufficient_for_counterexample"}
    expert_limits = normalized(" ".join(expert_questions["limits"]))
    assert contains_any(
        expert_limits,
        [
            "The two #257 questions can produce a counterexample if answered "
            "positively; they cannot prove the universal positive statement."
        ],
    )
    assert contains_any(
        expert_limits,
        [
            "No checked strictly weaker expert handoff currently implies "
            "universal Erdős #257 for every infinite support."
        ],
    )
    assert set(expert_question_details) == set(semantic_index_by_id)
    semantic_detail_by_id: dict[str, dict[str, Any]] = {}
    compact_identity_fields = (
        "id",
        "problem",
        "classification",
        "status",
        "exact_ask",
        "current_hypothesis",
        "hypothesis_confidence",
        "current_evidence",
        "discriminating_evidence",
    )
    for question_id, packet in expert_question_details.items():
        assert packet["packet_kind"] == "full_question"
        assert packet["count"] == len(packet["results"]) == 1
        assert packet["classification_legend"] == (
            expert_questions["classification_legend"]
        )
        assert packet["limits"] == expert_questions["limits"]
        assert encoded_bytes(packet) <= PACKET_BUDGET_BYTES
        row = packet["results"][0]
        assert row["id"] == question_id
        validate_full_question(row)
        index_row = semantic_index_by_id[question_id]
        assert all(
            row[field] == index_row[field]
            for field in compact_identity_fields
        )
        assert [
            {
                "id": alternative["id"],
                "statement": alternative["statement"],
            }
            for alternative in row["plausible_alternatives"]
        ] == index_row["plausible_alternatives"]
        consumers = row.get("consumer_declarations")
        assert isinstance(consumers, list) and consumers
        for consumer in consumers:
            assert isinstance(consumer.get("declaration"), str)
            assert consumer["declaration"].strip()
            assert isinstance(consumer.get("module"), str)
            assert consumer["module"].strip()
            assert isinstance(consumer.get("line"), int) and consumer["line"] > 0
        assert [
            f"{consumer['module']}:{consumer['line']}:{consumer['declaration']}"
            for consumer in consumers
        ] == index_row["checked_consumers"]
        for field in (
            "open_proposition_id",
            "source_claim_id",
            "verification_command",
        ):
            assert isinstance(row.get(field), str) and row[field].strip()
        semantic_detail_by_id[question_id] = row

    expert_handoffs = packets["expert_handoffs"]
    expert_handoff_details = packets["expert_handoff_details"]
    assert expert_handoffs["packet_kind"] == "compact_index"
    assert expert_handoffs["count"] == len(expert_handoffs["results"]) == 6
    assert expert_handoffs["domain_counts"] == {
        "mathematics": 5,
        "systems": 1,
    }
    assert encoded_bytes(expert_handoffs) <= PACKET_BUDGET_BYTES
    handoff_index_by_id = {
        row["id"]: row for row in expert_handoffs["results"]
    }
    assert len(handoff_index_by_id) == 6
    assert set(expert_handoff_details) == set(handoff_index_by_id)
    shared_index_fields = (
        "id",
        "problem",
        "classification",
        "status",
        "exact_ask",
        "current_hypothesis",
        "hypothesis_confidence",
        "plausible_alternatives",
        "current_evidence",
        "discriminating_evidence",
    )
    for row in handoff_index_by_id.values():
        validate_compact_question(row)
        assert row["detail_command"] == (
            "python3 scripts/query_expert_handoffs.py --question "
            f"{row['id']}"
        )
        if row["domain"] == "mathematics":
            semantic_row = semantic_index_by_id[row["id"]]
            assert all(
                row[field] == semantic_row[field]
                for field in shared_index_fields
            )
    handoff_detail_by_id: dict[str, dict[str, Any]] = {}
    for question_id, packet in expert_handoff_details.items():
        assert packet["packet_kind"] == "full_question"
        assert packet["count"] == len(packet["results"]) == 1
        assert encoded_bytes(packet) <= PACKET_BUDGET_BYTES
        row = packet["results"][0]
        assert row["id"] == question_id
        assert packet["domain_counts"] == {row["domain"]: 1}
        validate_full_question(row)
        index_row = handoff_index_by_id[question_id]
        assert all(
            row.get(field) == index_row.get(field)
            for field in compact_identity_fields
        )
        assert [
            {
                "id": alternative["id"],
                "statement": alternative["statement"],
            }
            for alternative in row["plausible_alternatives"]
        ] == index_row["plausible_alternatives"]
        if row["domain"] == "mathematics":
            semantic_row = semantic_detail_by_id[question_id]
            assert {
                key: value for key, value in row.items()
                if key != "domain"
            } == semantic_row
        handoff_detail_by_id[question_id] = row

    mathematical_handoffs_by_id = {
        question_id: row
        for question_id, row in handoff_detail_by_id.items()
        if row["domain"] == "mathematics"
    }
    expected_257_consumers = {
        "XQ257-second-channel-separation": {
            "half_mem_mersenneAchievementSet_of_secondChannelSeparationRat_from_seven",
            "positiveMersenneSupportValue_coe_finset_ne_half",
            "positiveMersenneSupportValue_eq_erdosSupportSeries",
        },
        "XQ257-middle-producer-tail-escape": {
            "half_mem_mersenneAchievementSet_of_middleProducerTailEscapeExceptNegThree",
            "positiveMersenneSupportValue_coe_finset_ne_half",
            "positiveMersenneSupportValue_eq_erdosSupportSeries",
        },
    }
    for question_id, expected_consumers in expected_257_consumers.items():
        row = mathematical_handoffs_by_id[question_id]
        assert row["problem"] == "257"
        assert {
            consumer["declaration"]
            for consumer in row["consumer_declarations"]
        } == expected_consumers
    pivot = mathematical_handoffs_by_id["XQ249-pivot-decorrelation"]
    assert "h <= L-s" in pivot["exact_ask"]
    assert (
        "all four 14/25, 1/100, 1/100 and 8/25 budgets"
        in pivot["current_hypothesis"]
    )
    pivot_alternatives = {
        row["id"]: row for row in pivot["plausible_alternatives"]
    }
    assert set(pivot_alternatives) == {
        "cofinal_four_budget_socket",
        "no_cofinal_joint_witness",
    }
    assert pivot_alternatives["cofinal_four_budget_socket"]["statement"] == (
        "All four budgets, overlap and room inequalities hold cofinally for "
        "every positive shift."
    )
    assert pivot_alternatives["no_cofinal_joint_witness"]["statement"] == (
        "For some h > 0, every s > 0 and eta in (0,1) has a cutoff after "
        "which no X,L meet the complete structural and four-budget conjunction."
    )

    adjacent = mathematical_handoffs_by_id[
        "XQ249-adjacent-phase-separation"
    ]
    assert "16(2X+h+L+2) <= 2^L" in adjacent["exact_ask"]
    adjacent_alternatives = {
        row["id"]: row for row in adjacent["plausible_alternatives"]
    }
    assert adjacent_alternatives["phase_locking"]["statement"] == (
        "For some positive shift there is a cutoff beyond which no admissible "
        "block, depth and adjacent pair meet the 19/25 threshold."
    )
    assert any(
        "Infinitely many bad blocks alone do not." in evidence
        for evidence in adjacent["discriminating_evidence"]
    )

    second_channel = mathematical_handoffs_by_id[
        "XQ257-second-channel-separation"
    ]
    second_channel_text = " ".join(
        [
            second_channel["current_hypothesis"],
            second_channel["known_obstruction"],
            *second_channel["current_evidence"],
        ]
    )
    assert "Theta(n^2)" not in second_channel_text
    assert (
        "no matching reduced-denominator lower bound"
        in second_channel_text
    )
    assert "1 <= n <= 1000" in second_channel_text
    assert "Rank 1001 onward is unmeasured" in second_channel_text
    assert "1033253069/8193024" in second_channel_text
    assert (
        "All 128 branch words of length seven occur"
        in second_channel_text
    )
    assert second_channel["measured_evidence_artifact"] == (
        "docs/measurements/second_channel_separation_probe.json"
    )
    assert second_channel["measurement_check_command"] == (
        "python3 scripts/probe_second_channel_separation.py --check"
    )

    middle = mathematical_handoffs_by_id[
        "XQ257-middle-producer-tail-escape"
    ]
    assert (
        "Prove C_s = -3 or (1 <= C_s and Theta_s < C_s)."
        in middle["exact_ask"]
    )
    middle_alternatives = {
        row["id"]: row for row in middle["plausible_alternatives"]
    }
    assert set(middle_alternatives) == {
        "full_middle_disjunction",
        "nonpositive_cell_counterexample",
        "positive_tail_counterexample",
    }
    assert middle_alternatives["full_middle_disjunction"]["statement"] == (
        "Every actual middle row satisfies C_s = -3 or 1 <= C_s with "
        "Theta_s < C_s."
    )
    assert middle_alternatives["nonpositive_cell_counterexample"][
        "statement"
    ] == "An actual middle row has C_s <= 0 with C_s != -3."
    assert middle_alternatives["positive_tail_counterexample"]["statement"] == (
        "An actual middle row has 1 <= C_s and Theta_s >= C_s."
    )
    systems_handoff = handoff_detail_by_id[SYSTEMS_EXPERT_QUESTION_ID]
    assert systems_handoff["domain"] == "systems"
    assert systems_handoff["classification"] == "external_validation"
    for field in (
        "exact_ask",
        "payoff",
        "boundary",
        "known_obstruction",
        "verification_command",
    ):
        assert isinstance(systems_handoff.get(field), str)
        assert systems_handoff[field].strip()
    assert systems_handoff["input_template"]["question_id"] == (
        systems_handoff["id"]
    )
    assert "acceptance" not in systems_handoff
    assert "review_template" not in systems_handoff
    rubric = systems_handoff.get("manual_review_rubric")
    assert isinstance(rubric, dict) and rubric
    assert all(
        isinstance(key, str) and key.strip()
        and isinstance(value, str) and value.strip()
        for key, value in rubric.items()
    )
    scalar_answer_fields = (
        "prior_project_context",
        "elapsed_seconds",
        "problem_249_status",
        "problem_257_status",
        "farey_bound_provenance",
        "farey_numerical_delta",
        "equivalent_antecedents",
        "substantial_antecedents",
    )
    assert all(
        systems_handoff["input_template"][field] is None
        for field in scalar_answer_fields
    )
    assert systems_handoff["consumer"]["command"]
    assert systems_handoff["consumer"]["review_template_command"] == (
        "python3 scripts/query_expert_handoffs.py --review-template "
        f"{SYSTEMS_EXPERT_QUESTION_ID}"
    )
    assert systems_handoff["consumer"]["final_review_command"]
    assert systems_handoff["verification_command"] == (
        "python3 scripts/query_expert_handoffs.py --check"
    )
    assert packets["expert_handoff_protocol_check"] == (
        "expert handoff protocol: 5 mathematical questions and "
        "1 systems question(s) verified"
    )
    review_template = packets["expert_handoff_review_template"]
    assert review_template["question_id"] == SYSTEMS_EXPERT_QUESTION_ID
    assert review_template["response_sha256"] is None
    assert review_template["evaluator_identity"] is None
    assert review_template["evaluated_at"] is None
    assert review_template["reviewer_provenance_verified"] is None
    assert review_template["timing_provenance_verified"] is None
    assert review_template["review_notes"] == ""
    assert review_template["final_outcome"] is None
    assert set(review_template["criteria"]) == set(rubric)
    assert all(value is None for value in review_template["criteria"].values())
    assert "acceptance" not in review_template
    assert encoded_bytes(review_template) <= PACKET_BUDGET_BYTES


def run_quick_check() -> int:
    """Verify the zero-build first-contact path from committed projections."""
    summary = quick_summary()
    human_surfaces = {path: read(path) for path in HUMAN_SURFACES}
    validate_human_first_contact(summary, human_surfaces)
    validate_public_semantic_census(
        semantic_census(),
        {path: read(path) for path in CENSUS_SURFACES},
    )
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
    args = parser.parse_args(argv)
    if args.quick:
        return run_quick_check()

    packets = collect_agent_packets()
    summary = packets["summary"]
    human_surfaces = {path: read(path) for path in HUMAN_SURFACES}
    validate_human_first_contact(summary, human_surfaces)
    validate_public_semantic_census(
        semantic_census(),
        {path: read(path) for path in CENSUS_SURFACES},
    )
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
        + len(packets["story_claims"])
        + 2
        + 1
        + len(packets["expert_questions_by_problem"])
        + len(packets["expert_question_details"])
        + 1
        + len(packets["expert_handoff_details"])
        + 2
        + 3
    )
    print(
        "cold-clone comprehension: bounded human first contact and "
        f"{query_count} typed query packets verified"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
