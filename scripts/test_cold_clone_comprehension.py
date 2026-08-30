#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial tests for bounded cold-clone comprehension."""

from __future__ import annotations

import argparse
import copy
import json
import re
import subprocess
import sys
from pathlib import Path

import check_cold_clone_comprehension as diagnostic
import query_route_memory as route_memory


ROOT = Path(__file__).resolve().parent.parent
ROUTE_MEMORY_SCRIPT = ROOT / "scripts" / "query_route_memory.py"
FROZEN_PROBLEMS = (68, 243, 249, 251, 257, 269, 1041, 1049)


def assert_rejected(packets: dict, label: str) -> None:
    try:
        diagnostic.validate_agent_packets(packets)
    except AssertionError:
        return
    raise AssertionError(f"semantic mutation escaped: {label}")


def assert_proof_plan_rejected(proof_plans: dict, label: str) -> None:
    try:
        diagnostic.validate_proof_plan_packets(proof_plans)
    except AssertionError:
        return
    raise AssertionError(f"proof-plan mutation escaped: {label}")


def check_proof_plan_mutations(proof_plans: dict) -> int:
    mutated = copy.deepcopy(proof_plans)
    mutated["blocked_integer_tail"]["application"]["obligations"] = [
        row
        for row in mutated["blocked_integer_tail"]["application"][
            "obligations"
        ]
        if row["name"] != "hdvd"
    ]
    assert_proof_plan_rejected(
        mutated, "proof-plan missing-obligation boundary"
    )

    mutated = copy.deepcopy(proof_plans)
    mutated["context_ready_curvature"]["exact_dependency_spine"][
        "steps"
    ] = []
    assert_proof_plan_rejected(
        mutated, "proof-plan exact dependency spine"
    )
    return 2


def assert_human_rejected(summary: dict, surfaces: dict[str, str], label: str) -> None:
    try:
        diagnostic.validate_human_first_contact(summary, surfaces)
    except AssertionError:
        return
    raise AssertionError(f"human first-contact mutation escaped: {label}")


def assert_census_rejected(
    census: dict, surfaces: dict[str, str], label: str
) -> None:
    try:
        diagnostic.validate_public_semantic_census(census, surfaces)
    except AssertionError:
        return
    raise AssertionError(f"public census mutation escaped: {label}")


def remove_semantic_anchor(text: str, token: str) -> str:
    """Delete every case-insensitive occurrence seen by the production check."""
    return re.sub(
        re.escape(diagnostic.normalized(token)),
        "",
        text,
        flags=re.IGNORECASE,
    )


def check_route_memory_cold_clone() -> int:
    """Exercise the tracked-only route-memory entry for every selector."""
    checked = 0
    for problem_number in FROZEN_PROBLEMS:
        result = subprocess.run(
            [
                sys.executable,
                str(ROUTE_MEMORY_SCRIPT),
                "--problem",
                str(problem_number),
            ],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            raise AssertionError(
                f"route-memory selector #{problem_number} failed: {result.stderr}"
            )
        packet = json.loads(result.stdout)
        if packet["problem"]["erdos_number"] != problem_number:
            raise AssertionError(f"route-memory crossed selector #{problem_number}")
        if route_memory.validate_packet(packet)["resume_state"] != packet["resume_state"]:
            raise AssertionError(f"route-memory resume identity drifted for #{problem_number}")
        checked += 1

    cross_problem = subprocess.run(
        [
            sys.executable,
            str(ROUTE_MEMORY_SCRIPT),
            "--problem",
            "249",
            "--route",
            "erdos257_half_story",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    if cross_problem.returncode != 2 or cross_problem.stdout:
        raise AssertionError("cross-problem route was not rejected by the CLI")
    if "cross_problem_route" not in cross_problem.stderr:
        raise AssertionError("cross-problem rejection lost its machine-readable code")
    return checked + 1


def main() -> int:
    route_memory_checks = check_route_memory_cold_clone()
    packets = diagnostic.collect_agent_packets()
    summary = packets["summary"]
    quick_summary = diagnostic.quick_summary()
    human_surfaces = {
        path: diagnostic.read(path) for path in diagnostic.HUMAN_SURFACES
    }
    diagnostic.validate_human_first_contact(quick_summary, human_surfaces)
    diagnostic.validate_human_first_contact(summary, human_surfaces)
    census = diagnostic.semantic_census()
    census_surfaces = {
        path: diagnostic.read(path) for path in diagnostic.CENSUS_SURFACES
    }
    diagnostic.validate_public_semantic_census(census, census_surfaces)
    gateway_paper = diagnostic.read(diagnostic.GATEWAY_PAPER)
    diagnostic.validate_gateway_opening(gateway_paper)
    agents = diagnostic.read("AGENTS.md")
    claude = diagnostic.read("CLAUDE.md")
    diagnostic.validate_cross_agent_entry(agents, claude)
    incremental_surfaces = {
        path: diagnostic.read(path)
        for path in diagnostic.INCREMENTAL_BUILD_SURFACES
    }
    diagnostic.validate_incremental_build_contract(incremental_surfaces)
    diagnostic.validate_agent_packets(packets)

    checks = 4
    for task_id, requirements in diagnostic.human_tasks(summary).items():
        for alternatives in requirements:
            mutated = copy.deepcopy(human_surfaces)
            mutated["README.md"] = diagnostic.normalized(mutated["README.md"])
            for token in alternatives:
                mutated["README.md"] = remove_semantic_anchor(
                    mutated["README.md"], token
                )
            assert_human_rejected(summary, mutated, f"{task_id}: {alternatives}")
            checks += 1

    mutated = copy.deepcopy(human_surfaces)
    mutated["README.md"] = mutated["README.md"].replace(
        "## What remains open", "## Deferred questions"
    )
    assert_human_rejected(summary, mutated, "first-contact section contract")
    checks += 1

    mutated_incremental = copy.deepcopy(incremental_surfaces)
    mutated_incremental[".github/workflows/lean.yml"] = mutated_incremental[
        ".github/workflows/lean.yml"
    ].replace("uses: actions/cache@", "uses: actions/cache-bypassed@", 1)
    try:
        diagnostic.validate_incremental_build_contract(mutated_incremental)
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("project-cache workflow deletion escaped")

    mutated_incremental = copy.deepcopy(incremental_surfaces)
    mutated_incremental["scripts/lean_fast_build.py"] = mutated_incremental[
        "scripts/lean_fast_build.py"
    ].replace('"--changed-from"', '"--all-from-scratch"', 1)
    try:
        diagnostic.validate_incremental_build_contract(mutated_incremental)
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("changed-cone planner deletion escaped")

    mutated = copy.deepcopy(human_surfaces)
    mutated["README.md"] = (
        "This is an exceptional and impressive research-grade achievement.\n"
        + mutated["README.md"]
    )
    assert_human_rejected(summary, mutated, "self-appraisal language")
    checks += 1

    mutated_census = copy.deepcopy(census_surfaces)
    mutated_census["docs/RESULTS.md"] = mutated_census[
        "docs/RESULTS.md"
    ].replace(
        "| mechanically nonrecurring candidates |",
        "| mechanically nonrecurring candidates CORRUPTED |",
        1,
    )
    assert_census_rejected(
        census, mutated_census, "live semantic census synchronization"
    )
    checks += 1

    mutated_census = copy.deepcopy(census_surfaces)
    mutated_census["docs/TRUTH_AUDIT.md"] = mutated_census[
        "docs/TRUTH_AUDIT.md"
    ].replace(
        (
            f"The `{census['demand_equivalent_total']}/"
            f"{census['demand_lattice_counts']['substantial']}` count"
        ),
        "The `0/0` count",
        1,
    )
    assert_census_rejected(
        census, mutated_census, "demand-lattice population distinction"
    )
    checks += 1

    mutated_paper = remove_semantic_anchor(
        gateway_paper, "An unbounded certificate supply"
    )
    try:
        diagnostic.validate_gateway_opening(mutated_paper)
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("gateway exact-open-edge deletion escaped")

    mutated_paper = gateway_paper.replace(
        r"for every infinite $A\subseteq\Npos$ (\#257)",
        r"for every infinite $A\subseteq\N$ (\#257)",
    )
    try:
        diagnostic.validate_gateway_opening(mutated_paper)
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("gateway positive-support notation mutation escaped")

    mutated_paper = gateway_paper.replace(
        "Open; exact reductions", "Proved"
    )
    try:
        diagnostic.validate_gateway_opening(mutated_paper)
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("gateway half-value status inflation escaped")

    mutated_paper = gateway_paper.replace(
        r"\paragraph{Reading map.}",
        r"\paragraph{Reading map.} Fake.lean module inventory",
    )
    try:
        diagnostic.validate_gateway_opening(mutated_paper)
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("gateway source-inventory leak escaped")

    # Delete the import the contract actually requires. This mutated
    # "@AGENTS.md", which is not a substring of "@AGENTS.override.md", so once
    # CLAUDE.md imported the compact entry the replace became a no-op and the
    # harness was asserting against an unmutated file.
    try:
        diagnostic.validate_cross_agent_entry(
            agents, claude.replace("@AGENTS.override.md", "")
        )
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("Claude shared-instruction import deletion escaped")

    for token, label in (
        ("## Eight-problem cold-start card", "agent direct fleet card"),
        (r"\sum_{n\ge1}p_n/2^n", "agent #251 mathematical statement"),
        ("`ai_workflow`", "agent standalone boundary"),
    ):
        try:
            diagnostic.validate_cross_agent_entry(
                agents.replace(token, "", 1), claude
            )
        except AssertionError:
            checks += 1
        else:
            raise AssertionError(f"{label} deletion escaped")

    mutated = copy.deepcopy(packets)
    mutated["summary"]["proof_authority"] = "unverified"
    assert_rejected(mutated, "proof authority")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["summary"]["remaining_open_propositions"] = []
    assert_rejected(mutated, "open boundary")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["summary"]["publication_family_count"] = 0
    assert_rejected(mutated, "contribution-family scale")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["route"]["route"]["query_steps"].remove(
        "python3 scripts/query_corpus.py --publication-architecture"
    )
    assert_rejected(mutated, "contribution-family first-read route")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["agent_native_navigation_route"]["route"]["action_steps"] = [
        step
        for step in mutated["agent_native_navigation_route"]["route"]["action_steps"]
        if "proof_workbench.py open" not in step
    ]
    assert_rejected(mutated, "agent-native navigation workbench handoff")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["agent_native_navigation_route"]["route"]["cold_clone_contract"][
        "navigation_requires_lean_build"
    ] = True
    assert_rejected(mutated, "agent-native zero-build navigation contract")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["agent_native_navigation_route"]["route"]["query_steps"].remove(
        "python3 scripts/query_corpus.py --search <ordinary-language-query>"
    )
    assert_rejected(mutated, "agent-native ordinary-language first drilldown")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["agent_native_navigation_route"]["route"]["query_steps"] = [
        step
        for step in mutated["agent_native_navigation_route"]["route"][
            "query_steps"
        ]
        if "--publication-artifact agent_native_navigation_guide" not in step
    ]
    assert_rejected(mutated, "agent-native publication handoff")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["agent_tour"]["intent_lenses"] = [
        row
        for row in mutated["agent_tour"]["intent_lenses"]
        if row["intent"] != "begin_a_checked_change"
    ]
    assert_rejected(mutated, "agent tour checked-change intent")
    checks += 1

    mutated = copy.deepcopy(packets)
    del mutated["agent_tour"]["cold_reader_contracts"]["ai_lab_researcher"]
    assert_rejected(mutated, "agent tour AI-lab reader contract")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["agent_native_navigation_route"]["route"]["action_steps"] = [
        step
        for step in mutated["agent_native_navigation_route"]["route"]["action_steps"]
        if "lean_fast_build.py" not in step
    ]
    assert_rejected(mutated, "agent-native focused incremental build handoff")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["discovery_searches"]["what other exact mathematics is there"][
        "results"
    ].insert(0, {"kind": "declaration", "name": "shadow_result"})
    assert_rejected(mutated, "contribution-family search priority")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["discovery_searches"][
        "what else is formally checked besides Erdos 249 and 257"
    ]["results"] = []
    assert_rejected(mutated, "ordinary corpus-breadth route discovery")
    checks += 1

    mutated = copy.deepcopy(packets)
    removed_family = next(iter(mutated["publication_families"]))
    mutated["publication_families"].pop(removed_family)
    assert_rejected(mutated, "contribution-family coverage")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["story_routes"]["erdos257_half_story"]["route"]["query_steps"].pop()
    assert_rejected(mutated, "#257 story route")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["story_routes"]["erdos249_diagonal_arithmetic"]["programme"][
        "claim_ceiling"
    ] = "This solves Erdős #249."
    assert_rejected(mutated, "programme claim ceiling")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["story_routes"]["boolean_mobius_constraints"]["programme"][
        "core_claims"
    ].pop()
    assert_rejected(mutated, "programme claim-route completeness")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["story_routes"]["transport_curvature_programme"][
        "release_provenance"
    ]["boundary"] = "Private work may supply proof authority."
    assert_rejected(mutated, "public-projection provenance boundary")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["discovery_searches"]["what remains open for 257"]["results"] = []
    assert_rejected(mutated, "natural-language route discovery")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["discovery_searches"]["what is reduced"]["results"].insert(
        0, {"kind": "declaration", "name": "shadow_reduction"}
    )
    assert_rejected(mutated, "claim-status route priority")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["discovery_searches"]["which claims are cited only"]["results"] = []
    assert_rejected(mutated, "cited-only status route")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["discovery_searches"]["list open claims"]["results"].insert(
        0, {"kind": "reading_route", "id": "shadow_open_route"}
    )
    assert_rejected(mutated, "open-claim status route priority")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["discovery_multi_searches"]["what is ruled out"]["results"] = []
    assert_rejected(mutated, "no-go programme route coverage")
    checks += 1

    checks += check_proof_plan_mutations(packets["proof_plans"])

    mutated = copy.deepcopy(packets)
    mutated["claim_statuses"]["conditional reduction"]["claims"][0][
        "remaining_open_proposition_ids"
    ] = []
    assert_rejected(mutated, "conditional status packet open boundary")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["claim_statuses"]["verified finite instance"]["claims"][0].pop(
        "bounded_domain", None
    )
    assert_rejected(mutated, "finite status packet bounded domain")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["claim_statuses"]["open"]["remaining_open_propositions"] = []
    assert_rejected(mutated, "open status packet proposition distinction")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["story_claims"]["half_greedy_two_thirds_band"]["claim"]["statement"] = (
        "The actual greedy orbit for 1/2 avoids the band."
    )
    assert_rejected(mutated, "#257 band orbit boundary")
    checks += 1

    mutated = copy.deepcopy(packets)
    last_producer = mutated["story_claims"]["last_producer_tail_escape_reduction"]
    last_producer["argument_neighbourhood"]["incoming"] = [
        row
        for row in last_producer["argument_neighbourhood"]["incoming"]
        if row["relation"] != "eliminates_case"
    ]
    assert_rejected(mutated, "#257 eliminated-case edge")
    checks += 1

    mutated = copy.deepcopy(packets)
    first_harmonic = mutated["story_claims"]["first_harmonic_certificate_interface"]
    first_harmonic["argument_neighbourhood"]["outgoing"] = [
        row
        for row in first_harmonic["argument_neighbourhood"]["outgoing"]
        if row["neighbour"]["id"] != "certificate_completeness"
    ]
    assert_rejected(mutated, "#249 completeness-consumer edge")
    checks += 1

    mutated = copy.deepcopy(packets)
    harmonic_pivot = mutated["story_claims"]["first_harmonic_pivot_decomposition"]
    harmonic_pivot["argument_neighbourhood"]["outgoing"] = [
        row
        for row in harmonic_pivot["argument_neighbourhood"]["outgoing"]
        if row["neighbour"]["id"] != "first_harmonic_certificate_interface"
    ]
    assert_rejected(mutated, "#249 harmonic-pivot consumer edge")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["expert_questions"]["results"][0]["status"] = "PROVED"
    assert_rejected(mutated, "expert-question OPEN boundary")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["expert_questions"]["results"][0]["exact_ask"] = ""
    assert_rejected(mutated, "expert-question exact ask")
    checks += 1

    mutated = copy.deepcopy(packets)
    first_question_id = mutated["expert_questions"]["results"][0]["id"]
    mutated["expert_question_details"][first_question_id]["results"][0][
        "consumer_declarations"
    ] = []
    assert_rejected(mutated, "expert-question checked consumer")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["expert_questions"]["packet_kind"] = "full_question"
    assert_rejected(mutated, "expert-question compact index")
    checks += 1

    mutated = copy.deepcopy(packets)
    first_question_id = next(iter(mutated["expert_question_details"]))
    mutated["expert_question_details"][first_question_id]["packet_kind"] = (
        "compact_index"
    )
    assert_rejected(mutated, "expert-question full drill-down")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["expert_questions_by_problem"]["249"]["results"].pop()
    mutated["expert_questions_by_problem"]["249"]["count"] = 2
    assert_rejected(mutated, "expert-question 5/3/2 problem split")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["expert_questions"]["results"][0]["classification"] = (
        "sufficient_for_counterexample"
    )
    assert_rejected(mutated, "expert-question classification partition")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["expert_questions"]["limits"] = [
        limit
        for limit in mutated["expert_questions"]["limits"]
        if "strictly weaker expert handoff" not in limit
    ]
    assert_rejected(mutated, "universal #257 expert-handoff boundary")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["expert_handoffs"]["domain_counts"] = {
        "mathematics": 6,
        "systems": 0,
    }
    assert_rejected(mutated, "cross-domain expert-handoff 5/1 split")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["expert_handoff_details"][diagnostic.SYSTEMS_EXPERT_QUESTION_ID][
        "results"
    ][0]["boundary"] = ""
    assert_rejected(mutated, "systems expert-handoff boundary")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["expert_handoffs"]["packet_kind"] = "full_question"
    assert_rejected(mutated, "cross-domain compact index")
    checks += 1

    mutated = copy.deepcopy(packets)
    first_handoff_id = next(iter(mutated["expert_handoff_details"]))
    mutated["expert_handoff_details"][first_handoff_id]["packet_kind"] = (
        "compact_index"
    )
    assert_rejected(mutated, "cross-domain full drill-down")
    checks += 1

    mutated = copy.deepcopy(packets)
    first_handoff_id = next(iter(mutated["expert_handoff_details"]))
    mutated["expert_handoff_details"][first_handoff_id]["results"][0][
        "plausible_alternatives"
    ][0]["consequence"] = ""
    assert_rejected(mutated, "full handoff alternative consequence")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["expert_handoff_protocol_check"] = "unchecked"
    assert_rejected(mutated, "expert-handoff protocol self-check")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["expert_handoffs"]["results"][0]["current_hypothesis"] = ""
    assert_rejected(mutated, "expert-handoff current hypothesis")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["expert_handoffs"]["results"][0]["hypothesis_confidence"] = (
        "certain"
    )
    assert_rejected(mutated, "expert-handoff hypothesis confidence")
    checks += 1

    mutated = copy.deepcopy(packets)
    alternatives = mutated["expert_handoffs"]["results"][0][
        "plausible_alternatives"
    ]
    alternatives[1]["id"] = alternatives[0]["id"]
    assert_rejected(mutated, "expert-handoff distinct alternatives")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["expert_handoffs"]["results"][0]["current_evidence"].pop()
    assert_rejected(mutated, "expert-handoff current evidence")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["expert_handoffs"]["results"][0]["discriminating_evidence"].pop()
    assert_rejected(mutated, "expert-handoff discriminating evidence")
    checks += 1

    mutated = copy.deepcopy(packets)
    second_channel = mutated["expert_handoff_details"][
        "XQ257-second-channel-separation"
    ]["results"][0]
    second_channel["consumer_declarations"].pop()
    assert_rejected(mutated, "#257 dual-consumer handoff")
    checks += 1

    mutated = copy.deepcopy(packets)
    pivot = mutated["expert_handoff_details"][
        "XQ249-pivot-decorrelation"
    ]["results"][0]
    pivot["exact_ask"] = pivot["exact_ask"].replace("h <= L-s", "h may exceed L-s")
    assert_rejected(mutated, "#249 pivot overlap condition")
    checks += 1

    mutated = copy.deepcopy(packets)
    pivot = mutated["expert_handoff_details"][
        "XQ249-pivot-decorrelation"
    ]["results"][0]
    pivot_negative = next(
        row for row in pivot["plausible_alternatives"]
        if row["id"] == "no_cofinal_joint_witness"
    )
    pivot_negative["statement"] = (
        "Infinitely many blocks fail one clause of the socket."
    )
    assert_rejected(mutated, "#249 pivot exact complement")
    checks += 1

    mutated = copy.deepcopy(packets)
    adjacent = mutated["expert_handoff_details"][
        "XQ249-adjacent-phase-separation"
    ]["results"][0]
    phase_locking = next(
        row for row in adjacent["plausible_alternatives"]
        if row["id"] == "phase_locking"
    )
    phase_locking["statement"] = (
        "Infinitely many blocks contain no good adjacent pair."
    )
    assert_rejected(mutated, "#249 adjacent eventual negation")
    checks += 1

    mutated = copy.deepcopy(packets)
    adjacent = mutated["expert_handoff_details"][
        "XQ249-adjacent-phase-separation"
    ]["results"][0]
    adjacent["exact_ask"] = adjacent["exact_ask"].replace(
        "16(2X+h+L+2) <= 2^L",
        "the dyadic-room inequality",
    )
    assert_rejected(mutated, "#249 adjacent explicit room inequality")
    checks += 1

    mutated = copy.deepcopy(packets)
    second_channel = mutated["expert_handoff_details"][
        "XQ257-second-channel-separation"
    ]["results"][0]
    second_channel["current_evidence"].append(
        "The reduced denominator height is on the scale 2^(Theta(n^2))."
    )
    assert_rejected(mutated, "#257 unproved height law")
    checks += 1

    mutated = copy.deepcopy(packets)
    second_channel = mutated["expert_handoff_details"][
        "XQ257-second-channel-separation"
    ]["results"][0]
    second_channel["current_evidence"][1] = (
        second_channel["current_evidence"][1]
        .replace("1 <= n <= 1000", "1 <= n <= 100")
        .replace("Rank 1001 onward", "Rank 101 onward")
    )
    assert_rejected(mutated, "#257 measured range contraction")
    checks += 1

    mutated = copy.deepcopy(packets)
    second_channel = mutated["expert_handoff_details"][
        "XQ257-second-channel-separation"
    ]["results"][0]
    second_channel["current_evidence"][2] = (
        "The finite orbit looks symbolically constrained."
    )
    assert_rejected(mutated, "#257 short-word discriminator")
    checks += 1

    mutated = copy.deepcopy(packets)
    middle = mutated["expert_handoff_details"][
        "XQ257-middle-producer-tail-escape"
    ]["results"][0]
    middle["exact_ask"] = middle["exact_ask"].replace(
        "C_s = -3 or (1 <= C_s and Theta_s < C_s)",
        "Theta_s < C_s whenever C_s != -3",
    )
    assert_rejected(mutated, "#257 middle exact disjunction")
    checks += 1

    mutated = copy.deepcopy(packets)
    middle = mutated["expert_handoff_details"][
        "XQ257-middle-producer-tail-escape"
    ]["results"][0]
    middle["plausible_alternatives"][1]["id"] = "old_cell_partition"
    assert_rejected(mutated, "#257 middle alternative partition")
    checks += 1

    mutated = copy.deepcopy(packets)
    systems = mutated["expert_handoff_details"][
        diagnostic.SYSTEMS_EXPERT_QUESTION_ID
    ]["results"][0]
    systems["acceptance"] = {"problem_status": "OPEN"}
    assert_rejected(mutated, "respondent packet evaluator-answer leak")
    checks += 1

    mutated = copy.deepcopy(packets)
    systems = mutated["expert_handoff_details"][
        diagnostic.SYSTEMS_EXPERT_QUESTION_ID
    ]["results"][0]
    systems.pop("manual_review_rubric")
    assert_rejected(mutated, "respondent packet manual rubric")
    checks += 1

    mutated = copy.deepcopy(packets)
    systems = mutated["expert_handoff_details"][
        diagnostic.SYSTEMS_EXPERT_QUESTION_ID
    ]["results"][0]
    systems["input_template"]["farey_numerical_delta"] = 0
    assert_rejected(mutated, "respondent packet scalar answer key")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["expert_handoff_review_template"]["criteria"].pop(
        next(iter(mutated["expert_handoff_review_template"]["criteria"]))
    )
    assert_rejected(mutated, "expert-handoff review-template shape")
    checks += 1

    conditional = next(
        claim_id for claim_id, packet in packets["claims"].items()
        if packet["claim"]["status"] == "conditional reduction"
    )
    mutated = copy.deepcopy(packets)
    mutated["claims"][conditional]["claim"]["remaining_open_proposition_ids"] = []
    assert_rejected(mutated, "conditional-open link")
    checks += 1

    finite = next(
        claim_id for claim_id, packet in packets["claims"].items()
        if packet["claim"]["status"] == "verified finite instance"
    )
    mutated = copy.deepcopy(packets)
    mutated["claims"][finite]["claim"].pop("bounded_domain", None)
    assert_rejected(mutated, "finite bound")
    checks += 1

    source_key = next(iter(packets["sources"]))
    mutated = copy.deepcopy(packets)
    mutated["sources"][source_key]["source"]["source_ref"] = "wrong.lean:1"
    assert_rejected(mutated, "source coordinate")
    checks += 1

    print(
        "test_cold_clone_comprehension: bounded baseline passed; "
        f"{checks - 3} semantic mutations were rejected; "
        f"route-memory cold-clone checks={route_memory_checks}"
    )
    return 0


def cli() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proof-plans-only", action="store_true")
    args = parser.parse_args()
    if args.proof_plans_only:
        proof_plans = diagnostic.collect_proof_plan_packets()
        diagnostic.validate_proof_plan_packets(proof_plans)
        rejected = check_proof_plan_mutations(proof_plans)
        print(
            "test_cold_clone_comprehension: proof-plan baseline passed; "
            f"{rejected} semantic mutations were rejected"
        )
        return 0
    return main()


if __name__ == "__main__":
    raise SystemExit(cli())
