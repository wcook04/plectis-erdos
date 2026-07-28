#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial tests for bounded cold-clone comprehension."""

from __future__ import annotations

import argparse
import copy
import re

import check_cold_clone_comprehension as diagnostic


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


def remove_semantic_anchor(text: str, token: str) -> str:
    """Delete every case-insensitive occurrence seen by the production check."""
    return re.sub(
        re.escape(diagnostic.normalized(token)),
        "",
        text,
        flags=re.IGNORECASE,
    )


def main() -> int:
    packets = diagnostic.collect_agent_packets()
    summary = packets["summary"]
    quick_summary = diagnostic.quick_summary()
    human_surfaces = {
        path: diagnostic.read(path) for path in diagnostic.HUMAN_SURFACES
    }
    diagnostic.validate_human_first_contact(quick_summary, human_surfaces)
    diagnostic.validate_human_first_contact(summary, human_surfaces)
    gateway_paper = diagnostic.read(diagnostic.GATEWAY_PAPER)
    diagnostic.validate_gateway_opening(gateway_paper)
    agents = diagnostic.read("AGENTS.md")
    claude = diagnostic.read("CLAUDE.md")
    diagnostic.validate_cross_agent_entry(agents, claude)
    diagnostic.validate_agent_packets(packets)

    checks = 3
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

    mutated = copy.deepcopy(human_surfaces)
    mutated["README.md"] = (
        "This is an exceptional and impressive research-grade achievement.\n"
        + mutated["README.md"]
    )
    assert_human_rejected(summary, mutated, "self-appraisal language")
    checks += 1

    mutated_paper = gateway_paper.replace(
        "An unbounded certificate supply", ""
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

    try:
        diagnostic.validate_cross_agent_entry(agents, claude.replace("@AGENTS.md", ""))
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("Claude shared-instruction import deletion escaped")

    try:
        diagnostic.validate_cross_agent_entry(
            agents.replace(
                "## Machine-first mathematics route",
                "## General reading",
            ),
            claude,
        )
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("shared machine-first entry deletion escaped")

    try:
        diagnostic.validate_cross_agent_entry(
            agents,
            claude.replace("machine-first", "paper-first"),
        )
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("Claude machine-first adapter deletion escaped")

    mutated = copy.deepcopy(packets)
    mutated["summary"]["proof_authority"] = "unverified"
    assert_rejected(mutated, "proof authority")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["problem_progress"]["semantic_cells"] = []
    assert_rejected(mutated, "problem-progress machine-first route")
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
        f"{checks - 3} semantic mutations were rejected"
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
