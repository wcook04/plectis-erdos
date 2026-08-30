#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep public navigation from treating unpublished work as corpus authority."""

from __future__ import annotations

import json
import subprocess
import sys
from copy import deepcopy
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
QUERY = ROOT / "scripts" / "query_corpus.py"
PUBLIC_PROBLEM_IDS = (68, 243, 249, 251, 257, 269, 1041, 1049)


def read(rel: str) -> str:
    return (ROOT / rel).read_text(encoding="utf-8")


def summary_packet() -> dict[str, object]:
    completed = subprocess.run(
        [sys.executable, str(QUERY)],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return json.loads(completed.stdout)


def boundary_errors(
    agents: str,
    scope: str,
    readme: str,
    claims: dict[str, object],
    methodology: dict[str, object],
    summary: dict[str, object],
) -> list[str]:
    """Return every missing public-proof boundary required at first contact."""
    errors: list[str] = []
    for phrase in (
        "not an entrypoint into any private development system",
        "Work only from the files\nin this repository",
        "never infer unpublished results or private machinery",
    ):
        if phrase not in agents:
            errors.append(f"agent entry lost public-boundary phrase: {phrase}")
    for phrase in (
        "Unreleased work, private repositories",
        "not part of\nthe public proof artefact",
    ):
        if phrase not in scope:
            errors.append(f"scope lost public-boundary phrase: {phrase}")
    if "do not infer results from private or unreleased work" not in readme:
        errors.append("README lost private-or-unreleased inference boundary")

    non_claims = {row["id"] for row in claims["non_claims"]}
    required_non_claims = {
        "not_private_root_equivalence",
        "not_hidden_proof_body_authority",
        "not_provider_proof_authority",
    }
    missing_non_claims = sorted(required_non_claims - non_claims)
    if missing_non_claims:
        errors.append(f"claim registry lost public-boundary non-claims: {missing_non_claims}")

    anti_principles = {row["id"]: row["statement"] for row in methodology["anti_principles"]}
    private_work_rule = anti_principles.get(
        "anti_principle.do_not_treat_graph_model_or_private_work_as_proof", ""
    )
    if "private proof sketch is not public proof authority" not in private_work_rule:
        errors.append("methodology lost private-proof authority boundary")

    projected_non_claims = {row["id"] for row in summary["non_claims"]}
    missing_projected = sorted(required_non_claims - projected_non_claims)
    if missing_projected:
        errors.append(f"bounded query lost public-boundary non-claims: {missing_projected}")
    return errors


def prior_art_errors(prior_art: str) -> list[str]:
    """Keep bibliography navigation subordinate to exact claim evidence."""
    required = (
        "python3 scripts/query_corpus.py --route trace_prior_art",
        "python3 scripts/query_corpus.py --claim <claim_id>",
        "remaining-open links",
        "is an evidence statement, not a novelty",
        "Failure to identify a matching source is\nnot evidence of novelty",
        "Lean source checked by the pinned Lean kernel remains\nproof authority",
    )
    return [
        f"prior-art map lost claim-faithful comparison boundary: {phrase}"
        for phrase in required
        if phrase not in prior_art
    ]


def related_problem_errors(related: str) -> list[str]:
    """Reject collapse between catalogue status and local mathematical effect."""
    required = (
        "external catalogue status and the local release status are separate facts",
        "--open remaining_open.erdos_249_irrationality",
        "--open remaining_open.universal_257_all_infinite_supports",
        "--claim prime_support_irrationality",
        "--claim sigma_transcendence",
        "The first two packets are `open`; the latter two are `cited only`",
        "records an `advances_open_target` edge",
        "untouched analogy",
    )
    return [
        f"related-problem map lost typed relation boundary: {phrase}"
        for phrase in required
        if phrase not in related
    ]


def portfolio_visibility_errors(packet: dict[str, object]) -> list[str]:
    """Require broad, source-bound result visibility without freezing a shortlist."""
    errors: list[str] = []
    expected = set(PUBLIC_PROBLEM_IDS)
    expected_labels = {f"erdos_{problem}" for problem in PUBLIC_PROBLEM_IDS}
    problem_ids = packet.get("problem_ids")
    if set(problem_ids or []) != expected_labels:
        errors.append("external-verification packet must cover exactly the eight public problems")

    results = packet.get("main_results")
    if not isinstance(results, list):
        return ["external-verification packet must expose a main_results portfolio"]

    by_problem: dict[int, list[dict[str, object]]] = {problem: [] for problem in PUBLIC_PROBLEM_IDS}
    seen_ids: set[object] = set()
    for row in results:
        if not isinstance(row, dict):
            errors.append("external-verification portfolio contains a non-record result")
            continue
        problem = row.get("problem")
        if problem not in expected:
            errors.append(f"external-verification result names an unknown problem: {problem!r}")
            continue
        result_id = row.get("id")
        if not isinstance(result_id, str) or not result_id:
            errors.append(f"problem {problem} result lacks a stable id")
        elif result_id in seen_ids:
            errors.append(f"external-verification result id is duplicated: {result_id}")
        else:
            seen_ids.add(result_id)
        for field in (
            "statement",
            "boundary",
            "original_declaration",
            "original_source",
            "wrapper_declaration",
        ):
            if not isinstance(row.get(field), str) or not row[field].strip():
                errors.append(f"problem {problem} result lacks source-bound {field}")
        source = row.get("original_source", "")
        wrapper = row.get("wrapper_declaration", "")
        if isinstance(source, str) and not source.startswith(("Erdos249257/", "ErdosProblems/")):
            errors.append(f"problem {problem} result has a non-public source route")
        if isinstance(wrapper, str) and not wrapper.startswith("Erdos249257.ExternalVerification."):
            errors.append(f"problem {problem} result has an unbound verification wrapper")
        boundary = str(row.get("boundary", "")).casefold()
        if not any(token in boundary for token in ("does not", "remain", "not ", "no ", "only ")):
            errors.append(f"problem {problem} result boundary lacks an explicit claim ceiling")
        if any(token in boundary for token in ("solves erdos", "settles erdos", "proves the problem")):
            errors.append(f"problem {problem} result boundary overclaims closure")
        by_problem[problem].append(row)

    for problem, rows in by_problem.items():
        if len(rows) < 2:
            errors.append(
                f"problem {problem} portfolio is underexposed: retain at least two distinct strong results"
            )
        identities = {
            (
                row.get("id"),
                row.get("original_declaration"),
                row.get("wrapper_declaration"),
            )
            for row in rows
        }
        if len(identities) != len(rows):
            errors.append(f"problem {problem} portfolio contains duplicate result identities")
    return errors


def main() -> int:
    """Assert that every first-contact surface preserves the public membrane."""
    agents = read("AGENTS.md")
    scope = read("SCOPE.md")
    readme = read("README.md")
    claims = json.loads(read("docs/claims.json"))
    methodology = json.loads(read("docs/methodology.json"))
    prior_art = read("docs/PRIOR_ART.md")
    related = read("docs/RELATED_PROBLEMS.md")
    summary = summary_packet()
    assert not boundary_errors(agents, scope, readme, claims, methodology, summary)
    assert not prior_art_errors(prior_art)
    assert not related_problem_errors(related)
    verification_packet = claims["external_verification_packet"]
    assert not portfolio_visibility_errors(verification_packet)

    missing_agent_rule = agents.replace(
        "never infer unpublished results or private machinery", "", 1
    )
    assert any(
        "agent entry lost public-boundary phrase" in error
        for error in boundary_errors(
            missing_agent_rule, scope, readme, claims, methodology, summary
        )
    )
    missing_projection = deepcopy(summary)
    missing_projection["non_claims"] = [
        row for row in summary["non_claims"] if row["id"] != "not_hidden_proof_body_authority"
    ]
    assert any(
        "bounded query lost public-boundary non-claims" in error
        for error in boundary_errors(
            agents, scope, readme, claims, methodology, missing_projection
        )
    )
    novelty_from_absence = prior_art.replace(
        "Failure to identify a matching source is\nnot evidence of novelty.",
        "Failure to identify a matching source establishes novelty.",
        1,
    )
    assert any(
        "prior-art map lost claim-faithful comparison boundary" in error
        for error in prior_art_errors(novelty_from_absence)
    )
    missing_claim_route = prior_art.replace(
        "python3 scripts/query_corpus.py --claim <claim_id>", "", 1
    )
    assert any(
        "prior-art map lost claim-faithful comparison boundary" in error
        for error in prior_art_errors(missing_claim_route)
    )
    collapsed_relation = related.replace(
        "The first two packets are `open`; the latter two are `cited only`.",
        "Every related solved problem is progress on the open targets.",
        1,
    )
    assert any(
        "related-problem map lost typed relation boundary" in error
        for error in related_problem_errors(collapsed_relation)
    )
    missing_open_handle = related.replace(
        "--open remaining_open.universal_257_all_infinite_supports", "", 1
    )
    assert any(
        "related-problem map lost typed relation boundary" in error
        for error in related_problem_errors(missing_open_handle)
    )
    underexposed_portfolio = deepcopy(verification_packet)
    underexposed_portfolio["main_results"] = [
        row
        for row in verification_packet["main_results"]
        if row["problem"] != 1049
        or row["id"] == "three_halves_corridor_no_go"
    ]
    assert any(
        "problem 1049 portfolio is underexposed" in error
        for error in portfolio_visibility_errors(underexposed_portfolio)
    )
    duplicate_portfolio = deepcopy(verification_packet)
    duplicate_portfolio["main_results"][1] = deepcopy(duplicate_portfolio["main_results"][0])
    assert any(
        "result id is duplicated" in error
        for error in portfolio_visibility_errors(duplicate_portfolio)
    )
    overclaiming_portfolio = deepcopy(verification_packet)
    overclaiming_portfolio["main_results"][0]["boundary"] = (
        "This result solves Erdos 68 and supplies independent proof authority."
    )
    assert any(
        "boundary overclaims closure" in error
        for error in portfolio_visibility_errors(overclaiming_portfolio)
    )
    private_source_portfolio = deepcopy(verification_packet)
    private_source_portfolio["main_results"][0]["original_source"] = (
        "/private/development/hidden.lean"
    )
    assert any(
        "non-public source route" in error
        for error in portfolio_visibility_errors(private_source_portfolio)
    )

    print(
        "test_public_artifact_boundary: first-contact surfaces reject "
        "private or unpublished proof authority and novelty inference; "
        "portfolio visibility preserves all eight problems and multiple "
        "source-bound strong results; 10 negative fixtures rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
