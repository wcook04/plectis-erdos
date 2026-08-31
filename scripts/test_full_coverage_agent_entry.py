#!/usr/bin/env python3
"""Validate complete ordinary-language cold-clone corpus orientation."""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path
from unittest.mock import patch

import query_corpus
import validation_singleflight as singleflight


ROOT = Path(__file__).resolve().parents[1]
ENVIRONMENT_CONTRACT = "clean_committed_snapshot_subprocess_environment_v1"


def require(condition: bool, message: str) -> None:
    """Keep the environment contract active when Python is run with -O."""
    if not condition:
        raise AssertionError(message)


def run_query(*args: str) -> dict:
    completed = subprocess.run(
        [sys.executable, "scripts/query_corpus.py", *args],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
        env=singleflight.command_environment(),
        timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
    )
    return json.loads(completed.stdout)


def check_query_environment() -> None:
    """Prove cold-clone overview queries ignore ambient process selectors."""
    hostile_environment = {
        "GIT_DIR": "/private/wrong-git-dir",
        "GIT_NAMESPACE": "refs/namespaces/wrong-release",
        "GIT_REPLACE_REF_BASE": "refs/replace/",
        "PYTHONPATH": "/private/wrong-python-path",
        "LC_ALL": "C",
        "LANG": "C",
        "PATH": "/private/wrong-bin",
    }
    completed = subprocess.CompletedProcess(
        [sys.executable, "scripts/query_corpus.py"],
        0,
        stdout="{}",
        stderr="",
    )
    with patch.dict(os.environ, hostile_environment, clear=False):
        with patch.object(subprocess, "run", return_value=completed) as run:
            require(run_query("--overview") == {}, "query result was not returned")

    require(len(run.call_args_list) == 1, "overview query was not exercised")
    kwargs = run.call_args.kwargs
    sanitized = kwargs["env"]
    for key in (
        "GIT_DIR",
        "GIT_NAMESPACE",
        "GIT_REPLACE_REF_BASE",
        "PYTHONPATH",
    ):
        require(key not in sanitized, f"ambient {key} leaked into overview query")
    require(sanitized["LC_ALL"] == "C.UTF-8", "canonical locale missing")
    require(sanitized["LANG"] == "C.UTF-8", "canonical LANG missing")
    require(sanitized["PATH"] == os.defpath, "ambient PATH leaked into overview query")
    require(
        kwargs["timeout"] == singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
        "overview query timeout drifted",
    )
    require(
        ENVIRONMENT_CONTRACT
        == "clean_committed_snapshot_subprocess_environment_v1",
        "full-coverage query environment contract drifted",
    )


def assert_complete(packet: dict) -> None:
    require(packet["kind"] == "repository_overview", "overview packet kind drifted")
    coverage = packet["coverage_receipt"]
    require(
        coverage["mathematical_programme_count"]
        == len(coverage["mathematical_programme_ids"]),
        "mathematical programme coverage count drifted",
    )
    require(
        coverage["mathematical_programme_count"] >= 10,
        "mathematical programme coverage regressed",
    )
    require(
        coverage["claim_status_class_count"] == 7,
        "claim status class coverage drifted",
    )
    require(
        coverage["remaining_open_proposition_count"]
        == len(coverage["remaining_open_proposition_ids"]),
        "open proposition coverage count drifted",
    )
    require(
        coverage["publication_family_count"] >= 21,
        "publication family coverage regressed",
    )
    require(
        coverage["publication_family_count"] == len(coverage["publication_family_ids"]),
        "publication family coverage count drifted",
    )
    require(
        coverage["curated_claim_count"] >= 99,
        "curated claim coverage regressed",
    )
    require(
        coverage["principal_claim_count"] == len(packet["principal_claims"]),
        "principal claim coverage count drifted",
    )
    require(
        len(packet["publication_family_index"]) == coverage["publication_family_count"],
        "publication family index count drifted",
    )
    require(len(packet["repository_map"]) == 6, "repository map coverage drifted")
    require(
        len(packet["answer_contract"]["required_coverage"]) == 5,
        "answer contract coverage drifted",
    )
    require(
        packet["companion_repository"]["name"] == "plectis",
        "companion repository name drifted",
    )
    require(
        packet["companion_repository"]["repository"]
        == "https://github.com/wcook04/plectis",
        "companion repository URL drifted",
    )
    require(
        "companion, not dependency" in packet["companion_repository"]["relationship"],
        "companion relationship boundary drifted",
    )
    for problem in packet["problem_fleet"]:
        expected = (
            "python3 scripts/query_route_memory.py --problem "
            f"{problem['erdos_number']}"
        )
        require(
            problem["route_memory"] == expected,
            f"route-memory command drifted for #{problem['erdos_number']}",
        )
    require(
        packet["next"]["route_memory"]
        == "python3 scripts/query_route_memory.py --problem <problem_number>",
        "next route-memory command drifted",
    )


def main() -> int:
    check_query_environment()
    explicit = run_query("--overview")
    ordinary = run_query(
        "--ask",
        "What is in this repository? Give me full coverage of everything here.",
    )
    assert_complete(explicit)
    assert_complete(ordinary)
    require(
        ordinary["query_interpretation"]["routed_by"]
        == "ordinary_cold_reader_phrase",
        "ordinary overview route drifted",
    )
    result_family_contract = ordinary["problem_result_family_contract"]
    require(
        result_family_contract["source"]
        == "docs/claims.json::external_verification_packet.review_matrix",
        "ordinary overview lost the authoritative result-family source",
    )
    require(
        result_family_contract["problem_fleet_source_projection"]
        == "inherited_once_here_instead_of_repeated_per_problem",
        "ordinary overview lost the explicit result-family inheritance marker",
    )

    for question in (
        "What's in this repo?",
        "What does this repo contain?",
        "Give me a complete repository overview.",
        "Tell me what is here.",
        "Give me the lay of the land.",
        "Walk me through this codebase.",
        "What are the interesting and non-trivial results?",
        "Explain this project to me.",
        "What has been formalized?",
        "Give me a comprehensive tour.",
        "What is Plectis Lean?",
        "Tell me everything interesting and non-trivial in this repo.",
    ):
        require(
            query_corpus.is_repository_overview_query(question),
            f"overview question was not recognized: {question}",
        )

    for specific_question in (
        "Explain why half-value membership remains open.",
        "What are the interesting results for Erdos 249?",
        "Walk me through theorem half_mem_of_greedy_hits.",
    ):
        require(
            not query_corpus.is_repository_overview_query(specific_question),
            f"specific question was misrouted as an overview: {specific_question}",
        )

    papers = run_query("--papers", "--format", "json")
    paper_question = run_query(
        "--ask",
        "Which papers should I read, in what order, and what does each establish?",
    )
    require(papers["kind"] == "paper_reading_guide", "papers packet kind drifted")
    require(
        paper_question["kind"] == "paper_reading_guide",
        "paper question route drifted",
    )
    require(
        papers["paper_count"] == len(papers["papers"]),
        "paper count does not match paper entries",
    )
    require(papers["paper_count"] >= 2, "paper reading guide coverage regressed")
    require(
        papers["default_gateway"]["id"] == "human_exposition",
        "paper gateway drifted",
    )
    require(
        papers["default_gateway"]["rendered_available_in_checkout"],
        "paper gateway is not checkout-local",
    )
    require(
        papers["companion_repository"]["name"] == "plectis",
        "paper companion repository drifted",
    )
    routed_artifacts = {
        step["artifact_id"]
        for step in papers["recommended_routes"]["understand_the_mathematics"]
        if "artifact_id" in step
    }
    registered = {
        row["id"]: row
        for row in papers["registered_publication_artifacts"]
    }
    require(
        routed_artifacts <= set(registered),
        "paper route referenced an unregistered artifact",
    )
    require(
        all(
            registered[artifact_id]["source_available_in_checkout"]
            and registered[artifact_id]["rendered_available_in_checkout"]
            for artifact_id in routed_artifacts
        ),
        "paper route referenced an unavailable artifact",
    )
    require(papers["paper_count"] >= 12, "full paper corpus coverage regressed")
    require(
        papers["clone_local_paper_index"] == "docs/papers/README.md",
        "clone-local paper index route drifted",
    )
    require(
        all(
            row["preferred_read_path"]
            and row["full_text_available_in_checkout"]
            for row in papers["papers"]
        ),
        "paper entry lost a checkout-local reading path",
    )
    require(
        "papers are exposition" in query_corpus.render_card(papers),
        "paper reading card lost its exposition boundary",
    )
    for question in (
        "Which paper should I read?",
        "What does each paper establish?",
        "Where are the papers?",
        "Show me the paper reading order.",
    ):
        require(
            query_corpus.is_paper_reading_query(question),
            f"paper question was not recognized: {question}",
        )

    print(
        "full coverage agent entry: pass "
        f"({ordinary['coverage_receipt']['mathematical_programme_count']} programmes; "
        f"{ordinary['coverage_receipt']['claim_status_class_count']} status classes; "
        f"{ordinary['coverage_receipt']['remaining_open_proposition_count']} exact open; "
        "companion surfaced)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
