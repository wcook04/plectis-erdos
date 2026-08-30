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
    assert packet["kind"] == "repository_overview"
    coverage = packet["coverage_receipt"]
    assert coverage["mathematical_programme_count"] == len(
        coverage["mathematical_programme_ids"]
    )
    assert coverage["mathematical_programme_count"] >= 10
    assert coverage["claim_status_class_count"] == 7
    assert coverage["remaining_open_proposition_count"] == len(
        coverage["remaining_open_proposition_ids"]
    )
    assert coverage["publication_family_count"] >= 21
    assert coverage["publication_family_count"] == len(
        coverage["publication_family_ids"]
    )
    assert coverage["curated_claim_count"] >= 99
    assert coverage["principal_claim_count"] == len(
        packet["principal_claims"]
    )
    assert len(packet["publication_family_index"]) == (
        coverage["publication_family_count"]
    )
    assert len(packet["repository_map"]) == 6
    assert len(packet["answer_contract"]["required_coverage"]) == 5
    assert packet["companion_repository"]["name"] == "plectis"
    assert packet["companion_repository"]["repository"] == (
        "https://github.com/wcook04/plectis"
    )
    assert "companion, not dependency" in (
        packet["companion_repository"]["relationship"]
    )
    for problem in packet["problem_fleet"]:
        expected = (
            "python3 scripts/query_route_memory.py --problem "
            f"{problem['erdos_number']}"
        )
        assert problem["route_memory"] == expected
    assert packet["next"]["route_memory"] == (
        "python3 scripts/query_route_memory.py --problem <problem_number>"
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
    assert ordinary["query_interpretation"]["routed_by"] == (
        "ordinary_cold_reader_phrase"
    )
    assert "weight reductions" in query_corpus.render_card(ordinary)

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
        assert query_corpus.is_repository_overview_query(question)

    for specific_question in (
        "Explain why half-value membership remains open.",
        "What are the interesting results for Erdos 249?",
        "Walk me through theorem half_mem_of_greedy_hits.",
    ):
        assert not query_corpus.is_repository_overview_query(
            specific_question
        )

    papers = run_query("--papers")
    paper_question = run_query(
        "--ask",
        "Which papers should I read, in what order, and what does each establish?",
    )
    assert papers["kind"] == "paper_reading_guide"
    assert paper_question["kind"] == "paper_reading_guide"
    assert papers["paper_count"] == len(papers["papers"])
    assert papers["paper_count"] >= 2
    assert papers["default_gateway"]["id"] == "human_exposition"
    assert papers["default_gateway"]["rendered_available_in_checkout"]
    assert papers["companion_repository"]["name"] == "plectis"
    routed_artifacts = {
        step["artifact_id"]
        for step in papers["recommended_routes"]["understand_the_mathematics"]
        if "artifact_id" in step
    }
    registered = {
        row["id"]: row
        for row in papers["registered_publication_artifacts"]
    }
    assert routed_artifacts <= set(registered)
    assert all(
        registered[artifact_id]["source_available_in_checkout"]
        and registered[artifact_id]["rendered_available_in_checkout"]
        for artifact_id in routed_artifacts
    )
    assert papers["paper_count"] >= 12
    assert papers["clone_local_paper_index"] == "docs/papers/README.md"
    assert all(
        row["preferred_read_path"]
        and row["full_text_available_in_checkout"]
        for row in papers["papers"]
    )
    assert "papers are exposition" in query_corpus.render_card(papers)
    for question in (
        "Which paper should I read?",
        "What does each paper establish?",
        "Where are the papers?",
        "Show me the paper reading order.",
    ):
        assert query_corpus.is_paper_reading_query(question)

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
