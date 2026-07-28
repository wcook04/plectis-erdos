#!/usr/bin/env python3
"""Validate complete ordinary-language cold-clone corpus orientation."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import query_corpus


ROOT = Path(__file__).resolve().parents[1]


def run_query(*args: str) -> dict:
    completed = subprocess.run(
        [sys.executable, "scripts/query_corpus.py", *args],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return json.loads(completed.stdout)


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


def main() -> int:
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
