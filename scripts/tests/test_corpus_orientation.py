#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Focused contracts for the bounded mathematical-signal first read."""

from __future__ import annotations

import _test_bootstrap  # noqa: F401

import json
import sys
import contextlib
import io
from unittest.mock import patch
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

import build_corpus_descriptor as builder


def test_descriptor_refresh_preserves_authored_readme() -> None:
    readme = ROOT / "README.md"
    original = readme.read_bytes()
    outputs = []
    def capture(path, content):
        outputs.append(path)
        return False
    with patch.object(sys, "argv", ["build_corpus_descriptor.py"]), \
         patch.object(builder, "write_if_changed", side_effect=capture), \
         contextlib.redirect_stdout(io.StringIO()):
        assert builder.main() == 0
    assert readme not in outputs, "descriptor refresh must not own the human README"
    assert readme.read_bytes() == original
    assert builder.OUTPUT in outputs
    assert builder.ORIENTATION_JSON in outputs
    assert builder.ORIENTATION_MARKDOWN in outputs


def test_palomar_signal_join_and_first_read_order() -> None:
    claims = json.loads((ROOT / "docs" / "claims.json").read_text(encoding="utf-8"))
    atlas = json.loads(
        (ROOT / "docs" / "declaration_atlas.json").read_text(encoding="utf-8")
    )
    orientation = builder.build_orientation(claims, atlas)
    assert orientation["scale"] == atlas["summary"]
    assert orientation["generated_source_share"] == builder.measured_generated_share(atlas)
    signal = orientation["mathematical_signal_first"]
    ranking = json.loads(
        (ROOT / "docs" / "PALOMAR_RESULT_SHOWCASE.json").read_text(encoding="utf-8")
    )["candidate_ranking"]
    main_results = {
        row["wrapper_declaration"]: row
        for row in claims["external_verification_packet"]["main_results"]
    }

    assert len(signal) == len(ranking)
    assert [row["rank"] for row in signal] == list(range(1, len(ranking) + 1))
    for candidate, row in zip(ranking, signal):
        result = main_results[candidate["declaration"]]
        assert row["family_id"] == candidate["family_id"]
        assert row["selection_status"] == candidate["selection_status"]
        assert row["interface"] == candidate["declaration"]
        assert row["source_declaration"] == result["original_declaration"]
        assert row["boundary"] == result["boundary"]

    markdown = builder.render_orientation_markdown(
        orientation, builder.build_selection_navigation(claims)
    )
    generated_orientation = json.loads(
        (ROOT / "docs" / "orientation.json").read_text(encoding="utf-8")
    )
    generated_markdown = (ROOT / "docs" / "reference" / "ORIENTATION.md").read_text(
        encoding="utf-8"
    )
    queries = orientation["queries"]
    assert queries["command"] == "python3 scripts/query_corpus.py"
    assert queries["selectors"]["route"] == "--route <route_or_programme_id>"
    assert all(
        not selector.startswith("python3 ")
        for selector in queries["selectors"].values()
    )
    assert generated_orientation["mathematical_signal_first"] == signal
    presentation = orientation["mathematical_signal_presentation"]
    showcase = json.loads(
        (ROOT / "docs" / "PALOMAR_RESULT_SHOWCASE.json").read_text(encoding="utf-8")
    )
    source_tiers = showcase["selection_contract"]["presentation_tiers"]
    assert presentation["authority"] == (
        "docs/PALOMAR_RESULT_SHOWCASE.json::selection_contract"
    )
    assert [row["tier_id"] for row in presentation["tiers"]] == [
        row["tier_id"] for row in sorted(source_tiers, key=lambda row: row["order"])
    ]
    assert presentation["relational_placements"]
    assert generated_markdown == markdown
    assert markdown.index("## Release provenance") < markdown.index("## What a claim status asserts")
    assert "--publication-architecture" in markdown
    assert "../EXTERNAL_VERIFICATION.md" in markdown
    assert "../orientation.json" in markdown
    assert "## Mathematical signal first" not in markdown
    assert "Interface, source declaration, and exact boundary, by rank" not in markdown
    for row in orientation["remaining_open_propositions"]:
        assert row["id"] in markdown and row["statement"] in markdown
    for row in orientation["mathematical_programmes"]:
        assert row["id"] in markdown and row["title"] in markdown and row["claim_ceiling"] in markdown
    assert len(
        (json.dumps(orientation, ensure_ascii=False, separators=(",", ":")) + "\n").encode(
            "utf-8"
        )
    ) <= builder.ORIENTATION_MAX_BYTES
    assert len(markdown.encode("utf-8")) <= builder.orientation_markdown_budget_bytes(
        len(orientation["remaining_open_propositions"]),
        len(orientation["mathematical_programmes"]),
    )


def test_descriptor_exposes_an_exact_commit_mathematical_reasoning_route() -> None:
    descriptor = builder.build()
    access = descriptor["access"]
    route = access["profiles"]["mathematical_reasoning"]

    assert access["schema"] == "plectis-public-corpus-access/1"
    assert access["clone_url"].endswith(".git")
    assert route["checkout_shape"] == "blobless_exact_commit_full_worktree"
    assert "scripts/query_corpus.py" in route["required_surfaces"]
    assert "research_corpus" in route["required_surfaces"]
    commands = route["pinned_materialization_commands"]
    assert any("<remote_ref>" in command for command in commands)
    assert any("<published_commit>" in command for command in commands)
    assert commands[-1].endswith("scripts/query_corpus.py --format card")
    assert "--depth=1" in commands[0]

    profiles = access["profiles"]
    assert set(profiles) == {
        "mathematical_reasoning",
        "lean_proof_only",
        "human_reader",
        "current_generated_corpus",
        "release_history",
    }
    assert any(
        "scripts/lean-sparse-checkout" in command
        for command in profiles["lean_proof_only"]["commands"]
    )
    assert profiles["lean_proof_only"]["commands"][-1].endswith(
        "scripts/lean_fast_build.py --jobs 2"
    )
    assert any(
        "scripts/reader-sparse-checkout" in command
        for command in profiles["human_reader"]["commands"]
    )
    assert "--depth=1" in profiles["current_generated_corpus"]["commands"][0]
    assert "--depth=1" not in profiles["release_history"]["commands"][0]


if __name__ == "__main__":
    test_descriptor_refresh_preserves_authored_readme()
    test_palomar_signal_join_and_first_read_order()
    test_descriptor_exposes_an_exact_commit_mathematical_reasoning_route()
    print("corpus orientation signal contracts passed")
