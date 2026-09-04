#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Focused contracts for the bounded mathematical-signal first read."""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

import build_corpus_descriptor as builder


def test_authored_readme_may_omit_generated_regions() -> None:
    authored = "# Reader entry\n\nBegin with the mathematical question.\n"
    assert builder.replace_readme_scale_strip(authored, "generated") == authored
    assert (
        builder.replace_readme_principal_declaration_anchors(authored, "generated")
        == authored
    )

    partials = (
        (
            builder.replace_readme_scale_strip,
            builder.README_SCALE_BEGIN,
        ),
        (
            builder.replace_readme_principal_declaration_anchors,
            builder.README_PRINCIPAL_END,
        ),
    )
    for replace, partial in partials:
        try:
            replace(authored + partial, "generated")
        except ValueError:
            pass
        else:
            raise AssertionError("a partial generated README region was accepted")


def test_palomar_signal_join_and_first_read_order() -> None:
    claims = json.loads((ROOT / "docs" / "claims.json").read_text(encoding="utf-8"))
    atlas = json.loads(
        (ROOT / "docs" / "declaration_atlas.json").read_text(encoding="utf-8")
    )
    orientation = builder.build_orientation(claims, atlas)
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
    generated_markdown = (ROOT / "docs" / "ORIENTATION.md").read_text(
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
    assert markdown.index("## Release provenance") < markdown.index(
        "## Mathematical signal first"
    ) < markdown.index("## What a claim status asserts")
    assert "### Reader tiers and relational boundaries" in markdown
    assert "conditional endpoint leverage" in markdown
    assert "deep mechanism and classification" in markdown
    assert "supporting and long tail" in markdown
    assert markdown.count("| ") >= len(ranking)
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


if __name__ == "__main__":
    test_authored_readme_may_omit_generated_regions()
    test_palomar_signal_join_and_first_read_order()
    test_descriptor_exposes_an_exact_commit_mathematical_reasoning_route()
    print("corpus orientation signal contracts passed")
