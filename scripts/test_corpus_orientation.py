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



def test_retained_companion_default_is_lossless_and_bounded() -> None:
    claims = json.loads((ROOT / "docs/claims.json").read_text())
    atlas = json.loads((ROOT / "docs/declaration_atlas.json").read_text())
    orientation = builder.build_orientation(claims, atlas)
    projected = orientation["editorial_architecture"]
    expected = claims["machine_readable_paper"]["publication_assembly"]["publication_architecture"]["retained_companions"]
    expanded = [dict(row, decision=row.get("decision", projected["retained_companion_default_decision"])) for row in projected["retained_companions"]]
    assert expanded == [{key: row[key] for key in ("source", "decision")} for row in expected]
    assert len((json.dumps(orientation, ensure_ascii=False, separators=(",", ":")) + "\n").encode()) <= builder.ORIENTATION_MAX_BYTES
    if expected:
        expected[0]["decision"] = "test_distinct_disposition"
        changed = builder.build_orientation(claims, atlas)
        assert changed["editorial_architecture"]["retained_companions"][0]["decision"] == "test_distinct_disposition"


def test_compact_programmes_preserve_open_statements_and_expand_exactly() -> None:
    import query_corpus
    claims = json.loads((ROOT / "docs/claims.json").read_text())
    atlas = json.loads((ROOT / "docs/declaration_atlas.json").read_text())
    orientation = builder.build_orientation(claims, atlas)
    assert [(r["id"], r["statement"]) for r in orientation["remaining_open_propositions"]] == [(r["id"], r["statement"]) for r in claims["remaining_open_propositions"]]
    assert all("advancement_status" not in row for row in orientation["remaining_open_propositions"])
    for row in claims["remaining_open_propositions"]:
        assert query_corpus.open_proposition_packet(row["id"])["open_proposition"]["advancement_status"] == row["advancement_status"]
    assert [r["id"] for r in orientation["principal_claims"]] == [r["id"] for r in claims["claims"] if r.get("readme_headline")]
    routes = [r for r in claims["machine_readable_paper"]["entrypoints"] if r.get("route_kind") == "mathematical_programme"]
    expanded = query_corpus.orientation_programme_details(orientation, claims)
    assert expanded == [{**r, "core_claim_count": len(r["core_claim_ids"])} for r in routes]
    assert orientation["mathematical_programmes"] == [{k:r[k] for k in ("id", "title", "claim_ceiling")} for r in routes]
    assert len((json.dumps(orientation, ensure_ascii=False, separators=(",", ":")) + "\n").encode()) <= builder.ORIENTATION_MAX_BYTES


if __name__ == "__main__":
    test_authored_readme_may_omit_generated_regions()
    test_palomar_signal_join_and_first_read_order()
    test_descriptor_exposes_an_exact_commit_mathematical_reasoning_route()
    test_retained_companion_default_is_lossless_and_bounded()
    test_compact_programmes_preserve_open_statements_and_expand_exactly()
    print("corpus orientation signal contracts passed")
