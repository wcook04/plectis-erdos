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

    assert len(signal) == len(ranking) == 9
    assert [row["rank"] for row in signal] == list(range(1, 10))
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
    assert generated_orientation["mathematical_signal_first"] == signal
    assert generated_markdown == markdown
    assert markdown.index("## Release provenance") < markdown.index(
        "## Mathematical signal first"
    ) < markdown.index("## What a claim status asserts")
    assert markdown.count("| ") >= 9
    assert len(markdown.encode("utf-8")) <= builder.ORIENTATION_MARKDOWN_MAX_BYTES


if __name__ == "__main__":
    test_palomar_signal_join_and_first_read_order()
    print("corpus orientation signal contracts passed")
