#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Contract tests for the generated declaration-search speed path."""

from __future__ import annotations

import gzip
import json
from pathlib import Path
from unittest.mock import patch

import build_declaration_search_index as builder
import query_corpus


ROOT = Path(__file__).resolve().parents[1]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def test_platform_independent_header() -> None:
    fixture = {"test": "portable"}
    with patch.object(query_corpus, "build_declaration_search_term_index", return_value=fixture):
        encoded = builder.render()
        require(encoded[:10] == b"\x1f\x8b\x08\x00\x00\x00\x00\x00\x00\xff",
                "gzip embeds a timestamp, filename, or platform OS byte")
        require(json.loads(gzip.decompress(encoded)) == fixture, "portable encoding changed content")
        require(encoded == builder.render(), "identical input changed compressed bytes")


def test_tracked_index_is_current() -> None:
    require(builder.OUTPUT.read_bytes() == builder.render(), "tracked search index differs from its producer")
    require(builder.receipt_mismatches(builder.OUTPUT.read_bytes()) == [], "search receipt is stale")


def test_index_is_bound_to_the_atlas_and_remains_bounded() -> None:
    compressed = builder.OUTPUT.read_bytes()
    require(len(compressed) < 16 * 1024 * 1024, "compressed search index exceeds budget")
    packet = json.loads(gzip.decompress(compressed))
    atlas = query_corpus.load("docs/declaration_atlas.json")
    require(packet["atlas_source_fingerprint"] == atlas["source_fingerprint"], "search index lost atlas identity")
    require(bool(packet["by_term"]) and bool(packet["by_name"]), "search index is empty")


def main() -> int:
    test_platform_independent_header()
    test_tracked_index_is_current()
    test_index_is_bound_to_the_atlas_and_remains_bounded()
    print("declaration search index: current, atlas-bound, and bounded PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
