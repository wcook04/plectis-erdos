#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Contract tests for the generated declaration-search speed path."""

from __future__ import annotations

import gzip
import json
from pathlib import Path

import build_declaration_search_index as builder
import query_corpus


ROOT = Path(__file__).resolve().parents[1]


def test_tracked_index_is_current() -> None:
    assert builder.OUTPUT.read_bytes() == builder.render()
    assert builder.receipt_mismatches(builder.OUTPUT.read_bytes()) == []


def test_index_is_bound_to_the_atlas_and_remains_bounded() -> None:
    compressed = builder.OUTPUT.read_bytes()
    assert len(compressed) < 16 * 1024 * 1024
    packet = json.loads(gzip.decompress(compressed))
    atlas = query_corpus.load("docs/declaration_atlas.json")
    assert packet["atlas_source_fingerprint"] == atlas["source_fingerprint"]
    assert packet["by_term"]
    assert packet["by_name"]


def main() -> int:
    test_tracked_index_is_current()
    test_index_is_bound_to_the_atlas_and_remains_bounded()
    print("declaration search index: current, atlas-bound, and bounded PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
