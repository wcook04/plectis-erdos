#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build the deterministic compressed index used by public corpus search."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import sys
from pathlib import Path

import query_corpus


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "docs" / "declaration_search_index.json.gz"
CHECK_RECEIPT = ROOT / "docs" / "declaration_search_index_check.json"
RECEIPT_SCHEMA = "erdos249257-declaration-search-index-check/1"
INPUTS = (
    ROOT / "scripts" / "build_declaration_search_index.py",
    ROOT / "scripts" / "query_corpus.py",
)


def render() -> bytes:
    packet = query_corpus.build_declaration_search_term_index()
    raw = json.dumps(
        packet,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return gzip.compress(raw, compresslevel=6, mtime=0)


def sha256_bytes(content: bytes) -> str:
    return f"sha256:{hashlib.sha256(content).hexdigest()}"


def receipt(content: bytes) -> dict[str, object]:
    atlas = query_corpus.load("docs/declaration_atlas.json")
    return {
        "schema": RECEIPT_SCHEMA,
        "index_sha256": sha256_bytes(content),
        "atlas_source_fingerprint": atlas["source_fingerprint"],
        "implementation_sha256": {
            path.relative_to(ROOT).as_posix(): sha256_bytes(path.read_bytes())
            for path in INPUTS
        },
    }


def receipt_mismatches(content: bytes) -> list[str]:
    if not CHECK_RECEIPT.is_file():
        return ["missing_receipt"]
    try:
        actual = json.loads(CHECK_RECEIPT.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError):
        return ["unreadable_receipt"]
    expected = receipt(content)
    return [key for key, value in expected.items() if actual.get(key) != value]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check", action="store_true", help="fail when the tracked index is stale"
    )
    args = parser.parse_args()
    if args.check:
        actual = OUTPUT.read_bytes() if OUTPUT.is_file() else b""
        mismatches = receipt_mismatches(actual)
        if not actual or mismatches:
            print(
                "declaration search index is stale; run "
                "python3 scripts/build_declaration_search_index.py; mismatches: "
                + ", ".join(mismatches or ["missing_index"])
            )
            return 1
        print(f"declaration search index current: {len(actual)} compressed bytes")
        return 0
    expected = render()
    OUTPUT.write_bytes(expected)
    CHECK_RECEIPT.write_text(
        json.dumps(receipt(expected), ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    print(f"wrote {OUTPUT.relative_to(ROOT)}: {len(expected)} compressed bytes")
    return 0


if __name__ == "__main__":
    sys.exit(main())
