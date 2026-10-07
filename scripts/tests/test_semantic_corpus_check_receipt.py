#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression checks for the content-addressed semantic-corpus fast path."""

from __future__ import annotations

import _test_bootstrap  # noqa: F401

import copy
import json
import tempfile
from pathlib import Path
from unittest.mock import patch

import build_semantic_corpus as builder
import check_cold_clone_comprehension as cold_clone


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def check_portable_receipt_boundary() -> None:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        output, local, tracked = (root / name for name in ("corpus", "local", "tracked"))
        surfaces = [root / name for name in ("results", "cold-paper", "systems-paper")]
        for path in (output, *surfaces):
            path.write_text("current\n", encoding="utf-8")
        with (
            patch.object(builder, "ROOT", root),
            patch.object(builder, "OUTPUT", output),
            patch.object(builder, "LOCAL_CHECK_RECEIPT", local),
            patch.object(builder, "TRACKED_CHECK_RECEIPT", tracked),
            patch.object(builder, "RESULTS", surfaces[0]),
            patch.object(builder, "COLD_CLONE_PAPER", surfaces[1]),
            patch.object(builder, "SYSTEMS_PAPER", surfaces[2]),
            patch.object(builder, "semantic_input_fingerprint", return_value="sha256:current"),
            patch.object(builder, "zone_files", return_value=[root / "zone"]),
            patch.object(builder, "collect", side_effect=AssertionError("preflight rebuilt the corpus")),
            patch.object(builder, "write_check_receipt", side_effect=AssertionError("preflight wrote a receipt")),
        ):
            receipt = {
                "schema": builder.CHECK_RECEIPT_SCHEMA,
                "builder_schema": "erdos249257-semantic-corpus/1",
                "input_fingerprint": "sha256:current",
                "output_digest": builder.file_digest(output),
                "surface_digests": {p.name: builder.file_digest(p) for p in surfaces},
                "summary": {"statement_nodes": 1, "declarations": 1, "orphan_count": 0},
            }
            local.write_text(json.dumps(receipt), encoding="utf-8")
            for content in (None, "malformed", "[]", "null", json.dumps({**receipt, "input_fingerprint": "old"})):
                if content is not None:
                    tracked.write_text(content, encoding="utf-8")
                require(builder.load_cached_check() == receipt, "warm-cache fixture is not valid")
                with patch.object(builder.sys, "argv", ["builder", "--check", "--tracked-only"]):
                    require(builder.main() == 1, "local receipt concealed missing/stale shipped evidence")
            tracked.write_text(json.dumps(receipt), encoding="utf-8")
            with patch.object(builder.sys, "argv", ["builder", "--check", "--tracked-only"]):
                require(builder.main() == 0, "current portable semantic evidence was rejected")
                surfaces[0].write_text("drift\n", encoding="utf-8")
                require(builder.main() == 1, "changed generated surface passed portable check")


def main() -> int:
    check_portable_receipt_boundary()
    receipt = json.loads(
        builder.safe_read_text(builder.TRACKED_CHECK_RECEIPT)
    )
    require(builder.load_cached_check(tracked_only=True) == receipt,
            "tracked semantic receipt is stale for the actual input tree")
    inputs = {
        "input_fingerprint": receipt["input_fingerprint"],
        "output_digest": receipt["output_digest"],
        "surface_digests": receipt["surface_digests"],
    }
    require(builder.receipt_matches(receipt, **inputs), "exact receipt was rejected")

    mutations = {
        "input fingerprint": ("input_fingerprint", "sha256:changed"),
        "output digest": ("output_digest", "sha256:changed"),
        "surface digest": ("surface_digests", {"docs/RESULTS.md": "sha256:changed"}),
    }
    for label, (field, value) in mutations.items():
        changed = dict(inputs)
        changed[field] = value
        require(
            not builder.receipt_matches(receipt, **changed),
            f"receipt accepted changed {label}",
        )

    public = receipt["summary"]["public_semantic_census"]
    census = cold_clone.semantic_census_from_public(copy.deepcopy(public))
    require(
        census["nonrecurring_total"] == public["nonrecurring"]["total"],
        "compact receipt lost the public nonrecurring census",
    )
    require(
        census["indexed_problem_ids"] == public["indexed_problem_ids"],
        "compact receipt lost the current indexed-problem scope",
    )
    require(
        census["open_antecedent_equivalent_total"]
        == public["open_antecedent_endpoint_equivalent_count"],
        "compact receipt lost the live open-antecedent relation census",
    )
    require(
        not any(key.startswith("demand_") for key in public),
        "compact receipt restored the retired DemandLedger aggregate census",
    )
    print("semantic corpus check receipt: exact-match and mutation checks pass")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
