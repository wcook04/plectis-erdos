#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression checks for the content-addressed semantic-corpus fast path."""

from __future__ import annotations

import copy
import json

import build_semantic_corpus as builder
import check_cold_clone_comprehension as cold_clone


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> int:
    receipt = json.loads(
        builder.safe_read_text(builder.TRACKED_CHECK_RECEIPT)
    )
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
        census["demand_equivalent_total"] == public["demand_equivalent_total"],
        "compact receipt lost the demand-equivalence census",
    )
    print("semantic corpus check receipt: exact-match and mutation checks pass")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
