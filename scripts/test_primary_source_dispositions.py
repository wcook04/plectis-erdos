#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial tests for the third-party source disposition checker."""

from __future__ import annotations

import copy
import json

from check_primary_source_dispositions import (
    LEDGER,
    NOTICE,
    ROOT,
    disposition_errors,
    metadata_private_path_errors,
    notice_errors,
    present_artifact_paths,
    tracked_paths,
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def reject(data: dict[str, object], marker: str, tracked: set[str], present: set[str]) -> None:
    errors = disposition_errors(data, tracked=tracked, present=present)
    require(errors and any(marker in error for error in errors), f"mutation was accepted: {marker}")


def main() -> int:
    release_checker = (ROOT / "scripts" / "check_release.py").read_text(encoding="utf-8")
    require(
        "check_primary_source_dispositions.py" in release_checker,
        "canonical release checker does not consume the disposition validator",
    )
    data = json.loads(LEDGER.read_text(encoding="utf-8"))
    notice = NOTICE.read_text(encoding="utf-8")
    requirements = (ROOT / "requirements-release.txt").read_text(encoding="utf-8")
    lake_manifest = (ROOT / "lake-manifest.json").read_text(encoding="utf-8")
    tracked = tracked_paths()
    present = present_artifact_paths()
    require(not disposition_errors(data, tracked=tracked, present=present), "live disposition ledger is invalid")
    require(
        not notice_errors(data, notice, requirements, lake_manifest),
        "live third-party notice is not synchronized with release authorities",
    )

    candidate = copy.deepcopy(data)
    candidate["artifacts"][0]["public_candidate_inclusion"] = True  # type: ignore[index]
    reject(candidate, "included without verified redistribution permission", tracked, present)

    missing_permission = copy.deepcopy(data)
    missing_permission["artifacts"][0]["disposition"] = "public_redistribution_verified"  # type: ignore[index]
    reject(missing_permission, "lacks verified permission status", tracked, present)

    duplicate = copy.deepcopy(data)
    duplicate["artifacts"][1]["path"] = duplicate["artifacts"][0]["path"]  # type: ignore[index]
    reject(duplicate, "artifact path is duplicated", tracked, present)

    untrusted_route = copy.deepcopy(data)
    untrusted_route["artifacts"][0]["official_retrieval_routes"] = ["http://example.invalid/source"]  # type: ignore[index]
    reject(untrusted_route, "HTTPS official retrieval route", tracked, present)

    wrong_inventory = copy.deepcopy(data)
    wrong_inventory["inventory"]["working_tree_only_count"] = 0  # type: ignore[index]
    reject(wrong_inventory, "inventory working_tree_only_count", tracked, present)

    weakened_policy = copy.deepcopy(data)
    weakened_policy["policy"]["allowed_dispositions"] = ["link_and_digest_only"]  # type: ignore[index]
    reject(weakened_policy, "canonical disposition set", tracked, present)

    wrong_root = copy.deepcopy(data)
    wrong_root["inventory"]["root"] = "docs/"  # type: ignore[index]
    reject(wrong_root, "inventory root", tracked, present)

    for payload in (b"/Users/private/source.pdf", b"C:\\Users\\private\\source.pdf"):
        metadata_errors = metadata_private_path_errors({"synthetic.md": payload})
        require(metadata_errors, "synthetic private metadata marker was accepted")

    missing_artifact = notice.replace(data["artifacts"][0]["path"], "", 1)  # type: ignore[index]
    notice_mutation_errors = notice_errors(data, missing_artifact, requirements, lake_manifest)
    require(
        any("missing artifact path" in error for error in notice_mutation_errors),
        "notice omission of an artifact row was accepted",
    )

    missing_manifest_boundary = notice.replace("pip --require-hashes", "pip", 1)
    manifest_mutation_errors = notice_errors(
        data, missing_manifest_boundary, requirements, lake_manifest
    )
    require(
        any("hash-pinned retrieval" in error for error in manifest_mutation_errors),
        "notice omission of the manifest permission boundary was accepted",
    )

    stale_summary = copy.deepcopy(data)
    stale_summary["artifacts"][0]["disposition"] = "public_redistribution_verified"  # type: ignore[index]
    stale_summary_errors = notice_errors(
        stale_summary, notice, requirements, lake_manifest
    )
    require(
        any("all-unverified summary" in error for error in stale_summary_errors),
        "a changed artifact disposition left stale notice prose green",
    )

    print(
        "test_primary_source_dispositions: baseline clean; "
        "5 unauthorized or inconsistent mutations, 2 private metadata fixtures, "
        "and 3 notice mutations rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
