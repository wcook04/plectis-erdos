#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial tests for the third-party source disposition checker."""

from __future__ import annotations

import copy
import json
import os
import tempfile
from pathlib import Path
from unittest.mock import patch

import check_primary_source_dispositions as checker
from check_primary_source_dispositions import (
    LEDGER,
    NOTICE,
    ROOT,
    disposition_errors,
    metadata_private_path_errors,
    notice_errors,
    present_artifact_paths,
    read_regular_bytes,
    safe_reference_file,
    tracked_paths,
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def reject(data: dict[str, object], marker: str, tracked: set[str], present: set[str]) -> None:
    errors = disposition_errors(data, tracked=tracked, present=present)
    require(errors and any(marker in error for error in errors), f"mutation was accepted: {marker}")


def check_reference_boundary() -> int:
    """Reject traversal and symlinked-parent support references."""
    with tempfile.TemporaryDirectory(prefix="primary-source-reference-") as raw:
        root = Path(raw) / "checkout"
        docs = root / "docs"
        docs.mkdir(parents=True)
        regular = docs / "support.md"
        regular.write_text("support\n", encoding="utf-8")
        require(
            safe_reference_file("docs/support.md", root=root),
            "regular support reference was rejected",
        )

        private = root.parent / "private.md"
        private.write_text("private\n", encoding="utf-8")
        require(
            not safe_reference_file("docs/../private.md", root=root),
            "support reference traversal escaped the checkout",
        )

        private_dir = root.parent / "private-dir"
        private_dir.mkdir()
        (private_dir / "record.md").write_text("private\n", encoding="utf-8")
        (docs / "linked").symlink_to(private_dir, target_is_directory=True)
        require(
            not safe_reference_file("docs/linked/record.md", root=root),
            "support reference followed a symlinked parent",
        )
    return 3


def main() -> int:
    reference_checks = check_reference_boundary()
    with tempfile.TemporaryDirectory(prefix="primary-source-boundary-") as raw:
        root = Path(raw)
        fifo = root / "disposition.fifo"
        os.mkfifo(fifo)
        try:
            read_regular_bytes(fifo, root=root)
        except OSError as error:
            require(
                "not a regular file" in str(error),
                f"special disposition input returned an unexpected error: {error}",
            )
        else:
            raise AssertionError("special disposition input was accepted")

        raced_parent = root / "input-parent"
        raced_parent.mkdir()
        original_parent = root / "input-parent-original"
        outside = root / "outside"
        outside.mkdir()
        raced_input = raced_parent / "metadata.json"
        raced_input.write_text("inside\n", encoding="utf-8")
        (outside / raced_input.name).write_text("outside\n", encoding="utf-8")
        original_open = checker.os.open

        def swap_parent(
            path: Path,
            flags: int,
            mode: int = 0o777,
            *,
            dir_fd: int | None = None,
        ) -> int:
            if dir_fd is not None and Path(path).name == raced_input.name:
                raced_parent.rename(original_parent)
                raced_parent.symlink_to(outside, target_is_directory=True)
            if dir_fd is not None:
                return original_open(path, flags, mode, dir_fd=dir_fd)
            return original_open(path, flags, mode)

        with patch.object(checker.os, "open", side_effect=swap_parent):
            observed = read_regular_bytes(raced_input, root=root)
        require(
            observed == b"inside\n",
            "disposition reader followed a swapped parent directory",
        )
        require(
            (original_parent / raced_input.name).is_file(),
            "disposition reader did not use the held parent descriptor",
        )
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

    unclassified_closure = copy.deepcopy(data)
    unclassified_closure["source_record_coverage"]["citation_only_source_records"].pop()  # type: ignore[index]
    reject(
        unclassified_closure,
        "source closure lacks an artifact-backed or citation-only disposition",
        tracked,
        present,
    )

    artifact_backed_as_citation_only = copy.deepcopy(data)
    artifact_backed_as_citation_only["source_record_coverage"]["citation_only_source_records"].append(  # type: ignore[index]
        artifact_backed_as_citation_only["artifacts"][0]["source_record"]  # type: ignore[index]
    )
    reject(
        artifact_backed_as_citation_only,
        "citation-only source record is artifact-backed",
        tracked,
        present,
    )

    future_closure = "docs/primary-sources/future-source-closure.md"
    reject(
        data,
        "source closure lacks an artifact-backed or citation-only disposition",
        tracked | {future_closure},
        present,
    )

    wrong_root = copy.deepcopy(data)
    wrong_root["inventory"]["root"] = "docs/"  # type: ignore[index]
    reject(wrong_root, "inventory root", tracked, present)

    noncanonical_path = copy.deepcopy(data)
    noncanonical_path["artifacts"][0]["path"] = noncanonical_path["artifacts"][0]["path"].replace(  # type: ignore[index]
        "docs/primary-sources/", "docs/primary-sources//", 1
    )
    reject(
        noncanonical_path,
        "artifact path must be a normalized relative path",
        tracked,
        present,
    )

    for payload in (b"/Users/private/source.pdf", b"C:\\Users\\private\\source.pdf"):
        metadata_errors = metadata_private_path_errors({"synthetic.md": payload})
        require(metadata_errors, "synthetic private metadata marker was accepted")

    # The notice may name the same artifact in both its inventory and its
    # provenance explanation. Remove every mention so this fixture represents
    # an actual omission rather than leaving the second reference authoritative.
    missing_artifact = notice.replace(data["artifacts"][0]["path"], "")  # type: ignore[index]
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
        "8 unauthorized or inconsistent mutations, 2 private metadata fixtures, "
        f"3 notice mutations, and {reference_checks} path-boundary checks rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
