#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check the public-candidate boundary for acquired third-party source files.

The disposition ledger is the authority for PDFs, scans, and source archives
kept while researching.  Retrieval routes, DOI/arXiv records, and digests are
not redistribution grants.  This checker therefore permits an absent
``working_tree_only`` artifact in a clean clone, but never permits an
unregistered or candidate-included binary, and verifies any copy that is
present locally without printing its contents.
"""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path, PurePosixPath
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "docs" / "primary-sources" / "redistribution-dispositions.json"
SOURCE_ROOT = ROOT / "docs" / "primary-sources"
SCHEMA = "plectis.third_party_source_redistribution_dispositions.v1"
DISPOSITIONS = {
    "public_redistribution_verified",
    "link_and_digest_only",
    "operator_permission_required",
    "unresolved_release_blocker",
}
ARTIFACT_SUFFIXES = (".pdf", ".scan", ".tar", ".tar.gz", ".tgz", ".zip", ".7z")


def require(condition: bool, message: str, errors: list[str]) -> None:
    if not condition:
        errors.append(message)


def artifact_path(value: Any, errors: list[str]) -> Path | None:
    if not isinstance(value, str) or not value.startswith("docs/primary-sources/"):
        errors.append(f"artifact path must stay under docs/primary-sources: {value!r}")
        return None
    pure = PurePosixPath(value)
    if pure.is_absolute() or ".." in pure.parts:
        errors.append(f"artifact path must be a normalized relative path: {value!r}")
        return None
    if not value.lower().endswith(ARTIFACT_SUFFIXES):
        errors.append(f"artifact path has an unsupported source-file suffix: {value!r}")
        return None
    return ROOT.joinpath(*pure.parts)


def tracked_paths() -> set[str]:
    result = subprocess.run(
        ["git", "ls-files", "--", "docs/primary-sources"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return {line for line in result.stdout.splitlines() if line}


def present_artifact_paths() -> set[str]:
    if not SOURCE_ROOT.is_dir():
        return set()
    return {
        path.relative_to(ROOT).as_posix()
        for path in SOURCE_ROOT.rglob("*")
        if path.is_file() and path.name != LEDGER.name and path.name.lower().endswith(ARTIFACT_SUFFIXES)
    }


def disposition_errors(
    data: dict[str, Any],
    *,
    tracked: set[str] | None = None,
    present: set[str] | None = None,
) -> list[str]:
    """Return every ledger, digest, and candidate-boundary failure."""
    errors: list[str] = []
    require(data.get("schema") == SCHEMA, f"ledger must use schema {SCHEMA}", errors)
    policy = data.get("policy")
    require(isinstance(policy, dict), "ledger policy must be an object", errors)
    if isinstance(policy, dict):
        require(
            policy.get("public_candidate_rule") == "Only public_redistribution_verified artifacts may be tracked in the public candidate.",
            "ledger must state the verified-permission candidate rule",
            errors,
        )
        require(
            "not redistribution permission" in str(policy.get("permission_boundary", "")),
            "ledger must distinguish retrieval/citation from redistribution permission",
            errors,
        )
    inventory = data.get("inventory")
    artifacts = data.get("artifacts")
    require(isinstance(inventory, dict), "ledger inventory must be an object", errors)
    require(isinstance(artifacts, list), "ledger artifacts must be a list", errors)
    if not isinstance(inventory, dict) or not isinstance(artifacts, list):
        return errors

    expected_counts = {
        "artifact_count": len(artifacts),
        "tracked_release_snapshot_count": 0,
        "working_tree_only_count": 0,
        "public_candidate_verified_count": 0,
        "link_and_digest_only_count": 0,
        "operator_permission_required_count": 0,
        "unresolved_release_blocker_count": 0,
    }
    seen: set[str] = set()
    listed_artifacts: set[str] = set()
    for index, record in enumerate(artifacts):
        if not isinstance(record, dict):
            errors.append(f"artifact record {index} must be an object")
            continue
        raw_path = record.get("path")
        local = artifact_path(raw_path, errors)
        if not isinstance(raw_path, str):
            continue
        listed_artifacts.add(raw_path)
        if raw_path in seen:
            errors.append(f"artifact path is duplicated: {raw_path}")
        seen.add(raw_path)
        digest = record.get("sha256")
        require(
            isinstance(digest, str) and len(digest) == 64 and all(c in "0123456789abcdef" for c in digest),
            f"{raw_path} must carry a lowercase SHA-256 digest",
            errors,
        )
        disposition = record.get("disposition")
        require(disposition in DISPOSITIONS, f"{raw_path} has an unknown disposition", errors)
        inventory_state = record.get("inventory_state")
        require(
            inventory_state in {"tracked_release_snapshot", "working_tree_only"},
            f"{raw_path} has an unknown inventory state",
            errors,
        )
        candidate = record.get("public_candidate_inclusion")
        require(isinstance(candidate, bool), f"{raw_path} candidate inclusion must be boolean", errors)
        permission_status = record.get("permission_evidence_status")
        routes = record.get("official_retrieval_routes")
        require(
            isinstance(routes, list) and routes and all(
                isinstance(route, str) and route.startswith("https://") for route in routes
            ),
            f"{raw_path} must retain at least one HTTPS official retrieval route",
            errors,
        )
        for field in ("source_record", "support_boundary_ref"):
            ref = record.get(field)
            require(isinstance(ref, str) and ref.startswith("docs/"), f"{raw_path} lacks {field}", errors)
            if isinstance(ref, str):
                ref_path = ROOT / ref
                require(ref_path.is_file() and not ref_path.is_symlink(), f"{raw_path} has unusable {field}", errors)
        consumers = record.get("consumer_refs")
        require(isinstance(consumers, list) and consumers, f"{raw_path} lacks consumer_refs", errors)
        if isinstance(consumers, list):
            for consumer in consumers:
                require(isinstance(consumer, str), f"{raw_path} has a non-string consumer ref", errors)
                if isinstance(consumer, str):
                    consumer_path = ROOT / consumer
                    require(consumer_path.is_file() and not consumer_path.is_symlink(), f"{raw_path} has unusable consumer ref", errors)

        if inventory_state == "tracked_release_snapshot":
            expected_counts["tracked_release_snapshot_count"] += 1
        elif inventory_state == "working_tree_only":
            expected_counts["working_tree_only_count"] += 1
        if disposition == "public_redistribution_verified":
            expected_counts["public_candidate_verified_count"] += 1
        elif disposition == "link_and_digest_only":
            expected_counts["link_and_digest_only_count"] += 1
        elif disposition == "operator_permission_required":
            expected_counts["operator_permission_required_count"] += 1
        elif disposition == "unresolved_release_blocker":
            expected_counts["unresolved_release_blocker_count"] += 1

        require(
            candidate is True and disposition == "public_redistribution_verified"
            or candidate is False,
            f"{raw_path} is included without verified redistribution permission",
            errors,
        )
        if disposition == "public_redistribution_verified":
            require(permission_status == "verified", f"{raw_path} lacks verified permission status", errors)
            require(record.get("permission_evidence_scope") == raw_path, f"{raw_path} permission scope is not artifact-exact", errors)
            require(bool(record.get("permission_evidence_locator")), f"{raw_path} lacks permission evidence locator", errors)
        elif permission_status == "verified":
            errors.append(f"{raw_path} claims verified permission under a non-verified disposition")

        if local is not None:
            if local.is_symlink():
                errors.append(f"{raw_path} must not be a symlink")
            elif local.is_file():
                observed = hashlib.sha256(local.read_bytes()).hexdigest()
                if isinstance(digest, str) and observed != digest:
                    errors.append(f"{raw_path} digest does not match the disposition ledger")
            elif inventory_state == "tracked_release_snapshot":
                errors.append(f"tracked artifact is missing: {raw_path}")

    if tracked is not None:
        tracked_artifacts = {path for path in tracked if path.lower().endswith(ARTIFACT_SUFFIXES)}
        for path in listed_artifacts:
            state = next((row.get("inventory_state") for row in artifacts if isinstance(row, dict) and row.get("path") == path), None)
            if path in tracked_artifacts and state != "tracked_release_snapshot":
                errors.append(f"working-tree-only artifact is tracked: {path}")
            if state == "tracked_release_snapshot" and path not in tracked_artifacts:
                errors.append(f"tracked-release artifact is not tracked: {path}")
        unlisted_tracked = sorted(tracked_artifacts - listed_artifacts)
        errors.extend(f"tracked source artifact is absent from the disposition ledger: {path}" for path in unlisted_tracked)
    if present is not None:
        errors.extend(f"present source artifact is absent from the disposition ledger: {path}" for path in sorted(present - listed_artifacts))

    for key, expected in expected_counts.items():
        if inventory.get(key) != expected:
            errors.append(f"inventory {key} is inconsistent with artifact records")
    verified = expected_counts["public_candidate_verified_count"]
    status = str(inventory.get("permission_evidence_status", ""))
    if verified == 0:
        require("none" in status or "not" in status, "inventory must say no bound record asserts permission", errors)
    return errors


def main() -> int:
    try:
        data = json.loads(LEDGER.read_text(encoding="utf-8"))
        errors = disposition_errors(data, tracked=tracked_paths(), present=present_artifact_paths())
    except (OSError, json.JSONDecodeError, subprocess.CalledProcessError) as exc:
        print(f"check_primary_source_dispositions: FAIL: {exc}", file=sys.stderr)
        return 1
    if errors:
        print(f"check_primary_source_dispositions: {len(errors)} failure(s)", file=sys.stderr)
        for error in errors:
            print(f"  FAIL {error}", file=sys.stderr)
        return 1
    count = len(data["artifacts"])
    print(
        "check_primary_source_dispositions: "
        f"{count} artifacts dispositioned; verified-permission candidate count 0; "
        "working-tree-only binaries excluded"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
