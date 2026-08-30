#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Executable accepted-only tests for the public contribution attribution rail."""

from __future__ import annotations

import copy
import json
import subprocess
import tempfile
from pathlib import Path
from unittest import mock

import build_research_contributions as contributions
import validation_singleflight as singleflight


ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / ".github" / "fixtures" / "unaccepted-research-return.json"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def accepted_source() -> tuple[str, dict, bytes]:
    receipt = json.loads(FIXTURE.read_text(encoding="utf-8"))
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
        env=contributions.git_environment(),
        timeout=contributions.GIT_LOOKUP_TIMEOUT_SECONDS,
    ).stdout.strip()
    receipt["record_kind"] = "accepted_receipt"
    receipt["return_id"] = "rr-contribution-projection-test"
    receipt["repository"]["starting_commit"] = head
    receipt["repository"]["proposed_commit"] = head
    receipt["repository"]["accepted_commit"] = head
    receipt["repository"]["changed_paths"] = ["docs/repository_identity.json"]
    receipt["evidence"][0]["artifacts"] = ["docs/repository_identity.json"]
    receipt["review"]["structural_validation"]["state"] = "valid"
    receipt["review"]["reproduction"]["state"] = "reproduced"
    receipt["review"]["accepted_handoff"]["state"] = "accepted"
    receipt["review"]["accepted_handoff"]["reviewer"] = "test reviewer"
    receipt["review"]["accepted_handoff"]["decided_at"] = "2026-08-30T00:00:00Z"
    receipt["review"]["accepted_handoff"]["authority_ref"] = f"git:{head}"
    receipt["identity"]["contributor"] = {
        "name": "Human Projection Contributor",
        "handle": "human-projection",
        "identifiers": ["orcid:test"],
    }
    receipt["identity"]["operator"] = {
        "relationship": "assisted_by",
        "name": "Release Operator",
    }
    receipt["identity"]["model_system"] = {
        "state": "disclosed",
        "name": "Test Model",
        "version": "1",
        "resources": ["bounded fixture"],
    }
    receipt["identity"]["provider"] = {
        "state": "disclosed",
        "name": "Test Provider",
        "version": "2026",
        "resources": [],
    }
    receipt["identity"]["material_collaborators"] = [{"name": "Collaborator", "role": "review"}]
    receipt["attribution"]["artifact_credit"] = [
        {"name": "Human Projection Contributor", "artifact_paths": ["docs/repository_identity.json"]}
    ]
    payload = contributions.canonical(receipt)
    return "rr-contribution-projection-test.json", receipt, payload


def main() -> int:
    require(
        contributions.GIT_LOOKUP_TIMEOUT_SECONDS
        == singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
        "contribution builder Git timeout drifted from the canonical boundary",
    )
    with tempfile.TemporaryDirectory() as directory:
        source_path = Path(directory) / FIXTURE.name
        source_path.write_bytes(FIXTURE.read_bytes())
        require(contributions.load_receipts(Path(directory)) == [], "unaccepted fixture entered attribution sources")

    with tempfile.TemporaryDirectory() as directory:
        name, _receipt, payload = accepted_source()
        Path(directory, name).write_bytes(payload)
        with mock.patch.object(contributions, "committed_receipt_paths", return_value=[]):
            require(
                contributions.load_receipts(Path(directory), require_committed=True) == [],
                "strict accepted-only loading inspected an uncommitted receipt",
            )

    original_route = contributions.public_result_family_route
    contributions.public_result_family_route = lambda problem: {
        "repository_path": f"docs/research-commons/RETURN_PACKAGE_EXAMPLE_{problem}.md",
        "anchor": "current-public-consumer-fan-in",
        "relative_link": f"RETURN_PACKAGE_EXAMPLE_{problem}.md#current-public-consumer-fan-in",
    }
    try:
        name, receipt, payload = accepted_source()
        projection = contributions.build_projection([(name, receipt, payload)])
    finally:
        contributions.public_result_family_route = original_route

    row = projection["chronological"][0]
    require(projection["filters"]["by_result_class"] == {"inconclusive": [receipt["return_id"]]}, "result class filter drifted")
    require(row["identity"]["contributor"]["name"] == "Human Projection Contributor", "human credit was lost")
    require(row["identity"]["operator"]["name"] == "Release Operator", "operator identity was collapsed")
    require(row["identity"]["model_system"]["name"] == "Test Model", "model disclosure was lost")
    require(row["identity"]["provider"]["name"] == "Test Provider", "provider disclosure was lost")
    require("current-public-consumer-fan-in" in row["public_frontier"]["relative_link"], "public frontier was not linked")
    human = contributions.human_projection(projection).decode("utf-8")
    for marker in ("Human Projection Contributor", "Release Operator", "Test Model", "Test Provider", "inconclusive"):
        require(marker in human, f"human attribution view omitted {marker}")
    require("commit_count" not in human and "diff_size" not in human, "activity leaderboard field entered attribution prose")

    print("build_research_contributions: unaccepted exclusion and human/operator/model/provider projection PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
