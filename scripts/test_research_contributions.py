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
    unaccepted = json.loads(FIXTURE.read_text(encoding="utf-8"))
    try:
        contributions.build_projection(
            [(FIXTURE.name, unaccepted, contributions.canonical(unaccepted))]
        )
    except ValueError as exc:
        require(
            "accepts accepted_receipt records only" in str(exc),
            "direct projection rejection omitted its accepted-only reason",
        )
    else:
        raise AssertionError("direct projection accepted an unaccepted record")

    with tempfile.TemporaryDirectory() as directory:
        source_path = Path(directory) / FIXTURE.name
        source_path.write_bytes(FIXTURE.read_bytes())
        require(contributions.load_receipts(Path(directory)) == [], "unaccepted fixture entered attribution sources")

    malformed_repository = copy.deepcopy(unaccepted)
    malformed_repository["record_kind"] = "accepted_receipt"
    malformed_repository["repository"] = []
    with tempfile.TemporaryDirectory() as directory:
        Path(directory, "malformed-repository.json").write_text(
            json.dumps(malformed_repository), encoding="utf-8"
        )
        try:
            contributions.load_receipts(Path(directory))
        except ValueError as exc:
            require(
                "repository: must be an object" in str(exc),
                "malformed repository rejection omitted its shape diagnostic",
            )
        except Exception as exc:
            raise AssertionError(
                f"malformed accepted repository crashed contribution loading: {exc}"
            ) from exc
        else:
            raise AssertionError("malformed accepted repository escaped validation")

    with tempfile.TemporaryDirectory() as directory:
        name, _receipt, payload = accepted_source()
        Path(directory, name).write_bytes(payload)
        with mock.patch.object(contributions, "committed_receipt_paths", return_value=[]):
            require(
                contributions.load_receipts(Path(directory), require_committed=True) == [],
                "strict accepted-only loading inspected an uncommitted receipt",
            )

    for invalid_problem in (249.0, "249", "../outside"):
        try:
            contributions.public_result_family_route(invalid_problem)
        except ValueError as exc:
            require(
                "roster problem integer" in str(exc),
                f"invalid public frontier route diagnostic drifted: {exc}",
            )
        else:
            raise AssertionError(
                f"public frontier route accepted invalid problem selector {invalid_problem!r}"
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

    architecture_name, architecture_receipt, _payload = accepted_source()
    architecture_name = "rr-architecture-contribution-projection-test.json"
    architecture_receipt["return_id"] = "rr-architecture-contribution-projection-test"
    architecture_receipt["frontier"] = {
        "track": "architecture",
        "area": "agent_workflow",
        "handle": "architecture-credit-rail",
        "bounded_question": "Can architecture work use the accepted credit rail?",
        "stop_condition": "Stop when the projection records track, area, path, and roles.",
        "starting_paths": ["CONTRIBUTING.md"],
    }
    architecture_receipt["result"].update(
        {
            "class": "checked_positive",
            "summary": "The accepted architecture artifact is projected without a problem number.",
            "claim_ceiling": "validated_architecture_change",
            "surviving_boundary": "Acceptance does not establish universal architecture quality.",
            "requested_disposition": "consider_architecture_adoption",
        }
    )
    architecture_receipt["attribution"]["artifact_credit"][0]["contribution_roles"] = [
        "conceptualization",
        "software",
    ]
    architecture_payload = contributions.canonical(architecture_receipt)
    architecture_projection = contributions.build_projection(
        [(architecture_name, architecture_receipt, architecture_payload)]
    )
    architecture_row = architecture_projection["chronological"][0]
    require(architecture_projection["filters"]["by_track"] == {"architecture": [architecture_receipt["return_id"]]}, "architecture track filter drifted")
    require(architecture_projection["filters"]["by_problem"] == {}, "architecture receipt entered a problem filter")
    require(architecture_projection["filters"]["by_architecture_area"] == {"agent_workflow": [architecture_receipt["return_id"]]}, "architecture area filter drifted")
    require(architecture_row["public_frontier"]["repository_path"].endswith("ARCHITECTURE_CONTRIBUTIONS.md"), "architecture contribution route was not projected")
    architecture_human = contributions.human_projection(architecture_projection).decode("utf-8")
    for marker in ("Architecture", "agent workflow", "conceptualization", "software"):
        require(marker in architecture_human, f"architecture contribution view omitted {marker}")

    print("build_research_contributions: unaccepted exclusion and human/operator/model/provider projection PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
