#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Executable accepted-only tests for recognition and impact facets."""

from __future__ import annotations

import copy
import json
import subprocess
import tempfile
from pathlib import Path

import build_research_contribution_recognition as recognition
import build_research_contributions as contributions
import validation_singleflight as singleflight


ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / ".github" / "fixtures" / "unaccepted-research-return.json"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def accepted_source() -> tuple[str, dict, bytes, str]:
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
    receipt["return_id"] = "rr-recognition-projection-test"
    receipt["repository"]["starting_commit"] = head
    receipt["repository"]["proposed_commit"] = head
    receipt["repository"]["accepted_commit"] = head
    receipt["repository"]["changed_paths"] = ["docs/repository_identity.json"]
    receipt["evidence"][0]["artifacts"] = ["docs/repository_identity.json"]
    receipt["review"]["structural_validation"]["state"] = "valid"
    receipt["review"]["reproduction"]["state"] = "reproduced"
    receipt["review"]["accepted_handoff"]["state"] = "accepted"
    receipt["review"]["accepted_handoff"]["reviewer"] = "Acceptance Reviewer"
    receipt["review"]["accepted_handoff"]["decided_at"] = "2026-08-30T00:00:00Z"
    receipt["review"]["accepted_handoff"]["authority_ref"] = f"git:{head}"
    receipt["identity"]["contributor"] = {
        "name": "Recognition Human",
        "handle": "recognition-human",
        "identifiers": ["id:human"],
    }
    receipt["identity"]["operator"] = {"relationship": "assisted_by", "name": "Recognition Operator"}
    receipt["identity"]["model_system"] = {
        "state": "disclosed",
        "name": "Recognition Model",
        "version": "2",
        "resources": ["test fixture"],
    }
    receipt["identity"]["provider"] = {
        "state": "disclosed",
        "name": "Recognition Provider",
        "version": "3",
        "resources": [],
    }
    receipt["identity"]["material_collaborators"] = [{"name": "Recognition Collaborator", "role": "review"}]
    receipt["attribution"]["artifact_credit"] = [
        {"name": "Recognition Human", "artifact_paths": ["docs/repository_identity.json"]}
    ]
    payload = contributions.canonical(receipt)
    return "rr-recognition-projection-test.json", receipt, payload, head


def main() -> int:
    require(
        recognition.GIT_LOOKUP_TIMEOUT_SECONDS
        == singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
        "recognition builder Git timeout drifted from the canonical boundary",
    )
    with tempfile.TemporaryDirectory() as directory:
        source_path = Path(directory) / FIXTURE.name
        source_path.write_bytes(FIXTURE.read_bytes())
        sources = contributions.load_receipts(Path(directory))
        empty = recognition.build_recognition(sources)
        require(empty["accepted_receipt_count"] == 0, "unaccepted fixture affected receipt denominator")
        require(empty["chronological"] == [], "unaccepted fixture entered recognition chronology")
        require(all(values == [] for values in empty["aggregates"].values()), "unaccepted fixture entered an aggregate facet")

    name, receipt, payload, head = accepted_source()
    original_route = contributions.public_result_family_route
    original_receipt_commit = recognition._receipt_source_commit
    contributions.public_result_family_route = lambda problem: {
        "repository_path": f"docs/research-commons/RETURN_PACKAGE_EXAMPLE_{problem}.md",
        "anchor": "current-public-consumer-fan-in",
        "relative_link": f"RETURN_PACKAGE_EXAMPLE_{problem}.md#current-public-consumer-fan-in",
    }
    recognition._receipt_source_commit = lambda row: head
    try:
        projection = recognition.build_recognition([(name, receipt, payload)])
    finally:
        contributions.public_result_family_route = original_route
        recognition._receipt_source_commit = original_receipt_commit

    row = projection["chronological"][0]
    require(projection["accepted_receipt_count"] == 1, "accepted receipt was not counted")
    require(row["record_kind"] == "accepted_receipt", "recognition row lost accepted kind")
    require(row["identity"]["contributor"]["name"] == "Recognition Human", "contributor facet lost human identity")
    require(row["identity"]["operator"]["name"] == "Recognition Operator", "operator facet was collapsed")
    require(row["identity"]["model_system"]["name"] == "Recognition Model", "model facet was lost")
    require(row["identity"]["provider"]["name"] == "Recognition Provider", "provider facet was lost")
    require(row["source"]["evidence_records"][0]["replay_state"] == "pending", "evidence replay state was reduced")
    require(row["impact_state"]["review_decisions"]["accepted_handoff"]["authority_ref"] == f"git:{head}", "review authority was lost")
    for facet in ("by_contributor", "by_operator_relationship", "by_model_system", "by_provider", "by_evidence_state", "by_review_state"):
        require(projection["aggregates"][facet], f"recognition facet is empty: {facet}")
        require(projection["aggregates"][facet][0]["accepted_receipts"][0]["return_id"] == receipt["return_id"], f"{facet} lost receipt provenance")

    human = recognition.human_projection(projection).decode("utf-8")
    for marker in ("Recognition Human", "Recognition Operator", "Recognition Model", "Recognition Provider", "pending"):
        require(marker in human, f"human recognition view omitted {marker}")
    require("commit_count" not in human and "diff_size" not in human, "recognition view exposed activity scoring")

    malformed = copy.deepcopy(projection)
    malformed["chronological"][0]["record_kind"] = "submitted_return"
    try:
        # Preserve the same source-bound hooks used to build the valid view.
        contributions.public_result_family_route = lambda problem: {
            "repository_path": f"docs/research-commons/RETURN_PACKAGE_EXAMPLE_{problem}.md",
            "anchor": "current-public-consumer-fan-in",
            "relative_link": f"RETURN_PACKAGE_EXAMPLE_{problem}.md#current-public-consumer-fan-in",
        }
        recognition._receipt_source_commit = lambda row: head
        try:
            recognition.validate_projection(malformed)
        except ValueError:
            pass
        else:
            raise AssertionError("non-accepted recognition row escaped validation")
    finally:
        contributions.public_result_family_route = original_route
        recognition._receipt_source_commit = original_receipt_commit

    print("recognition projection: unaccepted exclusion, accepted identity/evidence facets, provenance and no-score guards PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
