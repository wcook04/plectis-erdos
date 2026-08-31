#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Executable accepted-only tests for recognition and impact facets."""

from __future__ import annotations

import copy
import json
import os
import subprocess
import tempfile
from pathlib import Path
from unittest.mock import patch

import build_research_contribution_recognition as recognition
import build_research_contributions as contributions
import check_research_contribution_recognition as checker
import validate_research_return as return_validator
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
    starting = subprocess.run(
        ["git", "rev-parse", "HEAD^"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
        env=contributions.git_environment(),
        timeout=contributions.GIT_LOOKUP_TIMEOUT_SECONDS,
    ).stdout.strip()
    changed_path = subprocess.run(
        ["git", "diff-tree", "--no-commit-id", "--name-only", "-r", "HEAD"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
        env=contributions.git_environment(),
        timeout=contributions.GIT_LOOKUP_TIMEOUT_SECONDS,
    ).stdout.splitlines()[0]
    receipt["record_kind"] = "accepted_receipt"
    receipt["return_id"] = "rr-recognition-projection-test"
    receipt["repository"]["starting_commit"] = starting
    receipt["repository"]["proposed_commit"] = head
    receipt["repository"]["accepted_commit"] = head
    receipt["repository"]["changed_paths"] = [changed_path]
    receipt["evidence"][0]["artifacts"] = [changed_path]
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
    receipt["identity"]["operator"] = {"relationship": "named", "name": "Recognition Operator"}
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
        {"name": "Recognition Human", "artifact_paths": [changed_path]}
    ]
    payload = contributions.canonical(receipt)
    return "rr-recognition-projection-test.json", receipt, payload, head


def accepted_result_matrix() -> tuple[list[tuple[str, dict, bytes]], str]:
    """Build four accepted rows from the public fixture without minting receipts.

    The checked-in fixture remains a submitted, unaccepted adversarial input.
    These rows are an in-memory acceptance harness: each one receives the
    exact accepted state required by the intake validator, while retaining the
    fixture's bounded evidence shape.  This makes the projection test the
    actual consumer of all result classes rather than a policy-only assertion.
    """
    _name, seed, _payload, head = accepted_source()
    changed_path = seed["repository"]["changed_paths"][0]
    specifications = (
        (
            "positive",
            "checked_positive",
            "verified_finite_instance",
            "accept_handoff",
            "2026-08-30T00:00:01Z",
            "Human positive return",
        ),
        (
            "negative",
            "negative",
            "negative_for_bounded_route",
            "no_promotion",
            "2026-08-30T00:00:02Z",
            "Human negative return",
        ),
        (
            "inconclusive",
            "inconclusive",
            "inconclusive_attempt",
            "no_promotion",
            "2026-08-30T00:00:03Z",
            "Human inconclusive return",
        ),
        (
            "corrective",
            "corrective",
            "documentation_correction",
            "no_promotion",
            "2026-08-30T00:00:04Z",
            "Human corrective return",
        ),
    )
    sources: list[tuple[str, dict, bytes]] = []
    for suffix, result_class, claim_ceiling, disposition, accepted_at, contributor in specifications:
        receipt = copy.deepcopy(seed)
        receipt["return_id"] = f"rr-recognition-{suffix}-projection-test"
        receipt["result"].update(
            {
                "class": result_class,
                "summary": f"Accepted {suffix} projection fixture.",
                "claim_ceiling": claim_ceiling,
                "requested_disposition": disposition,
                "limitations": ["Projection fixture is not a solution of the open problem."],
                "surviving_boundary": "The universal Erdős #257 proposition remains open.",
            }
        )
        receipt["identity"]["contributor"] = {
            "name": contributor,
            "handle": f"recognition-{suffix}",
            "identifiers": [f"id:{suffix}"],
        }
        receipt["identity"]["operator"] = {
            "relationship": "named",
            "name": "Recognition Operator",
        }
        receipt["identity"]["model_system"] = {
            "state": "disclosed",
            "name": f"Recognition Model {suffix}",
            "version": "2",
            "resources": ["accepted-result matrix fixture"],
        }
        receipt["identity"]["provider"] = {
            "state": "disclosed",
            "name": "Recognition Provider",
            "version": "3",
            "resources": [],
        }
        receipt["attribution"]["artifact_credit"] = [
            {"name": contributor, "artifact_paths": [changed_path]}
        ]
        receipt["attribution"]["requested_display"] = (
            f"{contributor} — accepted {result_class} projection fixture"
        )
        receipt["repository"]["changed_paths"] = [changed_path]
        receipt["evidence"][0].update(
            {
                "command": "python3 scripts/query_corpus.py --problem 257",
                "exit_state": "passed",
                "exit_code": 0,
                "observed": f"Accepted {result_class} fixture evidence.",
                "artifacts": [changed_path],
                "replay_state": "reproduced",
            }
        )
        receipt["review"]["accepted_handoff"].update(
            {
                "state": "accepted",
                "reviewer": "Acceptance Reviewer",
                "decided_at": accepted_at,
                "authority_ref": f"git:{head}",
            }
        )
        for review_field in ("structural_validation", "reproduction"):
            receipt["review"][review_field].update(
                {
                    "reviewer": "Projection Validator",
                    "decided_at": accepted_at,
                    "authority_ref": f"git:{head}",
                }
            )
        if result_class == "corrective":
            receipt["correction_lineage"] = {
                "prior_return_reference": "rr-recognition-positive-projection-test",
                "affected_paths": [changed_path],
                "starting_commit": seed["repository"]["starting_commit"],
                "changed_evidence_or_wording": "Corrected the bounded result summary.",
                "reason": "The earlier accepted fixture used imprecise wording.",
                "disposition": "supersede",
            }
        payload = contributions.canonical(receipt)
        errors = return_validator.validate_document(
            receipt,
            require_accepted=True,
            repository_identity=checker.repository_identity_contract.load_identity(),
        )
        require(not errors, f"accepted {result_class} fixture failed intake validation: {errors}")
        sources.append((f"{receipt['return_id']}.json", receipt, payload))
    return sources, head


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

    committed_identity = checker.repository_identity_contract.load_identity()
    committed_projection = recognition.build_recognition(
        contributions.load_receipts(
            require_committed=True,
            repository_identity=committed_identity,
        )
    )
    with tempfile.TemporaryDirectory(dir="/tmp") as directory:
        output_root = Path(directory)
        json_output = output_root / "contributions.json"
        markdown_output = output_root / "CONTRIBUTION_RECOGNITION.md"
        json_output.write_bytes(checker._canonical_json(committed_projection))
        markdown_output.write_bytes(recognition.human_projection(committed_projection))
        require(
            checker.validate_outputs(
                json_output=json_output,
                markdown_output=markdown_output,
            ) == [],
            "recognition checker rejected a valid custom output path under /tmp",
        )

    with tempfile.TemporaryDirectory() as directory:
        output_root = Path(directory)
        target = output_root / "target"
        target.mkdir()
        linked = output_root / "linked"
        linked.symlink_to(target, target_is_directory=True)
        require(
            checker._has_symlink_component(linked / "contributions.json"),
            "recognition checker accepted an arbitrary symlinked output directory",
        )
        hidden = linked / ".." / "hidden.json"
        require(
            checker._has_symlink_component(hidden),
            "recognition checker normalized away a symlink before resolving ..",
        )
        regular = output_root / "regular.json"
        regular.write_bytes(b"{}")
        file_link = output_root / "file-link.json"
        file_link.symlink_to(regular)
        with patch.object(checker, "_has_symlink_component", return_value=False):
            payload, errors = checker._read_regular(file_link, "test output")
        require(payload is None, "recognition checker followed a substituted output file")
        require(
            any("cannot be read safely" in error for error in errors),
            "recognition checker did not retain the no-follow descriptor boundary",
        )
        fifo = output_root / "output.fifo"
        os.mkfifo(fifo)
        payload, errors = checker._read_regular(fifo, "test output")
        require(payload is None, "recognition checker accepted a special output file")
        require(
            any("not a regular file" in error for error in errors),
            "recognition checker did not reject a special output file",
        )

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

    architecture_receipt = copy.deepcopy(receipt)
    architecture_receipt["return_id"] = "rr-architecture-recognition-test"
    architecture_receipt["frontier"] = {
        "track": "architecture",
        "area": "validation",
        "handle": "accepted-architecture-recognition",
        "bounded_question": "Can accepted architecture work retain provenance and roles?",
        "stop_condition": "Stop when generic recognition and architecture facets validate.",
        "starting_paths": ["CONTRIBUTING.md"],
    }
    architecture_receipt["result"].update(
        {
            "class": "checked_positive",
            "summary": "Architecture recognition preserves its bounded accepted evidence.",
            "claim_ceiling": "validated_architecture_change",
            "surviving_boundary": "Acceptance does not establish mathematical truth or universal quality.",
            "requested_disposition": "consider_architecture_adoption",
        }
    )
    architecture_receipt["evidence"][0]["command"] = "python3 scripts/test_research_contribution_recognition.py"
    architecture_receipt["evidence"][0]["exit_state"] = "passed"
    architecture_receipt["evidence"][0]["exit_code"] = 0
    architecture_receipt["evidence"][0]["replay_state"] = "reproduced"
    architecture_receipt["review"]["mathematical_review"]["state"] = "not_required"
    architecture_receipt["review"]["claim_boundary_review"]["state"] = "not_required"
    for review_field in ("structural_validation", "reproduction"):
        architecture_receipt["review"][review_field]["reviewer"] = "Architecture Validator"
        architecture_receipt["review"][review_field]["decided_at"] = "2026-08-30T00:00:00Z"
    architecture_receipt["attribution"]["artifact_credit"][0]["contribution_roles"] = [
        "conceptualization",
        "validation",
    ]
    architecture_payload = contributions.canonical(architecture_receipt)
    architecture_errors = return_validator.validate_document(
        architecture_receipt,
        require_accepted=True,
        repository_identity=checker.repository_identity_contract.load_identity(),
    )
    require(not architecture_errors, f"accepted architecture fixture failed validation: {architecture_errors}")
    recognition._receipt_source_commit = lambda row: head
    try:
        architecture_projection = recognition.build_recognition(
            [("rr-architecture-recognition-test.json", architecture_receipt, architecture_payload)]
        )
    finally:
        recognition._receipt_source_commit = original_receipt_commit
    architecture_row = architecture_projection["chronological"][0]
    require(architecture_row["source"]["problem"] is None, "architecture recognition invented a problem")
    require(architecture_row["source"]["track"] == "architecture", "architecture recognition lost its track")
    require(architecture_projection["aggregates"]["by_problem"] == [], "architecture recognition entered a problem facet")
    require(architecture_projection["aggregates"]["by_architecture_area"][0]["key"] == "validation", "architecture area facet drifted")
    architecture_human = recognition.human_projection(architecture_projection).decode("utf-8")
    for marker in ("Architecture", "validation", "conceptualization"):
        require(marker in architecture_human, f"architecture recognition view omitted {marker}")

    matrix_sources, matrix_head = accepted_result_matrix()
    original_route = contributions.public_result_family_route
    original_receipt_commit = recognition._receipt_source_commit
    contributions.public_result_family_route = lambda problem: {
        "repository_path": f"docs/research-commons/RETURN_PACKAGE_EXAMPLE_{problem}.md",
        "anchor": "current-public-consumer-fan-in",
        "relative_link": f"RETURN_PACKAGE_EXAMPLE_{problem}.md#current-public-consumer-fan-in",
    }
    recognition._receipt_source_commit = lambda row: matrix_head
    try:
        matrix = recognition.build_recognition(matrix_sources)
    finally:
        contributions.public_result_family_route = original_route
        recognition._receipt_source_commit = original_receipt_commit

    require(matrix["accepted_receipt_count"] == 4, "result-class matrix did not count every accepted receipt")
    require(
        {row["result"]["class"] for row in matrix["chronological"]}
        == {"checked_positive", "negative", "inconclusive", "corrective"},
        "result-class matrix did not retain all accepted result classes",
    )
    require(
        matrix["aggregates"]["by_result_class"]
        and all(
            entry["denominator"] == {"accepted_receipts": 4}
            for entry in matrix["aggregates"]["by_result_class"]
        ),
        "result-class aggregate denominator is not the accepted-receipt count",
    )
    matrix_ids = {row["return_id"] for row in matrix["chronological"]}
    for facet in ("by_contributor", "by_model_system"):
        entries = matrix["aggregates"][facet]
        require(len(entries) == 4, f"{facet} did not preserve distinct accepted identities")
        require(
            {
                reference["return_id"]
                for entry in entries
                for reference in entry["accepted_receipts"]
            }
            == matrix_ids,
            f"{facet} did not retain exact accepted receipt provenance",
        )
    provider_entries = matrix["aggregates"]["by_provider"]
    require(
        len(provider_entries) == 1
        and provider_entries[0]["accepted_receipt_count"] == 4,
        "by_provider did not coalesce its intentionally shared disclosed provider",
    )
    require(
        {
            reference["return_id"]
            for reference in provider_entries[0]["accepted_receipts"]
        }
        == matrix_ids,
        "by_provider did not retain exact accepted receipt provenance",
    )
    for facet in ("by_operator_relationship", "by_material_collaborator"):
        entries = matrix["aggregates"][facet]
        require(len(entries) == 1, f"{facet} did not preserve its shared identity facet")
        require(
            entries[0]["accepted_receipt_count"] == 4
            and entries[0]["denominator"] == {"accepted_receipts": 4},
            f"{facet} collapsed its accepted-receipt denominator",
        )
    correction = matrix["chronological"][-1]
    require(
        correction["correction_lineage"]["disposition"] == "supersede",
        "corrective accepted receipt lost its correction disposition",
    )
    require(
        correction["impact_state"]["correction_lineage_state"] == "supersede",
        "corrective impact projection lost correction lineage",
    )
    require(
        len(matrix["aggregates"]["by_correction_lineage"]) == 2,
        "correction aggregate did not preserve the none/supersede split",
    )
    matrix_human = recognition.human_projection(matrix).decode("utf-8")
    for marker in (
        "checked_positive",
        "negative",
        "inconclusive",
        "corrective",
        "Recognition Model positive",
        "Recognition Operator",
        "supersede",
        "The universal Erdős #257 proposition remains open.",
    ):
        require(marker in matrix_human, f"matrix human view omitted {marker}")
    require(
        "commit_count" not in matrix_human and "diff_size" not in matrix_human,
        "result-class matrix exposed activity scoring",
    )

    malformed_aggregate = copy.deepcopy(projection)
    mutated_aggregate = False
    for entries in malformed_aggregate["aggregates"].values():
        if entries and entries[0].get("accepted_receipts"):
            entries[0]["accepted_receipts"][0]["return_id"] = []
            mutated_aggregate = True
            break
    require(mutated_aggregate, "recognition fixture did not expose an aggregate receipt")
    aggregate_errors = checker._aggregate_source_context_errors(
        malformed_aggregate, projection
    )
    require(
        any("return_id must be a string" in error for error in aggregate_errors),
        "recognition checker did not reject an unhashable aggregate return_id",
    )

    for label, field, malformed in (
        ("result.class", "class", {}),
        ("result.claim_ceiling", "claim_ceiling", []),
        ("result.requested_disposition", "requested_disposition", {}),
    ):
        malformed_receipt = copy.deepcopy(receipt)
        malformed_receipt["result"][field] = malformed
        try:
            recognition.build_recognition([(name, malformed_receipt, payload)])
        except ValueError as exc:
            require(label in str(exc), f"{label} rejection lacked a bounded diagnostic: {exc}")
        else:
            raise AssertionError(f"malformed {label} escaped recognition projection builder")

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
