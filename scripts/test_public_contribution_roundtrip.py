#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Simulate two public contribution journeys without creating real credit.

The people and adoption decisions here are fixtures only.  Existing Git paths
provide commit ancestry for the production acceptance validator; no receipt is
written to the repository's accepted-return directory.
"""

from __future__ import annotations

import copy
import tempfile
from pathlib import Path
from unittest import mock

import accept_research_return as acceptance
import build_research_contribution_recognition as recognition
import build_research_contributions as contributions
import test_accept_research_return as acceptance_fixture


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def submission(path: str, return_id: str, name: str) -> tuple[dict, str]:
    returned, head = acceptance_fixture.make_submission()
    returned["return_id"] = return_id
    returned["repository"]["changed_paths"] = [path]
    returned["frontier"]["starting_paths"] = [path]
    returned["evidence"][0]["artifacts"] = [path]
    returned["identity"]["contributor"] = {"name": name, "handle": None, "identifiers": []}
    returned["identity"]["operator"] = {"relationship": "same_as_contributor", "name": name}
    returned["attribution"]["requested_display"] = name + " — simulation fixture only"
    returned["attribution"]["artifact_credit"] = [
        {"name": name, "artifact_paths": [path]}
    ]
    return returned, head


def main() -> int:
    identity = acceptance.repository_identity_contract.load_identity()
    correction, head = submission(
        "docs/papers/full-text/erdos-257-mersenne-support-subseries.md",
        "rr-fixture-expository-correction", "Fixture Corrector"
    )
    correction["frontier"]["handle"] = "fixture/expository-correction"
    correction["frontier"]["bounded_question"] = "Does an explanation identify its assumption?"
    correction["result"].update(
        {
            "class": "corrective",
            "summary": "Simulation: a bounded explanation identifies its missing assumption.",
            "claim_ceiling": "documentation_correction",
            "surviving_boundary": "No mathematical theorem or claim status changes in this fixture.",
            "limitations": ["Simulation only; no real mathematical correction is submitted."],
            "requested_disposition": "review_correction",
        }
    )
    correction["correction_lineage"] = {
        "prior_return_reference": "none",
        "affected_paths": correction["repository"]["changed_paths"],
        "starting_commit": correction["repository"]["starting_commit"],
        "changed_evidence_or_wording": "Simulation: an assumption is made explicit.",
        "reason": "Simulation: the earlier explanation was ambiguous.",
        "disposition": "request_review",
    }
    correction["evidence"][0].update(
        {
            "command": "python3 scripts/test_contribution_entry.py",
            "exit_state": "passed",
            "exit_code": 0,
            "observed": "Simulation fixture; the contribution entry check passed separately.",
            "replay_state": "reproduced",
        }
    )
    correction["attribution"]["artifact_credit"][0]["contribution_roles"] = ["writing_review_editing"]

    architecture, architecture_head = submission(
        "docs/research-commons/ARCHITECTURE_CONTRIBUTIONS.md",
        "rr-fixture-architecture-idea",
        "Fixture Idea Originator",
    )
    require(head == architecture_head, "simulations use different checkout revisions")
    architecture["frontier"] = {
        "track": "architecture",
        "area": "public_experience",
        "handle": "fixture/idea-only-route",
        "bounded_question": "Can an ordinary-language architecture idea retain its originator?",
        "stop_condition": "Stop after a review decision and scoped credit projection.",
        "starting_paths": ["docs/research-commons/ARCHITECTURE_CONTRIBUTIONS.md"],
    }
    architecture["result"].update(
        {
            "class": "inconclusive",
            "summary": "Simulation: an idea is described in an adopted public guide.",
            "claim_ceiling": "architecture_proposal",
            "surviving_boundary": "No code or mathematical result is attributed to the idea originator.",
            "limitations": ["Simulation only; no outside idea was actually adopted."],
            "requested_disposition": "consider_architecture_adoption",
        }
    )
    architecture["evidence"][0].update(
        {
            "command": "python3 scripts/test_contribution_entry.py",
            "observed": "Simulation fixture; the public idea-entry check passed separately.",
        }
    )
    architecture["identity"]["operator"] = {
        "relationship": "named", "name": "Fixture Implementer"
    }
    architecture["identity"]["model_system"] = {
        "state": "disclosed", "name": "Fixture AI Assistant", "version": "simulation", "resources": []
    }
    architecture["identity"]["provider"] = {
        "state": "disclosed", "name": "Fixture Provider", "version": "simulation", "resources": []
    }
    architecture["attribution"]["artifact_credit"] = [
        {
            "name": "Fixture Idea Originator",
            "artifact_paths": architecture["repository"]["changed_paths"],
            "contribution_roles": ["conceptualization"],
        },
        {
            "name": "Fixture Implementer",
            "artifact_paths": architecture["repository"]["changed_paths"],
            "contribution_roles": ["writing_review_editing"],
        },
    ]

    accepted_sources = []
    for returned in (correction, architecture):
        template, errors = acceptance.build_decision_template(returned, repository_identity=identity)
        require(not errors and template is not None, f"submitted fixture invalid: {errors}")
        pending, errors = acceptance.build_candidate(returned, template, repository_identity=identity)
        require(pending is None and any("accepted_handoff" in error for error in errors),
                "a pending reviewer decision escaped the acceptance boundary")

        decision = acceptance_fixture.make_decision(head)
        decision["review"]["structural_validation"]["reviewer"] = "Fixture Validator"
        decision["review"]["reproduction"]["reviewer"] = "Fixture Replay Reviewer"
        decision["review"]["accepted_handoff"]["reviewer"] = "Fixture Adoption Reviewer"
        candidate, errors = acceptance.build_candidate(
            returned, decision, repository_identity=identity
        )
        require(not errors and candidate is not None, f"explicit adoption decision failed: {errors}")
        require(candidate["attribution"] == returned["attribution"],
                "acceptance changed scoped contributor credit")
        require(candidate["review"]["accepted_handoff"]["reviewer"] == "Fixture Adoption Reviewer",
                "adoption reviewer was lost")
        accepted_sources.append(
            (returned["return_id"] + ".json", candidate, contributions.canonical(candidate))
        )

    rejected = copy.deepcopy(architecture)
    rejected["return_id"] = "rr-fixture-rejected-idea"
    rejected["identity"]["contributor"]["name"] = "Fixture Rejected Originator"
    rejected["attribution"]["artifact_credit"][0]["name"] = "Fixture Rejected Originator"
    rejected_decision = acceptance_fixture.make_decision(head)
    rejected_decision["review"]["accepted_handoff"].update(
        {"state": "rejected", "reviewer": "Fixture Adoption Reviewer"}
    )
    refused, errors = acceptance.build_candidate(
        rejected, rejected_decision, repository_identity=identity
    )
    require(refused is None and any("accepted_handoff.state" in error for error in errors),
            "explicit reviewer rejection became an accepted receipt")
    rejected["review"]["accepted_handoff"] = copy.deepcopy(
        rejected_decision["review"]["accepted_handoff"]
    )
    with tempfile.TemporaryDirectory() as directory:
        Path(directory, rejected["return_id"] + ".json").write_bytes(contributions.canonical(rejected))
        require(contributions.load_receipts(Path(directory)) == [],
                "an unaccepted idea entered the accepted receipt source set")
    try:
        contributions.build_projection(
            accepted_sources + [(rejected["return_id"] + ".json", rejected, contributions.canonical(rejected))]
        )
    except ValueError as exc:
        require("accepts accepted_receipt records only" in str(exc),
                "unaccepted idea rejection lacked its accepted-only reason")
    else:
        raise AssertionError("an unaccepted idea entered contribution output")

    public_credit = contributions.build_projection(accepted_sources)
    with mock.patch.object(recognition, "_receipt_source_commit", return_value=head):
        public_recognition = recognition.build_recognition(accepted_sources)
    for problem in contributions.route_memory_receipt.ROSTER:
        route = contributions.public_result_family_route(problem)
        require(route["repository_path"] == "docs/CONTRIBUTE_BY_PAPER.md"
                and route["anchor"] == f"problem-{problem}",
                f"problem {problem} credit lacks its actual public entry")
    contribution_text = contributions.human_projection(public_credit).decode("utf-8")
    recognition_text = recognition.human_projection(public_recognition).decode("utf-8")
    for name in ("Fixture Corrector", "Fixture Idea Originator", "Fixture Implementer"):
        require(name in contribution_text and name in recognition_text,
                f"accepted scoped credit missing from both views: {name}")
    require("Fixture AI Assistant" in contribution_text + recognition_text,
            "disclosed AI assistance was lost from accepted credit")
    require("Fixture Adoption Reviewer" in contribution_text + recognition_text,
            "adoption reviewer was lost from accepted credit")
    require("Fixture Rejected Originator" not in contribution_text + recognition_text,
            "rejected idea entered accepted credit")
    require(public_credit["filters"]["by_problem"] == {"257": [correction["return_id"]]},
            "an architecture idea entered mathematical problem credit")
    require(public_credit["chronological"][0]["public_frontier"] == {
        "repository_path": "docs/CONTRIBUTE_BY_PAPER.md",
        "anchor": "problem-257",
        "relative_link": "../CONTRIBUTE_BY_PAPER.md#problem-257",
    }, "mathematical credit does not lead to the real public contribution entry")
    require(public_credit["filters"]["by_architecture_area"] ==
            {"public_experience": [architecture["return_id"]]},
            "architecture adoption lost its bounded area")
    require(architecture["attribution"]["existing_corpus_authorship_preserved"] is True,
            "architecture simulation claimed earlier corpus authorship")
    require(correction["attribution"]["existing_corpus_authorship_preserved"] is True
            and correction["review"]["problem_owned_proposition"]["state"] == "not_requested",
            "correction simulation appropriated prior mathematical credit or promoted a claim")
    print("public contribution round trip: correction and idea-only adoption decisions, "
          "accepted-only credit, roles, and rejected exclusion PASS (simulation fixtures only)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
