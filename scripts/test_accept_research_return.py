#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial executable checks for explicit public-return acceptance."""

from __future__ import annotations

import copy
import json
import subprocess
import sys
import tempfile
from pathlib import Path

import accept_research_return as acceptor


ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / ".github" / "fixtures" / "unaccepted-research-return.json"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def git(*arguments: str) -> str:
    completed = subprocess.run(
        ["git", *arguments],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
        env=acceptor.return_validator.git_environment(),
        timeout=acceptor.return_validator.GIT_COMMAND_TIMEOUT_SECONDS,
    )
    return completed.stdout.strip()


def make_submission() -> tuple[dict, str]:
    submission = json.loads(FIXTURE.read_text(encoding="utf-8"))
    head = git("rev-parse", "HEAD")
    submission["return_id"] = "rr-acceptance-test-submitted"
    submission["repository"]["starting_commit"] = git("rev-parse", "8313a1e0^")
    submission["repository"]["proposed_commit"] = head
    submission["repository"]["changed_paths"] = ["docs/repository_identity.json"]
    submission["evidence"][0]["artifacts"] = ["docs/repository_identity.json"]
    submission["attribution"]["artifact_credit"] = [
        {"name": submission["identity"]["contributor"]["name"], "artifact_paths": ["docs/repository_identity.json"]}
    ]
    return submission, head


def make_decision(head: str, *, decided_at: str = "2026-08-30T00:00:00Z") -> dict:
    review = {
        name: {
            "state": (
                "not_requested"
                if name in {"problem_owned_proposition", "core_promotion", "tagged_release_inclusion"}
                else "pending"
            ),
            "reviewer": None,
            "decided_at": None,
            "authority_ref": None,
            "notes": "not independently required for this bounded test",
        }
        for name in acceptor.REVIEW_NAMES
    }
    review["structural_validation"] = {
        "state": "valid",
        "reviewer": "test reviewer",
        "decided_at": decided_at,
        "authority_ref": "scripts/test_accept_research_return.py",
        "notes": "validator replayed",
    }
    review["reproduction"] = {
        "state": "reproduced",
        "reviewer": "test reviewer",
        "decided_at": decided_at,
        "authority_ref": "scripts/test_accept_research_return.py",
        "notes": "bounded fixture replayed",
    }
    review["accepted_handoff"] = {
        "state": "accepted",
        "reviewer": "test reviewer",
        "decided_at": decided_at,
        "authority_ref": f"git:{head}",
        "notes": "explicit test-only acceptance decision",
    }
    return {
        "schema": acceptor.DECISION_SCHEMA,
        "accepted_commit": head,
        "review": review,
    }


def main() -> int:
    submission, head = make_submission()
    identity = acceptor.repository_identity_contract.load_identity()
    decision = make_decision(head)
    candidate, errors = acceptor.build_candidate(
        submission,
        decision,
        repository_identity=identity,
    )
    require(not errors, f"explicit valid decision did not produce a candidate: {errors}")
    require(candidate is not None, "accepted candidate was not returned")
    require(candidate["record_kind"] == "accepted_receipt", "candidate is not an accepted receipt")
    require(candidate["repository"]["accepted_commit"] == head, "accepted commit was not bound")
    for field in ("identity", "frontier", "result", "evidence", "attribution"):
        require(candidate[field] == submission[field], f"acceptance rewrote submitted {field}")

    wrong_authority = copy.deepcopy(decision)
    wrong_authority["review"]["accepted_handoff"]["authority_ref"] = "git:" + "0" * 40
    rejected, rejection_errors = acceptor.build_candidate(
        submission,
        wrong_authority,
        repository_identity=identity,
    )
    require(rejected is None and any("authority" in error for error in rejection_errors), "wrong Git authority escaped")

    old_decision = make_decision(head, decided_at="2026-08-26T00:00:00Z")
    rejected, rejection_errors = acceptor.build_candidate(
        submission,
        old_decision,
        repository_identity=identity,
    )
    require(rejected is None and any("must not precede" in error for error in rejection_errors), "pre-submission acceptance escaped")

    binding, binding_errors, _ = acceptor.route_memory_binding_errors(
        submission,
        None,
        required=True,
    )
    require(binding is None and binding_errors, "required route-memory receipt was optional")

    with tempfile.TemporaryDirectory() as directory:
        output = Path(directory) / "accepted.json"
        output_error = acceptor.write_new_file(output, acceptor.canonical(candidate))
        require(output_error is None and output.is_file(), "atomic acceptance output was not published")
        duplicate_error = acceptor.write_new_file(output, b"second")
        require(duplicate_error == "output already exists", "existing acceptance output was overwritten")
        link = Path(directory) / "link.json"
        link.symlink_to(output)
        link_error = acceptor.write_new_file(link, b"linked")
        require(link_error == "output path must not be a symbolic link", "symlink output was followed")

        malformed = Path(directory) / "malformed-utf8.json"
        malformed.write_bytes(b"{\xff\n")
        decision_template = Path(directory) / "decision-template.json"
        malformed_cli = subprocess.run(
            [
                sys.executable,
                str(ROOT / "scripts" / "accept_research_return.py"),
                str(malformed),
                "--write-decision-template",
                str(decision_template),
            ],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
            env=acceptor.return_validator.git_environment(),
        )
        require(malformed_cli.returncode == 2, "acceptance did not classify malformed UTF-8 as CLI input failure")
        malformed_receipt = json.loads(malformed_cli.stdout)
        require(
            malformed_receipt["valid"] is False
            and any("utf-8" in error.lower() for error in malformed_receipt["errors"]),
            "acceptance did not emit a machine-readable decode diagnostic",
        )
        require("Traceback" not in malformed_cli.stderr, "acceptance emitted a traceback for malformed UTF-8")

    print("accept_research_return: explicit decision, ancestry, authority, route and output safety PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
