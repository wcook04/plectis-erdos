#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Small isolated fixtures for the reachable-history release gate."""

from __future__ import annotations

import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

import audit_reachable_release_history as audit


ROOT = Path(__file__).resolve().parent.parent
WORKFLOW = ROOT / ".github" / "workflows" / "reachable-history-trust.yml"

REPRODUCIBILITY_ENV = {
    "PYTHONPATH": "",
    "PYTHONNOUSERSITE": "1",
    "PYTHONDONTWRITEBYTECODE": "1",
    "PYTHONHASHSEED": "0",
    "PYTHONUTF8": "1",
    "LC_ALL": "C.UTF-8",
    "LANG": "C.UTF-8",
    "LANGUAGE": "C.UTF-8",
    "GIT_TERMINAL_PROMPT": "0",
    "GIT_CONFIG_NOSYSTEM": "1",
    "GIT_CONFIG_GLOBAL": "/tmp/plectis-ci-empty.gitconfig",
    "GIT_OPTIONAL_LOCKS": "0",
    "GIT_NO_REPLACE_OBJECTS": "1",
    "GIT_PAGER": "cat",
    "GIT_ASKPASS": "/bin/false",
}

# The reachable-history workflow deliberately runs directly on a disposable
# GitHub-hosted runner.  Its full-history scan is not a local checkout
# validation and therefore does not need the repository-local arbiter, but
# that exception is safe only while the workflow keeps this isolated shape.
REACHABLE_HISTORY_CI_EXECUTION_POSTURE = {
    "schema": "public-validation-execution-posture/1",
    "classification": "ci_only_isolated_runner_single_run",
    "consumer": ".github/workflows/reachable-history-trust.yml",
    "ci_only": True,
    "single_flight_required": False,
    "runner_checkout_isolated": True,
    "history_fetch_scope": "full_history_on_runner",
    "cache_scope": "none",
    "shared_checkout_write": False,
    "shared_build_cache": False,
    "duplicate_dependency_cache": False,
    "clone_or_worktree": False,
    "host_local_duplicate_work": False,
    "external_mutation": False,
}


WORKFLOW_CONSUMERS = (
    "python3 scripts/test_reachable_release_history.py --check",
    "python3 scripts/test_reachable_release_history_environment.py",
    "python3 scripts/test_reachable_release_history.py --release-gate",
)


def require(condition: bool, message: str) -> None:
    """Keep reachable-history checks active under ``python3 -O``."""
    if not condition:
        raise AssertionError(message)


def run_git(root: Path, *args: str) -> None:
    subprocess.run(["git", *args], cwd=root, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def execution_posture(workflow: str) -> dict[str, object]:
    """Prove why the history audit remains a disjoint CI-only consumer."""
    normalized = " ".join(workflow.split())
    require(
        normalized.count("runs-on: ubuntu-24.04") == 1,
        "reachable-history workflow must use one pinned runner",
    )
    budgets = re.findall(r"timeout-minutes: (\d+)", normalized)
    require(
        len(budgets) == 1 and 0 < int(budgets[0]) <= 120,
        "reachable-history workflow must bound the full-history scan",
    )
    require(
        "actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1" in normalized,
        "reachable-history workflow must pin checkout action",
    )
    require("fetch-depth: 0" in normalized, "history workflow must fetch full history")
    require(
        "filter: blob:none" not in normalized,
        "history workflow must clone every blob: the audit reads all of them, "
        "and a partial clone fetched them one object at a time until the job "
        "timed out (2026-09-05)",
    )
    require("fetch-tags: true" in normalized, "history workflow must fetch tags")
    require(
        "validation_singleflight.py" not in normalized,
        "history workflow must not route its isolated scan through single-flight",
    )
    require("git clone" not in normalized, "history workflow must not clone recursively")
    require("git worktree" not in normalized, "history workflow must not create worktrees")
    require("actions/cache" not in normalized, "history workflow must not share caches")
    positions = []
    for command in WORKFLOW_CONSUMERS:
        require(normalized.count(command) == 1, f"missing history workflow consumer: {command}")
        positions.append(normalized.index(command))
    require(
        positions == sorted(positions),
        "history consumers must remain sequential in one job",
    )
    return dict(REACHABLE_HISTORY_CI_EXECUTION_POSTURE)


def write(root: Path, relative: str, content: str | bytes) -> None:
    path = root / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    if isinstance(content, bytes):
        path.write_bytes(content)
    else:
        path.write_text(content, encoding="utf-8")


def test_workflow_environment_is_pinned() -> None:
    workflow = WORKFLOW.read_text(encoding="utf-8")
    environment_start = workflow.index("    env:\n")
    environment_end = workflow.index("    steps:\n", environment_start)
    environment = workflow[environment_start:environment_end].splitlines()
    for key, value in REPRODUCIBILITY_ENV.items():
        expected = f"      {key}: {json.dumps(value)}"
        require(expected in environment, f"workflow must pin {key} to {value!r}")
    for key in ("GIT_NAMESPACE", "GIT_REPLACE_REF_BASE"):
        require(
            f"      {key}:" not in environment,
            f"workflow must not export ambient Git selector {key}",
        )
    require("runs-on: ubuntu-24.04" in workflow, "workflow runner drifted")
    require(
        workflow.count("actions/setup-python@a26af69be951a213d495a4c3e4e4022e16d87065") == 1,
        "history workflow must install the commit-pinned Python runtime",
    )
    require(
        workflow.count('python-version: "3.12.9"') == 1,
        "history workflow must pin Python 3.12.9",
    )
    require(
        "cache:" not in workflow,
        "setup-python caching must stay disabled by omitting its provider input",
    )
    require(
        "actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1" in workflow,
        "workflow checkout action drifted",
    )
    require(
        execution_posture(workflow)["host_local_duplicate_work"] is False,
        "history workflow permits host-local duplicate work",
    )


def test_scanner_environment_neutralizes_askpass() -> None:
    original = os.environ.get("GIT_ASKPASS")
    os.environ["GIT_ASKPASS"] = "/foreign/askpass"
    try:
        environment = audit.git_environment()
    finally:
        if original is None:
            os.environ.pop("GIT_ASKPASS", None)
        else:
            os.environ["GIT_ASKPASS"] = original
    require(
        environment.get("GIT_ASKPASS") == "/bin/false",
        "history scanner retained ambient Git askpass state",
    )


def test_scanner_environment_neutralizes_runtime_context() -> None:
    hostile_environment = {
        "PYTHONHOME": "/foreign/python",
        "PYTHONPATH": "/foreign/modules",
        "PYTHONUSERBASE": "/foreign/userbase",
        "PYTHONSTARTUP": "/foreign/startup.py",
        "PYTHONBREAKPOINT": "foreign.breakpoint",
        "PYTHONWARNINGS": "error",
        "PYTHONHASHSEED": "random",
        "PYTHONOPTIMIZE": "2",
        "PYTHONUTF8": "0",
        "PYTHONNOUSERSITE": "0",
        "PYTHONDONTWRITEBYTECODE": "0",
        "LC_ALL": "C",
        "LANG": "en_US.UTF-8",
        "LANGUAGE": "fr_FR",
    }
    original = {key: os.environ.get(key) for key in hostile_environment}
    os.environ.update(hostile_environment)
    try:
        environment = audit.git_environment()
    finally:
        for key, value in original.items():
            if value is None:
                os.environ.pop(key, None)
            else:
                os.environ[key] = value
    for key in audit.PYTHON_CONTEXT_KEYS - {
        "PYTHONHASHSEED",
        "PYTHONNOUSERSITE",
        "PYTHONDONTWRITEBYTECODE",
        "PYTHONUTF8",
    }:
        require(key not in environment, f"history scanner retained ambient {key}")
    for key in audit.LOCALE_KEYS:
        require(environment.get(key) == "C.UTF-8", f"history scanner did not pin {key}")
    for key in ("PYTHONHASHSEED", "PYTHONNOUSERSITE", "PYTHONDONTWRITEBYTECODE", "PYTHONUTF8"):
        require(environment.get(key) == {"PYTHONHASHSEED": "0", "PYTHONNOUSERSITE": "1", "PYTHONDONTWRITEBYTECODE": "1", "PYTHONUTF8": "1"}[key], f"history scanner did not pin {key}")


def test_deleted_artifact_stays_bound_to_reachable_history() -> None:
    with tempfile.TemporaryDirectory(prefix="reachable-history-fixture-") as temporary:
        root = Path(temporary)
        run_git(root, "init", "-q")
        run_git(root, "config", "user.email", "fixture@example.invalid")
        run_git(root, "config", "user.name", "fixture")
        manifest = {
            "schema": "plectis.third_party_source_redistribution_dispositions.v1",
            "artifacts": [
                {
                    "path": "docs/primary-sources/fixture.pdf",
                    "sha256": "0" * 64,
                    "disposition": "link_and_digest_only",
                }
            ],
        }
        write(root, "docs/primary-sources/redistribution-dispositions.json", json.dumps(manifest))
        write(root, "docs/primary-sources/fixture.pdf", b"%PDF fixture\n")
        run_git(root, "add", ".")
        run_git(root, "commit", "-qm", "add fixture source")
        run_git(root, "rm", "-q", "docs/primary-sources/fixture.pdf")
        run_git(root, "commit", "-qm", "quarantine fixture source")

        report = audit.build_audit(root)
        records = report["artifact_history"]
        require(records, "deleted fixture blob was not found in reachable history")
        require(
            all(record["retrievable_from_reachable_ref"] for record in records),
            "deleted fixture blob was not retrievable from a reachable ref",
        )
        record = records[0]
        require(len(record["object_id"]) == 40, "fixture object id was not a Git object id")
        require(
            record["paths"] == ["docs/primary-sources/fixture.pdf"],
            "history fixture path drifted",
        )
        require(record["introducing_commits"], "fixture introduction commit was not recorded")
        require(record["removing_commits"], "fixture removal commit was not recorded")
        require(record["reachable_refs"], "fixture reachable refs were not recorded")
        blockers = report["release_blockers"]
        require(
            any(item["kind"] == "historical_third_party_artifact" for item in blockers),
            "historical artifact blocker was not emitted",
        )
        require(
            any(item["removing_commits"] for item in blockers),
            "historical artifact removal was not retained in the blocker",
        )
        remediation = report["release_decision"]["operator_remediation"]
        require(
            set(remediation["protected_refs"]) == {row["ref"] for row in report["refs"]},
            "remediation did not protect every reachable ref",
        )
        require(
            any(
                selection["object_id"] == record["object_id"]
                and selection["paths"] == record["paths"]
                for selection in remediation["object_path_selection"]
            ),
            "remediation omitted the deleted fixture object and path",
        )
        require(
            not audit_consumer_errors(report),
            "valid artifact remediation packet was rejected by the consumer",
        )


def test_renamed_artifact_stays_bound_to_manifest_path_history() -> None:
    with tempfile.TemporaryDirectory(prefix="reachable-history-rename-") as temporary:
        root = Path(temporary)
        run_git(root, "init", "-q")
        run_git(root, "config", "user.email", "fixture@example.invalid")
        run_git(root, "config", "user.name", "fixture")
        manifest = {
            "schema": "plectis.third_party_source_redistribution_dispositions.v1",
            "artifacts": [
                {
                    "path": "docs/primary-sources/old-name.pdf",
                    "sha256": "0" * 64,
                    "disposition": "link_and_digest_only",
                }
            ],
        }
        write(root, "docs/primary-sources/redistribution-dispositions.json", json.dumps(manifest))
        write(root, "docs/primary-sources/old-name.pdf", b"%PDF renamed fixture\n")
        run_git(root, "add", ".")
        run_git(root, "commit", "-qm", "add named fixture source")
        run_git(
            root,
            "mv",
            "docs/primary-sources/old-name.pdf",
            "docs/primary-sources/new-name.pdf",
        )
        run_git(root, "commit", "-qm", "rename fixture source")

        report = audit.build_audit(root)
        records = [
            record
            for record in report["artifact_history"]
            if record["paths"] == ["docs/primary-sources/old-name.pdf"]
        ]
        require(records, "renamed manifest artifact blob was omitted from history")
        require(
            any(record["removing_commits"] for record in records),
            "renamed manifest artifact removal was not retained in path history",
        )
        require(
            any(
                blocker["kind"] == "historical_third_party_artifact"
                and blocker["paths"] == ["docs/primary-sources/old-name.pdf"]
                for blocker in report["release_blockers"]
            ),
            "renamed manifest artifact did not remain a historical release blocker",
        )


def test_scanner_source_fingerprint_is_required() -> None:
    with tempfile.TemporaryDirectory(prefix="reachable-history-fingerprint-") as temporary:
        root = Path(temporary)
        run_git(root, "init", "-q")
        run_git(root, "config", "user.email", "fixture@example.invalid")
        run_git(root, "config", "user.name", "fixture")
        write(root, "README.md", "fixture\n")
        run_git(root, "add", ".")
        run_git(root, "commit", "-qm", "fixture baseline")

        report = audit.build_audit(root)
        current = audit.build_audit(root)
        require(
            report["scanner_source_sha256"] == current["scanner_source_sha256"],
            "identical history scans changed scanner source fingerprint",
        )
        report["scanner_source_sha256"] = "sha256:" + "0" * 64
        require(
            any(
                "different scanner source revision" in error
                for error in audit.comparison_errors(report, current, root)
            ),
            "scanner source fingerprint drift was not detected",
        )


def test_secret_finding_is_redacted() -> None:
    key_begin = b"-----BEGIN " + b"PRIVATE KEY-----"
    key_end = b"-----END " + b"PRIVATE KEY-----"
    secret = key_begin + b"\n" + b"fixture" + b"-only-secret-material\n" + key_end + b"\n"
    security, _, _ = audit._content_findings("a" * 40, ["fixture.txt"], secret)
    rendered = json.dumps(security, sort_keys=True)
    require(
        security and security[0]["kind"] == "private_key_material_marker",
        "private-key marker was not detected",
    )
    require(
        b"fixture-only-secret-material" not in rendered.encode("utf-8"),
        "secret fixture material was not redacted",
    )
    require("redacted_fingerprints" in rendered, "redacted fingerprints were not emitted")


def test_token_families_are_detected_and_redacted() -> None:
    for label, token in (
        ("GitLab", b"glpat-" + b"g" * 24),
        ("npm", b"npm_" + b"n" * 24),
    ):
        security, _, _ = audit._content_findings("b" * 40, ["fixture.txt"], token)
        rendered = json.dumps(security, sort_keys=True).encode("utf-8")
        require(
            security and security[0]["kind"] == "credential_token_marker",
            f"{label} token marker was not detected",
        )
        require(token not in rendered, f"{label} token fixture was not redacted")


def test_non_atomic_audit_requires_an_explicit_current_release_block() -> None:
    with tempfile.TemporaryDirectory(prefix="reachable-history-non-atomic-") as temporary:
        root = Path(temporary)
        run_git(root, "init", "-q")
        run_git(root, "config", "user.email", "fixture@example.invalid")
        run_git(root, "config", "user.name", "fixture")
        write(root, "README.md", "fixture\n")
        run_git(root, "add", ".")
        run_git(root, "commit", "-qm", "fixture baseline")

        report = audit.build_audit(root)
        current = audit.build_audit(root)
        scan = report["scan"]
        require(isinstance(scan, dict), "history scan payload is not an object")
        scan.update(
            {
                "scan_consistent": False,
                "scan_end_commit": audit.head_commit(root),
                "end_refs": report["refs"],
                "ref_changes": [],
            }
        )
        report["release_blockers"] = [{"kind": "non_atomic_scan"}]
        report["release_decision"]["safe_for_public_clone"] = False
        require(
            audit.comparison_errors(report, current, root) == [],
            "explicit non-atomic release block was incorrectly treated as drift",
        )

        original_refs = report["refs"]
        malformed_ref_fields = (
            ("ref", "refs/", "lacks a valid ref name"),
            ("object_id", "not-a-git-object-id", "lacks a valid object id"),
            ("object_type", "not-a-git-object-type", "lacks a valid object type"),
            ("peeled_commit", "not-a-git-object-id", "lacks a valid peeled commit"),
            ("ref_class", "not-the-derived-class", "lacks a valid ref class"),
        )
        for field, malformed_value, expected_error in malformed_ref_fields:
            report["refs"] = [
                {**original_refs[0], field: malformed_value},
                *original_refs[1:],
            ]
            require(
                any(
                    f"ref snapshot row 0 {expected_error}" in error
                    for error in audit_consumer_errors(report)
                ),
                f"malformed reachable-ref {field} was accepted",
            )
        report["refs"] = original_refs

        report["release_blockers"] = []
        require(
            audit.comparison_errors(report, current, root),
            "missing non-atomic release block was not detected",
        )
        report["release_blockers"] = [{"kind": "historical_secret"}]
        require(
            any("lacks a non-empty object id" in error for error in audit_consumer_errors(report)),
            "object-backed blocker without an object id was accepted",
        )
        report["release_blockers"] = [
            {"kind": "historical_secret", "object_id": "a" * 40}
        ]
        report["release_decision"]["safe_for_public_clone"] = False
        report["release_decision"]["operator_remediation"]["object_path_selection"] = []
        require(
            any(
                "omits object-backed blocker selection" in error
                for error in audit_consumer_errors(report)
            ),
            "object-backed blocker omitted from remediation selection was accepted",
        )
        report["release_blockers"] = [
            {
                "kind": "historical_secret",
                "object_id": "a" * 40,
                "disposition": "release_blocked_redacted_secret_review_required",
            }
        ]
        report["release_decision"]["operator_remediation"]["object_path_selection"] = [
            {
                "object_id": "a" * 40,
                "selection_reason": "historical_secret",
                "governing_disposition": "wrong-disposition",
            }
        ]
        require(
            any(
                "governing disposition that does not match the blocker" in error
                for error in audit_consumer_errors(report)
            ),
            "mismatched remediation governing disposition was accepted",
        )
        context = {
            "paths": ["history-secret.txt"],
            "object_type": "blob",
            "size_bytes": 37,
            "introducing_commits": ["b" * 40],
            "removing_commits": [],
            "object_history_commits": ["b" * 40],
            "reachable_refs": ["refs/heads/main"],
            "retrievable_from_reachable_ref": True,
            "current_head_exposure": False,
        }
        report["release_blockers"] = [
            {
                "kind": "historical_secret",
                "object_id": "a" * 40,
                "disposition": "release_blocked_redacted_secret_review_required",
                **context,
            }
        ]
        report["release_decision"]["operator_remediation"]["object_path_selection"] = [
            {
                "object_id": "a" * 40,
                **context,
                "paths": ["wrong-history-secret.txt"],
                "selection_reason": "historical_secret",
                "governing_disposition": "release_blocked_redacted_secret_review_required",
            }
        ]
        require(
            any(
                "has mismatched paths context" in error
                for error in audit_consumer_errors(report)
            ),
            "mismatched remediation object context was accepted",
        )
        context["size_bytes"] = "37"
        report["release_blockers"] = [
            {
                "kind": "historical_secret",
                "object_id": "a" * 40,
                "disposition": "release_blocked_redacted_secret_review_required",
                **context,
            }
        ]
        require(
            any(
                "lacks a valid object size" in error
                for error in audit_consumer_errors(report)
            ),
            "malformed remediation object size was accepted",
        )


def audit_consumer_errors(report: dict[str, object]) -> list[str]:
    """Import the evidence consumer without running the repository-wide scan."""
    import test_reachable_release_history as consumer

    return (
        consumer.ref_snapshot_errors(report)
        + consumer.blocker_context_errors(report)
        + consumer.remediation_selection_errors(report)
    )


if __name__ == "__main__":
    test_workflow_environment_is_pinned()
    test_scanner_environment_neutralizes_askpass()
    test_deleted_artifact_stays_bound_to_reachable_history()
    test_renamed_artifact_stays_bound_to_manifest_path_history()
    test_scanner_source_fingerprint_is_required()
    test_secret_finding_is_redacted()
    test_token_families_are_detected_and_redacted()
    test_non_atomic_audit_requires_an_explicit_current_release_block()
    posture = execution_posture(WORKFLOW.read_text(encoding="utf-8"))
    print(
        "test_reachable_release_history_environment: history boundary and redaction fixtures pass "
        f"({posture['classification']})"
    )
