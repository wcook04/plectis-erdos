#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Release-consumption checks for the redacted reachable-history audit."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

import audit_reachable_release_history as audit


ROOT = Path(__file__).resolve().parents[1]

REMEDIATION_LIST_FIELDS = (
    "protected_identities",
    "protected_refs",
    "ref_changes_during_scan",
    "object_path_selection",
    "expected_commit_tag_receipt_consequences",
    "collaborator_and_fork_coordination",
    "verification_commands",
    "rollback_material",
    "outbound_mutation_requiring_explicit_operator_approval",
)
OBJECT_CONTEXT_FIELDS = (
    "object_type",
    "size_bytes",
    "introducing_commits",
    "removing_commits",
    "object_history_commits",
    "reachable_refs",
    "retrievable_from_reachable_ref",
    "current_head_exposure",
)
REMEDIATION_OBJECT_FIELDS = OBJECT_CONTEXT_FIELDS + (
    "selection_reason",
    "governing_disposition",
)
GIT_OBJECT_ID_RE = re.compile(r"[0-9a-f]{40}")
GIT_OBJECT_TYPES = frozenset({"blob", "commit", "tag", "tree"})
REPORTED_OBJECT_TYPES = GIT_OBJECT_TYPES | {"missing"}


def _valid_ref_name(value: object) -> bool:
    """Require a non-empty ref beneath Git's refs namespace."""
    return (
        isinstance(value, str)
        and value.startswith("refs/")
        and len(value) > len("refs/")
        and not any(character.isspace() for character in value)
    )


def _object_context_value_errors(label: str, row: dict[str, object]) -> list[str]:
    """Reject malformed object context even when a report is non-atomic."""
    errors: list[str] = []
    paths = row.get("paths")
    if isinstance(paths, list) and any(
        not isinstance(path, str) or not path for path in paths
    ):
        errors.append(f"{label} contains an invalid object path")
    object_type = row.get("object_type")
    if not isinstance(object_type, str) or object_type not in REPORTED_OBJECT_TYPES:
        errors.append(f"{label} lacks a valid object type")
    size_bytes = row.get("size_bytes")
    if object_type == "missing" and size_bytes is not None:
        errors.append(f"{label} has a size for a missing object")
    elif object_type != "missing" and (
        not isinstance(size_bytes, int)
        or isinstance(size_bytes, bool)
        or size_bytes < 0
    ):
        errors.append(f"{label} lacks a valid object size")
    for field in (
        "introducing_commits",
        "removing_commits",
        "object_history_commits",
    ):
        commits = row.get(field)
        if isinstance(commits, list) and any(
            not isinstance(commit, str) or not GIT_OBJECT_ID_RE.fullmatch(commit)
            for commit in commits
        ):
            errors.append(f"{label} has invalid {field} context")
    reachable_refs = row.get("reachable_refs")
    if isinstance(reachable_refs, list) and any(
        not isinstance(ref_row, dict)
        or not _valid_ref_name(ref_row.get("ref"))
        or not isinstance(ref_row.get("ref_class"), str)
        or not ref_row["ref_class"]
        or ref_row["ref_class"] != audit._ref_class(ref_row["ref"])
        for ref_row in reachable_refs
    ):
        errors.append(f"{label} has invalid reachable ref context")
    return errors


def adversarial_context_errors() -> list[str]:
    """Reject forged object and ref context before it can support a red decision."""
    base = {
        "kind": "historical_secret",
        "object_id": "a" * 40,
        "paths": ["docs/example.txt"],
        "object_type": "blob",
        "size_bytes": 1,
        "introducing_commits": ["b" * 40],
        "removing_commits": [],
        "object_history_commits": ["b" * 40],
        "reachable_refs": [{"ref": "refs/tags/v1", "ref_class": "tag"}],
        "retrievable_from_reachable_ref": True,
        "current_head_exposure": False,
    }
    cases = (
        ("forged object type", {**base, "object_type": "forged-object-type"}, "valid object type"),
        (
            "forged ref class",
            {**base, "reachable_refs": [{"ref": "refs/tags/v1", "ref_class": "branch"}]},
            "invalid reachable ref context",
        ),
        ("sized missing object", {**base, "object_type": "missing"}, "size for a missing object"),
    )
    errors: list[str] = []
    for label, blocker, expected in cases:
        found = blocker_context_errors({"release_blockers": [blocker]})
        if not any(expected in error for error in found):
            errors.append(f"{label} context was accepted")
    return errors


def _ref_snapshot_errors(label: str, rows: object) -> list[str]:
    """Validate frozen ref rows before trusting non-atomic boundary evidence."""
    if not isinstance(rows, list):
        return [f"{label} is not a list"]
    errors: list[str] = []
    for index, row in enumerate(rows):
        row_label = f"{label} row {index}"
        if not isinstance(row, dict):
            errors.append(f"{row_label} is not an object")
            continue
        ref = row.get("ref")
        if not _valid_ref_name(ref):
            errors.append(f"{row_label} lacks a valid ref name")
        object_id = row.get("object_id")
        if not isinstance(object_id, str) or not GIT_OBJECT_ID_RE.fullmatch(object_id):
            errors.append(f"{row_label} lacks a valid object id")
        if row.get("object_type") not in GIT_OBJECT_TYPES:
            errors.append(f"{row_label} lacks a valid object type")
        peeled_commit = row.get("peeled_commit")
        if not isinstance(peeled_commit, str) or (
            peeled_commit and not GIT_OBJECT_ID_RE.fullmatch(peeled_commit)
        ):
            errors.append(f"{row_label} lacks a valid peeled commit")
        ref_class = row.get("ref_class")
        if (
            not isinstance(ref_class, str)
            or not ref_class
            or isinstance(ref, str) and ref_class != audit._ref_class(ref)
        ):
            errors.append(f"{row_label} lacks a valid ref class")
    return errors


def ref_snapshot_errors(report: dict[str, object]) -> list[str]:
    """Validate report ref snapshots, including both sides of a moving scan."""
    errors = _ref_snapshot_errors("history audit ref snapshot", report.get("refs"))
    scan = report.get("scan")
    if isinstance(scan, dict) and scan.get("scan_consistent") is not True:
        errors.extend(
            _ref_snapshot_errors(
                "history audit end ref snapshot", scan.get("end_refs")
            )
        )
    return errors


def blocker_context_errors(report: dict[str, object]) -> list[str]:
    """Keep non-atomic reports from omitting object exposure context."""
    blockers = report.get("release_blockers")
    if not isinstance(blockers, list):
        return []
    errors: list[str] = []
    for index, blocker in enumerate(blockers):
        if not isinstance(blocker, dict) or blocker.get("kind") == "non_atomic_scan":
            continue
        if "object_id" not in blocker:
            errors.append(
                f"object-backed release blocker {index} ({blocker.get('kind', 'unknown')}) "
                "lacks a non-empty object id"
            )
            continue
        label = f"object-backed release blocker {index} ({blocker.get('kind', 'unknown')})"
        if not isinstance(blocker.get("object_id"), str) or not GIT_OBJECT_ID_RE.fullmatch(
            blocker["object_id"]
        ):
            errors.append(f"{label} lacks a valid 40-character Git object id")
        if not isinstance(blocker.get("paths"), list) or not blocker["paths"]:
            errors.append(f"{label} lacks object paths")
        for field in OBJECT_CONTEXT_FIELDS:
            if field not in blocker:
                errors.append(f"{label} lacks {field} context")
        for field in (
            "introducing_commits",
            "removing_commits",
            "object_history_commits",
            "reachable_refs",
        ):
            if not isinstance(blocker.get(field), list):
                errors.append(f"{label} has non-list {field} context")
        if not isinstance(blocker.get("retrievable_from_reachable_ref"), bool):
            errors.append(f"{label} lacks boolean retrievability context")
        if not isinstance(blocker.get("current_head_exposure"), bool):
            errors.append(f"{label} lacks boolean current-head exposure")
        errors.extend(_object_context_value_errors(label, blocker))
        if blocker.get("kind") == "historical_third_party_artifact":
            disposition = blocker.get("manifest_disposition")
            if not isinstance(disposition, str) or not disposition:
                errors.append(f"{label} lacks its artifact disposition")
            digest = blocker.get("manifest_sha256")
            if (
                not isinstance(digest, str)
                or len(digest) != 64
                or any(character not in "0123456789abcdef" for character in digest)
            ):
                errors.append(f"{label} lacks a valid artifact disposition digest")
    return errors


def remediation_errors(decision: dict[str, object]) -> list[str]:
    """Require a complete reversible operator packet for a red decision."""
    if decision.get("safe_for_public_clone") is not False:
        return []
    remediation = decision.get("operator_remediation")
    if not isinstance(remediation, dict):
        return ["blocked history decision lacks its operator remediation packet"]
    errors: list[str] = []
    if not isinstance(remediation.get("decision_id"), str) or not remediation.get("decision_id"):
        errors.append("operator remediation lacks a decision identifier")
    if remediation.get("status") != "operator_approval_required_before_any_outbound_mutation":
        errors.append("operator remediation does not require approval before outbound mutation")
    for field in REMEDIATION_LIST_FIELDS:
        if not isinstance(remediation.get(field), list):
            errors.append(f"operator remediation field is not a list: {field}")
    protected_refs = remediation.get("protected_refs")
    if isinstance(protected_refs, list) and not protected_refs:
        errors.append("operator remediation does not protect any refs")
    verification = remediation.get("verification_commands")
    if isinstance(verification, list) and not verification:
        errors.append("operator remediation has no verification commands")
    rollback = remediation.get("rollback_material")
    if isinstance(rollback, list) and not rollback:
        errors.append("operator remediation has no rollback material")
    outbound = remediation.get("outbound_mutation_requiring_explicit_operator_approval")
    if isinstance(outbound, list) and not outbound:
        errors.append("operator remediation names no outbound mutation requiring approval")
    action = remediation.get("agent_action_taken")
    if not isinstance(action, str) or not action:
        errors.append("operator remediation lacks the agent action boundary")
    selections = remediation.get("object_path_selection")
    if isinstance(selections, list):
        for index, selection in enumerate(selections):
            if not isinstance(selection, dict):
                errors.append(f"operator remediation object selection {index} is not an object")
                continue
            if not isinstance(selection.get("object_id"), str) or not GIT_OBJECT_ID_RE.fullmatch(
                selection["object_id"]
            ):
                errors.append(
                    f"operator remediation object selection {index} lacks a valid 40-character Git object id"
                )
            if not isinstance(selection.get("paths"), list) or not selection["paths"]:
                errors.append(f"operator remediation object selection {index} lacks paths")
            for field in REMEDIATION_OBJECT_FIELDS:
                if field not in selection:
                    errors.append(
                        f"operator remediation object selection {index} lacks {field} context"
                    )
            for field in (
                "introducing_commits",
                "removing_commits",
                "object_history_commits",
                "reachable_refs",
            ):
                if not isinstance(selection.get(field), list):
                    errors.append(
                        f"operator remediation object selection {index} has non-list {field}"
                    )
            if not isinstance(selection.get("retrievable_from_reachable_ref"), bool):
                errors.append(
                    f"operator remediation object selection {index} lacks boolean retrievability"
                )
            if not isinstance(selection.get("current_head_exposure"), bool):
                errors.append(
                    f"operator remediation object selection {index} lacks boolean current-head exposure"
                )
            errors.extend(
                _object_context_value_errors(
                    f"operator remediation object selection {index}", selection
                )
            )
            if not isinstance(selection.get("selection_reason"), str) or not selection["selection_reason"]:
                errors.append(
                    f"operator remediation object selection {index} lacks selection reason"
                )
            if not isinstance(selection.get("governing_disposition"), str) or not selection["governing_disposition"]:
                errors.append(
                    f"operator remediation object selection {index} lacks governing disposition"
                )
            if selection.get("selection_reason") == "historical_third_party_artifact":
                manifest_disposition = selection.get("manifest_disposition")
                if not isinstance(manifest_disposition, str) or not manifest_disposition:
                    errors.append(
                        f"operator remediation object selection {index} lacks its artifact disposition"
                    )
                elif manifest_disposition != selection.get("governing_disposition"):
                    errors.append(
                        f"operator remediation object selection {index} has mismatched artifact and governing dispositions"
                    )
                digest = selection.get("manifest_sha256")
                if (
                    not isinstance(digest, str)
                    or len(digest) != 64
                    or any(character not in "0123456789abcdef" for character in digest)
                ):
                    errors.append(
                        f"operator remediation object selection {index} lacks a valid artifact digest"
                    )
    return errors


def remediation_selection_errors(report: dict[str, object]) -> list[str]:
    """Require one reversible packet selection for every object-backed blocker."""
    blockers = report.get("release_blockers")
    decision = report.get("release_decision")
    if not isinstance(blockers, list) or not isinstance(decision, dict):
        return []
    if decision.get("safe_for_public_clone") is not False:
        return []
    remediation = decision.get("operator_remediation")
    if not isinstance(remediation, dict):
        return []
    selections = remediation.get("object_path_selection")
    if not isinstance(selections, list):
        return []
    selected_pairs = {
        (selection.get("object_id"), selection.get("selection_reason"))
        for selection in selections
        if isinstance(selection, dict)
    }
    errors: list[str] = []
    for index, blocker in enumerate(blockers):
        if not isinstance(blocker, dict) or blocker.get("kind") == "non_atomic_scan":
            continue
        object_id = blocker.get("object_id")
        kind = blocker.get("kind", "unknown")
        if not isinstance(object_id, str) or not GIT_OBJECT_ID_RE.fullmatch(object_id):
            continue
        if (object_id, kind) not in selected_pairs:
            errors.append(
                f"operator remediation omits object-backed blocker selection {index} "
                f"({kind})"
            )
            continue
        expected_disposition = (
            blocker.get("manifest_disposition")
            if kind == "historical_third_party_artifact"
            else blocker.get("disposition", blocker.get("manifest_disposition"))
        )
        matching_selections = [
            selection
            for selection in selections
            if isinstance(selection, dict)
            and selection.get("object_id") == object_id
            and selection.get("selection_reason") == kind
        ]
        if not isinstance(expected_disposition, str) or not expected_disposition:
            errors.append(
                f"object-backed blocker {index} ({kind}) lacks a governing disposition"
            )
            continue
        if any(
            selection.get("governing_disposition") != expected_disposition
            for selection in matching_selections
        ):
            errors.append(
                f"operator remediation selection for blocker {index} ({kind}) "
                "has a governing disposition that does not match the blocker"
            )
        binding_fields = ("paths",) + OBJECT_CONTEXT_FIELDS
        if kind == "historical_third_party_artifact":
            binding_fields += ("manifest_disposition", "manifest_sha256")
        for selection in matching_selections:
            for field in binding_fields:
                if selection.get(field) != blocker.get(field):
                    errors.append(
                        f"operator remediation selection for blocker {index} ({kind}) "
                        f"has mismatched {field} context"
                    )
            if kind == "private_or_working_ref" and selection.get("ref") != blocker.get("path"):
                errors.append(
                    f"operator remediation selection for blocker {index} ({kind}) "
                    "has mismatched ref context"
                )
    return errors


def license_selection_errors(report: dict[str, object]) -> list[str]:
    """Require custom-license blockers to be in the reversible action packet."""
    blockers = report.get("release_blockers")
    decision = report.get("release_decision")
    if not isinstance(blockers, list) or not isinstance(decision, dict):
        return []
    remediation = decision.get("operator_remediation")
    if not isinstance(remediation, dict):
        return []
    selections = remediation.get("object_path_selection")
    if not isinstance(selections, list):
        return []
    selected_pairs = {
        (selection.get("object_id"), selection.get("selection_reason"))
        for selection in selections
        if isinstance(selection, dict)
    }
    return [
        "historical custom-license blocker is missing from operator remediation selection"
        for blocker in blockers
        if isinstance(blocker, dict)
        and blocker.get("kind") == "historical_license_marker"
        and (blocker.get("object_id"), "historical_license_marker")
        not in selected_pairs
    ]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="validate evidence without treating known hazards as a test error (default when no mode is given)",
    )
    parser.add_argument("--release-gate", action="store_true", help="fail when the public clone is not safe")
    parser.add_argument("--report", type=Path, default=audit.REPORT_PATH)
    args = parser.parse_args(argv)
    if not args.check and not args.release_gate:
        # Bare invocation (no flags) is what every other scripts/test_*.py accepts and
        # what a plain `python3 scripts/test_reachable_release_history.py` run should do.
        # Default to the same non-gating validation CI runs on every push; the stricter
        # --release-gate stays an explicit opt-in and is unaffected by this default.
        args.check = True
    try:
        report = json.loads(args.report.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        # Naming the exception class told a reader nothing about which file was
        # missing or how to produce it, and this check compares against a
        # committed audit the operator owns rather than one it may generate.
        try:
            location = args.report.relative_to(ROOT)
        except ValueError:
            location = args.report
        print(
            f"test_reachable_release_history: cannot read {location} "
            f"({type(exc).__name__}: {exc})",
            file=sys.stderr,
        )
        print(
            "This check compares the committed reachable-history audit against a "
            "fresh scan, so it cannot run without that committed report. The "
            "report carries a release decision over the repository's whole "
            "object history and is an operator artifact, not a projection to "
            "regenerate casually. To produce one:\n"
            "  python3 scripts/audit_reachable_release_history.py --write-report\n"
            "then read its release_decision before committing it.",
            file=sys.stderr,
        )
        return 2
    errors = adversarial_context_errors()
    if errors:
        for error in errors:
            print(f"test_reachable_release_history: ERROR: {error}", file=sys.stderr)
        return 2
    current = audit.build_audit(ROOT)
    errors = audit.comparison_errors(report, current, ROOT)
    errors.extend(ref_snapshot_errors(report))
    errors.extend(blocker_context_errors(report))
    if errors:
        for error in errors:
            print(f"test_reachable_release_history: ERROR: {error}", file=sys.stderr)
        return 2
    decision = report["release_decision"]
    remediation_errors_found = remediation_errors(decision)
    remediation_errors_found.extend(remediation_selection_errors(report))
    remediation_errors_found.extend(license_selection_errors(report))
    if remediation_errors_found:
        for error in remediation_errors_found:
            print(f"test_reachable_release_history: ERROR: {error}", file=sys.stderr)
        return 2
    blockers = len(report.get("release_blockers", []))
    print(
        "test_reachable_release_history: evidence bound to current reachable history; "
        f"{blockers} blocker(s); decision={decision['status']}"
    )
    if args.release_gate and decision.get("safe_for_public_clone") is not True:
        print("test_reachable_release_history: RELEASE BLOCKED: reachable history is not safe", file=sys.stderr)
        return 3
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

