#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Verify the committed accepted-receipt recognition views.

This is a read-only consumer of the recognition builder.  It loads accepted
receipts from the committed checkout, validates the machine-readable view,
and compares both generated artifacts byte-for-byte with their deterministic
receipt-derived projections.  It does not count activity or infer scientific
importance.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
from typing import Any

import build_research_contribution_recognition as recognition
import build_research_contributions as contributions
import repository_identity as repository_identity_contract


ROOT = Path(__file__).resolve().parents[1]
JSON_OUTPUT = ROOT / "docs" / "research-commons" / "contribution-recognition.json"
MARKDOWN_OUTPUT = ROOT / "docs" / "research-commons" / "CONTRIBUTION_RECOGNITION.md"

# Aggregate entries repeat source references so that every accepted-only facet
# remains auditable without joining back to the chronological rail.  Keep the
# consumer check explicit about that contract: projection equality is still
# authoritative, but a missing context field should identify the broken
# provenance boundary rather than only report generic aggregate drift.
AGGREGATE_SOURCE_CONTEXT_FIELDS = (
    "accepted_at",
    "identity",
    "receipt_path",
    "receipt_sha256",
    "accepted_commit",
    "accepted_commit_url",
    "accepted_receipt_url",
    "artifact_credit_paths",
    "artifact_credit_urls",
    "evidence_artifact_paths",
    "evidence_artifact_urls",
    "problem",
    "result_class",
    "result_summary",
    "claim_ceiling",
    "requested_disposition",
    "evidence_states",
    "evidence_records",
    "reproduction_state",
    "review_states",
    "review_authorities",
    "review_decisions",
    "correction_lineage_state",
    "limitations",
    "surviving_boundary",
    "problem_owned_proposition_state",
    "core_promotion_state",
    "tagged_release_inclusion_state",
)


def _canonical_json(value: dict[str, Any]) -> bytes:
    return (
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    ).encode("utf-8")


def _has_symlink_component(path: Path) -> bool:
    """Reject output paths that would read through a substituted directory."""
    current = Path(os.path.abspath(path))
    while True:
        if current.is_symlink():
            try:
                platform_aliases = {
                    Path("/tmp"): Path("/private/tmp"),
                    Path("/var"): Path("/private/var"),
                }
                alias_target = platform_aliases.get(current)
                if alias_target is None or current.resolve(strict=True) != alias_target:
                    return True
            except OSError:
                return True
            current = current.resolve(strict=True)
        if current.parent == current:
            return False
        current = current.parent


def _read_regular(path: Path, label: str) -> tuple[bytes | None, list[str]]:
    if _has_symlink_component(path):
        return None, [f"{label}: generated output path must not traverse symbolic links"]
    if not path.is_file():
        return None, [f"{label}: generated output is missing or not a regular file"]
    try:
        return path.read_bytes(), []
    except OSError as exc:
        return None, [f"{label}: generated output cannot be read: {exc}"]


def _aggregate_source_context_errors(
    actual: dict[str, Any], expected: dict[str, Any]
) -> list[str]:
    """Name source-bound context omitted or changed inside aggregate facets."""
    expected_by_id = {
        row["return_id"]: row["source"] for row in expected["chronological"]
    }
    aggregates = actual.get("aggregates")
    if not isinstance(aggregates, dict):
        return []
    errors: list[str] = []
    for facet, entries in aggregates.items():
        if not isinstance(entries, list):
            continue
        for entry in entries:
            if not isinstance(entry, dict):
                continue
            accepted_receipts = entry.get("accepted_receipts")
            if not isinstance(accepted_receipts, list):
                continue
            for reference in accepted_receipts:
                if not isinstance(reference, dict):
                    continue
                return_id = reference.get("return_id")
                expected_reference = expected_by_id.get(return_id)
                if not isinstance(expected_reference, dict):
                    continue
                mismatched = [
                    field
                    for field in AGGREGATE_SOURCE_CONTEXT_FIELDS
                    if reference.get(field) != expected_reference.get(field)
                ]
                if mismatched:
                    errors.append(
                        "machine projection: aggregate "
                        f"{facet} receipt {return_id} is not source-bound for "
                        f"{', '.join(mismatched)}"
                    )
    return errors


def _receipt_membership_errors(
    actual: dict[str, Any], expected: dict[str, Any]
) -> list[str]:
    """Report accepted-receipt set drift before generic projection drift."""
    actual_rows = actual.get("chronological")
    expected_rows = expected.get("chronological")
    if not isinstance(actual_rows, list) or not isinstance(expected_rows, list):
        return []
    actual_ids = [
        row.get("return_id")
        for row in actual_rows
        if isinstance(row, dict) and isinstance(row.get("return_id"), str)
    ]
    expected_ids = [
        row["return_id"]
        for row in expected_rows
        if isinstance(row, dict) and isinstance(row.get("return_id"), str)
    ]
    errors: list[str] = []
    missing = sorted(set(expected_ids) - set(actual_ids))
    unexpected = sorted(set(actual_ids) - set(expected_ids))
    if missing or unexpected:
        errors.append(
            "machine projection: accepted-receipt membership drifted "
            f"(missing={missing or 'none'}; unexpected={unexpected or 'none'})"
        )
    duplicates = sorted(
        return_id for return_id in set(actual_ids) if actual_ids.count(return_id) > 1
    )
    if duplicates:
        errors.append(
            "machine projection: accepted-receipt membership contains duplicate ids: "
            + ", ".join(duplicates)
        )
    return errors


def validate_outputs(
    *,
    json_output: Path = JSON_OUTPUT,
    markdown_output: Path = MARKDOWN_OUTPUT,
) -> list[str]:
    """Return concrete failures for the committed-source projection pair."""
    errors: list[str] = []
    try:
        identity_contract = repository_identity_contract.load_identity()
        expected = recognition.build_recognition(
            contributions.load_receipts(
                require_committed=True,
                repository_identity=identity_contract,
            )
        )
    except (
        KeyError,
        OSError,
        TypeError,
        ValueError,
        repository_identity_contract.IdentityError,
    ) as exc:
        return [f"committed accepted-receipt source is invalid: {exc}"]

    json_payload, json_errors = _read_regular(json_output, "machine projection")
    errors.extend(json_errors)
    actual: dict[str, Any] | None = None
    if json_payload is not None:
        try:
            parsed = json.loads(json_payload)
        except json.JSONDecodeError as exc:
            errors.append(f"machine projection: invalid JSON: {exc}")
        else:
            if not isinstance(parsed, dict):
                errors.append("machine projection: top-level value must be an object")
            else:
                actual = parsed
                errors.extend(_receipt_membership_errors(actual, expected))
                try:
                    recognition.validate_projection(actual)
                except (AttributeError, KeyError, OSError, TypeError, ValueError) as exc:
                    errors.append(f"machine projection: semantic validation failed: {exc}")
                errors.extend(_aggregate_source_context_errors(actual, expected))
                if actual != expected:
                    errors.append(
                        "machine projection: content differs from committed accepted-receipt derivation"
                    )
                if json_payload != _canonical_json(expected):
                    errors.append(
                        "machine projection: bytes are not the canonical deterministic projection"
                    )

    markdown_payload, markdown_errors = _read_regular(markdown_output, "human projection")
    errors.extend(markdown_errors)
    if markdown_payload is not None:
        expected_markdown = recognition.human_projection(expected)
        if markdown_payload != expected_markdown:
            errors.append(
                "human projection: content differs from committed accepted-receipt derivation"
            )

    if actual is not None and actual.get("accepted_receipt_count") != len(
        expected["chronological"]
    ):
        errors.append("machine projection: accepted-receipt denominator drifted")
    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", dest="json_output", type=Path, default=JSON_OUTPUT)
    parser.add_argument(
        "--markdown", dest="markdown_output", type=Path, default=MARKDOWN_OUTPUT
    )
    args = parser.parse_args(argv)
    errors = validate_outputs(
        json_output=args.json_output,
        markdown_output=args.markdown_output,
    )
    if errors:
        print(f"check_research_contribution_recognition: {len(errors)} failure(s)")
        for error in errors:
            print(f"  FAIL {error}")
        return 1
    print(
        "check_research_contribution_recognition: committed accepted-receipt "
        "machine and human views verified"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
