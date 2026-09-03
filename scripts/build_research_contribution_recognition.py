#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Generate accepted-only contribution recognition and impact views.

The existing contribution ledger preserves complete accepted receipts.  This
projection adds deterministic, receipt-linked facets for answering who
contributed what, and what review or release state that artifact has.  It is
deliberately not a scientific leaderboard: every count is a factual count of
accepted receipts with an explicit denominator, and aggregate entries are
sorted by stable key rather than by count.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any
from urllib.parse import quote

import build_research_contributions as contributions
import repository_identity as repository_identity_contract
import validation_singleflight as singleflight


ROOT = Path(__file__).resolve().parents[1]
JSON_OUTPUT = ROOT / "docs/research-commons/contribution-recognition.json"
MARKDOWN_OUTPUT = ROOT / "docs/research-commons/CONTRIBUTION_RECOGNITION.md"
SCHEMA = "accepted-research-contribution-recognition/1"
SCHEMA_PATH = "docs/research-commons/schema/research-contribution-recognition.schema.json"
COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")
GIT_LOOKUP_TIMEOUT_SECONDS = singleflight.GIT_COMMAND_TIMEOUT_SECONDS
FORBIDDEN_KEYS = frozenset(
    {
        "rank",
        "ranking",
        "score",
        "points",
        "commit_count",
        "diff_size",
        "token_spend",
        "compute_spend",
        "model_quality",
        "popularity",
    }
)

FACET_NAMES = (
    "by_contributor",
    "by_artifact_credit",
    "by_material_collaborator",
    "by_model_system",
    "by_provider",
    "by_operator_relationship",
    "by_track",
    "by_problem",
    "by_architecture_area",
    "by_result_class",
    "by_requested_disposition",
    "by_evidence_state",
    "by_reproduction_state",
    "by_review_state",
    "by_correction_lineage",
    "by_problem_owned_proposition_state",
    "by_core_promotion_state",
    "by_tagged_release_inclusion_state",
)
REVIEW_FIELDS = (
    "structural_validation",
    "reproduction",
    "mathematical_review",
    "claim_boundary_review",
    "accepted_handoff",
    "problem_owned_proposition",
    "core_promotion",
    "tagged_release_inclusion",
)
PROJECTION_FIELDS = frozenset(
    {
        "schema",
        "schema_path",
        "artifact_role",
        "generated_by",
        "source_projection",
        "source_directory",
        "source_policy",
        "authority_boundary",
        "ordering_policy",
        "comparison_policy",
        "accepted_receipt_count",
        "denominator",
        "chronological",
        "aggregates",
    }
)
RECOGNITION_ROW_FIELDS = frozenset(
    {
        "return_id",
        "accepted_at",
        "receipt_path",
        "receipt_sha256",
        "record_kind",
        "identity",
        "repository",
        "frontier",
        "public_frontier",
        "result",
        "evidence",
        "review",
        "attribution",
        "correction_lineage",
        "source",
        "impact_state",
    }
)
AGGREGATE_ENTRY_FIELDS = frozenset(
    {
        "key",
        "label",
        "detail",
        "accepted_receipt_count",
        "denominator",
        "accepted_receipts",
    }
)


def canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":"))


def checkout_path(relative: str, label: str) -> Path:
    """Resolve a repository-relative input without following checkout links."""
    candidate = Path(relative)
    if candidate.is_absolute() or ".." in candidate.parts:
        raise ValueError(f"{label} must stay repository-relative: {relative}")
    path = ROOT / candidate
    current = ROOT
    for component in candidate.parts:
        current /= component
        if current.is_symlink():
            raise ValueError(f"{label} uses a symbolic link: {relative}")
    return path


def load_schema_contract() -> dict[str, Any]:
    path = checkout_path(SCHEMA_PATH, "recognition schema contract")
    try:
        value = json.loads(contributions.safe_receipt_bytes(path))
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        raise ValueError(f"recognition schema contract cannot be loaded: {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise ValueError("recognition schema contract must be a JSON object")
    return value


def validate_schema_contract(schema: dict[str, Any]) -> None:
    if schema.get("$schema") != "https://json-schema.org/draft/2020-12/schema":
        raise ValueError("recognition schema contract is not draft 2020-12")
    properties = schema.get("properties")
    if not isinstance(properties, dict):
        raise ValueError("recognition schema contract properties are missing")
    if properties.get("schema", {}).get("const") != SCHEMA:
        raise ValueError("recognition schema contract schema const is stale")
    if properties.get("schema_path", {}).get("const") != SCHEMA_PATH:
        raise ValueError("recognition schema contract path const is stale")
    expected_required = {
        "schema",
        "schema_path",
        "artifact_role",
        "generated_by",
        "source_projection",
        "source_directory",
        "source_policy",
        "authority_boundary",
        "ordering_policy",
        "comparison_policy",
        "accepted_receipt_count",
        "denominator",
        "chronological",
        "aggregates",
    }
    if set(schema.get("required", [])) != expected_required:
        raise ValueError("recognition schema contract required fields drifted")
    aggregate_properties = properties.get("aggregates", {}).get("properties", {})
    if set(aggregate_properties) != set(FACET_NAMES):
        raise ValueError("recognition schema contract aggregate facets drifted")
    if properties.get("aggregates", {}).get("additionalProperties") is not False:
        raise ValueError("recognition schema contract permits unknown aggregate facets")
    if aggregate_properties.get("by_review_state") != {
        "type": "array",
        "items": {"$ref": "#/$defs/reviewStateAggregateEntry"},
    }:
        raise ValueError("recognition schema contract review aggregate detail is untyped")


def _path_label(path: str) -> str:
    return "/".join(quote(part, safe="-._~") for part in Path(path).parts)


def _accepted_blob_url(origin: str, accepted_commit: str, path: str) -> str:
    return f"{origin.rstrip('/')}/blob/{accepted_commit}/{_path_label(path)}"


def _receipt_source_commit(row: dict[str, Any]) -> str:
    """Find the first-parent commit containing this exact accepted receipt blob.

    ``repository.accepted_commit`` identifies the accepted artifact generation;
    it need not be the later commit that records the receipt itself.  Resolve
    the receipt URL from its content hash so the two provenance claims remain
    distinct and independently verifiable.
    """
    receipt_path = row["receipt_path"]
    _validate_relative_repository_path(receipt_path, f"{row['return_id']}: receipt path")
    receipt_sha256 = row["receipt_sha256"]
    if not isinstance(receipt_sha256, str) or not receipt_sha256.startswith("sha256:"):
        raise ValueError(f"{row['return_id']}: receipt hash is malformed")
    try:
        history = subprocess.run(
            ["git", "log", "--format=%H", "--first-parent", "--", receipt_path],
            cwd=ROOT,
            env=contributions.git_environment(),
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            check=False,
            text=True,
            timeout=GIT_LOOKUP_TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired as exc:
        raise ValueError(
            f"{row['return_id']}: receipt source history lookup timed out after "
            f"{GIT_LOOKUP_TIMEOUT_SECONDS} seconds"
        ) from exc
    except OSError as exc:
        raise ValueError(
            f"{row['return_id']}: receipt source history lookup could not be launched: "
            f"{exc}"
        ) from exc
    if history.returncode != 0:
        raise ValueError(f"{row['return_id']}: receipt source history cannot be inspected")
    for candidate in history.stdout.splitlines():
        if not COMMIT_RE.fullmatch(candidate):
            continue
        try:
            payload = subprocess.run(
                ["git", "show", f"{candidate}:{receipt_path}"],
                cwd=ROOT,
                env=contributions.git_environment(),
                stdout=subprocess.PIPE,
                stderr=subprocess.DEVNULL,
                check=False,
                timeout=GIT_LOOKUP_TIMEOUT_SECONDS,
            )
        except subprocess.TimeoutExpired as exc:
            raise ValueError(
                f"{row['return_id']}: receipt source payload lookup timed out after "
                f"{GIT_LOOKUP_TIMEOUT_SECONDS} seconds"
            ) from exc
        except OSError as exc:
            raise ValueError(
                f"{row['return_id']}: receipt source payload lookup could not be launched: "
                f"{exc}"
            ) from exc
        if payload.returncode == 0 and contributions.sha256(payload.stdout) == receipt_sha256:
            return candidate
    raise ValueError(
        f"{row['return_id']}: receipt bytes are not present in first-parent history"
    )


def _receipt_reference(row: dict[str, Any]) -> dict[str, Any]:
    repository = row["repository"]
    accepted_commit = repository["accepted_commit"]
    origin = repository["origin"].rstrip("/")
    if not isinstance(accepted_commit, str) or not COMMIT_RE.fullmatch(accepted_commit):
        raise ValueError(f"{row['return_id']}: accepted commit is not a full hexadecimal commit")
    artifact_paths = [
        path
        for credit in row["attribution"]["artifact_credit"]
        for path in credit["artifact_paths"]
    ]
    for path in artifact_paths:
        _validate_relative_repository_path(
            path, f"{row['return_id']}: artifact-credit path"
        )
    receipt_path = row["receipt_path"]
    _validate_relative_repository_path(receipt_path, f"{row['return_id']}: receipt path")
    receipt_source_commit = _receipt_source_commit(row)
    evidence_artifacts = sorted(
        {
            path
            for evidence in row["evidence"]
            for path in evidence["artifacts"]
        }
    )
    for path in evidence_artifacts:
        _validate_relative_repository_path(
            path, f"{row['return_id']}: evidence artifact path"
        )
    def artifact_url(path: str) -> str:
        return _accepted_blob_url(origin, accepted_commit, path)

    track = contributions.contribution_track(row["frontier"])
    return {
        "return_id": row["return_id"],
        "accepted_at": row["accepted_at"],
        "identity": _identity_reference(row),
        "receipt_path": receipt_path,
        "receipt_sha256": row["receipt_sha256"],
        "accepted_commit": accepted_commit,
        "accepted_commit_url": f"{origin}/commit/{accepted_commit}",
        "accepted_receipt_url": _accepted_blob_url(
            origin, receipt_source_commit, receipt_path
        ),
        "artifact_credit_paths": sorted(set(artifact_paths)),
        "artifact_credit_urls": [artifact_url(path) for path in sorted(set(artifact_paths))],
        "evidence_artifact_paths": evidence_artifacts,
        "evidence_artifact_urls": [artifact_url(path) for path in evidence_artifacts],
        "track": track,
        "scope_label": contributions.contribution_scope_label(row["frontier"]),
        "problem": row["frontier"].get("problem"),
        "architecture_area": row["frontier"].get("area") if track == "architecture" else None,
        "result_class": row["result"]["class"],
        "result_summary": row["result"]["summary"],
        "claim_ceiling": row["result"]["claim_ceiling"],
        "requested_disposition": row["result"]["requested_disposition"],
        "evidence_states": [
            {
                "exit_state": evidence["exit_state"],
                "replay_state": evidence["replay_state"],
            }
            for evidence in row["evidence"]
        ],
        "evidence_records": _evidence_records(row),
        "reproduction_state": row["review"]["reproduction"]["state"],
        "review_states": {
            field: row["review"][field]["state"] for field in REVIEW_FIELDS
        },
        "review_decisions": _review_decisions(row),
        "correction_lineage_state": (
            row["correction_lineage"]["disposition"]
            if row.get("correction_lineage") is not None
            else "none"
        ),
        "limitations": list(row["result"]["limitations"]),
        "surviving_boundary": row["result"]["surviving_boundary"],
        "problem_owned_proposition_state": row["review"]["problem_owned_proposition"]["state"],
        "core_promotion_state": row["review"]["core_promotion"]["state"],
        "tagged_release_inclusion_state": row["review"]["tagged_release_inclusion"]["state"],
        "review_authorities": _review_authorities(row),
    }


def _identity_reference(row: dict[str, Any]) -> dict[str, Any]:
    """Preserve human, operator, collaborator, model, and provider roles."""
    identity = row["identity"]
    contributor = identity["contributor"]
    operator = identity["operator"]
    return {
        "contributor": {
            "name": contributor["name"],
            "handle": contributor.get("handle"),
            "identifiers": list(contributor.get("identifiers", [])),
        },
        "operator": {
            "relationship": operator["relationship"],
            "name": operator.get("name"),
        },
        "material_collaborators": [
            {"name": value["name"], "role": value["role"]}
            for value in identity.get("material_collaborators", [])
        ],
        "model_system": _disclosure_snapshot(identity.get("model_system")),
        "provider": _disclosure_snapshot(identity.get("provider")),
    }


def _review_authority_url(row: dict[str, Any], authority_ref: Any) -> str | None:
    """Link only authority references whose target type is explicit and safe."""
    if not isinstance(authority_ref, str) or not authority_ref:
        return None
    repository = row["repository"]
    origin = repository["origin"].rstrip("/")
    if authority_ref.startswith("git:"):
        commit = authority_ref.removeprefix("git:")
        if not COMMIT_RE.fullmatch(commit):
            return None
        return f"{origin}/commit/{commit}"
    if authority_ref.startswith(("https://", "http://")):
        return authority_ref
    if not authority_ref.startswith(
        ("scripts/", "docs/", "ErdosProblems/", "examples/", "formal_math/")
    ):
        return None
    try:
        _validate_relative_repository_path(authority_ref, "review authority reference")
    except ValueError:
        return None
    return (
        f"{origin}/blob/{repository['accepted_commit']}/{_path_label(authority_ref)}"
    )


def _review_authorities(row: dict[str, Any]) -> dict[str, dict[str, Any]]:
    review = row["review"]
    return {
        field: {
            "authority_ref": review[field].get("authority_ref"),
            "authority_url": _review_authority_url(
                row, review[field].get("authority_ref")
            ),
        }
        for field in REVIEW_FIELDS
    }


def _review_decisions(row: dict[str, Any]) -> dict[str, dict[str, Any]]:
    """Preserve each accepted review decision without reducing it to a state."""
    review = row["review"]
    authorities = _review_authorities(row)
    return {
        field: {
            "state": review[field]["state"],
            "authority_ref": review[field].get("authority_ref"),
            "authority_url": authorities[field]["authority_url"],
            "decided_at": review[field].get("decided_at"),
            "reviewer": review[field].get("reviewer"),
            "notes": review[field].get("notes"),
        }
        for field in REVIEW_FIELDS
    }


def _impact_state(row: dict[str, Any]) -> dict[str, Any]:
    review = row["review"]
    correction_lineage = row.get("correction_lineage")
    track = contributions.contribution_track(row["frontier"])
    return {
        "track": track,
        "scope_label": contributions.contribution_scope_label(row["frontier"]),
        "problem": row["frontier"].get("problem"),
        "architecture_area": row["frontier"].get("area") if track == "architecture" else None,
        "result_class": row["result"]["class"],
        "claim_ceiling": row["result"]["claim_ceiling"],
        "requested_disposition": row["result"]["requested_disposition"],
        "evidence_states": [
            {
                "exit_state": evidence["exit_state"],
                "replay_state": evidence["replay_state"],
            }
            for evidence in row["evidence"]
        ],
        "reproduction_state": review["reproduction"]["state"],
        "review_states": {
            field: review[field]["state"] for field in REVIEW_FIELDS
        },
        "correction_lineage_state": (
            correction_lineage["disposition"]
            if correction_lineage is not None
            else "none"
        ),
        "limitations": list(row["result"]["limitations"]),
        "surviving_boundary": row["result"]["surviving_boundary"],
        "problem_owned_proposition_state": review["problem_owned_proposition"]["state"],
        "core_promotion_state": review["core_promotion"]["state"],
        "tagged_release_inclusion_state": review["tagged_release_inclusion"]["state"],
        "review_authorities": _review_authorities(row),
        "review_decisions": _review_decisions(row),
    }


def _recognition_row(
    name: str,
    receipt: dict[str, Any],
    payload: bytes,
) -> dict[str, Any]:
    if receipt.get("record_kind") != "accepted_receipt":
        raise ValueError(f"{name}: recognition projection accepts accepted_receipt only")
    frontier = receipt.get("frontier")
    if not isinstance(frontier, dict):
        raise ValueError(f"{name}: accepted frontier must be an object")
    try:
        contributions.contribution_track(frontier)
    except ValueError as exc:
        raise ValueError(f"{name}: accepted frontier is invalid: {exc}") from exc
    result = receipt.get("result")
    if not isinstance(result, dict):
        raise ValueError(f"{name}: accepted result must be an object")
    for field in ("class", "claim_ceiling", "requested_disposition"):
        if not isinstance(result.get(field), str):
            raise ValueError(f"{name}: accepted result.{field} must be a string")
    row = contributions.project_receipt(name, receipt, payload)
    row["record_kind"] = "accepted_receipt"
    row["public_frontier"] = contributions.public_contribution_route(row["frontier"])
    row["source"] = _receipt_reference(row)
    if row.get("correction_lineage") is not None:
        _correction_lineage_detail(row)
    row["impact_state"] = _impact_state(row)
    return row


def _disclosure_snapshot(value: Any) -> dict[str, Any]:
    """Keep disclosed system metadata separate from human credit identity."""
    if not isinstance(value, dict):
        return {"state": "not_recorded"}
    state = value.get("state", "not_recorded")
    if state != "disclosed":
        return {"state": state}
    return {
        "state": state,
        "name": value["name"],
        "version": value.get("version"),
        "resources": list(value.get("resources", [])),
    }


def _correction_lineage_detail(
    row: dict[str, Any],
    references: dict[str, dict[str, Any]] | None = None,
) -> dict[str, Any] | None:
    lineage = row.get("correction_lineage")
    if lineage is None:
        return None
    starting_commit = lineage["starting_commit"]
    origin = row["repository"]["origin"].rstrip("/")
    affected_paths = sorted(set(lineage["affected_paths"]))
    for path in affected_paths:
        _validate_relative_repository_path(
            path, f"{row['return_id']}: correction affected path"
        )
    prior_reference = (references or {}).get(lineage["prior_return_reference"])
    return {
        "state": "present",
        "disposition": lineage["disposition"],
        "prior_return_reference": lineage["prior_return_reference"],
        "prior_receipt_url": (
            prior_reference.get("accepted_receipt_url")
            if prior_reference is not None
            else None
        ),
        "starting_commit": starting_commit,
        "starting_commit_url": (
            f"{origin}/commit/{starting_commit}"
            if COMMIT_RE.fullmatch(starting_commit)
            else None
        ),
        "affected_paths": affected_paths,
        "affected_path_urls": [
            f"{origin}/blob/{row['repository']['accepted_commit']}/{_path_label(path)}"
            for path in affected_paths
        ],
        "changed_evidence_or_wording": lineage["changed_evidence_or_wording"],
        "reason": lineage["reason"],
    }


def _evidence_records(row: dict[str, Any]) -> list[dict[str, Any]]:
    """Retain each accepted receipt's complete evidence observation and links."""
    origin = row["repository"]["origin"].rstrip("/")
    accepted_commit = row["repository"]["accepted_commit"]
    return [
        {
            "command": evidence["command"],
            "observed": evidence["observed"],
            "environment": evidence["environment"],
            "exit_state": evidence["exit_state"],
            "exit_code": evidence["exit_code"],
            "replay_state": evidence["replay_state"],
            "artifacts": list(evidence["artifacts"]),
            "artifact_urls": [
                f"{origin}/blob/{accepted_commit}/{_path_label(path)}"
                for path in evidence["artifacts"]
            ],
        }
        for evidence in row["evidence"]
    ]


def _artifact_credit_records(
    row: dict[str, Any],
    path: str,
    references: dict[str, dict[str, Any]] | None = None,
) -> list[dict[str, Any]]:
    """Bind each artifact-credit name to its receipt, identity, and impact context."""
    identity = row["identity"]
    contributor = identity["contributor"]
    origin = row["repository"]["origin"].rstrip("/")
    accepted_commit = row["repository"]["accepted_commit"]
    artifact_url = f"{origin}/blob/{accepted_commit}/{_path_label(path)}"
    records = []
    for credit in row["attribution"]["artifact_credit"]:
        if path not in credit["artifact_paths"]:
            continue
        records.append(
            {
                "return_id": row["return_id"],
                "accepted_at": row["accepted_at"],
                "receipt_path": row["receipt_path"],
                "receipt_sha256": row["receipt_sha256"],
                "credit_name": credit["name"],
                "contribution_roles": list(credit.get("contribution_roles", [])),
                "contributor": {
                    "name": contributor["name"],
                    "handle": contributor.get("handle"),
                    "identifiers": list(contributor.get("identifiers", [])),
                },
                "operator": {
                    "relationship": identity["operator"]["relationship"],
                    "name": identity["operator"].get("name"),
                },
                "material_collaborators": [
                    {"name": value["name"], "role": value["role"]}
                    for value in identity.get("material_collaborators", [])
                ],
                "model_system": _disclosure_snapshot(identity.get("model_system")),
                "provider": _disclosure_snapshot(identity.get("provider")),
                "result_summary": row["result"]["summary"],
                "impact_state": _impact_state(row),
                "correction_lineage": _correction_lineage_detail(row, references),
                "evidence_records": _evidence_records(row),
                "evidence_artifact_paths": list(row["source"]["evidence_artifact_paths"]),
                "evidence_artifact_urls": list(row["source"]["evidence_artifact_urls"]),
                "accepted_commit": accepted_commit,
                "accepted_commit_url": row["source"]["accepted_commit_url"],
                "accepted_receipt_url": row["source"]["accepted_receipt_url"],
                "artifact_url": artifact_url,
            }
        )
    return sorted(records, key=canonical)


def _entity_descriptor(
    facet: str,
    row: dict[str, Any],
    references: dict[str, dict[str, Any]] | None = None,
) -> list[tuple[str, str, dict[str, Any]]]:
    identity = row["identity"]
    if facet == "by_contributor":
        value = identity["contributor"]
        detail = {
            "name": value["name"],
            "handle": value.get("handle"),
            "identifiers": list(value.get("identifiers", [])),
        }
        label = value["name"]
        if value.get("handle"):
            label += f" (@{value['handle']})"
        elif value.get("identifiers"):
            label += f" — {value['identifiers'][0]}"
        return [(canonical(detail), label, detail)]
    if facet == "by_artifact_credit":
        paths = sorted(
            {
                path
                for credit in row["attribution"]["artifact_credit"]
                for path in credit["artifact_paths"]
            }
        )
        return [
            (
                path,
                path,
                {
                    "artifact_path": path,
                    "credit_records": _artifact_credit_records(row, path, references),
                },
            )
            for path in paths
        ]
    if facet == "by_material_collaborator":
        values = identity.get("material_collaborators", [])
        if not values:
            return [("none_recorded", "none recorded", {"state": "none_recorded"})]
        return [
            (
                canonical({"name": value["name"], "role": value["role"]}),
                f"{value['name']} ({value['role']})",
                {"name": value["name"], "role": value["role"]},
            )
            for value in values
        ]
    if facet in {"by_model_system", "by_provider"}:
        field = "model_system" if facet == "by_model_system" else "provider"
        value = identity.get(field)
        state = value.get("state", "not_recorded") if isinstance(value, dict) else "not_recorded"
        if state == "disclosed":
            detail = {
                "state": state,
                "name": value["name"],
                "version": value.get("version"),
                "resources": list(value.get("resources", [])),
            }
            label = value["name"]
            if value.get("version"):
                label += f" {value['version']}"
        else:
            detail = {"state": state}
            label = state
        return [(canonical(detail), label, detail)]
    if facet == "by_operator_relationship":
        value = identity["operator"]
        relationship = value["relationship"]
        detail = {
            "relationship": relationship,
            "operator_name": value.get("name"),
        }
        label = relationship
        if value.get("name"):
            label += f" — {value['name']}"
        return [(canonical(detail), label, detail)]
    if facet == "by_track":
        track = contributions.contribution_track(row["frontier"])
        return [(track, track, {"track": track})]
    if facet == "by_problem":
        if contributions.contribution_track(row["frontier"]) != "mathematics":
            return []
        problem = str(row["frontier"]["problem"])
        return [(problem, f"Erdős #{problem}", {"problem": row["frontier"]["problem"]})]
    if facet == "by_architecture_area":
        if contributions.contribution_track(row["frontier"]) != "architecture":
            return []
        area = row["frontier"]["area"]
        return [(area, area, {"architecture_area": area})]
    if facet == "by_result_class":
        value = row["result"]["class"]
        return [(value, value, {"result_class": value})]
    if facet == "by_requested_disposition":
        value = row["result"]["requested_disposition"]
        return [(value, value, {"requested_disposition": value})]
    if facet == "by_reproduction_state":
        value = row["review"]["reproduction"]["state"]
        return [(value, value, {"reproduction_state": value})]
    if facet == "by_evidence_state":
        return [
            (
                canonical(
                    {
                        "exit_state": evidence["exit_state"],
                        "replay_state": evidence["replay_state"],
                    }
                ),
                f"{evidence['exit_state']}/{evidence['replay_state']}",
                {
                    "exit_state": evidence["exit_state"],
                    "replay_state": evidence["replay_state"],
                },
            )
            for evidence in row["evidence"]
        ]
    if facet == "by_review_state":
        return [
            (
                canonical({"review_field": field, "state": row["review"][field]["state"]}),
                f"{field}={row['review'][field]['state']}",
                {"review_field": field, "state": row["review"][field]["state"]},
            )
            for field in REVIEW_FIELDS
        ]
    review_field_by_facet = {
        "by_problem_owned_proposition_state": "problem_owned_proposition",
        "by_core_promotion_state": "core_promotion",
        "by_tagged_release_inclusion_state": "tagged_release_inclusion",
    }
    if facet in review_field_by_facet:
        field = review_field_by_facet[facet]
        value = row["review"][field]["state"]
        return [(value, value, {f"{field}_state": value})]
    if facet == "by_correction_lineage":
        detail = _correction_lineage_detail(row, references)
        if detail is None:
            return [("none", "none recorded", {"state": "none"})]
        return [(canonical(detail), detail["disposition"], detail)]
    raise ValueError(f"unsupported recognition facet {facet!r}")


def _aggregate(
    rows: list[dict[str, Any]],
    facet: str,
    references: dict[str, dict[str, Any]],
) -> list[dict[str, Any]]:
    groups: dict[str, dict[str, Any]] = {}
    rows_by_id = {row["return_id"]: row for row in rows}
    for row in rows:
        for key, label, detail in _entity_descriptor(facet, row, references):
            group = groups.setdefault(
                key,
                {"key": key, "label": label, "detail": detail, "return_ids": []},
            )
            if facet == "by_artifact_credit":
                records = {
                    canonical(record): record
                    for record in (
                        group["detail"].get("credit_records", [])
                        + detail.get("credit_records", [])
                    )
                }
                group["detail"] = {
                    **group["detail"],
                    "credit_records": [records[key] for key in sorted(records)],
                }
            if row["return_id"] not in group["return_ids"]:
                group["return_ids"].append(row["return_id"])
    denominator = len(rows)
    result = []
    for key in sorted(groups):
        group = groups[key]
        return_ids = group["return_ids"]
        detail = group["detail"]
        review_field = None
        if facet == "by_review_state":
            review_field = detail["review_field"]
        else:
            review_field = {
                "by_reproduction_state": "reproduction",
                "by_problem_owned_proposition_state": "problem_owned_proposition",
                "by_core_promotion_state": "core_promotion",
                "by_tagged_release_inclusion_state": "tagged_release_inclusion",
            }.get(facet)
        if review_field is not None:
            detail = dict(detail)
            detail["review_authorities"] = [
                {
                    "return_id": return_id,
                    **rows_by_id[return_id]["impact_state"]["review_authorities"][
                        review_field
                    ],
                }
                for return_id in return_ids
            ]
            detail["review_decisions"] = [
                {
                    "return_id": return_id,
                    "decision": rows_by_id[return_id]["impact_state"]["review_decisions"][
                        review_field
                    ],
                }
                for return_id in return_ids
            ]
        result.append(
            {
                "key": group["key"],
                "label": group["label"],
                "detail": detail,
                "accepted_receipt_count": len(return_ids),
                "denominator": {"accepted_receipts": denominator},
                "accepted_receipts": [references[return_id] for return_id in return_ids],
            }
        )
    return result


def _walk_forbidden_keys(value: Any) -> str | None:
    if isinstance(value, dict):
        for key, child in value.items():
            if key.casefold() in FORBIDDEN_KEYS:
                return key
            found = _walk_forbidden_keys(child)
            if found is not None:
                return found
    elif isinstance(value, list):
        for child in value:
            found = _walk_forbidden_keys(child)
            if found is not None:
                return found
    return None


def _validate_relative_repository_path(value: Any, label: str) -> None:
    """Reject paths that could escape or address repository control data."""
    if not isinstance(value, str) or not value:
        raise ValueError(f"{label}: repository path is missing or malformed")
    if "\\" in value or "\x00" in value:
        raise ValueError(f"{label}: unsafe repository path")
    raw_parts = value.split("/")
    if any(part in {"", "."} for part in raw_parts):
        raise ValueError(f"{label}: unsafe repository path")
    candidate = Path(value)
    if (
        candidate.is_absolute()
        or "." in candidate.parts
        or ".." in candidate.parts
        or ".git" in candidate.parts
    ):
        raise ValueError(f"{label}: unsafe repository path")


def validate_projection(projection: dict[str, Any]) -> None:
    """Validate the semantic contract of a generated recognition view."""
    validate_schema_contract(load_schema_contract())
    identity_contract = repository_identity_contract.load_identity()
    allowed_origins = {
        identity_contract["current"]["origin"],
        *(
            historical["origin"]
            for historical in identity_contract["historical_receipt_contracts"]
        ),
    }
    if set(projection) != PROJECTION_FIELDS:
        raise ValueError("recognition projection has unknown or missing top-level fields")
    if projection.get("schema") != SCHEMA:
        raise ValueError("recognition projection schema is not current")
    if projection.get("schema_path") != SCHEMA_PATH:
        raise ValueError("recognition projection schema path is not current")
    forbidden = _walk_forbidden_keys(projection)
    if forbidden is not None:
        raise ValueError(f"recognition projection contains forbidden activity key: {forbidden}")
    rows = projection.get("chronological")
    if not isinstance(rows, list):
        raise ValueError("recognition projection chronological rows are missing")
    count = projection.get("accepted_receipt_count")
    if count != len(rows) or projection.get("denominator") != {"accepted_receipts": len(rows)}:
        raise ValueError("recognition projection denominator does not match accepted rows")
    ids: list[str] = []
    references: dict[str, dict[str, Any]] = {}
    for row in rows:
        if not isinstance(row, dict) or not set(row) <= RECOGNITION_ROW_FIELDS:
            raise ValueError("recognition projection contains unknown row fields")
        return_id = row.get("return_id")
        if row.get("record_kind") != "accepted_receipt" or not isinstance(return_id, str):
            raise ValueError("recognition projection contains a non-accepted or malformed row")
        if return_id in references:
            raise ValueError(f"recognition projection duplicates receipt {return_id}")
        source = row.get("source")
        repository = row.get("repository")
        if not isinstance(source, dict) or not isinstance(repository, dict):
            raise ValueError(f"{return_id}: recognition source reference is missing")
        try:
            expected_public_frontier = contributions.public_contribution_route(row["frontier"])
        except (KeyError, TypeError, ValueError) as exc:
            raise ValueError(f"{return_id}: public frontier route cannot be derived: {exc}") from exc
        if row.get("public_frontier") != expected_public_frontier:
            raise ValueError(f"{return_id}: public frontier route is not source-bound")
        if repository.get("origin") not in allowed_origins:
            raise ValueError(
                f"{return_id}: repository origin is not a canonical standalone origin"
            )
        receipt_path = row.get("receipt_path")
        _validate_relative_repository_path(receipt_path, f"{return_id}: receipt path")
        if Path(receipt_path).parent.as_posix() != "docs/research-commons/returns":
            raise ValueError(f"{return_id}: receipt path is outside the accepted-receipt directory")
        accepted_commit = repository.get("accepted_commit")
        if not isinstance(accepted_commit, str) or not COMMIT_RE.fullmatch(accepted_commit):
            raise ValueError(f"{return_id}: recognition accepted commit is malformed")
        expected_url = f"{repository['origin'].rstrip('/')}/commit/{accepted_commit}"
        if source.get("accepted_commit_url") != expected_url:
            raise ValueError(f"{return_id}: accepted commit URL is not source-bound")
        expected_receipt_url = _accepted_blob_url(
            repository["origin"], _receipt_source_commit(row), receipt_path
        )
        if source.get("accepted_receipt_url") != expected_receipt_url:
            raise ValueError(f"{return_id}: accepted receipt URL is not source-bound")
        if source.get("receipt_path") != row.get("receipt_path"):
            raise ValueError(f"{return_id}: receipt path reference drifted")
        for field, url_field in (
            ("artifact_credit_paths", "artifact_credit_urls"),
            ("evidence_artifact_paths", "evidence_artifact_urls"),
        ):
            paths = source.get(field)
            if not isinstance(paths, list):
                raise ValueError(f"{return_id}: source {field} is malformed")
            for path in paths:
                _validate_relative_repository_path(path, f"{return_id}: {field}")
            urls = source.get(url_field)
            if not isinstance(urls, list):
                raise ValueError(f"{return_id}: source {url_field} is malformed")
            if len(urls) != len(paths) or not all(isinstance(url, str) and url for url in urls):
                raise ValueError(f"{return_id}: source {url_field} is malformed")
            expected_urls = [
                _accepted_blob_url(repository["origin"], accepted_commit, path)
                for path in paths
            ]
            if urls != expected_urls:
                raise ValueError(
                    f"{return_id}: source reference is not bound for {url_field}"
                )
        lineage = row.get("correction_lineage")
        if lineage is not None:
            if not isinstance(lineage, dict) or not isinstance(lineage.get("affected_paths"), list):
                raise ValueError(f"{return_id}: correction lineage paths are malformed")
            for path in lineage["affected_paths"]:
                _validate_relative_repository_path(path, f"{return_id}: correction affected path")
        try:
            expected_source = _receipt_reference(row)
        except (KeyError, TypeError, ValueError) as exc:
            raise ValueError(f"{return_id}: source reference cannot be derived: {exc}") from exc
        if source != expected_source:
            raise ValueError(f"{return_id}: source reference is not bound to the accepted row")
        try:
            expected_impact_state = _impact_state(row)
        except (KeyError, TypeError, ValueError) as exc:
            raise ValueError(f"{return_id}: impact state cannot be derived: {exc}") from exc
        if row.get("impact_state") != expected_impact_state:
            raise ValueError(f"{return_id}: impact state is not bound to the accepted row")
        ids.append(return_id)
        references[return_id] = source
    expected_ids = [
        row["return_id"]
        for row in sorted(rows, key=lambda row: (row["accepted_at"], row["return_id"]))
    ]
    if ids != expected_ids:
        raise ValueError("recognition chronological order is not deterministic")
    aggregates = projection.get("aggregates")
    if not isinstance(aggregates, dict):
        raise ValueError("recognition aggregate views are missing")
    if set(aggregates) != set(FACET_NAMES):
        raise ValueError("recognition aggregate views have unknown or missing facets")
    for facet in FACET_NAMES:
        entries = aggregates.get(facet)
        if not isinstance(entries, list):
            raise ValueError(f"recognition aggregate facet is missing: {facet}")
        previous_key = None
        for entry in entries:
            if not isinstance(entry, dict):
                raise ValueError(f"{facet}: aggregate entry is malformed")
            if set(entry) != AGGREGATE_ENTRY_FIELDS:
                raise ValueError(f"{facet}: aggregate entry has unknown or missing fields")
            key = entry.get("key")
            if not isinstance(key, str) or (previous_key is not None and key <= previous_key):
                raise ValueError(f"{facet}: aggregate keys are not strictly sorted")
            previous_key = key
            return_ids = [reference.get("return_id") for reference in entry.get("accepted_receipts", [])]
            if not return_ids or any(return_id not in references for return_id in return_ids):
                raise ValueError(f"{facet}: aggregate references an unknown receipt")
            if entry.get("accepted_receipt_count") != len(return_ids):
                raise ValueError(f"{facet}: aggregate count does not match receipt references")
            if entry.get("denominator") != {"accepted_receipts": len(rows)}:
                raise ValueError(f"{facet}: aggregate denominator drifted")
        if entries != _aggregate(rows, facet, references):
            raise ValueError(f"{facet}: aggregate projection drifted from accepted rows")
def build_recognition(
    sources: list[tuple[str, dict[str, Any], bytes]],
) -> dict[str, Any]:
    rows = [
        _recognition_row(name, receipt, payload)
        for name, receipt, payload in sources
    ]
    rows.sort(key=lambda row: (row["accepted_at"], row["return_id"]))
    return_ids = [row["return_id"] for row in rows]
    if len(return_ids) != len(set(return_ids)):
        raise ValueError("recognition projection received duplicate accepted receipt ids")
    references = {row["return_id"]: row["source"] for row in rows}
    aggregates = {
        facet: _aggregate(rows, facet, references) for facet in FACET_NAMES
    }
    projection = {
        "schema": SCHEMA,
        "schema_path": SCHEMA_PATH,
        "artifact_role": "generated_accepted_receipt_recognition_and_impact_view",
        "generated_by": "scripts/build_research_contribution_recognition.py",
        "source_projection": "scripts/build_research_contribution_recognition.py",
        "source_directory": "docs/research-commons/returns",
        "source_policy": (
            "strict accepted_receipt records only; detached route-memory sidecars are "
            "separate intake authority and are not consumed by this projection"
        ),
        "authority_boundary": (
            "This is a receipt-derived recognition and release-state view. It does not establish "
            "mathematical novelty, proof authority, scientific quality, ownership, endorsement, "
            "independent review, or release authority. Detached route-memory sidecars are "
            "validated at intake but remain separate route authority and are not recognition credit."
        ),
        "ordering_policy": (
            "Chronological rows use accepted_at then return_id. Aggregate entries use stable "
            "lexicographic keys, never commit count, diff size, token spend, compute spend, or activity."
        ),
        "comparison_policy": (
            "Counts are factual accepted-receipt counts with an explicit accepted-receipt denominator; "
            "they are not rankings or measures of mathematical importance. Undisclosed, not_used, and "
            "not_recorded identity states remain visibly distinct from disclosed identities. Equal counts "
            "remain ties; stable-key ordering is navigation and never a rank."
        ),
        "accepted_receipt_count": len(rows),
        "denominator": {"accepted_receipts": len(rows)},
        "chronological": rows,
        "aggregates": aggregates,
    }
    validate_projection(projection)
    return projection


def _md(value: Any) -> str:
    text = " ".join(str(value).split())
    for character in ("\\", "`", "*", "_", "[", "]", "<", ">"):
        text = text.replace(character, "\\" + character)
    return text


def _code(value: Any) -> str:
    return " ".join(str(value).split()).replace("`", "'")


def _disclosure_text(value: dict[str, Any]) -> str:
    """Render disclosed system metadata without merging it into human credit."""
    state = value.get("state", "not_recorded")
    if state != "disclosed":
        return str(state)
    parts = [str(value.get("name", "disclosed"))]
    if value.get("version"):
        parts.append(str(value["version"]))
    resources = value.get("resources")
    if isinstance(resources, list) and resources:
        parts.append("resources: " + ", ".join(str(item) for item in resources))
    return " — ".join(parts)


def _contributor_identity_text(value: dict[str, Any]) -> str:
    """Render contributor disambiguators without conflating identity roles."""
    parts = [_md(value["name"])]
    if value.get("handle"):
        parts.append(f"handle: {_md(value['handle'])}")
    identifiers = value.get("identifiers")
    if isinstance(identifiers, list) and identifiers:
        parts.append("identifiers: " + ", ".join(_md(item) for item in identifiers))
    return " — ".join(parts)


def _review_detail_text(
    review: dict[str, Any],
    review_authorities: dict[str, dict[str, Any]] | None = None,
) -> str:
    """Render decision authority without reducing review to an unexplained state."""
    decisions = []
    review_authorities = review_authorities or {}
    for field in REVIEW_FIELDS:
        decision = review[field]
        details = [f"state=`{_code(decision['state'])}`"]
        for key in ("authority_ref", "decided_at", "reviewer", "notes"):
            value = decision.get(key)
            details.append(f"{key}={_md(value) if value is not None else 'none'}")
        authority_url = review_authorities.get(field, {}).get("authority_url")
        if isinstance(authority_url, str):
            authority_ref = decision.get("authority_ref") or "authority"
            details.append(
                "authority_url="
                f"[`{_code(authority_ref)}`]({authority_url})"
            )
        decisions.append(f"{_code(field)}: " + "; ".join(details))
    return " | ".join(decisions)


def _authority_text(authority: Any) -> str:
    """Render a review authority as a link when its URL is source-bound."""
    if not isinstance(authority, dict):
        return "none"
    authority_ref = authority.get("authority_ref")
    authority_url = authority.get("authority_url")
    if isinstance(authority_url, str) and authority_url:
        return f"[`{_code(authority_ref or 'authority')}`]({authority_url})"
    return _md(authority_ref) if authority_ref is not None else "none"


def _review_decision_text(decision: Any) -> str:
    """Render an aggregate review decision with its full recorded context."""
    if not isinstance(decision, dict):
        return "none"
    authority = {
        "authority_ref": decision.get("authority_ref"),
        "authority_url": decision.get("authority_url"),
    }
    return "; ".join(
        [
            f"state={_md(decision.get('state', 'unknown'))}",
            f"authority={_authority_text(authority)}",
            f"decided_at={_md(decision['decided_at']) if decision.get('decided_at') is not None else 'none'}",
            f"reviewer={_md(decision['reviewer']) if decision.get('reviewer') is not None else 'none'}",
            f"notes={_md(decision['notes']) if decision.get('notes') is not None else 'none'}",
        ]
    )


def _receipt_link(row: dict[str, Any]) -> str:
    return (
        f"[receipt:{_md(row['return_id'])}]"
        f"({row['source']['accepted_receipt_url']})"
    )


def _path_link(path: str) -> str:
    return f"[`{_code(path)}`](../../{_path_label(path)})"


def _source_path_link(path: str, url: str) -> str:
    return f"[`{_code(path)}`]({url})"


def _accepted_commit_path_link(repository: dict[str, Any], path: str) -> str:
    origin = repository["origin"].rstrip("/")
    accepted_commit = repository["accepted_commit"]
    return _source_path_link(
        path,
        f"{origin}/blob/{accepted_commit}/{_path_label(path)}",
    )


def _accepted_reference_path_link(reference: dict[str, Any], path: str) -> str:
    """Link an aggregate correction path to each receipt's accepted generation."""
    origin = reference["accepted_commit_url"].rsplit("/commit/", 1)[0]
    return _source_path_link(
        path,
        f"{origin}/blob/{reference['accepted_commit']}/{_path_label(path)}",
    )


def _accepted_reference_receipt_link(reference: dict[str, Any]) -> str:
    return (
        f"[receipt:{_md(reference['return_id'])}]"
        f"({reference['accepted_receipt_url']})"
    )


def _aggregate_source_links(accepted_receipts: list[dict[str, Any]]) -> str:
    """Render aggregate source links without hiding the receipt provenance."""
    rendered = []
    for reference in accepted_receipts:
        artifact_credit = ", ".join(
            _source_path_link(path, url)
            for path, url in zip(
                reference["artifact_credit_paths"], reference["artifact_credit_urls"]
            )
        ) or "none"
        evidence = ", ".join(
            _source_path_link(path, url)
            for path, url in zip(
                reference["evidence_artifact_paths"], reference["evidence_artifact_urls"]
            )
        ) or "none"
        evidence_states = ", ".join(
            f"exit={_md(item['exit_state'])}, replay={_md(item['replay_state'])}"
            for item in reference["evidence_states"]
        ) or "none"
        evidence_records = []
        for evidence_record in reference["evidence_records"]:
            evidence_paths = evidence_record.get("artifacts", [])
            evidence_urls = evidence_record.get("artifact_urls", [])
            artifacts = ", ".join(
                _source_path_link(path, url)
                for path, url in zip(evidence_paths, evidence_urls)
            ) or "none"
            evidence_records.append(
                f"command=`{_code(evidence_record['command'])}`; "
                f"observed={_md(evidence_record['observed'])}; "
                f"environment={_md(evidence_record['environment'])}; "
                f"exit_state={_md(evidence_record['exit_state'])}; "
                f"exit_code={_md(evidence_record['exit_code'])}; "
                f"replay_state={_md(evidence_record['replay_state'])}; "
                f"artifacts={artifacts}"
            )
        review_states = ", ".join(
            f"{_md(field)}={_md(state)}"
            for field, state in sorted(reference["review_states"].items())
        ) or "none"
        review_authorities = ", ".join(
            f"{_md(field)}={_authority_text(authority)}"
            for field, authority in sorted(reference["review_authorities"].items())
        ) or "none"
        review_decisions = ", ".join(
            f"{_md(field)}={_review_decision_text(decision)}"
            for field, decision in sorted(reference["review_decisions"].items())
        ) or "none"
        identity = reference["identity"]
        contributor = _contributor_identity_text(identity["contributor"])
        operator = _md(identity["operator"]["relationship"])
        if identity["operator"].get("name"):
            operator += f" — {_md(identity['operator']['name'])}"
        collaborators = ", ".join(
            f"{_md(value['name'])} ({_md(value['role'])})"
            for value in identity["material_collaborators"]
        ) or "none recorded"
        limitations = ", ".join(
            _md(item) for item in reference["limitations"]
        ) or "none"
        rendered.append(
            f"receipt={_accepted_reference_receipt_link(reference)}; "
            f"accepted_at={_md(reference['accepted_at'])}; "
            f"identity=contributor={contributor}; "
            f"operator={operator}; "
            f"material_collaborators={collaborators}; "
            f"model_system={_md(_disclosure_text(identity['model_system']))}; "
            f"provider={_md(_disclosure_text(identity['provider']))}; "
            f"accepted_commit=[`{_code(reference['accepted_commit'])}`]({reference['accepted_commit_url']}); "
            f"track={_md(reference['track'])}; scope={_md(reference['scope_label'])}; "
            f"result_class={_md(reference['result_class'])}; "
            f"result_summary={_md(reference['result_summary'])}; "
            f"claim_ceiling={_md(reference['claim_ceiling'])}; "
            f"requested_disposition={_md(reference['requested_disposition'])}; "
            f"evidence_states={evidence_states}; "
            f"evidence_records={' | '.join(evidence_records) or 'none'}; "
            f"reproduction_state={_md(reference['reproduction_state'])}; "
            f"review_states={review_states}; "
            f"review_authorities={review_authorities}; "
            f"review_decisions={review_decisions}; "
            f"correction_lineage_state={_md(reference['correction_lineage_state'])}; "
            f"core_promotion_state={_md(reference['core_promotion_state'])}; "
            f"tagged_release_inclusion_state={_md(reference['tagged_release_inclusion_state'])}; "
            f"limitations={limitations}; "
            f"surviving_boundary={_md(reference['surviving_boundary'])}; "
            f"problem_owned_proposition_state={_md(reference['problem_owned_proposition_state'])}; "
            f"artifact_credit={artifact_credit}; evidence={evidence}"
        )
    return " | ".join(rendered) or "none"


def _aggregate_detail_text(
    detail: dict[str, Any],
    accepted_receipts: list[dict[str, Any]] | None = None,
) -> str:
    """Render machine aggregate detail without hiding source-bound fields."""
    parts = []
    accepted_receipts = accepted_receipts or []
    for key in sorted(detail):
        value = detail[key]
        if key == "affected_paths" and isinstance(value, list):
            if accepted_receipts:
                rendered = ", ".join(
                    _accepted_reference_path_link(reference, path)
                    for reference in accepted_receipts
                    for path in value
                )
            else:
                rendered = ", ".join(_path_link(path) for path in value)
        elif key == "affected_path_urls" and isinstance(value, list):
            paths = detail.get("affected_paths", [])
            rendered = ", ".join(
                _source_path_link(path, url)
                for path, url in zip(paths, value)
            ) or "none"
        elif key == "prior_receipt_url" and isinstance(value, str):
            rendered = (
                f"[receipt:{_md(detail.get('prior_return_reference', 'prior receipt'))}]"
                f"({value})"
            )
        elif key == "starting_commit_url" and isinstance(value, str):
            label = detail.get("starting_commit", "starting commit")
            rendered = f"[`{_code(label)}`]({value})"
        elif key == "credit_records" and isinstance(value, list):
            rendered_items = []
            artifact_path = detail.get("artifact_path", "artifact")
            for record in value:
                contributor = record.get("contributor", {})
                contributor_parts = [_md(contributor.get("name", "unknown"))]
                if contributor.get("handle"):
                    contributor_parts.append(
                        f"handle: {_md(contributor['handle'])}"
                    )
                if contributor.get("identifiers"):
                    contributor_parts.append(
                        "identifiers: "
                        + ", ".join(_md(item) for item in contributor["identifiers"])
                    )
                operator = record.get("operator", {})
                operator_text = _md(operator.get("relationship", "unknown"))
                if operator.get("name"):
                    operator_text += f" — {_md(operator['name'])}"
                collaborators = ", ".join(
                    f"{_md(item.get('name', 'unknown'))} ({_md(item.get('role', 'unknown'))})"
                    for item in record.get("material_collaborators", [])
                ) or "none recorded"
                receipt_url = record.get("accepted_receipt_url")
                receipt_text = (
                    f"[receipt:{_md(record.get('return_id', 'receipt'))}]({receipt_url})"
                    if isinstance(receipt_url, str)
                    else _md(record.get("return_id", "receipt"))
                )
                artifact_url = record.get("artifact_url")
                artifact_text = (
                    _source_path_link(artifact_path, artifact_url)
                    if isinstance(artifact_url, str)
                    else _md(artifact_path)
                )
                impact = record.get("impact_state", {})
                evidence_states = ", ".join(
                    f"exit={_md(item.get('exit_state', 'unknown'))}, replay={_md(item.get('replay_state', 'unknown'))}"
                    for item in impact.get("evidence_states", [])
                ) or "none"
                evidence_paths = record.get("evidence_artifact_paths", [])
                evidence_urls = record.get("evidence_artifact_urls", [])
                evidence_artifacts = ", ".join(
                    _source_path_link(path, url)
                    for path, url in zip(evidence_paths, evidence_urls)
                ) or "none"
                evidence_records = []
                for evidence in record.get("evidence_records", []):
                    evidence_paths = evidence.get("artifacts", [])
                    evidence_urls = evidence.get("artifact_urls", [])
                    rendered_artifacts = ", ".join(
                        _source_path_link(path, url)
                        for path, url in zip(evidence_paths, evidence_urls)
                    ) or "none"
                    evidence_records.append(
                        f"command=`{_code(evidence.get('command', 'unknown'))}`; "
                        f"observed={_md(evidence.get('observed', 'unknown'))}; "
                        f"environment={_md(evidence.get('environment', 'unknown'))}; "
                        f"exit_state={_md(evidence.get('exit_state', 'unknown'))}; "
                        f"exit_code={_md(evidence.get('exit_code', 'unknown'))}; "
                        f"replay_state={_md(evidence.get('replay_state', 'unknown'))}; "
                        f"artifacts={rendered_artifacts}"
                    )
                review_states = ", ".join(
                    f"{_md(field)}={_md(state)}"
                    for field, state in sorted(impact.get("review_states", {}).items())
                ) or "none"
                review_authorities = []
                for field, authority in sorted(
                    impact.get("review_authorities", {}).items()
                ):
                    authority_ref = authority.get("authority_ref")
                    authority_url = authority.get("authority_url")
                    if isinstance(authority_url, str):
                        authority_text = (
                            f"[`{_code(authority_ref or 'authority')}`]({authority_url})"
                        )
                    elif authority_ref is None:
                        authority_text = "none"
                    else:
                        authority_text = _md(authority_ref)
                    review_authorities.append(f"{_md(field)}={authority_text}")
                limitations = ", ".join(
                    _md(item) for item in impact.get("limitations", [])
                ) or "none"
                correction = record.get("correction_lineage")
                if correction is None:
                    correction_text = "none"
                else:
                    prior_url = correction.get("prior_receipt_url")
                    prior_reference = correction.get("prior_return_reference", "prior receipt")
                    prior_text = (
                        f"[receipt:{_md(prior_reference)}]({prior_url})"
                        if isinstance(prior_url, str)
                        else _md(prior_reference)
                    )
                    starting_url = correction.get("starting_commit_url")
                    starting_text = (
                        f"[`{_code(correction.get('starting_commit', 'starting commit'))}`]({starting_url})"
                        if isinstance(starting_url, str)
                        else _md(correction.get("starting_commit", "none"))
                    )
                    affected_paths = correction.get("affected_paths", [])
                    affected_urls = correction.get("affected_path_urls", [])
                    affected_text = ", ".join(
                        _source_path_link(path, url)
                        for path, url in zip(affected_paths, affected_urls)
                    ) or "none"
                    correction_text = (
                        f"state={_md(correction.get('state', 'present'))}; "
                        f"disposition={_md(correction.get('disposition', 'unknown'))}; "
                        f"prior={prior_text}; starting_commit={starting_text}; "
                        f"affected_paths={affected_text}; "
                        f"changed_evidence_or_wording={_md(correction.get('changed_evidence_or_wording', 'unknown'))}; "
                        f"reason={_md(correction.get('reason', 'unknown'))}"
                    )
                rendered_items.append(
                    f"{receipt_text}; accepted_at={_md(record.get('accepted_at', 'unknown'))}; "
                    f"receipt_path={_md(record.get('receipt_path', 'unknown'))}; "
                    f"receipt_sha256={_md(record.get('receipt_sha256', 'unknown'))}; "
                    f"credit_name={_md(record.get('credit_name', 'unknown'))}; "
                    f"contribution_roles={', '.join(_md(role) for role in record.get('contribution_roles', [])) or 'not recorded'}; "
                    f"contributor={' — '.join(contributor_parts)}; "
                    f"operator={operator_text}; collaborators={collaborators}; "
                    f"model_system={_md(_disclosure_text(record.get('model_system', {'state': 'not_recorded'})))}; "
                    f"provider={_md(_disclosure_text(record.get('provider', {'state': 'not_recorded'})))}; "
                    f"artifact={artifact_text}; track={_md(impact.get('track', 'unknown'))}; scope={_md(impact.get('scope_label', 'unknown'))}; "
                    f"result_class={_md(impact.get('result_class', 'unknown'))}; "
                    f"result_summary={_md(record.get('result_summary', 'unknown'))}; "
                    f"claim_ceiling={_md(impact.get('claim_ceiling', 'unknown'))}; "
                    f"requested_disposition={_md(impact.get('requested_disposition', 'unknown'))}; "
                    f"evidence_states={evidence_states}; evidence_artifacts={evidence_artifacts}; "
                    f"evidence_records={' | '.join(evidence_records) or 'none'}; "
                    f"reproduction_state={_md(impact.get('reproduction_state', 'unknown'))}; "
                    f"review_states={review_states}; review_authorities={' | '.join(review_authorities) or 'none'}; "
                    f"correction_lineage={correction_text}; "
                    f"correction_lineage_state={_md(impact.get('correction_lineage_state', 'unknown'))}; "
                    f"problem_owned_proposition_state={_md(impact.get('problem_owned_proposition_state', 'unknown'))}; "
                    f"core_promotion_state={_md(impact.get('core_promotion_state', 'unknown'))}; "
                    f"tagged_release_inclusion_state={_md(impact.get('tagged_release_inclusion_state', 'unknown'))}; "
                    f"limitations={limitations}; "
                    f"surviving_boundary={_md(impact.get('surviving_boundary', 'unknown'))}"
                )
            rendered = " | ".join(rendered_items) or "none"
        elif key == "review_authorities" and isinstance(value, list):
            rendered_items = []
            for authority in value:
                return_id = authority.get("return_id", "receipt")
                authority_ref = authority.get("authority_ref")
                authority_url = authority.get("authority_url")
                if isinstance(authority_url, str):
                    authority_text = (
                        f"[`{_code(authority_ref or 'authority')}`]({authority_url})"
                    )
                elif authority_ref is None:
                    authority_text = "none"
                else:
                    authority_text = _md(authority_ref)
                rendered_items.append(
                    f"{_md(return_id)}={authority_text}"
                )
            rendered = ", ".join(rendered_items) or "none"
        elif key == "review_decisions" and isinstance(value, list):
            rendered = " | ".join(
                f"{_md(item.get('return_id', 'receipt'))}="
                f"{_review_decision_text(item.get('decision'))}"
                for item in value
                if isinstance(item, dict)
            ) or "none"
        elif isinstance(value, list):
            rendered = ", ".join(_md(item) for item in value) or "none"
        elif value is None:
            rendered = "none"
        elif isinstance(value, bool):
            rendered = str(value).lower()
        else:
            rendered = _md(value)
        parts.append(f"`{_code(key)}`={rendered}")
    return "; ".join(parts) or "none"


def human_projection(projection: dict[str, Any]) -> bytes:
    rows = projection["chronological"]
    # REUSE-IgnoreStart — these strings are emitted into the generated
    # projection's own header; they do not license this script.
    lines = [
        "<!-- SPDX-FileCopyrightText: 2026 Will Cook -->",
        "<!-- SPDX-License-Identifier: Apache-2.0 -->",
    # REUSE-IgnoreEnd
        "",
        "# Accepted contribution recognition and impact",
        "",
        "This generated public view answers which contributor or disclosed system "
        "contributed which accepted artifact, to which bounded problem, with what "
        "evidence and review state. It consumes accepted receipts only.",
        "",
        "Each accepted row carries a `public_frontier` route to the complete result-family "
        "fan-in and exact surviving boundary for its problem. That route is navigation "
        "context only; it does not create credit or promote the returned claim.",
        "",
        "The aggregate counts below are factual accepted-receipt counts with the "
        "stated denominator. They are not rankings, measures of mathematical "
        "importance, proof quality, novelty, ownership, endorsement, or model quality. "
        "Entries are sorted by stable key, not by count; equal counts remain tied and "
        "the stable-key order is navigation, not a rank. Human contributors, operators, "
        "collaborators, model systems, and providers remain separate identities; "
        "undisclosed and not-used states are not inferred to be disclosed.",
        "",
        "Credit boundary: each row records only the narrow artifact paths and evidence "
        "named by its accepted receipt. Contributors retain clear credit for that work; "
        "Will Cook's pre-existing corpus authorship, provenance, and prior contributions "
        "remain distinct and are not reassigned by this projection.",
        "",
        "Detached route-memory sidecars may bind an accepted-return intake, but they remain "
        "separate route authority and are not copied into or counted by this accepted-receipt view.",
        "",
        "The denominator is the total accepted-receipt count. Facets are independent: "
        "a receipt can appear in multiple entries within a multi-valued facet such as "
        "collaborators or evidence, so entry counts are not percentages and must not "
        "be summed as a total.",
        "",
        f"Accepted-receipt denominator: `{projection['denominator']['accepted_receipts']}`.",
        "",
        "Machine-readable projection: [contribution-recognition.json](contribution-recognition.json). "
        "Contributor contract: [CONTRIBUTING.md](../../CONTRIBUTING.md) and "
        "[CREDIT_POLICY.md](CREDIT_POLICY.md).",
        "Projection contract: [research-contribution-recognition.schema.json](schema/research-contribution-recognition.schema.json).",
        "Cold-clone validation: `python3 scripts/check_research_contribution_recognition.py` "
        "(read-only; verifies committed receipts and both generated views).",
        "",
        "Retrieve one accepted record by its exact return id:",
        "",
        "```sh",
        "jq --arg return_id \"<accepted-return-id>\" \\",
        "  '.chronological[] | select(.return_id == $return_id)' \\",
        "  docs/research-commons/contribution-recognition.json",
        "```",
        "",
        "The row's `receipt_path`, `receipt_sha256`, and `repository.accepted_commit` "
        "are the provenance anchors for every displayed facet. An empty match is "
        "correct for a submitted, rejected, or sidecar-only return until an "
        "accepted receipt is committed.",
        "",
        "## How to read an accepted record",
        "",
        "A `checked_positive`, `negative`, `inconclusive`, or `corrective` return can be "
        "recognized after acceptance. Recognition credits only the exact artifact and "
        "evidence named by its accepted receipt; it is not a score for commits, diff "
        "size, model use, or contributor activity.",
        "",
        "- Start with the result class, claim ceiling, limitations, and surviving "
        "boundary. These fields describe the returned artifact and do not promote a "
        "mathematical claim.",
        "- Follow the artifact-credit paths, accepted receipt, accepted commit, "
        "evidence records, and review-authority links. A missing authority remains "
        "missing, and acceptance is not independent mathematical review.",
        "- For a corrective record, follow `correction_lineage` and its `retain`, "
        "`supersede`, or `withdraw` disposition; the prior receipt remains "
        "discoverable.",
        "- Treat `tagged_release_inclusion_state` as a release fact only. It does not "
        "imply inclusion, endorsement, ownership, or mathematical importance.",
        "",
        "## Accepted artifact records",
        "",
    ]
    for row in rows:
        identity = row["identity"]
        repository = row["repository"]
        result = row["result"]
        review = row["review"]
        source = row["source"]
        collaborators = identity.get("material_collaborators", [])
        collaborator_text = (
            "; ".join(f"{item['name']} ({item['role']})" for item in collaborators)
            if collaborators
            else "none recorded"
        )
        artifact_urls_by_path = dict(
            zip(source["artifact_credit_paths"], source["artifact_credit_urls"])
        )
        evidence_urls_by_path = dict(
            zip(source["evidence_artifact_paths"], source["evidence_artifact_urls"])
        )
        evidence_text = "; ".join(
            f"{item['exit_state']}/{item['replay_state']}" for item in row["evidence"]
        )
        evidence_record_text = "; ".join(
            f"command=`{_code(item['command'])}`; "
            f"observed={_md(item['observed'])}; "
            f"environment={_md(item['environment'])}; "
            f"exit=`{_code(item['exit_state'])}`; "
            f"replay=`{_code(item['replay_state'])}`; "
            + "artifacts="
            + ", ".join(
                _source_path_link(path, evidence_urls_by_path[path])
                for path in item["artifacts"]
            )
            for item in row["evidence"]
        )
        review_text = "; ".join(
            f"{field}={review[field]['state']}" for field in REVIEW_FIELDS
        )
        review_detail_text = _review_detail_text(
            review, row["impact_state"]["review_authorities"]
        )
        impact_evidence_text = "; ".join(
            f"{item['exit_state']}/{item['replay_state']}"
            for item in row["impact_state"]["evidence_states"]
        )
        impact_review_text = "; ".join(
            f"{field}={row['impact_state']['review_states'][field]}"
            for field in REVIEW_FIELDS
        )
        artifact_credit_text = "; ".join(
            f"{_md(credit['name'])}"
            + (
                f" ({', '.join(_md(role) for role in credit['contribution_roles'])})"
                if credit.get("contribution_roles")
                else ""
            )
            + ": "
            + ", ".join(
                _source_path_link(path, artifact_urls_by_path[path])
                for path in credit["artifact_paths"]
            )
            for credit in row["attribution"]["artifact_credit"]
        )
        evidence_path_text = ", ".join(
            _source_path_link(path, evidence_urls_by_path[path])
            for path in source["evidence_artifact_paths"]
        )
        model = identity.get("model_system", {"state": "not_recorded"})
        provider = identity.get("provider", {"state": "not_recorded"})
        model_text = _disclosure_text(model)
        provider_text = _disclosure_text(provider)
        scope_label = contributions.contribution_scope_label(row["frontier"])
        track = contributions.contribution_track(row["frontier"])
        route_label = (
            f"Erdős #{row['frontier']['problem']} current fan-in"
            if track == "mathematics"
            else "architecture contribution path"
        )
        lines.extend(
            [
                f"### {_md(row['accepted_at'])} — {_md(scope_label)} — {_md(result['class'])}",
                "",
                f"- Receipt: {_receipt_link(row)}",
                f"- Contributor: {_contributor_identity_text(identity['contributor'])}",
                f"- Operator relationship: `{_code(identity['operator']['relationship'])}` — {_md(identity['operator'].get('name') or 'undisclosed')}",
                f"- Material collaborators: {_md(collaborator_text)}",
                f"- Model/system disclosure: `{_code(model.get('state', 'not_recorded'))}` — {_md(model_text)}",
                f"- Provider disclosure: `{_code(provider.get('state', 'not_recorded'))}` — {_md(provider_text)}",
                f"- Track/frontier: `{_code(track)}` — {_md(scope_label)} — `{_code(row['frontier']['handle'])}`",
                f"- Public frontier: [{_md(route_label)}]({row['public_frontier']['relative_link']})",
                f"- Result and claim ceiling: `{_code(result['class'])}` / `{_code(result['claim_ceiling'])}`",
                f"- Requested disposition: `{_code(result['requested_disposition'])}`",
                f"- Reproduction state: `{_code(review['reproduction']['state'])}`",
                f"- Review states: {_md(review_text)}",
                f"- Review decision details: {review_detail_text}",
                f"- Impact projection: track=`{_code(row['impact_state']['track'])}`; scope={_md(row['impact_state']['scope_label'])}; result_class=`{_code(row['impact_state']['result_class'])}`; claim_ceiling=`{_code(row['impact_state']['claim_ceiling'])}`; requested_disposition=`{_code(row['impact_state']['requested_disposition'])}`; evidence_states=`{_code(impact_evidence_text)}`; reproduction_state=`{_code(row['impact_state']['reproduction_state'])}`; review_states={_md(impact_review_text)}; correction_lineage_state=`{_code(row['impact_state']['correction_lineage_state'])}`; problem_owned_proposition_state=`{_code(row['impact_state']['problem_owned_proposition_state'])}`; core_promotion_state=`{_code(row['impact_state']['core_promotion_state'])}`; tagged_release_inclusion_state=`{_code(row['impact_state']['tagged_release_inclusion_state'])}`",
                f"- Core-promotion state: `{_code(review['core_promotion']['state'])}`",
                f"- Tagged-release inclusion: `{_code(review['tagged_release_inclusion']['state'])}`",
                f"- Summary: {_md(result['summary'])}",
                f"- Surviving claim boundary: {_md(result['surviving_boundary'])}",
                f"- Evidence/replay states: `{_code(evidence_text)}`",
                f"- Evidence records: {evidence_record_text}",
                f"- Limitations: {_md('; '.join(result['limitations']))}",
                f"- Accepted commit: [`{repository['accepted_commit']}`]({source['accepted_commit_url']})",
                f"- Receipt source hash: `{source['receipt_sha256']}`",
                f"- Artifact-credit paths: {artifact_credit_text}",
                f"- Evidence-artifact paths: {evidence_path_text}",
            ]
        )
        if "correction_lineage" in row:
            lineage = row["correction_lineage"]
            prior_reference = lineage["prior_return_reference"]
            prior_row = next(
                (candidate for candidate in rows if candidate["return_id"] == prior_reference),
                None,
            )
            if prior_row is None:
                prior_text = (
                    f"`{_code(prior_reference)}` (not present in this accepted-receipt projection)"
                )
            else:
                prior_text = f"{_receipt_link(prior_row)} (accepted receipt)"
            starting_commit = lineage["starting_commit"]
            origin = repository["origin"].rstrip("/")
            if COMMIT_RE.fullmatch(starting_commit):
                starting_commit_text = (
                    f"[`{_code(starting_commit)}`]({origin}/commit/{starting_commit})"
                )
            else:
                starting_commit_text = f"`{_code(starting_commit)}`"
            affected_text = ", ".join(
                _accepted_commit_path_link(repository, path)
                for path in lineage["affected_paths"]
            )
            lines.append(
                "- Correction/supersession lineage: "
                + f"prior={prior_text}; disposition=`{_code(lineage['disposition'])}`; "
                + f"starting_commit={starting_commit_text}; affected={affected_text}; "
                + f"changed_evidence_or_wording={_md(lineage['changed_evidence_or_wording'])}; "
                + f"reason={_md(lineage['reason'])}"
            )
        lines.append("")

    lines.extend(["## Factual accepted-receipt aggregates", ""])
    for facet in FACET_NAMES:
        title = facet.removeprefix("by_").replace("_", " ").title()
        lines.extend(
            [
                f"### {title}",
                "",
                f"Denominator: `{projection['denominator']['accepted_receipts']}` accepted receipts; entries are stable-key sorted.",
                "",
            ]
        )
        for entry in projection["aggregates"][facet]:
            links = ", ".join(
                _receipt_link(next(row for row in rows if row["return_id"] == reference["return_id"]))
                for reference in entry["accepted_receipts"]
            )
            lines.extend(
                [
                    f"- `{_code(entry['label'])}` — accepted receipts: `{entry['accepted_receipt_count']}` — {links}",
                    f"  Detail: {_aggregate_detail_text(entry['detail'], entry['accepted_receipts'])}",
                    f"  Source links: {_aggregate_source_links(entry['accepted_receipts'])}",
                ]
            )
        lines.append("")
    lines.extend(
        [
            "The accepted receipt remains the attribution evidence. Its evidence, "
            "limitations, correction lineage, and surviving boundary control the "
            "meaning of every projection row; Git history, claim authority, and "
            "release authority remain separate.",
            "",
        ]
    )
    return "\n".join(lines).encode("utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail when generated views are stale")
    args = parser.parse_args(argv)
    try:
        identity_contract = repository_identity_contract.load_identity()
        projection = build_recognition(
            contributions.load_receipts(
                require_committed=True,
                repository_identity=identity_contract,
            )
        )
    except (OSError, ValueError, repository_identity_contract.IdentityError) as exc:
        print(f"build_research_contribution_recognition: {exc}")
        return 1
    json_payload = (json.dumps(projection, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode(
        "utf-8"
    )
    markdown_payload = human_projection(projection)
    if args.check:
        current = (
            contributions.output_is_current(JSON_OUTPUT, json_payload)
            and contributions.output_is_current(MARKDOWN_OUTPUT, markdown_payload)
        )
        if not current:
            print("contribution recognition views are stale; run this builder without --check")
            return 1
        print("contribution recognition views current: accepted receipts only")
        return 0
    try:
        contributions.write_projection_outputs(
            json_payload,
            markdown_payload,
            json_output=JSON_OUTPUT,
            markdown_output=MARKDOWN_OUTPUT,
        )
    except (OSError, ValueError) as exc:
        print(f"build_research_contribution_recognition: {exc}")
        return 1
    print("wrote accepted-only contribution recognition and impact views")
    return 0


if __name__ == "__main__":
    sys.exit(main())
