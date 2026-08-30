"""Bind continuation state and return packages to canonical route memory.

The route-memory corpus remains the only authority for route IDs, statuses,
and Lean locators.  This module stores only a digest-bound consultation and a
contributor's relationship to those already-recorded routes.
"""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
from pathlib import Path
from typing import Any

import validation_singleflight as singleflight


ROUTE_MEMORY_PATH = "docs/research-commons/route-memory/route_memory.json"
CONSULTATION_SCHEMA = "research-route-memory-consultation/1"
RETURN_RECEIPT_SCHEMA = "research-route-memory-return/1"
RELATIONSHIPS = frozenset({"confirms", "narrows", "supersedes", "unrelated"})
DISPOSITIONS = frozenset({"consulted", "no_applicable_route"})
ROSTER = frozenset({68, 243, 249, 251, 257, 269, 1041, 1049})
CANONICAL_DOCUMENT_FIELDS = frozenset(
    {"schema", "authority_posture", "scope", "recording_rule", "records"}
)
CANONICAL_AUTHORITY_POSTURE = (
    "navigation record of checked, tracked corpus boundaries; not a claim registry, "
    "proof authority, or a statement of problem status"
)


def _error(errors: list[str], path: str, message: str) -> None:
    errors.append(f"{path}: {message}")


def _nonempty_string(value: Any, path: str, errors: list[str]) -> str | None:
    if not isinstance(value, str) or not value.strip():
        _error(errors, path, "must be a nonempty string")
        return None
    return value


def _relative_path(value: Any, path: str, errors: list[str]) -> str | None:
    text = _nonempty_string(value, path, errors)
    if text is None:
        return None
    candidate = Path(text)
    raw_parts = text.split("/")
    if (
        candidate.is_absolute()
        or "\\" in text
        or any(part in {"", ".", ".."} for part in raw_parts)
        or not candidate.parts
    ):
        _error(
            errors,
            path,
            "must be a canonical repository-relative path without empty, '.', '..', or backslash segments",
        )
    return text


def _platform_alias_target(path: Path) -> Path | None:
    """Return the target of a verified macOS system-directory alias."""
    aliases = {
        Path("/tmp"): Path("/private/tmp"),
        Path("/var"): Path("/private/var"),
    }
    target = aliases.get(path)
    if target is None:
        return None
    try:
        return target if path.resolve(strict=True) == target else None
    except OSError:
        return None


def path_has_symlink_component(path: Path, root: Path) -> bool:
    """Reject route-corpus reads that could substitute bytes through a link."""
    candidate = Path(os.path.abspath(path))
    checkout = Path(os.path.abspath(root))
    try:
        candidate.relative_to(checkout)
    except ValueError:
        return True
    current = Path(candidate.anchor)
    for component in candidate.parts[1:]:
        current /= component
        if current.is_symlink():
            target = _platform_alias_target(current)
            if target is None:
                return True
            current = target
    return False


def canonical_corpus(root: Path) -> tuple[dict[int, dict[str, Any]], str]:
    """Return canonical route records and the digest of their tracked source."""
    source = root / ROUTE_MEMORY_PATH
    if path_has_symlink_component(source, root):
        raise ValueError("canonical route memory source must not traverse symbolic links")
    try:
        payload = source.read_bytes()
        relative = source.relative_to(root).as_posix()
        committed = subprocess.run(
            ["git", "-C", str(root), "show", f"HEAD:{relative}"],
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            check=False,
            env=singleflight.command_environment(),
            timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
        )
    except (OSError, ValueError, subprocess.TimeoutExpired) as exc:
        raise ValueError(
            "canonical route memory source must be readable from tracked HEAD"
        ) from exc
    if committed.returncode != 0 or committed.stdout != payload:
        raise ValueError("canonical route memory source must match tracked HEAD")
    try:
        document = json.loads(payload.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError("canonical route memory is not valid UTF-8 JSON") from exc
    if not isinstance(document, dict):
        raise ValueError("canonical route memory must be a JSON object")
    if set(document) != CANONICAL_DOCUMENT_FIELDS:
        raise ValueError(
            "canonical route memory has an ambiguous top-level contract"
        )
    if document.get("schema") != "research_route_memory_v1":
        raise ValueError("canonical route memory has an invalid schema")
    if document.get("authority_posture") != CANONICAL_AUTHORITY_POSTURE:
        raise ValueError(
            "canonical route memory authority posture must remain navigation-only"
        )
    for field in ("scope", "recording_rule"):
        value = document.get(field)
        if not isinstance(value, str) or not value.strip():
            raise ValueError(f"canonical route memory {field} must be nonempty text")
    records = document.get("records")
    if not isinstance(records, list):
        raise ValueError("canonical route memory records must be an array")
    if len(records) != len(ROSTER):
        raise ValueError("canonical route memory must cover the complete public roster")
    required = {
        "problem",
        "route_id",
        "status",
        "actual_established",
        "failure_boundary",
        "next_obligation",
        "evidence",
        "prerequisites_and_assumptions",
        "route",
    }
    indexed: dict[int, dict[str, Any]] = {}
    route_ids: set[str] = set()
    for record in records:
        if not isinstance(record, dict) or set(record) != required:
            raise ValueError("canonical route memory contains an ambiguous record")
        problem = record.get("problem")
        route_id = record.get("route_id")
        if not isinstance(problem, int) or problem not in ROSTER:
            raise ValueError("canonical route memory contains an unknown problem")
        if problem in indexed or not isinstance(route_id, str) or not route_id.strip():
            raise ValueError(
                "canonical route memory contains duplicate or invalid route identity"
            )
        if route_id in route_ids:
            raise ValueError(
                "canonical route memory contains duplicate route identity"
            )
        route_ids.add(route_id)
        for field in (
            "status",
            "actual_established",
            "failure_boundary",
            "next_obligation",
            "prerequisites_and_assumptions",
            "route",
        ):
            value = record.get(field)
            if not isinstance(value, str) or not value.strip():
                raise ValueError(
                    f"canonical route memory record {route_id} has invalid {field}"
                )
        indexed[problem] = record
    if set(indexed) != ROSTER:
        raise ValueError("canonical route memory does not cover the public roster")
    return {
        problem: record for problem, record in indexed.items()
    }, "sha256:" + hashlib.sha256(payload).hexdigest()


def consultation_for_problem(problem: int, root: Path, *, no_applicable_route: bool = False) -> dict[str, Any]:
    records, digest = canonical_corpus(root)
    record = records.get(problem)
    if record is None:
        raise ValueError(f"route memory has no roster record for problem {problem}")
    routes: list[dict[str, str]] = []
    disposition = "no_applicable_route" if no_applicable_route else "consulted"
    if not no_applicable_route:
        routes.append({"route_id": record["route_id"], "status": record["status"]})
    return {
        "schema": CONSULTATION_SCHEMA,
        "problem": problem,
        "route_memory": {"path": ROUTE_MEMORY_PATH, "sha256": digest},
        "disposition": disposition,
        "routes": routes,
    }


def return_receipt_template(consultation: dict[str, Any]) -> dict[str, Any]:
    """Create a fillable receipt without copying route text or locators."""
    return {
        "schema": RETURN_RECEIPT_SCHEMA,
        "return_id": "<set-to-return-id>",
        "problem": consultation["problem"],
        "route_memory": consultation["route_memory"],
        "disposition": consultation["disposition"],
        "relationships": [
            {
                "route_id": route["route_id"],
                "observed_status": route["status"],
                "relationship": "unrelated",
                "changed_evidence": [],
            }
            for route in consultation["routes"]
        ],
    }


def _validate_route_memory_binding(
    value: Any,
    path: str,
    root: Path,
    errors: list[str],
) -> tuple[dict[int, dict[str, Any]], str] | None:
    if not isinstance(value, dict):
        _error(errors, path, "must be an object")
        return None
    if set(value) != {"path", "sha256"}:
        _error(errors, path, "must contain exactly path and sha256")
        return None
    source = _nonempty_string(value.get("path"), f"{path}.path", errors)
    digest = _nonempty_string(value.get("sha256"), f"{path}.sha256", errors)
    if source != ROUTE_MEMORY_PATH:
        _error(errors, f"{path}.path", "must name the canonical route-memory source")
    if isinstance(source, str) and ("ai_workflow" in source.lower() or Path(source).is_absolute()):
        _error(errors, f"{path}.path", "must not reference a private or local path")
    try:
        records, actual_digest = canonical_corpus(root)
    except ValueError as exc:
        _error(errors, path, str(exc))
        return None
    if digest != actual_digest:
        _error(errors, f"{path}.sha256", "does not match the current canonical route-memory digest")
    return records, actual_digest


def validate_consultation(value: Any, root: Path) -> list[str]:
    errors: list[str] = []
    if not isinstance(value, dict):
        return ["route_memory_consultation: must be an object"]
    fields = {"schema", "problem", "route_memory", "disposition", "routes"}
    if set(value) != fields:
        _error(errors, "route_memory_consultation", "must contain exactly schema, problem, route_memory, disposition, and routes")
    if value.get("schema") != CONSULTATION_SCHEMA:
        _error(errors, "route_memory_consultation.schema", f"must be {CONSULTATION_SCHEMA}")
    problem = value.get("problem")
    if not isinstance(problem, int) or problem not in ROSTER:
        _error(errors, "route_memory_consultation.problem", "must name a roster problem")
    binding = _validate_route_memory_binding(value.get("route_memory"), "route_memory_consultation.route_memory", root, errors)
    disposition = value.get("disposition")
    if disposition not in DISPOSITIONS:
        _error(errors, "route_memory_consultation.disposition", f"must be one of {sorted(DISPOSITIONS)}")
    routes = value.get("routes")
    if not isinstance(routes, list):
        _error(errors, "route_memory_consultation.routes", "must be an array")
        return errors
    if binding is None or not isinstance(problem, int):
        return errors
    records, _ = binding
    canonical = records.get(problem)
    expected = [] if disposition == "no_applicable_route" else [canonical]
    if canonical is None:
        _error(errors, "route_memory_consultation.problem", "has no canonical route record")
        return errors
    if len(routes) != len(expected):
        _error(errors, "route_memory_consultation.routes", "does not match the selected route-memory disposition")
        return errors
    for index, route in enumerate(routes):
        base = f"route_memory_consultation.routes[{index}]"
        if not isinstance(route, dict) or set(route) != {"route_id", "status"}:
            _error(errors, base, "must contain exactly route_id and status")
            continue
        if route.get("route_id") != canonical["route_id"]:
            _error(errors, f"{base}.route_id", "is unknown or belongs to another problem")
        if route.get("status") != canonical["status"]:
            _error(errors, f"{base}.status", "does not match canonical route-memory status")
    return errors


def validate_return_receipt(
    value: Any,
    returned: dict[str, Any],
    consultation: dict[str, Any],
    root: Path,
) -> list[str]:
    """Validate a contributor relationship without allowing route-memory mutation."""
    errors = validate_consultation(consultation, root)
    if not isinstance(value, dict):
        return errors + ["route_memory_return: must be an object"]
    fields = {"schema", "return_id", "problem", "route_memory", "disposition", "relationships"}
    if set(value) != fields:
        _error(errors, "route_memory_return", "must contain exactly schema, return_id, problem, route_memory, disposition, and relationships")
    if value.get("schema") != RETURN_RECEIPT_SCHEMA:
        _error(errors, "route_memory_return.schema", f"must be {RETURN_RECEIPT_SCHEMA}")
    if value.get("return_id") != returned.get("return_id"):
        _error(errors, "route_memory_return.return_id", "must equal return.json return_id")
    consultation_map = consultation if isinstance(consultation, dict) else {}
    returned_frontier = returned.get("frontier")
    frontier_problem = (
        returned_frontier.get("problem")
        if isinstance(returned_frontier, dict)
        else None
    )
    expected_problem = consultation_map.get("problem")
    if value.get("problem") != expected_problem or frontier_problem != expected_problem:
        _error(errors, "route_memory_return.problem", "must equal both the opened session and return frontier problem")
    binding = _validate_route_memory_binding(value.get("route_memory"), "route_memory_return.route_memory", root, errors)
    if value.get("route_memory") != consultation_map.get("route_memory"):
        _error(errors, "route_memory_return.route_memory", "does not match the opened continuation consultation")
    disposition = value.get("disposition")
    if disposition != consultation_map.get("disposition"):
        _error(errors, "route_memory_return.disposition", "does not match the opened continuation consultation")
    relationships = value.get("relationships")
    if not isinstance(relationships, list):
        _error(errors, "route_memory_return.relationships", "must be an array")
        return errors
    if binding is None:
        return errors
    records, _ = binding
    expected_routes = consultation_map.get("routes") if isinstance(consultation_map.get("routes"), list) else []
    expected_ids = {route.get("route_id") for route in expected_routes if isinstance(route, dict)}
    if disposition == "no_applicable_route":
        if relationships:
            _error(errors, "route_memory_return.relationships", "must be empty when no_applicable_route was recorded")
        return errors
    seen: set[str] = set()
    for index, relationship in enumerate(relationships):
        base = f"route_memory_return.relationships[{index}]"
        fields = {"route_id", "observed_status", "relationship", "changed_evidence"}
        if not isinstance(relationship, dict) or set(relationship) != fields:
            _error(errors, base, "must contain exactly route_id, observed_status, relationship, and changed_evidence")
            continue
        route_id = relationship.get("route_id")
        if not isinstance(route_id, str) or route_id not in expected_ids:
            _error(errors, f"{base}.route_id", "is unknown or belongs to another problem")
            continue
        if route_id in seen:
            _error(errors, f"{base}.route_id", "must not be repeated")
        seen.add(route_id)
        canonical = records.get(expected_problem)
        if canonical is None or canonical.get("route_id") != route_id:
            _error(errors, f"{base}.route_id", "does not resolve in canonical route memory")
            continue
        if relationship.get("observed_status") != canonical.get("status"):
            _error(errors, f"{base}.observed_status", "inflates or mismatches canonical route-memory status")
        relation = relationship.get("relationship")
        if relation not in RELATIONSHIPS:
            _error(errors, f"{base}.relationship", f"must be one of {sorted(RELATIONSHIPS)}")
        changed = relationship.get("changed_evidence")
        if not isinstance(changed, list):
            _error(errors, f"{base}.changed_evidence", "must be an array")
            continue
        for changed_index, item in enumerate(changed):
            _relative_path(item, f"{base}.changed_evidence[{changed_index}]", errors)
        # Keep malformed JSON values on the validation-error path.  Calling
        # ``set`` on a dict/list here would raise TypeError and crash the
        # acceptance consumer instead of rejecting the sidecar safely.
        hashable_paths = [item for item in changed if isinstance(item, str)]
        if len(hashable_paths) != len(set(hashable_paths)):
            _error(errors, f"{base}.changed_evidence", "must not contain duplicates")
        if relation == "supersedes":
            if not changed:
                _error(errors, f"{base}.changed_evidence", "must name changed evidence when superseding a route")
            repository = returned.get("repository")
            changed_paths = (
                repository.get("changed_paths")
                if isinstance(repository, dict)
                else None
            )
            if not isinstance(changed_paths, list) or not changed_paths or not all(
                isinstance(path, str) and path for path in changed_paths
            ):
                _error(
                    errors,
                    f"{base}.changed_evidence",
                    "return.repository.changed_paths must be a nonempty string list before supersession binding",
                )
            elif not set(hashable_paths).issubset(set(changed_paths)):
                _error(errors, f"{base}.changed_evidence", "must be included in return.repository.changed_paths")
        elif changed:
            _error(errors, f"{base}.changed_evidence", "is only valid when the relationship is supersedes")
    if seen != expected_ids:
        _error(errors, "route_memory_return.relationships", "must cover every consulted route exactly once")
    return errors


def validate_detached_return_receipt(value: Any, returned: dict[str, Any], root: Path) -> list[str]:
    """Validate a package sidecar when the original session directory is absent."""
    if not isinstance(value, dict):
        return ["route_memory_return: must be an object"]
    relationships = value.get("relationships")
    if not isinstance(relationships, list):
        return ["route_memory_return.relationships: must be an array"]
    consultation = {
        "schema": CONSULTATION_SCHEMA,
        "problem": value.get("problem"),
        "route_memory": value.get("route_memory"),
        "disposition": value.get("disposition"),
        "routes": [
            {"route_id": item.get("route_id"), "status": item.get("observed_status")}
            for item in relationships
            if isinstance(item, dict)
        ],
    }
    return validate_return_receipt(value, returned, consultation, root)
