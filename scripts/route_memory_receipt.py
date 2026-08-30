"""Bind continuation state and return packages to canonical route memory.

The route-memory corpus remains the only authority for route IDs, statuses,
and Lean locators.  This module stores only a digest-bound consultation and a
contributor's relationship to those already-recorded routes.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import stat
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
SOURCE_CURRENT_FIELDS = frozenset(
    {
        "module",
        "declarations",
        "producer_socket",
        "paper_consumers",
        "public_consumers",
        "next_analytic_obligation",
    }
)
SOURCE_DECLARATION_FIELDS = frozenset({"name", "line", "role"})
PRODUCER_SOCKET_FIELDS = frozenset(
    {"id", "status", "statement", "required_hypotheses", "not_supplied_by"}
)
CONSUMER_FIELDS = frozenset({"path", "locators"})
PUBLIC_CONSUMER_FIELDS = frozenset({"path", "locator"})
RELATED_FAMILY_REQUIRED_FIELDS = frozenset(
    {
        "route_id",
        "status",
        "source_declaration",
        "source_module",
        "source_anchor",
        "mechanism",
        "boundary",
        "next_research_route",
    }
)
RELATED_FAMILY_OPTIONAL_FIELDS = frozenset(
    {
        "comparator_declaration",
        "comparator_anchor",
        "comparator_transport_commit",
        "comparator_registration_commit",
        "solution_export",
        "solution_export_anchor",
        "supporting_declarations",
        "evidence_mode",
        "paper_consumers",
        "public_consumers",
    }
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


def read_regular_bytes(path: Path, root: Path) -> bytes:
    """Read canonical route memory through a no-follow regular-file descriptor."""
    if path_has_symlink_component(path, root):
        raise ValueError("canonical route memory source must not traverse symbolic links")
    flags = os.O_RDONLY
    flags |= getattr(os, "O_CLOEXEC", 0)
    flags |= getattr(os, "O_NONBLOCK", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise ValueError("canonical route memory source could not be opened safely") from exc
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise ValueError("canonical route memory source must be a regular file")
        chunks: list[bytes] = []
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                return b"".join(chunks)
            chunks.append(chunk)
    except OSError as exc:
        raise ValueError("canonical route memory source could not be read safely") from exc
    finally:
        os.close(descriptor)


def _validate_source_current(record: dict[str, Any]) -> None:
    """Keep source-current handoff metadata strict without widening route authority."""
    if record.get("problem") != 251:
        return
    evidence = record.get("evidence")
    if not isinstance(evidence, dict):
        raise ValueError("#251 route evidence must be an object")
    for field in ("source_declaration", "comparator_declaration", "comparator_commit"):
        value = evidence.get(field)
        if not isinstance(value, str) or not value.strip():
            raise ValueError(f"#251 route evidence {field} must be nonempty")
    if not re.fullmatch(r"[0-9a-f]{40}", evidence["comparator_commit"]):
        raise ValueError("#251 route evidence comparator_commit must be a 40-hex commit")
    source_current = evidence.get("source_current")
    if not isinstance(source_current, dict) or set(source_current) != SOURCE_CURRENT_FIELDS:
        raise ValueError("#251 route evidence source_current has an ambiguous shape")
    if source_current.get("module") != "ErdosProblems/Erdos251/PrimeGapDyadicTail.lean":
        raise ValueError("#251 source-current handoff must name PrimeGapDyadicTail.lean")
    if not isinstance(source_current.get("next_analytic_obligation"), str) or not source_current["next_analytic_obligation"].strip():
        raise ValueError("#251 source-current handoff must name its next analytic obligation")
    declarations = source_current.get("declarations")
    if not isinstance(declarations, list) or not declarations:
        raise ValueError("#251 source-current declarations must be a nonempty array")
    seen_names: set[str] = set()
    for declaration in declarations:
        if not isinstance(declaration, dict) or set(declaration) != SOURCE_DECLARATION_FIELDS:
            raise ValueError("#251 source-current declaration has an ambiguous shape")
        name = declaration.get("name")
        line = declaration.get("line")
        role = declaration.get("role")
        if not isinstance(name, str) or not name.strip() or name in seen_names:
            raise ValueError("#251 source-current declaration has an invalid or duplicate name")
        if not isinstance(line, int) or line < 1:
            raise ValueError("#251 source-current declaration line must be positive")
        if not isinstance(role, str) or not role.strip():
            raise ValueError("#251 source-current declaration role must be nonempty")
        seen_names.add(name)
    producer = source_current.get("producer_socket")
    if not isinstance(producer, dict) or set(producer) != PRODUCER_SOCKET_FIELDS:
        raise ValueError("#251 source-current producer socket has an ambiguous shape")
    if producer.get("id") != "cofinal_adjacent_small_mismatch":
        raise ValueError("#251 source-current producer socket id is not canonical")
    if producer.get("status") != "unproved":
        raise ValueError("#251 source-current producer socket must remain unproved")
    for field in ("statement",):
        if not isinstance(producer.get(field), str) or not producer[field].strip():
            raise ValueError(f"#251 producer socket {field} must be nonempty")
    for field in ("required_hypotheses", "not_supplied_by"):
        value = producer.get(field)
        if not isinstance(value, list) or not value or not all(
            isinstance(item, str) and item.strip() for item in value
        ):
            raise ValueError(f"#251 producer socket {field} must be a nonempty string array")
    for field, expected_fields in (
        ("paper_consumers", CONSUMER_FIELDS),
        ("public_consumers", PUBLIC_CONSUMER_FIELDS),
    ):
        consumers = source_current.get(field)
        if not isinstance(consumers, list) or not consumers:
            raise ValueError(f"#251 source-current {field} must be a nonempty array")
        for consumer in consumers:
            if not isinstance(consumer, dict) or set(consumer) != expected_fields:
                raise ValueError(f"#251 source-current {field} entry has an ambiguous shape")
            if not isinstance(consumer.get("path"), str) or not consumer["path"].strip():
                raise ValueError(f"#251 source-current {field} path must be nonempty")
            locator_key = "locators" if field == "paper_consumers" else "locator"
            locator = consumer.get(locator_key)
            if field == "paper_consumers":
                if not isinstance(locator, list) or not locator or not all(
                    isinstance(item, str) and item.strip() for item in locator
                ):
                    raise ValueError("#251 paper consumer locators must be a nonempty string array")
            elif not isinstance(locator, str) or not locator.strip():
                raise ValueError("#251 public consumer locator must be nonempty")


def _validate_related_families(record: dict[str, Any]) -> None:
    """Validate compact result-family evidence without making it claim authority."""
    evidence = record.get("evidence")
    if not isinstance(evidence, dict):
        raise ValueError("canonical route memory evidence must be an object")
    related = evidence.get("related_families")
    if related is None:
        return
    if not isinstance(related, dict) or not related:
        raise ValueError("canonical route memory related_families must be a nonempty object")
    problem = record["problem"]
    for family_id, family in related.items():
        if not isinstance(family_id, str) or not re.fullmatch(r"[a-z0-9][a-z0-9_]*", family_id):
            raise ValueError("canonical route memory related_families has an invalid family id")
        if not isinstance(family, dict):
            raise ValueError(
                f"canonical route memory related family {family_id} must be an object"
            )
        allowed = RELATED_FAMILY_REQUIRED_FIELDS | RELATED_FAMILY_OPTIONAL_FIELDS
        if not RELATED_FAMILY_REQUIRED_FIELDS.issubset(family) or not set(family) <= allowed:
            raise ValueError(
                f"canonical route memory related family {family_id} has an ambiguous shape"
            )
        if family.get("route_id") != f"erdos_{problem}_{family_id}":
            raise ValueError(
                f"canonical route memory related family {family_id} has a mismatched route id"
            )
        for field in (
            "route_id",
            "status",
            "source_declaration",
            "source_module",
            "mechanism",
            "boundary",
            "next_research_route",
        ):
            value = family.get(field)
            if not isinstance(value, str) or not value.strip():
                raise ValueError(
                    f"canonical route memory related family {family_id} has invalid {field}"
                )
        source_module = family["source_module"]
        source_path = Path(source_module)
        if (
            source_path.is_absolute()
            or "\\" in source_module
            or any(part in {"", ".", ".."} for part in source_module.split("/"))
        ):
            raise ValueError(
                f"canonical route memory related family {family_id} has an invalid source module"
            )
        if not isinstance(family["source_anchor"], int) or family["source_anchor"] < 1:
            raise ValueError(
                f"canonical route memory related family {family_id} has an invalid source anchor"
            )
        supporting = family.get("supporting_declarations")
        if supporting is not None and (
            not isinstance(supporting, list)
            or not supporting
            or not all(isinstance(item, str) and item.strip() for item in supporting)
        ):
            raise ValueError(
                f"canonical route memory related family {family_id} has invalid supporting declarations"
            )
        evidence_mode = family.get("evidence_mode")
        if evidence_mode is not None and (
            not isinstance(evidence_mode, str) or not evidence_mode.strip()
        ):
            raise ValueError(
                f"canonical route memory related family {family_id} has invalid evidence mode"
            )
        for field, expected_fields in (
            ("paper_consumers", CONSUMER_FIELDS),
            ("public_consumers", PUBLIC_CONSUMER_FIELDS),
        ):
            consumers = family.get(field)
            if consumers is None:
                continue
            if not isinstance(consumers, list) or not consumers:
                raise ValueError(
                    f"canonical route memory related family {family_id} {field} must be a nonempty array"
                )
            for consumer in consumers:
                if not isinstance(consumer, dict) or set(consumer) != expected_fields:
                    raise ValueError(
                        f"canonical route memory related family {family_id} {field} entry has an ambiguous shape"
                    )
                if not isinstance(consumer.get("path"), str) or not consumer["path"].strip():
                    raise ValueError(
                        f"canonical route memory related family {family_id} {field} path must be nonempty"
                    )
                locator_key = "locators" if field == "paper_consumers" else "locator"
                locator = consumer.get(locator_key)
                if field == "paper_consumers":
                    if not isinstance(locator, list) or not locator or not all(
                        isinstance(item, str) and item.strip() for item in locator
                    ):
                        raise ValueError(
                            f"canonical route memory related family {family_id} paper consumer locators must be a nonempty string array"
                        )
                elif not isinstance(locator, str) or not locator.strip():
                    raise ValueError(
                        f"canonical route memory related family {family_id} public consumer locator must be nonempty"
                    )
        comparator = family.get("comparator_declaration")
        comparator_anchor = family.get("comparator_anchor")
        if comparator is None and comparator_anchor is not None:
            raise ValueError(
                f"canonical route memory related family {family_id} has an orphan comparator anchor"
            )
        if comparator is not None and (
            not isinstance(comparator, str) or not comparator.strip()
        ):
            raise ValueError(
                f"canonical route memory related family {family_id} has invalid comparator declaration"
            )
        if comparator_anchor is not None and (
            not isinstance(comparator_anchor, int) or comparator_anchor < 1
        ):
            raise ValueError(
                f"canonical route memory related family {family_id} has invalid comparator anchor"
            )
        solution = family.get("solution_export")
        solution_anchor = family.get("solution_export_anchor")
        if solution is None and solution_anchor is not None:
            raise ValueError(
                f"canonical route memory related family {family_id} has an orphan solution anchor"
            )
        if solution is not None and (not isinstance(solution, str) or not solution.strip()):
            raise ValueError(
                f"canonical route memory related family {family_id} has invalid solution export"
            )
        if solution_anchor is not None and (
            not isinstance(solution_anchor, int) or solution_anchor < 1
        ):
            raise ValueError(
                f"canonical route memory related family {family_id} has invalid solution anchor"
            )
        for field in (
            "comparator_transport_commit",
            "comparator_registration_commit",
        ):
            value = family.get(field)
            if value is not None and (
                not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{40}", value)
            ):
                raise ValueError(
                    f"canonical route memory related family {family_id} has invalid {field}"
                )


def canonical_corpus(root: Path) -> tuple[dict[int, dict[str, Any]], str]:
    """Return canonical route records and the digest of their tracked source."""
    source = root / ROUTE_MEMORY_PATH
    if path_has_symlink_component(source, root):
        raise ValueError("canonical route memory source must not traverse symbolic links")
    try:
        payload = read_regular_bytes(source, root)
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
        _validate_source_current(record)
        _validate_related_families(record)
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
