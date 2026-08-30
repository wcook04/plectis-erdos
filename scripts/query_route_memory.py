#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build and validate a bounded, claim-safe route-memory packet.

This is deliberately an adapter over the committed navigation projections.  It
does not introduce a route registry or promote claims: ``docs/problems.json``
owns problem/module identity and ``docs/claims.json`` owns reviewed claims,
entrypoints, families, and open propositions.  A packet records those joins,
the exact source snapshot, and a deterministic resume identity so an agent can
resume work without silently crossing a problem or an edited checkout.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Mapping

import validation_singleflight as singleflight


ROOT = Path(__file__).resolve().parent.parent
SCHEMA = "erdos249257-route-memory/1"
RESUME_SCHEMA = "erdos249257-resume-state/1"
ENVIRONMENT_CONTRACT = "clean_committed_snapshot_subprocess_environment_v1"
SOURCE_FILES = (
    "docs/problems.json",
    "docs/claims.json",
    "docs/orientation.json",
)


class RouteMemoryError(ValueError):
    """A machine-readable route-memory rejection."""

    def __init__(self, code: str, detail: str) -> None:
        self.code = code
        super().__init__(f"{code}: {detail}")


def _json(path: Path) -> dict[str, Any]:
    if _path_has_symlink_component(path):
        raise RouteMemoryError("unsafe_source_path", str(path))
    if not path.is_file() or path.is_symlink():
        raise RouteMemoryError("source_missing", str(path))
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise RouteMemoryError("source_unreadable", str(path)) from exc
    if not isinstance(value, dict):
        raise RouteMemoryError("source_shape", str(path))
    return value


def _source_digests(root: Path) -> dict[str, str]:
    digests: dict[str, str] = {}
    for relative in SOURCE_FILES:
        path = root / relative
        if _path_has_symlink_component(path):
            raise RouteMemoryError("unsafe_source_path", relative)
        if not path.is_file() or path.is_symlink():
            raise RouteMemoryError("source_missing", relative)
        digests[relative] = "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()
    return digests


def _research_source_digests(
    root: Path, problem: Mapping[str, Any]
) -> dict[str, str]:
    """Fingerprint an attached public research corpus, when one exists.

    ``docs/problems.json`` is the indexed route authority, but its embedded
    digests are not enough to make a resume packet source-current on their
    own.  Include the referenced corpus files in the packet identity and
    reject an index whose published digest no longer matches its file.
    """
    research = problem.get("research_corpus")
    if research is None:
        return {}
    if not isinstance(research, Mapping):
        raise RouteMemoryError("research_source_shape", str(problem.get("problem_id")))
    files = research.get("files")
    if not isinstance(files, Mapping):
        raise RouteMemoryError("research_source_shape", "research_corpus.files")
    digests: dict[str, str] = {}
    for key, row in files.items():
        if not isinstance(row, Mapping):
            raise RouteMemoryError("research_source_shape", str(key))
        raw_path = row.get("path")
        if not isinstance(raw_path, str) or not raw_path:
            raise RouteMemoryError("research_source_missing", str(key))
        relative = Path(raw_path)
        if relative.is_absolute() or ".." in relative.parts:
            raise RouteMemoryError("invented_source_path", raw_path)
        path = root / relative
        if _path_has_symlink_component(path):
            raise RouteMemoryError("unsafe_source_path", raw_path)
        if not path.is_file() or path.is_symlink():
            raise RouteMemoryError("research_source_missing", raw_path)
        digest = "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()
        if row.get("content_digest") != digest:
            raise RouteMemoryError("research_source_stale", raw_path)
        digests[str(key)] = digest
    return digests


def _head(root: Path) -> str:
    try:
        completed = subprocess.run(
            ["git", "-C", str(root), "rev-parse", "HEAD"],
            check=True,
            capture_output=True,
            text=True,
            timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
            env=singleflight.command_environment(),
        )
    except (OSError, subprocess.SubprocessError) as exc:
        raise RouteMemoryError("git_identity_unavailable", str(exc)) from exc
    value = completed.stdout.strip()
    if not re.fullmatch(r"[0-9a-f]{40}", value):
        raise RouteMemoryError("git_identity_invalid", value or "empty HEAD")
    return value


def _canonical_digest(value: Any) -> str:
    encoded = json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


def _is_allowed_platform_alias(path: Path) -> bool:
    """Keep documented macOS temp-directory aliases usable for packets."""
    try:
        aliases = {
            Path("/var"): Path("/private/var"),
            Path("/tmp"): Path("/private/tmp"),
        }
        return path in aliases and path.resolve(strict=True) == aliases[path]
    except OSError:
        return False


def _path_has_symlink_component(path: Path) -> bool:
    """Reject packet input that could substitute bytes through a path link."""
    if path.is_symlink():
        return True
    current = Path(os.path.abspath(path.parent))
    while True:
        if current.is_symlink():
            if not _is_allowed_platform_alias(current):
                return True
            current = current.resolve(strict=True)
            continue
        if current.parent == current:
            return False
        current = current.parent


def _problem_row(root: Path, selector: str | int) -> dict[str, Any]:
    problems = _json(root / "docs" / "problems.json").get("problems", [])
    token = str(selector).strip()
    match_number = re.fullmatch(r"(?:#|erdos\s*)?(\d+)", token, re.IGNORECASE)
    for row in problems:
        if not isinstance(row, Mapping):
            continue
        if match_number and int(row.get("erdos_number", -1)) == int(match_number.group(1)):
            return dict(row)
        if token.casefold() == str(row.get("problem_id", "")).casefold():
            return dict(row)
    raise RouteMemoryError("unknown_problem", token)


def _entrypoints(root: Path) -> list[dict[str, Any]]:
    claims = _json(root / "docs" / "claims.json")
    rows = claims.get("machine_readable_paper", {}).get("entrypoints", [])
    return [dict(row) for row in rows if isinstance(row, Mapping) and row.get("id")]


def _problem_target_claim_ids(problem: Mapping[str, Any]) -> set[str]:
    """Return only claim ids explicitly owned by the problem's open registry."""
    number = problem.get("erdos_number")
    if number == 249:
        return {"erdos_249"}
    if number == 257:
        return {"universal_257"}
    return set()


def _route_for(
    root: Path, problem: Mapping[str, Any], route_id: str | None
) -> tuple[dict[str, Any] | None, list[str]]:
    rows = _entrypoints(root)
    expected_targets = _problem_target_claim_ids(problem)
    if route_id is None:
        available = sorted(
            str(row["id"])
            for row in rows
            if expected_targets.intersection(set(row.get("problem_target_claim_ids", [])))
        )
        return None, available
    route = next((row for row in rows if row.get("id") == route_id), None)
    if route is None:
        raise RouteMemoryError("invented_route", route_id)
    if route.get("route_kind") != "mathematical_programme":
        raise RouteMemoryError("route_not_problem_bound", route_id)
    route_targets = set(route.get("problem_target_claim_ids", []))
    if not expected_targets or not route_targets.intersection(expected_targets):
        raise RouteMemoryError(
            "cross_problem_route",
            f"{route_id} is not bound to {problem.get('problem_id')}",
        )
    if route_targets - expected_targets:
        raise RouteMemoryError("cross_problem_route", route_id)
    return route, sorted(
        str(row["id"])
        for row in rows
        if expected_targets.intersection(set(row.get("problem_target_claim_ids", [])))
    )


def _claims_for(root: Path, route: Mapping[str, Any] | None) -> list[dict[str, Any]]:
    if route is None:
        return []
    claims = _json(root / "docs" / "claims.json")
    index = {
        str(row.get("id")): row
        for row in claims.get("claims", [])
        if isinstance(row, Mapping) and row.get("id")
    }
    ids: list[str] = []
    for claim_id in [*route.get("problem_target_claim_ids", []), *route.get("core_claim_ids", [])]:
        if claim_id not in ids:
            ids.append(str(claim_id))
    result: list[dict[str, Any]] = []
    module_digests: dict[str, str] = {}
    for claim_id in ids:
        row = index.get(claim_id)
        if row is None:
            raise RouteMemoryError("invented_claim_reference", claim_id)
        declarations: list[dict[str, Any]] = []
        for declaration in row.get("declarations", []):
            if not isinstance(declaration, Mapping):
                raise RouteMemoryError("invented_declaration_reference", claim_id)
            module = str(declaration.get("module", ""))
            if not module:
                raise RouteMemoryError("invented_declaration_reference", claim_id)
            if module not in module_digests:
                module_digests[module] = _safe_module_digest(root, module)
            declarations.append(
                {
                    **dict(declaration),
                    "source_digest": module_digests[module],
                }
            )
        result.append(
            {
                "id": claim_id,
                "status": row.get("status"),
                "paper_label": row.get("paper_label"),
                "declarations": declarations,
                "remaining_open_proposition_ids": list(
                    row.get("remaining_open_proposition_ids", [])
                ),
            }
        )
    return result


def _families_for(root: Path, claim_ids: set[str]) -> list[dict[str, Any]]:
    claims = _json(root / "docs" / "claims.json")
    families = claims.get("machine_readable_paper", {}).get("publication_assembly", {}).get(
        "contribution_families", []
    )
    result: list[dict[str, Any]] = []
    for family in families:
        if not isinstance(family, Mapping):
            continue
        selected = [str(value) for value in family.get("claim_ids", []) if value in claim_ids]
        if selected:
            result.append(
                {
                    "id": family.get("id"),
                    "claim_ids": selected,
                    "source_route": family.get("source_route"),
                    "view_decision": family.get("view_decision"),
                }
            )
    return result


def _module_refs(problem: Mapping[str, Any]) -> list[dict[str, Any]]:
    refs: list[dict[str, Any]] = []
    for module in problem.get("modules", []):
        if not isinstance(module, Mapping):
            continue
        refs.append(
            {
                "module": module.get("module"),
                "path": module.get("path"),
                "content_digest": module.get("content_digest"),
                "declaration_count": module.get("declaration_count"),
            }
        )
    return refs


def _safe_module_digest(root: Path, module: str) -> str:
    relative = Path(module)
    if relative.is_absolute() or ".." in relative.parts:
        raise RouteMemoryError("invented_source_path", module)
    path = root / relative
    if _path_has_symlink_component(path):
        raise RouteMemoryError("unsafe_source_path", module)
    if not path.is_file() or path.is_symlink():
        raise RouteMemoryError("declaration_source_missing", module)
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def _problem_module_owners(root: Path) -> dict[str, set[str]]:
    problems = _json(root / "docs" / "problems.json")
    owners: dict[str, set[str]] = {}
    for problem in problems.get("problems", []):
        if not isinstance(problem, Mapping):
            continue
        problem_id = str(problem.get("problem_id"))
        for module in problem.get("modules", []):
            if isinstance(module, Mapping) and module.get("path"):
                owners.setdefault(str(module["path"]), set()).add(problem_id)
    return owners


def _compact_open_rows(
    problem: Mapping[str, Any], route: Mapping[str, Any] | None, *, root: Path
) -> list[dict[str, Any]]:
    rows = [
        {
            "id": row.get("id"),
            "statement": row.get("statement"),
            "source": "docs/problems.json::problems[].open_obligations",
        }
        for row in problem.get("open_obligations", [])
        if isinstance(row, Mapping)
    ]
    if route is not None:
        claims = _json(root / "docs" / "claims.json")
        by_id = {
            row.get("id"): row
            for row in claims.get("remaining_open_propositions", [])
            if isinstance(row, Mapping)
        }
        for open_id in route.get("remaining_open_proposition_ids", []):
            row = by_id.get(open_id)
            if row is not None and not any(item["id"] == open_id for item in rows):
                rows.append(
                    {
                        "id": open_id,
                        "statement": row.get("statement"),
                        "source": "docs/claims.json::remaining_open_propositions",
                    }
                )
    return rows


def build_packet(
    problem_selector: str | int,
    route_id: str | None = None,
    *,
    root: Path = ROOT,
) -> dict[str, Any]:
    problem = _problem_row(root, problem_selector)
    route, available_routes = _route_for(root, problem, route_id)
    claim_refs = _claims_for(root, route)
    claim_ids = {row["id"] for row in claim_refs}
    family_refs = _families_for(root, claim_ids)
    module_refs = _module_refs(problem)
    research_source_digests = _research_source_digests(root, problem)
    consulted = [str(route["id"])] if route is not None else []
    related = [str(value) for value in route.get("related_route_ids", [])] if route else []
    route_relationships = [
        {"from": str(route["id"]), "to": related_id, "relation": "related_route"}
        for related_id in related
    ]
    source_digests = _source_digests(root)
    source_commit = _head(root)
    selector = {
        "problem_id": problem["problem_id"],
        "route_id": route["id"] if route else None,
    }
    identity_material = {
        "selector": selector,
        "source_commit": source_commit,
        "source_digests": source_digests,
        "consulted_route_ids": consulted,
        "related_route_ids": related,
        "claim_ids": [row["id"] for row in claim_refs],
        "family_ids": [row["id"] for row in family_refs],
        "module_paths": [row["path"] for row in module_refs],
        "research_source_digests": research_source_digests,
    }
    state_id = _canonical_digest(identity_material)
    packet = {
        "schema": SCHEMA,
        "kind": "route_memory",
        "route_memory_id": f"{problem['problem_id']}:{route['id'] if route else 'unrouted'}",
        "authority_posture": "derived_navigation_resume_state_not_claim_or_proof_authority",
        "selector": selector,
        "problem": {
            "problem_id": problem["problem_id"],
            "erdos_number": problem["erdos_number"],
            "short_title": problem["short_title"],
            "status": problem["status"],
            "question": problem["question"],
            "library_root": problem["library_root"],
            "claim_registry_status": problem["claim_registry_status"],
        },
        "route": {
            "id": route["id"] if route else None,
            "title": route.get("title") if route else None,
            "claim_ceiling": route.get("claim_ceiling") if route else None,
            "available_route_ids": available_routes,
        },
        "consulted_route_ids": consulted,
        "related_route_ids": related,
        "route_relationships": route_relationships,
        "claims": claim_refs,
        "families": family_refs,
        "modules": module_refs,
        "research_corpus": problem.get("research_corpus"),
        "note": problem.get("note"),
        "paper": problem.get("paper"),
        "open_obligations": _compact_open_rows(problem, route, root=root),
        "source_snapshot": {
            "commit": source_commit,
            "digests": source_digests,
            "tracked_sources": list(SOURCE_FILES),
            "research_corpus_digests": research_source_digests,
        },
        "resume_state": {
            "schema": RESUME_SCHEMA,
            "state_id": state_id,
            "selector": selector,
            "source_commit": source_commit,
            "source_digests": source_digests,
            "research_corpus_digests": research_source_digests,
        },
        "boundaries": {
            "claim_authority": "docs/claims.json",
            "problem_authority": "docs/problems.json",
            "navigation_authority": "docs/orientation.json",
            "proof_authority": "pinned Lean kernel over committed sources",
            "promotion_rule": "This packet never changes claim status or promotes a declaration.",
        },
    }
    packet["packet_digest"] = _canonical_digest(packet)
    return packet


def _reject_if(condition: bool, code: str, detail: str) -> None:
    if condition:
        raise RouteMemoryError(code, detail)


def validate_packet(packet: Mapping[str, Any], *, root: Path = ROOT) -> dict[str, Any]:
    if not isinstance(packet, Mapping) or packet.get("schema") != SCHEMA:
        raise RouteMemoryError("schema_mismatch", str(packet.get("schema")))
    selector = packet.get("selector")
    if not isinstance(selector, Mapping) or not selector.get("problem_id"):
        raise RouteMemoryError("selector_missing", "selector.problem_id")
    expected = build_packet(
        str(selector["problem_id"]),
        str(selector["route_id"]) if selector.get("route_id") else None,
        root=root,
    )
    snapshot = packet.get("source_snapshot")
    _reject_if(not isinstance(snapshot, Mapping), "source_snapshot_missing", "source_snapshot")
    if snapshot.get("commit") != expected["source_snapshot"]["commit"]:
        raise RouteMemoryError("stale_source_snapshot", "source commit differs from HEAD")
    if snapshot.get("digests") != expected["source_snapshot"]["digests"]:
        raise RouteMemoryError("stale_source_snapshot", "source digest differs from checkout")
    if snapshot.get("research_corpus_digests") != expected["source_snapshot"][
        "research_corpus_digests"
    ]:
        raise RouteMemoryError(
            "stale_source_snapshot", "research corpus digest differs from checkout"
        )
    if snapshot.get("tracked_sources") != expected["source_snapshot"][
        "tracked_sources"
    ]:
        raise RouteMemoryError(
            "stale_source_snapshot", "tracked source set differs from checkout"
        )
    expected_claims = {row["id"]: row for row in expected["claims"]}
    module_owners = _problem_module_owners(root)
    for claim in packet.get("claims", []):
        if not isinstance(claim, Mapping) or claim.get("id") not in expected_claims:
            raise RouteMemoryError("invented_reference", "claim")
        expected_declarations = {
            (row.get("name"), row.get("module"), row.get("line"), row.get("source_digest"))
            for row in expected_claims[claim["id"]].get("declarations", [])
        }
        for declaration in claim.get("declarations", []):
            if not isinstance(declaration, Mapping):
                raise RouteMemoryError("invented_declaration_reference", str(claim["id"]))
            key = (
                declaration.get("name"),
                declaration.get("module"),
                declaration.get("line"),
                declaration.get("source_digest"),
            )
            if key in expected_declarations:
                continue
            owners = module_owners.get(str(declaration.get("module")), set())
            if owners and expected["problem"]["problem_id"] not in owners:
                raise RouteMemoryError(
                    "cross_problem_declaration", str(declaration.get("module"))
                )
            raise RouteMemoryError("invented_declaration_reference", str(claim["id"]))
    critical = (
        "route_memory_id",
        "selector",
        "problem",
        "route",
        "consulted_route_ids",
        "related_route_ids",
        "route_relationships",
        "claims",
        "families",
        "modules",
        "research_corpus",
        "note",
        "paper",
        "open_obligations",
        "boundaries",
    )
    for field in critical:
        if packet.get(field) != expected.get(field):
            if field == "route":
                raise RouteMemoryError("cross_problem_route", "route binding differs from selector")
            if field in {"claims", "families", "modules"}:
                raise RouteMemoryError("invented_reference", field)
            raise RouteMemoryError("packet_mismatch", field)
    resume = packet.get("resume_state")
    _reject_if(not isinstance(resume, Mapping), "resume_state_missing", "resume_state")
    if resume != expected["resume_state"]:
        raise RouteMemoryError("resume_state_mismatch", "resume identity is not reproducible")
    if packet.get("packet_digest") != _canonical_digest(
        {key: value for key, value in packet.items() if key != "packet_digest"}
    ):
        raise RouteMemoryError("packet_digest_mismatch", "packet content changed")
    return dict(packet)


def _card(packet: Mapping[str, Any]) -> str:
    problem = packet["problem"]
    route = packet["route"]
    rows = [
        f"route-memory {packet['route_memory_id']} | problem #{problem['erdos_number']}",
        f"route={route['id'] or 'unrouted'} claims={len(packet['claims'])} families={len(packet['families'])}",
    ]
    if route["id"] is None:
        available = route.get("available_route_ids", [])
        if not isinstance(available, list):
            available = []
        rows.append(f"available_routes={','.join(str(value) for value in available) or 'none'}")
    else:
        related = packet.get("related_route_ids", [])
        if isinstance(related, list) and related:
            rows.append(f"related_routes={','.join(str(value) for value in related)}")
    rows.append(
        f"resume={packet['resume_state']['state_id']} commit={packet['source_snapshot']['commit']}"
    )
    return "\n".join(rows)


def _load_packet(argument: str) -> dict[str, Any]:
    if argument == "-":
        value = json.load(sys.stdin)
    else:
        path = Path(argument)
        if _path_has_symlink_component(path):
            raise RouteMemoryError("unsafe_input_path", argument)
        value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise RouteMemoryError("packet_shape", argument)
    return value


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--problem", metavar="ID_OR_NUMBER")
    group.add_argument("--validate", metavar="PACKET_JSON")
    parser.add_argument("--route", metavar="ROUTE_ID")
    parser.add_argument("--format", choices=("json", "card"), default="json")
    args = parser.parse_args(argv)
    try:
        if args.validate and args.route:
            raise RouteMemoryError(
                "validate_route_override",
                "--route cannot be combined with --validate; packet selector is authoritative",
            )
        packet = (
            validate_packet(_load_packet(args.validate))
            if args.validate
            else build_packet(args.problem, args.route)
        )
    except (OSError, json.JSONDecodeError, RouteMemoryError) as exc:
        print(f"route-memory error: {exc}", file=sys.stderr)
        return 2
    if args.format == "card":
        print(_card(packet))
    else:
        print(json.dumps(packet, ensure_ascii=False, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
