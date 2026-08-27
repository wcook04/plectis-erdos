#!/usr/bin/env python3
"""Verify the source/currentness boundary of the #1041 L1 handoff receipt.

This checker does not prove the mathematics.  It verifies that the receipt still
names the observed mutable packet generation, that both correction result IDs
are present in that packet's currentness record, and that every named formal or
supporting artifact still has the recorded content hash and path-local commit.
If the packet owner lands a newer generation, the checker emits a typed
``reentry_required`` result instead of treating the old receipt as current.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[5]
DEFAULT_ROUTE = Path(
    "docs/formal_math/review_routes/"
    "erdos1041_l1_correction_source_result_handoff.v1.json"
)


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _path_from_root(value: str) -> Path:
    path = Path(value)
    return path if path.is_absolute() else REPO_ROOT / path


def _git_head(path: Path) -> str:
    relative = path.relative_to(REPO_ROOT)
    result = subprocess.run(
        ["git", "log", "-1", "--format=%H", "--", str(relative)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0 or not result.stdout.strip():
        raise ValueError(f"no path-local git commit for {relative}")
    return result.stdout.strip()


def _load(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        value = json.load(handle)
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {path}")
    return value


def _result(status: str, **fields: Any) -> dict[str, Any]:
    return {"schema": "erdos1041_l1_correction_handoff_check_v1", "status": status, **fields}


def _fail(message: str, **fields: Any) -> int:
    print(json.dumps(_result("failed", error=message, **fields), indent=2, sort_keys=True))
    return 1


def verify(route_path: Path) -> int:
    try:
        route = _load(route_path)
        if route.get("status") != "observed_current_negative_reentry_handoff":
            return _fail("route status is not the explicit negative re-entry handoff state")
        source_generation = route["source_generation"]
        packet_path = _path_from_root(source_generation["packet_path"])
        current_packet_sha = _sha256(packet_path)
        observed_packet_sha = source_generation["observed_packet_sha256"]
        if current_packet_sha != observed_packet_sha:
            print(
                json.dumps(
                    _result(
                        "reentry_required",
                        route_path=str(route_path.relative_to(REPO_ROOT)),
                        packet_path=str(packet_path.relative_to(REPO_ROOT)),
                        observed_packet_sha256=observed_packet_sha,
                        current_packet_sha256=current_packet_sha,
                        observed_packet_commit=source_generation["observed_packet_commit"],
                        reentry_condition="packet_generation_changed",
                    ),
                    indent=2,
                    sort_keys=True,
                )
            )
            return 2

        packet = _load(packet_path)
        currentness = packet["correction_currentness"]
        if currentness.get("status") != "current_packet_reconciles_landed_corrections":
            return _fail("packet currentness is not in the expected correction-reconciled state")
        correction_rows = {
            row["result_id"]: row for row in currentness["correction_commits"]
        }
        edges = route["result_edges"]
        edge_ids = [edge["source_result_id"] for edge in edges]
        if len(edge_ids) != len(set(edge_ids)):
            return _fail("duplicate source_result_id in receipt")
        version_delta = route.get("version_delta")
        if version_delta is None or version_delta.get("packet_result_ids") != edge_ids:
            return _fail("version delta does not preserve the ordered source-result edge list")
        if version_delta.get("current_packet_sha256") != current_packet_sha:
            return _fail("version delta packet hash disagrees with source generation")
        if version_delta.get("current_packet_commit") != source_generation["observed_packet_commit"]:
            return _fail("version delta packet commit disagrees with source generation")
        authority = route.get("mathematical_authority")
        expected_interfaces = [
            declaration
            for edge in edges
            for declaration in edge["source_declarations"]
        ]
        if authority is None or authority.get("canonical_interfaces") != expected_interfaces:
            return _fail("mathematical authority interfaces disagree with the exact source declarations")
        if authority.get("consumer") != "mathematical_closure_engine_and_packet_frontier_coevolution":
            return _fail("mathematical authority consumer is not the named downstream consumer")
        if not authority.get("open_boundary") or not authority.get("falsifier"):
            return _fail("mathematical authority must retain an open boundary and falsifier")
        if source_generation["correction_commits"] != [
            row["commit"] for row in currentness["correction_commits"]
        ]:
            return _fail("receipt correction commits disagree with packet currentness")

        checked_artifacts = 0
        for edge in edges:
            result_id = edge["source_result_id"]
            currentness_row = correction_rows.get(result_id)
            if currentness_row is None:
                return _fail(f"packet currentness lacks {result_id}")
            if edge["formal_source_commit"] != currentness_row["commit"]:
                return _fail(f"formal source commit disagrees for {result_id}")
            if edge["formal_source_path"] not in currentness_row["source_paths"]:
                return _fail(f"formal source path is absent from currentness for {result_id}")
            if edge["source_declarations"] != currentness_row["formal_declarations"]:
                return _fail(f"formal declaration list disagrees for {result_id}")

            formal_path = _path_from_root(edge["formal_source_path"])
            if _sha256(formal_path) != edge["formal_source_sha256"]:
                return _fail(f"formal source hash drift for {result_id}")
            if _git_head(formal_path) != edge["formal_source_commit"]:
                return _fail(f"formal source commit drift for {result_id}")
            formal_text = formal_path.read_text(encoding="utf-8")
            for declaration in edge["source_declarations"]:
                if declaration.rsplit(".", 1)[-1] not in formal_text:
                    return _fail(f"missing Lean declaration anchor {declaration}")

            expected_support = {
                item["path"]: item for item in edge["supporting_artifacts"]
            }
            expected_paths = set(currentness_row["source_paths"]) - {edge["formal_source_path"]}
            if set(expected_support) != expected_paths:
                return _fail(f"supporting artifact set disagrees for {result_id}")
            for artifact in edge["supporting_artifacts"]:
                artifact_path = _path_from_root(artifact["path"])
                if _sha256(artifact_path) != artifact["sha256"]:
                    return _fail(f"supporting artifact hash drift for {artifact['path']}")
                if _git_head(artifact_path) != artifact["commit"]:
                    return _fail(f"supporting artifact commit drift for {artifact['path']}")
                checked_artifacts += 1

        print(
            json.dumps(
                _result(
                    "ok",
                    route_path=str(route_path.relative_to(REPO_ROOT)),
                    packet_path=str(packet_path.relative_to(REPO_ROOT)),
                    packet_sha256=current_packet_sha,
                    packet_commit=source_generation["observed_packet_commit"],
                    checked_result_ids=edge_ids,
                    currentness_status=currentness["status"],
                    checked_formal_sources=len(edges),
                    checked_supporting_artifacts=checked_artifacts,
                    reentry_condition=route["reentry_contract"]["exact_condition"],
                ),
                indent=2,
                sort_keys=True,
            )
        )
        return 0
    except (KeyError, OSError, ValueError, json.JSONDecodeError) as exc:
        return _fail(str(exc))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--route", type=Path, default=DEFAULT_ROUTE)
    args = parser.parse_args()
    route_path = args.route if args.route.is_absolute() else REPO_ROOT / args.route
    return verify(route_path)


if __name__ == "__main__":
    sys.exit(main())
