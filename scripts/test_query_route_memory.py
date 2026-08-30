#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial tests for the claim-safe route-memory query consumer."""

from __future__ import annotations

import copy
import json
import os
import subprocess
import sys
from pathlib import Path
from unittest.mock import patch

import query_route_memory as route_memory


ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts" / "query_route_memory.py"
PROBLEMS = (68, 243, 249, 251, 257, 269, 1041, 1049)


def assert_rejected(packet: dict, code: str) -> None:
    try:
        route_memory.validate_packet(packet)
    except route_memory.RouteMemoryError as exc:
        assert exc.code == code, f"expected {code}, got {exc.code}: {exc}"
        return
    raise AssertionError(f"mutation escaped: {code}")


def main() -> int:
    hostile = {
        "GIT_DIR": str(ROOT / "not-a-git-directory"),
        "GIT_NAMESPACE": "hostile-namespace",
        "GIT_REPLACE_REF_BASE": "refs/replace/hostile/",
    }
    with patch.dict(os.environ, hostile, clear=False):
        packets = {
            number: route_memory.build_packet(str(number)) for number in PROBLEMS
        }
    assert set(packets) == set(PROBLEMS)
    for number, packet in packets.items():
        assert packet["problem"]["erdos_number"] == number
        assert packet["selector"]["problem_id"] == f"erdos_{number}"
        assert packet["resume_state"]["source_commit"] == packet["source_snapshot"]["commit"]
        assert packet["resume_state"]["state_id"].startswith("sha256:")
        assert packet["source_snapshot"]["tracked_sources"] == list(route_memory.SOURCE_FILES)
        assert route_memory.validate_packet(packet)["packet_digest"] == packet["packet_digest"]
    research_packet = packets[1041]
    research = research_packet["research_corpus"]
    assert research["directory"] == "research_corpus/Erdos1041"
    assert research["strongest_result_summary"]["result_count"] == 35
    assert research["authority_posture"].startswith("public_safe_research_evidence")
    assert set(research_packet["source_snapshot"]["research_corpus_digests"]) == {
        "frontier",
        "strongest_results",
        "manifest",
        "checkpoint",
    }
    assert research_packet["resume_state"]["research_corpus_digests"] == research_packet[
        "source_snapshot"
    ]["research_corpus_digests"]
    routed_declarations = [
        declaration
        for claim in route_memory.build_packet("249", "erdos249_certificate_story")["claims"]
        for declaration in claim["declarations"]
    ]
    assert routed_declarations
    assert all(row["source_digest"].startswith("sha256:") for row in routed_declarations)

    # A route for #257 must never be accepted under #249, even though both
    # routes are valid navigation entries in the same claims projection.
    assert_rejected(
        copy.deepcopy(packets[249])
        | {"selector": {"problem_id": "erdos_249", "route_id": "erdos257_half_story"}},
        "cross_problem_route",
    )
    # The validator catches an invented route before it can become resumable.
    invented = copy.deepcopy(packets[249])
    invented["selector"]["route_id"] = "route_not_in_claims"
    assert_rejected(invented, "invented_route")
    # A changed source digest is a stale sidecar, not a new identity.
    stale = copy.deepcopy(packets[249])
    stale["source_snapshot"]["digests"]["docs/claims.json"] = "sha256:" + "0" * 64
    assert_rejected(stale, "stale_source_snapshot")
    stale_research = copy.deepcopy(research_packet)
    stale_research["source_snapshot"]["research_corpus_digests"]["frontier"] = (
        "sha256:" + "0" * 64
    )
    assert_rejected(stale_research, "stale_source_snapshot")
    # A fabricated claim/declaration reference cannot be smuggled into a
    # packet by merely updating its digest fields.
    routed = route_memory.build_packet("249", "erdos249_certificate_story")
    invented_claim = copy.deepcopy(routed)
    invented_claim["claims"][0]["id"] = "claim_made_up"
    assert_rejected(invented_claim, "invented_reference")
    cross_declaration = copy.deepcopy(routed)
    cross_declaration["claims"][1]["declarations"][0]["module"] = (
        "ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean"
    )
    assert_rejected(cross_declaration, "cross_problem_declaration")
    cross_route = copy.deepcopy(routed)
    cross_route["consulted_route_ids"] = ["erdos257_half_story"]
    assert_rejected(cross_route, "packet_mismatch")

    # Exercise the real CLI, including the optimized interpreter path.
    completed = subprocess.run(
        [sys.executable, str(SCRIPT), "--problem", "249", "--route", "erdos249_certificate_story"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    cli_packet = json.loads(completed.stdout)
    assert route_memory.validate_packet(cli_packet)["route"]["id"] == "erdos249_certificate_story"
    cli_validate = subprocess.run(
        [sys.executable, str(SCRIPT), "--validate", "-"],
        cwd=ROOT,
        input=json.dumps(cli_packet),
        check=False,
        capture_output=True,
        text=True,
    )
    assert cli_validate.returncode == 0, cli_validate.stderr
    assert json.loads(cli_validate.stdout)["resume_state"] == cli_packet["resume_state"]
    stale_cli = copy.deepcopy(cli_packet)
    stale_cli["source_snapshot"]["commit"] = "0" * 40
    stale_result = subprocess.run(
        [sys.executable, str(SCRIPT), "--validate", "-"],
        cwd=ROOT,
        input=json.dumps(stale_cli),
        check=False,
        capture_output=True,
        text=True,
    )
    assert stale_result.returncode == 2
    assert stale_result.stdout == ""
    assert "stale_source_snapshot" in stale_result.stderr
    optimized = subprocess.run(
        [sys.executable, "-O", str(SCRIPT), "--problem", "257", "--format", "card"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    assert optimized.stdout.startswith("route-memory erdos_257:unrouted | problem #257")
    print("query_route_memory: 8 selectors, stale/cross-problem/invented guards, CLI normal/-O PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
