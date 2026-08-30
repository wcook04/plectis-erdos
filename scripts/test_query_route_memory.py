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
import validation_singleflight as singleflight


ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts" / "query_route_memory.py"
PROBLEMS = (68, 243, 249, 251, 257, 269, 1041, 1049)


def require(condition: bool, message: str) -> None:
    """Keep CLI environment assertions active when Python is run with -O."""
    if not condition:
        raise AssertionError(message)


def assert_rejected(packet: dict, code: str) -> None:
    try:
        route_memory.validate_packet(packet)
    except route_memory.RouteMemoryError as exc:
        require(exc.code == code, f"expected {code}, got {exc.code}: {exc}")
        return
    raise AssertionError(f"mutation escaped: {code}")


def run_cli(
    *args: str,
    input_text: str | None = None,
    optimized: bool = False,
    check: bool = False,
) -> subprocess.CompletedProcess[str]:
    """Run route-memory CLI checks without ambient process state or hangs."""
    executable = [sys.executable]
    if optimized:
        executable.append("-O")
    return subprocess.run(
        [*executable, str(SCRIPT), *args],
        cwd=ROOT,
        input=input_text,
        check=check,
        capture_output=True,
        text=True,
        env=singleflight.command_environment(),
        timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
    )


def check_cli_environment() -> None:
    """Prove route-memory CLI fixtures ignore hostile inherited selectors."""
    hostile_environment = {
        "GIT_DIR": str(ROOT / "not-a-git-directory"),
        "GIT_NAMESPACE": "hostile-namespace",
        "GIT_REPLACE_REF_BASE": "refs/replace/hostile/",
        "PYTHONPATH": "/private/wrong-python-path",
        "LC_ALL": "C",
        "LANG": "C",
        "PATH": "/private/wrong-bin",
    }
    completed = subprocess.CompletedProcess([], 0, stdout="{}", stderr="")
    with patch.dict(os.environ, hostile_environment, clear=False):
        with patch.object(subprocess, "run", return_value=completed) as run:
            observed = run_cli("--problem", "249")

    require(observed is completed, "route-memory CLI result was not returned")
    require(len(run.call_args_list) == 1, "route-memory CLI was not exercised")
    kwargs = run.call_args.kwargs
    sanitized = kwargs["env"]
    for key in (
        "GIT_DIR",
        "GIT_NAMESPACE",
        "GIT_REPLACE_REF_BASE",
        "PYTHONPATH",
    ):
        require(key not in sanitized, f"ambient {key} leaked into route-memory CLI")
    require(sanitized["LC_ALL"] == "C.UTF-8", "canonical locale missing")
    require(sanitized["LANG"] == "C.UTF-8", "canonical LANG missing")
    require(sanitized["PATH"] == os.defpath, "ambient PATH leaked into route-memory CLI")
    require(
        kwargs["timeout"] == singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
        "route-memory CLI timeout drifted",
    )


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
    require(set(packets) == set(PROBLEMS), "route-memory packet set drifted")
    for number, packet in packets.items():
        require(
            packet["problem"]["erdos_number"] == number,
            f"route-memory problem identity drifted for #{number}",
        )
        require(
            packet["selector"]["problem_id"] == f"erdos_{number}",
            f"route-memory selector drifted for #{number}",
        )
        require(
            packet["resume_state"]["source_commit"] == packet["source_snapshot"]["commit"],
            f"route-memory source commit drifted for #{number}",
        )
        require(
            packet["resume_state"]["state_id"].startswith("sha256:"),
            f"route-memory state digest is malformed for #{number}",
        )
        require(
            packet["source_snapshot"]["tracked_sources"] == list(route_memory.SOURCE_FILES),
            f"route-memory tracked source set drifted for #{number}",
        )
        require(
            route_memory.validate_packet(packet)["packet_digest"] == packet["packet_digest"],
            f"route-memory packet digest is stale for #{number}",
        )
    research_packet = packets[1041]
    research = research_packet["research_corpus"]
    require(
        research["directory"] == "research_corpus/Erdos1041",
        "#1041 research corpus route drifted",
    )
    require(
        research["strongest_result_summary"]["result_count"] == 35,
        "#1041 strongest-result count drifted",
    )
    require(
        research["authority_posture"].startswith("public_safe_research_evidence"),
        "#1041 research authority posture drifted",
    )
    require(
        set(research_packet["source_snapshot"]["research_corpus_digests"]) == {
            "frontier",
            "strongest_results",
            "manifest",
            "checkpoint",
        },
        "#1041 research corpus digest set drifted",
    )
    require(
        research_packet["resume_state"]["research_corpus_digests"]
        == research_packet["source_snapshot"]["research_corpus_digests"],
        "#1041 resume digest set is not source-bound",
    )
    routed_declarations = [
        declaration
        for claim in route_memory.build_packet("249", "erdos249_certificate_story")["claims"]
        for declaration in claim["declarations"]
    ]
    require(routed_declarations, "routed #249 packet has no declarations")
    require(
        all(row["source_digest"].startswith("sha256:") for row in routed_declarations),
        "routed #249 declaration digest is malformed",
    )

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
    stale_sources = copy.deepcopy(packets[249])
    stale_sources["source_snapshot"]["tracked_sources"] = ["docs/claims.json"]
    assert_rejected(stale_sources, "stale_source_snapshot")
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
    check_cli_environment()
    completed = run_cli(
        "--problem", "249", "--route", "erdos249_certificate_story", check=True
    )
    cli_packet = json.loads(completed.stdout)
    require(
        route_memory.validate_packet(cli_packet)["route"]["id"]
        == "erdos249_certificate_story",
        "normal CLI route identity drifted",
    )
    cli_validate = run_cli(
        "--validate", "-", input_text=json.dumps(cli_packet)
    )
    require(cli_validate.returncode == 0, cli_validate.stderr)
    require(
        json.loads(cli_validate.stdout)["resume_state"] == cli_packet["resume_state"],
        "normal CLI validation changed resume state",
    )
    stale_cli = copy.deepcopy(cli_packet)
    stale_cli["source_snapshot"]["commit"] = "0" * 40
    stale_result = run_cli(
        "--validate", "-", input_text=json.dumps(stale_cli)
    )
    require(stale_result.returncode == 2, "stale CLI packet was accepted")
    require(stale_result.stdout == "", "stale CLI packet emitted a success payload")
    require(
        "stale_source_snapshot" in stale_result.stderr,
        "stale CLI packet omitted its rejection code",
    )
    # A packet path must not be substituted through a symlink; stdin remains
    # available for ordinary pipelines and this guard protects file-based CLI
    # intake from reading an unreviewed target.
    import tempfile

    with tempfile.TemporaryDirectory(prefix="route-memory-link-") as temp_dir:
        packet_path = Path(temp_dir) / "packet.json"
        link_path = Path(temp_dir) / "packet-link.json"
        # The path guard must run before packet parsing, so an intentionally
        # malformed payload keeps this adversarial check independent of a
        # sibling commit moving HEAD between packet generation and intake.
        packet_path.write_text("{}", encoding="utf-8")
        link_path.symlink_to(packet_path)
        linked = run_cli("--validate", str(link_path))
        require(linked.returncode == 2, "symlinked packet path was accepted")
        require(linked.stdout == "", "symlinked packet path emitted a payload")
        require(
            "unsafe_input_path" in linked.stderr,
            "symlinked packet path omitted its rejection code",
        )
    with tempfile.TemporaryDirectory(prefix="route-memory-module-link-") as temp_dir:
        module_root = Path(temp_dir)
        outside = module_root / "outside"
        outside.mkdir()
        (outside / "Module.lean").write_text("external", encoding="utf-8")
        (module_root / "Erdos249257").symlink_to(outside, target_is_directory=True)
        try:
            route_memory._safe_module_digest(
                module_root, "Erdos249257/Module.lean"
            )
        except route_memory.RouteMemoryError as exc:
            require(
                exc.code == "unsafe_source_path",
                f"nested module symlink returned {exc.code}",
            )
        else:
            raise AssertionError("nested module symlink was accepted")
    with tempfile.TemporaryDirectory(prefix="route-memory-research-link-") as temp_dir:
        research_root = Path(temp_dir)
        outside = research_root / "outside"
        outside.mkdir()
        frontier = outside / "FRONTIER.md"
        frontier.write_text("external", encoding="utf-8")
        digest = "sha256:" + route_memory.hashlib.sha256(
            frontier.read_bytes()
        ).hexdigest()
        (research_root / "research_corpus").symlink_to(
            outside, target_is_directory=True
        )
        research_problem = {
            "problem_id": "erdos_1041",
            "research_corpus": {
                "files": {
                    "frontier": {
                        "path": "research_corpus/FRONTIER.md",
                        "content_digest": digest,
                    }
                }
            },
        }
        try:
            route_memory._research_source_digests(research_root, research_problem)
        except route_memory.RouteMemoryError as exc:
            require(
                exc.code == "unsafe_source_path",
                f"nested research symlink returned {exc.code}",
            )
        else:
            raise AssertionError("nested research symlink was accepted")
    optimized = run_cli(
        "--problem", "257", "--format", "card", optimized=True, check=True
    )
    require(
        optimized.stdout.startswith("route-memory erdos_257:unrouted | problem #257"),
        "optimized CLI card output drifted",
    )
    require(
        "available_routes=boolean_mobius_constraints,erdos257_half_story,half_carry_compactness_programme,structured_support_families"
        in optimized.stdout,
        "unrouted CLI card omitted canonical route choices",
    )
    print("query_route_memory: 8 selectors, stale/cross-problem/invented guards, CLI normal/-O PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
