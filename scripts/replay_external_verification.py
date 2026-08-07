#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Replay one bounded Comparator interface outside GitHub Actions.

The reviewer supplies the full commit and tree from an immutable release
manifest.  This script fetches exactly that commit into a disposable checkout,
builds the three pinned Comparator tools, runs one positive statement comparison
and its deliberate one-statement mismatch, and writes an independent receipt.
It refuses branch names, synthetic pull-request merge commits, insecure
non-systemd fallback execution, and any source-tree mismatch.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import platform
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
CONTRACT_RELATIVE = Path("verification/external-verification-release-contract.json")
SCHEMA = "erdos-external-verification-independent-replay-receipt/1"
FULL_SHA_RE = re.compile(r"[0-9a-f]{40}")
SYNTHETIC_MERGE_MESSAGE_RE = re.compile(
    r"Merge [0-9a-f]{40} into [0-9a-f]{40}(?:\n|$)"
)
LOG_TAIL_BYTES = 12_000


class ReplayError(RuntimeError):
    """Raised when exact replay cannot proceed or does not verify."""


def sha256_bytes(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    if not path.is_file():
        raise ReplayError(f"required replay input is absent: {path}")
    return sha256_bytes(path.read_bytes())


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ReplayError(f"could not read JSON {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise ReplayError(f"JSON root must be an object: {path}")
    return value


def full_sha(value: str, field: str) -> str:
    if FULL_SHA_RE.fullmatch(value) is None:
        raise ReplayError(f"{field} must be a full lowercase Git id")
    return value


def run(
    argv: list[str],
    *,
    cwd: Path,
    timeout: int | None = None,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        argv,
        cwd=cwd,
        env=env,
        capture_output=True,
        text=True,
        check=False,
        timeout=timeout,
    )


def checked_run(
    argv: list[str],
    *,
    cwd: Path,
    timeout: int | None = None,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    completed = run(argv, cwd=cwd, timeout=timeout, env=env)
    if completed.returncode != 0:
        detail = (completed.stderr or completed.stdout).strip()
        raise ReplayError(f"command failed ({completed.returncode}): {' '.join(argv)}\n{detail}")
    return completed


def git(root: Path, *args: str) -> str:
    return checked_run(["git", *args], cwd=root).stdout.strip()


def bounded_tail(text: str) -> str:
    return text.encode("utf-8", errors="replace")[-LOG_TAIL_BYTES:].decode(
        "utf-8", errors="replace"
    )


def load_contract(root: Path) -> dict[str, Any]:
    value = load_json(root / CONTRACT_RELATIVE)
    if value.get("schema") != "erdos-external-verification-release-contract/1":
        raise ReplayError("unsupported external-verification release contract")
    pins = value.get("toolchain")
    if not isinstance(pins, dict) or set(pins) != {
        "comparator",
        "lean4export",
        "landrun",
    }:
        raise ReplayError("release contract has malformed tool pins")
    for name, revision in pins.items():
        full_sha(revision, f"toolchain.{name}")
    replay = value.get("replay")
    if not isinstance(replay, dict):
        raise ReplayError("release contract lacks the replay unit")
    return value


def check_programs() -> None:
    missing = [
        program
        for program in ("git", "lake", "go", "systemctl", "systemd-run", "timeout")
        if shutil.which(program) is None
    ]
    if missing:
        raise ReplayError("missing required executable(s): " + ", ".join(missing))
    if platform.system() != "Linux":
        raise ReplayError("secure Comparator replay requires Linux with systemd")


def prepare_source(
    workspace: Path,
    repository: str,
    source_commit: str,
    source_tree: str,
) -> Path:
    source = workspace / "source"
    source.mkdir()
    checked_run(["git", "init", "-q"], cwd=source)
    checked_run(["git", "remote", "add", "origin", repository], cwd=source)
    checked_run(
        ["git", "fetch", "--depth=1", "--no-tags", "origin", source_commit],
        cwd=source,
        timeout=300,
    )
    checked_run(["git", "checkout", "--detach", "--quiet", "FETCH_HEAD"], cwd=source)
    observed_commit = git(source, "rev-parse", "HEAD^{commit}")
    observed_tree = git(source, "rev-parse", "HEAD^{tree}")
    if observed_commit != source_commit:
        raise ReplayError(f"fetched commit {observed_commit} != requested {source_commit}")
    if observed_tree != source_tree:
        raise ReplayError(f"fetched tree {observed_tree} != requested {source_tree}")
    message = git(source, "show", "-s", "--format=%B", source_commit)
    if SYNTHETIC_MERGE_MESSAGE_RE.match(message):
        raise ReplayError("GitHub pull-request synthetic merge commit is forbidden")
    return source


def prepare_tools(
    workspace: Path, contract: dict[str, Any]
) -> tuple[dict[str, Path], dict[str, str]]:
    pins = contract["toolchain"]
    comparator = workspace / "comparator"
    lean4export = workspace / "lean4export"
    landrun_source = workspace / "landrun-source"
    observed_revisions = {}
    for name, repository, revision, destination in (
        (
            "comparator",
            "https://github.com/leanprover/comparator.git",
            pins["comparator"],
            comparator,
        ),
        (
            "lean4export",
            "https://github.com/leanprover/lean4export.git",
            pins["lean4export"],
            lean4export,
        ),
        (
            "landrun",
            "https://github.com/zouuup/landrun.git",
            pins["landrun"],
            landrun_source,
        ),
    ):
        checked_run(
            ["git", "clone", "--filter=blob:none", "--no-checkout", repository, str(destination)],
            cwd=workspace,
            timeout=300,
        )
        checked_run(["git", "checkout", "--detach", revision], cwd=destination)
        observed_revisions[name] = git(destination, "rev-parse", "HEAD")
        if observed_revisions[name] != revision:
            raise ReplayError(f"tool checkout does not match pin: {destination.name}")
    checked_run(["lake", "build", "comparator"], cwd=comparator, timeout=1200)
    checked_run(["lake", "build", "lean4export"], cwd=lean4export, timeout=1200)
    landrun = workspace / "landrun"
    checked_run(
        ["go", "build", "-o", str(landrun), "cmd/landrun/main.go"],
        cwd=landrun_source,
        timeout=600,
    )
    return (
        {
            "comparator": comparator / ".lake/build/bin/comparator",
            "lean4export": lean4export / ".lake/build/bin/lean4export",
            "landrun": landrun,
        },
        observed_revisions,
    )


def sandbox_mode(source: Path) -> str:
    user = run(["systemctl", "--user", "show-environment"], cwd=source)
    if user.returncode == 0:
        return "user-manager"
    system = run(["sudo", "-n", "systemctl", "show-environment"], cwd=source)
    if system.returncode == 0:
        return "system-manager-nonprivileged-unit"
    raise ReplayError("no usable systemd manager; refusing an insecure fallback")


def comparator_command(
    *,
    source: Path,
    tools: dict[str, Path],
    mode: str,
    config: str,
) -> tuple[list[str], dict[str, str]]:
    environment = dict(os.environ)
    environment["COMPARATOR_LANDRUN"] = str(tools["landrun"])
    environment["COMPARATOR_LEAN4EXPORT"] = str(tools["lean4export"])
    common = [
        "--property=RestrictAddressFamilies=~AF_UNIX",
        "--pipe",
        "-E",
        f"PATH={environment['PATH']}",
        "-E",
        f"COMPARATOR_LANDRUN={tools['landrun']}",
        "-E",
        f"COMPARATOR_LEAN4EXPORT={tools['lean4export']}",
        f"--working-directory={source}",
        "--",
        "lake",
        "env",
        str(tools["comparator"]),
        config,
    ]
    if mode == "user-manager":
        command = ["timeout", "20m", "systemd-run", "--user", *common]
    else:
        command = [
            "timeout",
            "20m",
            "sudo",
            "-n",
            "systemd-run",
            f"--uid={os.getuid()}",
            f"--gid={os.getgid()}",
            *common,
        ]
    return command, environment


def result_row(completed: subprocess.CompletedProcess[str]) -> dict[str, Any]:
    combined = completed.stdout + completed.stderr
    return {
        "exit_code": completed.returncode,
        "log_sha256": sha256_bytes(combined.encode("utf-8", errors="replace")),
        "log_tail": bounded_tail(combined),
    }


def execute(
    *,
    source_commit: str,
    source_tree: str,
    output: Path,
    workspace: Path | None,
) -> tuple[dict[str, Any], int]:
    full_sha(source_commit, "source_commit")
    full_sha(source_tree, "source_tree")
    started = dt.datetime.now(dt.timezone.utc)
    temporary: tempfile.TemporaryDirectory[str] | None = None
    if workspace is None:
        temporary = tempfile.TemporaryDirectory(prefix="external-verification-replay-")
        workspace = Path(temporary.name)
    else:
        if workspace.exists() and any(workspace.iterdir()):
            raise ReplayError(f"workspace must be absent or empty: {workspace}")
        workspace.mkdir(parents=True, exist_ok=True)
    receipt: dict[str, Any] = {
        "schema": SCHEMA,
        "result": "fail",
        "execution_surface": "reviewer_local_linux_outside_github_actions",
        "started_at_utc": started.isoformat(),
        "source": {"commit": source_commit, "tree": source_tree},
    }
    exit_code = 1
    try:
        check_programs()
        bootstrap_contract = load_contract(ROOT)
        source = prepare_source(
            workspace,
            bootstrap_contract["repository"],
            source_commit,
            source_tree,
        )
        source_contract = load_contract(source)
        if source_contract != bootstrap_contract:
            raise ReplayError("bootstrap contract differs from the commit-pinned source contract")
        positive_config = source_contract["replay"]["positive_config"]
        negative_config = source_contract["replay"]["negative_config"]
        positive = load_json(source / positive_config)
        negative = load_json(source / negative_config)
        expected_theorem = source_contract["replay"]["theorem"]
        if positive.get("theorem_names") != [expected_theorem]:
            raise ReplayError("positive replay config is not the contracted one-theorem unit")
        if negative.get("theorem_names") != [expected_theorem]:
            raise ReplayError("negative replay config is not the contracted one-theorem unit")
        if positive.get("permitted_axioms") != source_contract["replay"]["permitted_axioms"]:
            raise ReplayError("positive replay axiom budget differs from contract")
        checked_run(["lake", "exe", "cache", "get"], cwd=source, timeout=1200)
        tools, observed_revisions = prepare_tools(workspace, source_contract)
        mode = sandbox_mode(source)
        positive_command, environment = comparator_command(
            source=source,
            tools=tools,
            mode=mode,
            config=positive_config,
        )
        negative_command, _ = comparator_command(
            source=source,
            tools=tools,
            mode=mode,
            config=negative_config,
        )
        positive_run = run(
            positive_command, cwd=source, timeout=1300, env=environment
        )
        negative_run = run(
            negative_command, cwd=source, timeout=1300, env=environment
        )
        positive_row = result_row(positive_run)
        negative_row = result_row(negative_run)
        expected_diagnostic = source_contract["replay"]["expected_negative_diagnostic"]
        negative_text = negative_run.stdout + negative_run.stderr
        passed = (
            positive_run.returncode == 0
            and negative_run.returncode != 0
            and expected_diagnostic in negative_text
        )
        receipt.update(
            {
                "result": "pass" if passed else "fail",
                "source": {
                    "repository": source_contract["repository"],
                    "commit": source_commit,
                    "tree": source_tree,
                    "expected_commit": source_commit,
                    "observed_commit": git(source, "rev-parse", "HEAD^{commit}"),
                    "expected_tree": source_tree,
                    "observed_tree": git(source, "rev-parse", "HEAD^{tree}"),
                    "identity_verified": True,
                    "contract_sha256": sha256_file(source / CONTRACT_RELATIVE),
                },
                "toolchain": {
                    "expected_revisions": source_contract["toolchain"],
                    "observed_revisions": observed_revisions,
                    "revisions_match": observed_revisions
                    == source_contract["toolchain"],
                    "binary_digests": {
                        name: sha256_file(path) for name, path in tools.items()
                    },
                },
                "statement_contract": {
                    "theorem": expected_theorem,
                    "permitted_axioms": positive["permitted_axioms"],
                    "positive_config": positive_config,
                    "positive_config_sha256": sha256_file(source / positive_config),
                    "negative_config": negative_config,
                    "negative_config_sha256": sha256_file(source / negative_config),
                },
                "sandbox_mode": mode,
                "checks": {
                    "positive": positive_row,
                    "negative": negative_row,
                    "negative_expected_diagnostic": expected_diagnostic,
                    "negative_expected_diagnostic_observed": expected_diagnostic
                    in negative_text,
                },
            }
        )
        exit_code = 0 if passed else 1
    except (ReplayError, subprocess.TimeoutExpired) as exc:
        receipt["error"] = str(exc)
        exit_code = 1
    finally:
        receipt["completed_at_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
        if temporary is not None:
            temporary.cleanup()
    return receipt, exit_code


def replay_plan(source_commit: str, source_tree: str) -> dict[str, Any]:
    full_sha(source_commit, "source_commit")
    full_sha(source_tree, "source_tree")
    value = load_contract(ROOT)
    return {
        "schema": "erdos-external-verification-independent-replay-plan/1",
        "execution_surface": "reviewer_local_linux_outside_github_actions",
        "source": {
            "repository": value["repository"],
            "commit": source_commit,
            "tree": source_tree,
        },
        "toolchain": value["toolchain"],
        "statement_contract": value["replay"],
        "security": {
            "requires_linux_systemd_transient_unit": True,
            "network_disabled_inside_comparator": True,
            "floating_ref_accepted": False,
            "github_pull_request_merge_sha_accepted": False,
        },
    }


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser()
    subparsers = result.add_subparsers(dest="command", required=True)
    for name in ("plan", "run"):
        sub = subparsers.add_parser(name)
        sub.add_argument("--source-commit", required=True)
        sub.add_argument("--source-tree", required=True)
        if name == "run":
            sub.add_argument("--output", type=Path, required=True)
            sub.add_argument("--workspace", type=Path)
    return result


def main() -> int:
    args = parser().parse_args()
    try:
        if args.command == "plan":
            print(json.dumps(replay_plan(args.source_commit, args.source_tree), indent=2))
            return 0
        receipt, exit_code = execute(
            source_commit=args.source_commit,
            source_tree=args.source_tree,
            output=args.output.resolve(),
            workspace=args.workspace.resolve() if args.workspace else None,
        )
        print(args.output)
        if exit_code != 0:
            print(f"independent replay failed: {receipt.get('error', 'Comparator verdict')}")
        return exit_code
    except ReplayError as exc:
        print(f"independent replay error: {exc}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
