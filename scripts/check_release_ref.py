#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Run the release gate against a clean committed Git snapshot.

This wrapper is for shared or intentionally dirty worktrees.  It resolves one
commit, creates a disposable local clone, and runs every independent release
gate there.  A failing gate does not suppress later diagnostics; the first
nonzero exit code remains the process result.  Uncommitted files in the
caller's checkout are never copied into the validation snapshot.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import stat
import subprocess
import tempfile
import time
from collections.abc import Mapping
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
SCHEMA = "erdos249257-clean-ref-release-receipt/1"
TAIL_BYTES = 16_000
DIRTY_PATH_LIMIT = 120
ENVIRONMENT_CONTRACT = "clean_committed_snapshot_subprocess_environment_v1"
SOURCE_REPOSITORY_LABEL = "local_checkout"
SANITIZED_GIT_ENVIRONMENT_KEYS = (
    "GIT_DIR",
    "GIT_WORK_TREE",
    "GIT_INDEX_FILE",
    "GIT_NAMESPACE",
    "GIT_REPLACE_REF_BASE",
    "GIT_OBJECT_DIRECTORY",
    "GIT_ALTERNATE_OBJECT_DIRECTORIES",
    "GIT_COMMON_DIR",
)
SANITIZED_RUNTIME_ENVIRONMENT_KEYS = (
    "PYTHONHOME",
    "PYTHONPATH",
    "PYTHONSTARTUP",
    "PYTHONUSERBASE",
    "PYTHONBREAKPOINT",
    "PYTHONWARNINGS",
    "PYTHONHASHSEED",
    "PYTHONOPTIMIZE",
    "PYTHONUTF8",
    "PYTHONNOUSERSITE",
    "PYTHONDONTWRITEBYTECODE",
    "LC_ALL",
    "LANG",
    "LANGUAGE",
)
RELEASE_COMMANDS = (
    ("python3", "scripts/check_release.py"),
    ("python3", "scripts/test_root_import_closure.py"),
    ("python3", "scripts/test_release_source_identity.py"),
    ("python3", "scripts/test_query_route_memory.py"),
)


class SnapshotError(RuntimeError):
    """Raised when the requested clean snapshot cannot be prepared."""


def is_safe_snapshot_file(root: Path, path: Path) -> bool:
    """Return whether a snapshot input is a regular, non-symlinked file."""
    root = Path(os.path.abspath(root))
    candidate = Path(os.path.abspath(path))
    current = candidate
    while True:
        if current.is_symlink():
            return False
        if current == root:
            break
        if current.parent == current:
            return False
        current = current.parent
    return candidate.is_file()


def clean_environment(base: Mapping[str, str] | None = None) -> dict[str, str]:
    """Run snapshot subprocesses without inherited Git, Python, or locale state."""
    environment = dict(os.environ if base is None else base)
    for key in list(environment):
        if key.startswith("GIT_CONFIG_"):
            environment.pop(key, None)
    for key in SANITIZED_GIT_ENVIRONMENT_KEYS + SANITIZED_RUNTIME_ENVIRONMENT_KEYS:
        environment.pop(key, None)
    environment.update(
        {
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_CONFIG_GLOBAL": os.devnull,
            "GIT_OPTIONAL_LOCKS": "0",
            "GIT_NO_REPLACE_OBJECTS": "1",
            "GIT_PAGER": "cat",
            "GIT_TERMINAL_PROMPT": "0",
            "GIT_ASKPASS": "/bin/false",
            "PATH": os.defpath,
            "LC_ALL": "C.UTF-8",
            "LANG": "C.UTF-8",
            "LANGUAGE": "C.UTF-8",
            "PYTHONHASHSEED": "0",
            "PYTHONNOUSERSITE": "1",
            "PYTHONDONTWRITEBYTECODE": "1",
            "PYTHONUTF8": "1",
        }
    )
    return environment


def run(
    argv: list[str],
    *,
    cwd: Path,
    timeout: int | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        argv,
        cwd=cwd,
        capture_output=True,
        text=True,
        check=False,
        timeout=timeout,
        env=clean_environment(),
    )


def resolve_commit(ref: str) -> str:
    completed = run(["git", "rev-parse", "--verify", f"{ref}^{{commit}}"], cwd=ROOT)
    if completed.returncode != 0:
        raise SnapshotError(
            completed.stderr.strip() or f"could not resolve commit ref {ref!r}"
        )
    commit = completed.stdout.strip()
    if re.fullmatch(r"[0-9a-f]{40}", commit) is None:
        raise SnapshotError(f"resolved ref is not a full commit id: {commit!r}")
    return commit


def dirty_paths() -> list[str]:
    completed = run(
        ["git", "status", "--short", "--untracked-files=all"],
        cwd=ROOT,
    )
    if completed.returncode != 0:
        return []
    return [line[3:] for line in completed.stdout.splitlines() if line]


def bounded_tail(text: str | bytes) -> str:
    encoded = (
        text
        if isinstance(text, bytes)
        else text.encode("utf-8", errors="replace")
    )
    return encoded[-TAIL_BYTES:].decode("utf-8", errors="replace")


def parse_release_summary(stdout: str) -> dict[str, Any]:
    match = re.search(
        r"all ([0-9,]+) checks passed for release ([^\s]+)",
        stdout,
    )
    if match:
        return {
            "reported_check_count": int(match.group(1).replace(",", "")),
            "reported_release": match.group(2),
        }
    failed = re.search(r"([0-9,]+) checks", stdout)
    return {
        "reported_check_count": (
            int(failed.group(1).replace(",", "")) if failed else None
        ),
        "reported_release": None,
    }


def prepare_clone(commit: str, parent: Path) -> Path:
    clone = parent / "repo"
    cloned = run(
        [
            "git",
            "clone",
            "--local",
            "--no-hardlinks",
            "--no-checkout",
            "--quiet",
            str(ROOT),
            str(clone),
        ],
        cwd=ROOT,
    )
    if cloned.returncode != 0:
        raise SnapshotError(cloned.stderr.strip() or "local clone failed")
    checked_out = run(
        ["git", "checkout", "--detach", "--quiet", commit],
        cwd=clone,
    )
    if checked_out.returncode != 0:
        raise SnapshotError(
            checked_out.stderr.strip() or f"could not check out {commit}"
        )
    missing = [
        command[1]
        for command in RELEASE_COMMANDS
        if not is_safe_snapshot_file(clone, clone / command[1])
    ]
    if missing:
        raise SnapshotError(
            "snapshot does not contain required release command(s): "
            + ", ".join(missing)
        )
    return clone


def receipt_base(ref: str, commit: str, caller_dirty_paths: list[str]) -> dict[str, Any]:
    dirty_path_count = len(caller_dirty_paths)
    return {
        "schema": SCHEMA,
        "requested_ref": ref,
        "resolved_commit": commit,
        "snapshot_posture": "clean_committed_clone_excludes_caller_worktree_changes",
        "source_repository": SOURCE_REPOSITORY_LABEL,
        "caller_worktree_dirty_path_count": dirty_path_count,
        "caller_worktree_dirty_paths": caller_dirty_paths[:DIRTY_PATH_LIMIT],
        "caller_worktree_dirty_path_limit": DIRTY_PATH_LIMIT,
        "caller_worktree_dirty_paths_truncated": dirty_path_count > DIRTY_PATH_LIMIT,
        "subprocess_environment": {
            "contract": ENVIRONMENT_CONTRACT,
            "sanitized_git_selectors": list(SANITIZED_GIT_ENVIRONMENT_KEYS),
            "sanitized_runtime_variables": list(SANITIZED_RUNTIME_ENVIRONMENT_KEYS),
            "canonical_values": {
                "GIT_CONFIG_GLOBAL": os.devnull,
                "GIT_CONFIG_NOSYSTEM": "1",
                "GIT_OPTIONAL_LOCKS": "0",
                "GIT_NO_REPLACE_OBJECTS": "1",
                "GIT_PAGER": "cat",
                "GIT_TERMINAL_PROMPT": "0",
                "GIT_ASKPASS": "/bin/false",
                "PATH": os.defpath,
                "LC_ALL": "C.UTF-8",
                "LANG": "C.UTF-8",
                "LANGUAGE": "C.UTF-8",
                "PYTHONHASHSEED": "0",
                "PYTHONNOUSERSITE": "1",
                "PYTHONDONTWRITEBYTECODE": "1",
                "PYTHONUTF8": "1",
            },
        },
        "release_command": list(RELEASE_COMMANDS[0]),
        "release_commands": [list(command) for command in RELEASE_COMMANDS],
    }


def gate_coverage(gate_results: list[dict[str, Any]]) -> dict[str, Any]:
    """Summarize which configured gates started, completed, or remained unrun."""
    completed_gate_count = sum(
        result.get("exit_code") is not None for result in gate_results
    )
    failed_gate_count = sum(
        result.get("exit_code") not in (None, 0) for result in gate_results
    )
    timed_out_gate_count = sum(
        result.get("status") == "timeout" for result in gate_results
    )
    return {
        "configured_gate_count": len(RELEASE_COMMANDS),
        "started_gate_count": len(gate_results),
        "completed_gate_count": completed_gate_count,
        "failed_gate_count": failed_gate_count,
        "timed_out_gate_count": timed_out_gate_count,
        "all_configured_gates_completed": (
            completed_gate_count == len(RELEASE_COMMANDS)
            and timed_out_gate_count == 0
        ),
        "not_run_commands": [
            list(command) for command in RELEASE_COMMANDS[len(gate_results) :]
        ],
    }


def validate_ref(
    ref: str,
    *,
    timeout_seconds: int,
    probe_only: bool,
) -> tuple[dict[str, Any], int]:
    commit = resolve_commit(ref)
    caller_dirty_paths = dirty_paths()
    started_at = datetime.now(timezone.utc).isoformat()
    started = time.monotonic()
    with tempfile.TemporaryDirectory(prefix="plectis-clean-release-") as temp:
        clone = prepare_clone(commit, Path(temp))
        checked_out = run(["git", "rev-parse", "HEAD"], cwd=clone)
        if checked_out.stdout.strip() != commit:
            raise SnapshotError("disposable clone resolved a different commit")
        if probe_only:
            elapsed = round(time.monotonic() - started, 3)
            return (
                {
                    **receipt_base(ref, commit, caller_dirty_paths),
                    "mode": "probe_only",
                    "status": "clean_snapshot_prepared",
                    "started_at": started_at,
                    "completed_at": datetime.now(timezone.utc).isoformat(),
                    "wall_time_seconds": elapsed,
                    "gate_exit_code": None,
                    "gate_coverage": gate_coverage([]),
                },
                0,
            )
        gate_results: list[dict[str, Any]] = []
        stdout_parts: list[str] = []
        stderr_parts: list[str] = []
        active_command: tuple[str, ...] | None = None
        deadline = time.monotonic() + timeout_seconds
        try:
            for command in RELEASE_COMMANDS:
                active_command = command
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    raise subprocess.TimeoutExpired(command, timeout_seconds)
                completed = run(
                    list(command),
                    cwd=clone,
                    timeout=remaining,
                )
                stdout_parts.append(completed.stdout)
                stderr_parts.append(completed.stderr)
                gate_results.append(
                    {
                        "command": list(command),
                        "exit_code": completed.returncode,
                        "stdout_tail": bounded_tail(completed.stdout),
                        "stderr_tail": bounded_tail(completed.stderr),
                    }
                )
            elapsed = round(time.monotonic() - started, 3)
            stdout = "\n".join(stdout_parts)
            stderr = "\n".join(stderr_parts)
            failed_results = [
                result for result in gate_results if result["exit_code"] != 0
            ]
            exit_code = (
                failed_results[0]["exit_code"] if failed_results else 0
            )
            summary = parse_release_summary(stdout)
            return (
                {
                    **receipt_base(ref, commit, caller_dirty_paths),
                    "mode": "release_gate",
                    "status": (
                        "passed" if exit_code == 0 else "failed"
                    ),
                    "started_at": started_at,
                    "completed_at": datetime.now(timezone.utc).isoformat(),
                    "wall_time_seconds": elapsed,
                    "gate_exit_code": exit_code,
                    "gate_results": gate_results,
                    "failed_gate_count": len(failed_results),
                    "gate_coverage": gate_coverage(gate_results),
                    **summary,
                    "stdout_tail": bounded_tail(stdout),
                    "stderr_tail": bounded_tail(stderr),
                },
                exit_code,
            )
        except subprocess.TimeoutExpired as error:
            elapsed = round(time.monotonic() - started, 3)
            timed_out_stdout = bounded_tail(error.stdout or "")
            timed_out_stderr = bounded_tail(error.stderr or "")
            if active_command is not None:
                gate_results.append(
                    {
                        "command": list(active_command),
                        "exit_code": None,
                        "status": "timeout",
                        "stdout_tail": timed_out_stdout,
                        "stderr_tail": timed_out_stderr,
                    }
                )
            return (
                {
                    **receipt_base(ref, commit, caller_dirty_paths),
                    "mode": "release_gate",
                    "status": "timeout",
                    "started_at": started_at,
                    "completed_at": datetime.now(timezone.utc).isoformat(),
                    "wall_time_seconds": elapsed,
                    "gate_exit_code": None,
                    "timeout_seconds": timeout_seconds,
                    "timed_out_command": (
                        list(active_command) if active_command is not None else None
                    ),
                    "gate_results": gate_results,
                    "failed_gate_count": sum(
                        result.get("exit_code") not in (None, 0)
                        for result in gate_results
                    ),
                    "gate_coverage": gate_coverage(gate_results),
                    "reported_check_count": None,
                    "reported_release": None,
                    "stdout_tail": bounded_tail(
                        "\n".join([*stdout_parts, timed_out_stdout])
                    ),
                    "stderr_tail": bounded_tail(
                        "\n".join([*stderr_parts, timed_out_stderr])
                    ),
                },
                124,
            )


def write_receipt(path: Path, receipt: dict[str, Any]) -> None:
    path = safe_receipt_path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(receipt, ensure_ascii=False, indent=2) + "\n"
    flags = os.O_WRONLY | os.O_CREAT | os.O_TRUNC
    flags |= getattr(os, "O_NOFOLLOW", 0)
    flags |= getattr(os, "O_NONBLOCK", 0)
    flags |= getattr(os, "O_CLOEXEC", 0)
    try:
        descriptor = os.open(path, flags, 0o644)
    except OSError as exc:
        raise SnapshotError(
            f"receipt destination could not be opened safely: {path}"
        ) from exc
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise SnapshotError(f"receipt destination is not a regular file: {path}")
        with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
            descriptor = -1
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
    except OSError as exc:
        raise SnapshotError(
            f"receipt destination could not be written safely: {path}"
        ) from exc
    finally:
        if descriptor >= 0:
            os.close(descriptor)


def safe_receipt_path(path: Path) -> Path:
    """Reject symlinked receipt destinations without restricting their root."""
    candidate = Path(os.path.abspath(path))
    current = candidate
    while True:
        if current.is_symlink():
            raise SnapshotError(f"receipt destination contains a symlink: {candidate}")
        if current.parent == current:
            break
        current = current.parent
    if candidate.exists() and not candidate.is_file():
        raise SnapshotError(f"receipt destination is not a regular file: {candidate}")
    return candidate


def render_text(receipt: dict[str, Any]) -> str:
    header = (
        f"check_release_ref: {receipt['status']} "
        f"ref={receipt['requested_ref']} "
        f"commit={receipt['resolved_commit'][:12]} "
        f"caller_dirty_paths={receipt['caller_worktree_dirty_path_count']}"
    )
    if receipt["mode"] == "probe_only":
        return header
    body = receipt.get("stdout_tail", "").rstrip()
    error = receipt.get("stderr_tail", "").rstrip()
    return "\n".join(part for part in (header, body, error) if part)


def build_parser() -> argparse.ArgumentParser:
    """Build the CLI parser, including the internal single-flight contract."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ref", default="HEAD")
    parser.add_argument("--timeout-seconds", type=int, default=900)
    parser.add_argument("--probe-only", action="store_true")
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--format", choices=("text", "json"), default="text")
    parser.add_argument(
        "--singleflight-worker",
        action="store_true",
        help=argparse.SUPPRESS,
    )
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    if args.timeout_seconds <= 0:
        parser.error("--timeout-seconds must be positive")
    try:
        receipt, exit_code = validate_ref(
            args.ref,
            timeout_seconds=args.timeout_seconds,
            probe_only=args.probe_only,
        )
    except (SnapshotError, OSError, subprocess.SubprocessError) as error:
        print(f"check_release_ref: {error}")
        return 2
    if args.receipt is not None:
        write_receipt(args.receipt, receipt)
    if args.format == "json":
        print(json.dumps(receipt, ensure_ascii=False, indent=2))
    else:
        print(render_text(receipt))
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
