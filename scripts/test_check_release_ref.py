#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression contract for clean committed-snapshot release validation."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

import check_release_ref


TIMEOUT_SECONDS = 1


def git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def commit_path(root: Path, path: str, message: str) -> str:
    git(root, "add", "--", path)
    git(root, "commit", "-qm", message)
    return git(root, "rev-parse", "HEAD")


def gate_source(*, exit_code: int, summary: str) -> str:
    return (
        "#!/usr/bin/env python3\n"
        f"print({summary!r})\n"
        f"raise SystemExit({exit_code})\n"
    )


def auxiliary_gate_source(*, label: str, exit_code: int) -> str:
    return (
        "#!/usr/bin/env python3\n"
        f"print({label!r})\n"
        f"raise SystemExit({exit_code})\n"
    )


def main() -> int:
    original_root = check_release_ref.ROOT
    try:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            hostile_environment = {
                "GIT_DIR": "/private/wrong-git-dir",
                "GIT_WORK_TREE": "/private/wrong-work-tree",
                "GIT_INDEX_FILE": "/private/wrong-index",
                "GIT_NAMESPACE": "wrong-namespace",
                "GIT_REPLACE_REF_BASE": "refs/replacements/wrong",
                "GIT_OBJECT_DIRECTORY": "/private/wrong-objects",
                "GIT_ALTERNATE_OBJECT_DIRECTORIES": "/private/wrong-alternates",
                "GIT_COMMON_DIR": "/private/wrong-common",
            }
            with patch.dict(os.environ, hostile_environment, clear=False):
                sanitized = check_release_ref.clean_environment()
                assert all(key not in sanitized for key in hostile_environment)
                assert sanitized["PATH"] == os.environ["PATH"]
                child = check_release_ref.run(
                    [
                        sys.executable,
                        "-c",
                        "import json, os; print(json.dumps({k: os.environ[k] for k in "
                        "('GIT_DIR', 'GIT_NAMESPACE', 'GIT_REPLACE_REF_BASE') "
                        "if k in os.environ}))",
                    ],
                    cwd=root,
                )
                assert child.returncode == 0
                assert json.loads(child.stdout) == {}
            git(root, "init", "-q")
            git(root, "config", "user.email", "release-ref-test@example.invalid")
            git(root, "config", "user.name", "Clean ref release test")
            (root / "scripts").mkdir()
            (root / "caller.txt").write_text("committed\n", encoding="utf-8")
            (root / "scripts" / "check_release.py").write_text(
                gate_source(
                    exit_code=0,
                    summary="check_release: all 17 checks passed for release v-test",
                ),
                encoding="utf-8",
            )
            (root / "scripts" / "test_root_import_closure.py").write_text(
                auxiliary_gate_source(
                    label="test_root_import_closure: synthetic root census",
                    exit_code=0,
                ),
                encoding="utf-8",
            )
            (root / "scripts" / "test_release_source_identity.py").write_text(
                auxiliary_gate_source(
                    label="test_release_source_identity: synthetic source adversary",
                    exit_code=0,
                ),
                encoding="utf-8",
            )
            (root / "scripts" / "test_query_route_memory.py").write_text(
                auxiliary_gate_source(
                    label="test_query_route_memory: synthetic route-memory adversary",
                    exit_code=0,
                ),
                encoding="utf-8",
            )
            git(root, "add", ".")
            git(root, "commit", "-qm", "passing release snapshot")
            passing_commit = git(root, "rev-parse", "HEAD")

            (root / "caller.txt").write_text(
                "uncommitted caller edit\n", encoding="utf-8"
            )
            (root / "untracked.txt").write_text(
                "uncommitted caller file\n", encoding="utf-8"
            )
            check_release_ref.ROOT = root

            probe, probe_exit = check_release_ref.validate_ref(
                passing_commit,
                timeout_seconds=30,
                probe_only=True,
            )
            assert probe_exit == 0
            assert probe["status"] == "clean_snapshot_prepared"
            assert probe["resolved_commit"] == passing_commit
            assert probe["subprocess_environment"] == {
                "contract": check_release_ref.ENVIRONMENT_CONTRACT,
                "sanitized_git_selectors": list(
                    check_release_ref.SANITIZED_GIT_ENVIRONMENT_KEYS
                ),
            }
            assert set(probe["caller_worktree_dirty_paths"]) == {
                "caller.txt",
                "untracked.txt",
            }
            assert not probe["caller_worktree_dirty_paths_truncated"]
            assert probe["gate_coverage"] == {
                "configured_gate_count": 4,
                "started_gate_count": 0,
                "completed_gate_count": 0,
                "failed_gate_count": 0,
                "timed_out_gate_count": 0,
                "all_configured_gates_completed": False,
                "not_run_commands": probe["release_commands"],
            }

            many_dirty_paths = [
                f"untracked-{index:03d}.txt"
                for index in range(check_release_ref.DIRTY_PATH_LIMIT + 5)
            ]
            bounded_receipt = check_release_ref.receipt_base(
                "HEAD",
                passing_commit,
                many_dirty_paths,
            )
            assert bounded_receipt["caller_worktree_dirty_path_count"] == len(
                many_dirty_paths
            )
            assert len(bounded_receipt["caller_worktree_dirty_paths"]) == (
                check_release_ref.DIRTY_PATH_LIMIT
            )
            assert bounded_receipt["caller_worktree_dirty_paths_truncated"]

            passed, passed_exit = check_release_ref.validate_ref(
                passing_commit,
                timeout_seconds=30,
                probe_only=False,
            )
            assert passed_exit == 0
            assert passed["status"] == "passed"
            assert passed["reported_check_count"] == 17
            assert passed["reported_release"] == "v-test"
            assert "uncommitted caller edit" not in passed["stdout_tail"]
            assert passed["release_commands"] == [
                ["python3", "scripts/check_release.py"],
                ["python3", "scripts/test_root_import_closure.py"],
                ["python3", "scripts/test_release_source_identity.py"],
                ["python3", "scripts/test_query_route_memory.py"],
            ]
            assert [row["exit_code"] for row in passed["gate_results"]] == [
                0,
                0,
                0,
                0,
            ]
            assert passed["failed_gate_count"] == 0
            assert passed["gate_coverage"] == {
                "configured_gate_count": 4,
                "started_gate_count": 4,
                "completed_gate_count": 4,
                "failed_gate_count": 0,
                "timed_out_gate_count": 0,
                "all_configured_gates_completed": True,
                "not_run_commands": [],
            }

            (root / "scripts" / "test_root_import_closure.py").write_text(
                auxiliary_gate_source(
                    label="test_root_import_closure: synthetic root census",
                    exit_code=9,
                ),
                encoding="utf-8",
            )
            root_failure_commit = commit_path(
                root,
                "scripts/test_root_import_closure.py",
                "failing root closure snapshot",
            )
            root_failed, root_failed_exit = check_release_ref.validate_ref(
                root_failure_commit,
                timeout_seconds=30,
                probe_only=False,
            )
            assert root_failed_exit == 9
            assert root_failed["status"] == "failed"
            assert [row["exit_code"] for row in root_failed["gate_results"]] == [
                0,
                9,
                0,
                0,
            ]
            assert root_failed["failed_gate_count"] == 1
            assert root_failed["gate_coverage"]["completed_gate_count"] == 4
            assert root_failed["gate_coverage"]["failed_gate_count"] == 1
            assert root_failed["gate_coverage"]["all_configured_gates_completed"]
            assert "synthetic root census" in root_failed["stdout_tail"]
            assert "synthetic source adversary" in root_failed["stdout_tail"]

            (root / "scripts" / "test_root_import_closure.py").write_text(
                auxiliary_gate_source(
                    label="test_root_import_closure: synthetic root census",
                    exit_code=0,
                ),
                encoding="utf-8",
            )
            commit_path(
                root,
                "scripts/test_root_import_closure.py",
                "restore passing root closure",
            )

            (root / "scripts" / "test_release_source_identity.py").write_text(
                auxiliary_gate_source(
                    label="test_release_source_identity: synthetic source adversary",
                    exit_code=11,
                ),
                encoding="utf-8",
            )
            source_failure_commit = commit_path(
                root,
                "scripts/test_release_source_identity.py",
                "failing source identity snapshot",
            )
            source_failed, source_failed_exit = check_release_ref.validate_ref(
                source_failure_commit,
                timeout_seconds=30,
                probe_only=False,
            )
            assert source_failed_exit == 11
            assert source_failed["status"] == "failed"
            assert [row["exit_code"] for row in source_failed["gate_results"]] == [
                0,
                0,
                11,
                0,
            ]
            assert source_failed["failed_gate_count"] == 1
            assert "synthetic source adversary" in source_failed["stdout_tail"]

            (root / "scripts" / "test_release_source_identity.py").write_text(
                auxiliary_gate_source(
                    label="test_release_source_identity: synthetic source adversary",
                    exit_code=0,
                ),
                encoding="utf-8",
            )
            commit_path(
                root,
                "scripts/test_release_source_identity.py",
                "restore passing source identity",
            )

            (root / "scripts" / "test_query_route_memory.py").write_text(
                auxiliary_gate_source(
                    label="test_query_route_memory: synthetic route-memory adversary",
                    exit_code=13,
                ),
                encoding="utf-8",
            )
            route_failed_commit = commit_path(
                root,
                "scripts/test_query_route_memory.py",
                "failing route-memory snapshot",
            )
            route_failed, route_failed_exit = check_release_ref.validate_ref(
                route_failed_commit,
                timeout_seconds=30,
                probe_only=False,
            )
            assert route_failed_exit == 13
            assert route_failed["status"] == "failed"
            assert [row["exit_code"] for row in route_failed["gate_results"]] == [
                0,
                0,
                0,
                13,
            ]
            assert route_failed["failed_gate_count"] == 1
            assert "synthetic route-memory adversary" in route_failed["stdout_tail"]

            (root / "scripts" / "test_query_route_memory.py").write_text(
                auxiliary_gate_source(
                    label="test_query_route_memory: synthetic route-memory adversary",
                    exit_code=0,
                ),
                encoding="utf-8",
            )
            commit_path(
                root,
                "scripts/test_query_route_memory.py",
                "restore passing route memory",
            )

            (root / "scripts" / "check_release.py").write_text(
                gate_source(
                    exit_code=7,
                    summary="check_release: 2 failure(s) across 17 checks",
                ),
                encoding="utf-8",
            )
            failing_commit = commit_path(
                root,
                "scripts/check_release.py",
                "failing release snapshot",
            )

            old_again, old_again_exit = check_release_ref.validate_ref(
                passing_commit,
                timeout_seconds=30,
                probe_only=False,
            )
            assert old_again_exit == 0
            assert old_again["resolved_commit"] == passing_commit
            assert old_again["status"] == "passed"

            failed, failed_exit = check_release_ref.validate_ref(
                failing_commit,
                timeout_seconds=30,
                probe_only=False,
            )
            assert failed_exit == 7
            assert failed["status"] == "failed"
            assert failed["resolved_commit"] == failing_commit
            assert failed["reported_check_count"] == 17
            assert failed["reported_release"] is None
            assert [row["exit_code"] for row in failed["gate_results"]] == [
                7,
                0,
                0,
                0,
            ]
            assert failed["failed_gate_count"] == 1
            assert "synthetic root census" in failed["stdout_tail"]
            assert "synthetic source adversary" in failed["stdout_tail"]

            (root / "scripts" / "check_release.py").write_text(
                "import time\n"
                "print('release gate started', flush=True)\n"
                f"time.sleep({TIMEOUT_SECONDS + 2})\n",
                encoding="utf-8",
            )
            timeout_commit = commit_path(
                root,
                "scripts/check_release.py",
                "timed-out release snapshot",
            )
            timed_out, timeout_exit = check_release_ref.validate_ref(
                timeout_commit,
                timeout_seconds=TIMEOUT_SECONDS,
                probe_only=False,
            )
            assert timeout_exit == 124
            assert timed_out["status"] == "timeout"
            assert timed_out["resolved_commit"] == timeout_commit
            assert timed_out["timeout_seconds"] == TIMEOUT_SECONDS
            assert timed_out["timed_out_command"] == [
                "python3",
                "scripts/check_release.py",
            ]
            assert timed_out["failed_gate_count"] == 0
            assert timed_out["gate_coverage"] == {
                "configured_gate_count": 4,
                "started_gate_count": 1,
                "completed_gate_count": 0,
                "failed_gate_count": 0,
                "timed_out_gate_count": 1,
                "all_configured_gates_completed": False,
                "not_run_commands": [
                    ["python3", "scripts/test_root_import_closure.py"],
                    ["python3", "scripts/test_release_source_identity.py"],
                    ["python3", "scripts/test_query_route_memory.py"],
                ],
            }
            assert "release gate started" in timed_out["stdout_tail"]

            try:
                check_release_ref.resolve_commit("missing-ref")
            except check_release_ref.SnapshotError:
                pass
            else:
                raise AssertionError("missing ref was accepted")
    finally:
        check_release_ref.ROOT = original_root

    print(
        "test_check_release_ref: caller dirt excluded, exact commits selected, "
        "dirty paths bounded, root disk census and immutable source adversary "
        "always reported, first failing gate exit preserved, and timeout receipt "
        "coverage serialized"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
