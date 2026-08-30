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


def require(condition: bool, message: str) -> None:
    """Keep release-ref assurance failures active when run with ``python -O``."""
    if not condition:
        raise AssertionError(message)


def test_snapshot_command_path_boundary() -> None:
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        private = root / "private"
        private.mkdir()
        (private / "entry.py").write_text("print('outside')\n", encoding="utf-8")
        commands = root / "commands"
        commands.mkdir()
        (commands / "linked.py").symlink_to(private / "entry.py")
        require(
            not check_release_ref.is_safe_snapshot_file(root, commands / "linked.py"),
            "snapshot command guard accepted a symlinked file",
        )
        (root / "scripts").symlink_to(private, target_is_directory=True)
        require(
            not check_release_ref.is_safe_snapshot_file(
                root, root / "scripts" / "entry.py"
            ),
            "snapshot command guard accepted a symlinked parent directory",
        )


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
    test_snapshot_command_path_boundary()
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
                "GIT_CONFIG_GLOBAL": "/private/wrong-gitconfig",
                "GIT_TERMINAL_PROMPT": "1",
                "GIT_ASKPASS": "/private/wrong-askpass",
                "PYTHONHOME": "/private/wrong-python-home",
                "PYTHONPATH": "/private/wrong-python-path",
                "PYTHONOPTIMIZE": "2",
                "PYTHONWARNINGS": "error",
                "PYTHONHASHSEED": "random",
                "LC_ALL": "C",
                "LANG": "C",
                "LANGUAGE": "C",
                "PATH": "/private/wrong-bin",
            }
            with patch.dict(os.environ, hostile_environment, clear=False):
                sanitized = check_release_ref.clean_environment()
                require(
                    all(
                        key not in sanitized
                        for key in (
                            "GIT_DIR",
                            "GIT_WORK_TREE",
                            "GIT_INDEX_FILE",
                            "GIT_NAMESPACE",
                            "GIT_REPLACE_REF_BASE",
                            "GIT_OBJECT_DIRECTORY",
                            "GIT_ALTERNATE_OBJECT_DIRECTORIES",
                            "GIT_COMMON_DIR",
                            "PYTHONHOME",
                            "PYTHONPATH",
                            "PYTHONOPTIMIZE",
                            "PYTHONWARNINGS",
                        )
                    ),
                    "release-ref environment retained inherited selector or Python state",
                )
                require(
                    sanitized["GIT_CONFIG_GLOBAL"] == os.devnull,
                    "release-ref environment did not disable global Git config",
                )
                require(
                    sanitized["GIT_CONFIG_NOSYSTEM"] == "1",
                    "release-ref environment did not disable system Git config",
                )
                require(
                    sanitized["GIT_TERMINAL_PROMPT"] == "0"
                    and sanitized["GIT_ASKPASS"] == "/bin/false",
                    "release-ref environment retained interactive Git controls",
                )
                require(
                    sanitized["PATH"] == os.defpath,
                    "release-ref environment did not pin PATH",
                )
                require(
                    sanitized["LC_ALL"] == "C.UTF-8"
                    and sanitized["LANG"] == "C.UTF-8"
                    and sanitized["LANGUAGE"] == "C.UTF-8",
                    "release-ref environment did not pin locale",
                )
                require(
                    sanitized["PYTHONHASHSEED"] == "0"
                    and sanitized["PYTHONNOUSERSITE"] == "1"
                    and sanitized["PYTHONDONTWRITEBYTECODE"] == "1"
                    and sanitized["PYTHONUTF8"] == "1",
                    "release-ref environment did not pin Python runtime state",
                )
                child = check_release_ref.run(
                    [
                        sys.executable,
                        "-c",
                        "import json, os; print(json.dumps({k: os.environ[k] for k in "
                        "('GIT_DIR', 'GIT_NAMESPACE', 'GIT_REPLACE_REF_BASE', "
                        "'PYTHONPATH', 'PYTHONHOME', 'LC_ALL', 'LANG') "
                        "if k in os.environ}))",
                    ],
                    cwd=root,
                )
                require(child.returncode == 0, "sanitized child process failed")
                require(
                    json.loads(child.stdout)
                    == {"LC_ALL": "C.UTF-8", "LANG": "C.UTF-8"},
                    "sanitized child process inherited Git, Python, or locale state",
                )
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
            require(probe_exit == 0, "probe validation failed")
            require(
                probe["status"] == "clean_snapshot_prepared",
                "probe did not prepare a clean snapshot",
            )
            require(
                probe["resolved_commit"] == passing_commit,
                "probe selected the wrong immutable commit",
            )
            require(
                probe["source_repository"] == check_release_ref.SOURCE_REPOSITORY_LABEL,
                "probe receipt exposed a local checkout path",
            )
            require(
                probe["subprocess_environment"] == {
                    "contract": check_release_ref.ENVIRONMENT_CONTRACT,
                    "sanitized_git_selectors": list(
                        check_release_ref.SANITIZED_GIT_ENVIRONMENT_KEYS
                    ),
                    "sanitized_runtime_variables": list(
                        check_release_ref.SANITIZED_RUNTIME_ENVIRONMENT_KEYS
                    ),
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
                "probe omitted the subprocess environment contract",
            )
            require(
                set(probe["caller_worktree_dirty_paths"]) == {
                    "caller.txt",
                    "untracked.txt",
                },
                "probe misreported caller worktree dirt",
            )
            require(
                not probe["caller_worktree_dirty_paths_truncated"],
                "probe unexpectedly truncated caller dirt",
            )
            require(
                probe["gate_coverage"] == {
                    "configured_gate_count": 4,
                    "started_gate_count": 0,
                    "completed_gate_count": 0,
                    "failed_gate_count": 0,
                    "timed_out_gate_count": 0,
                    "all_configured_gates_completed": False,
                    "not_run_commands": probe["release_commands"],
                },
                "probe gate coverage receipt is incomplete",
            )

            many_dirty_paths = [
                f"untracked-{index:03d}.txt"
                for index in range(check_release_ref.DIRTY_PATH_LIMIT + 5)
            ]
            bounded_receipt = check_release_ref.receipt_base(
                "HEAD",
                passing_commit,
                many_dirty_paths,
            )
            require(
                bounded_receipt["caller_worktree_dirty_path_count"]
                == len(many_dirty_paths),
                "bounded receipt lost the complete caller dirt count",
            )
            require(
                len(bounded_receipt["caller_worktree_dirty_paths"])
                == check_release_ref.DIRTY_PATH_LIMIT,
                "bounded receipt exceeded its dirty-path limit",
            )
            require(
                bounded_receipt["caller_worktree_dirty_paths_truncated"],
                "bounded receipt failed to mark truncated caller dirt",
            )

            passed, passed_exit = check_release_ref.validate_ref(
                passing_commit,
                timeout_seconds=30,
                probe_only=False,
            )
            require(passed_exit == 0, "passing release snapshot failed")
            require(passed["status"] == "passed", "passing snapshot was not passed")
            require(
                passed["reported_check_count"] == 17,
                "passing snapshot lost the reported check count",
            )
            require(
                passed["reported_release"] == "v-test",
                "passing snapshot lost the reported release",
            )
            require(
                "uncommitted caller edit" not in passed["stdout_tail"],
                "caller worktree text leaked into the release receipt",
            )
            require(
                passed["release_commands"] == [
                    ["python3", "scripts/check_release.py"],
                    ["python3", "scripts/test_root_import_closure.py"],
                    ["python3", "scripts/test_release_source_identity.py"],
                    ["python3", "scripts/test_query_route_memory.py"],
                ],
                "release command coverage changed unexpectedly",
            )
            require(
                [row["exit_code"] for row in passed["gate_results"]]
                == [0, 0, 0, 0],
                "passing snapshot did not report every gate exit",
            )
            require(
                passed["failed_gate_count"] == 0,
                "passing snapshot reported a failed gate",
            )
            require(
                passed["gate_coverage"] == {
                    "configured_gate_count": 4,
                    "started_gate_count": 4,
                    "completed_gate_count": 4,
                    "failed_gate_count": 0,
                    "timed_out_gate_count": 0,
                    "all_configured_gates_completed": True,
                    "not_run_commands": [],
                },
                "passing snapshot gate coverage receipt is incomplete",
            )

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
            require(root_failed_exit == 9, "root gate failure exit was not preserved")
            require(
                root_failed["status"] == "failed",
                "root gate failure was not reported as failed",
            )
            require(
                [row["exit_code"] for row in root_failed["gate_results"]]
                == [0, 9, 0, 0],
                "root gate failure receipt lost gate exits",
            )
            require(
                root_failed["failed_gate_count"] == 1,
                "root gate failure count is incorrect",
            )
            require(
                root_failed["gate_coverage"]["completed_gate_count"] == 4,
                "root gate failure did not complete the configured gates",
            )
            require(
                root_failed["gate_coverage"]["failed_gate_count"] == 1,
                "root gate failure coverage count is incorrect",
            )
            require(
                root_failed["gate_coverage"]["all_configured_gates_completed"],
                "root gate failure receipt lost completion coverage",
            )
            require(
                "synthetic root census" in root_failed["stdout_tail"],
                "root gate failure receipt lost root-gate output",
            )
            require(
                "synthetic source adversary" in root_failed["stdout_tail"],
                "root gate failure receipt lost later-gate output",
            )

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
            require(
                source_failed_exit == 11,
                "source identity gate exit was not preserved",
            )
            require(
                source_failed["status"] == "failed",
                "source identity gate failure was not reported as failed",
            )
            require(
                [row["exit_code"] for row in source_failed["gate_results"]]
                == [0, 0, 11, 0],
                "source identity gate receipt lost gate exits",
            )
            require(
                source_failed["failed_gate_count"] == 1,
                "source identity gate failure count is incorrect",
            )
            require(
                "synthetic source adversary" in source_failed["stdout_tail"],
                "source identity failure receipt lost gate output",
            )

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
            require(
                route_failed_exit == 13,
                "route-memory gate exit was not preserved",
            )
            require(
                route_failed["status"] == "failed",
                "route-memory gate failure was not reported as failed",
            )
            require(
                [row["exit_code"] for row in route_failed["gate_results"]]
                == [0, 0, 0, 13],
                "route-memory gate receipt lost gate exits",
            )
            require(
                route_failed["failed_gate_count"] == 1,
                "route-memory gate failure count is incorrect",
            )
            require(
                "synthetic route-memory adversary" in route_failed["stdout_tail"],
                "route-memory failure receipt lost gate output",
            )

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
            require(old_again_exit == 0, "previous passing commit did not replay")
            require(
                old_again["resolved_commit"] == passing_commit,
                "previous passing commit was not selected immutably",
            )
            require(
                old_again["status"] == "passed",
                "previous passing commit lost its passing status",
            )

            failed, failed_exit = check_release_ref.validate_ref(
                failing_commit,
                timeout_seconds=30,
                probe_only=False,
            )
            require(failed_exit == 7, "release gate failure exit was not preserved")
            require(
                failed["status"] == "failed",
                "release gate failure was not reported as failed",
            )
            require(
                failed["resolved_commit"] == failing_commit,
                "release gate failure selected the wrong immutable commit",
            )
            require(
                failed["reported_check_count"] == 17,
                "release gate failure lost the reported check count",
            )
            require(
                failed["reported_release"] is None,
                "failed release gate reported a release value",
            )
            require(
                [row["exit_code"] for row in failed["gate_results"]]
                == [7, 0, 0, 0],
                "release gate failure receipt lost gate exits",
            )
            require(
                failed["failed_gate_count"] == 1,
                "release gate failure count is incorrect",
            )
            require(
                "synthetic root census" in failed["stdout_tail"],
                "release gate failure receipt lost root-gate output",
            )
            require(
                "synthetic source adversary" in failed["stdout_tail"],
                "release gate failure receipt lost later-gate output",
            )

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
            require(timeout_exit == 124, "timeout exit was not normalized to 124")
            require(
                timed_out["status"] == "timeout",
                "timed-out release gate was not reported as timeout",
            )
            require(
                timed_out["resolved_commit"] == timeout_commit,
                "timeout receipt selected the wrong immutable commit",
            )
            require(
                timed_out["timeout_seconds"] == TIMEOUT_SECONDS,
                "timeout receipt lost its configured timeout",
            )
            require(
                timed_out["timed_out_command"]
                == ["python3", "scripts/check_release.py"],
                "timeout receipt lost the timed-out command",
            )
            require(
                timed_out["failed_gate_count"] == 0,
                "timeout receipt misclassified the interrupted gate",
            )
            require(
                timed_out["gate_coverage"] == {
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
                },
                "timeout receipt gate coverage is incomplete",
            )
            require(
                "release gate started" in timed_out["stdout_tail"],
                "timeout receipt lost gate output",
            )

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
