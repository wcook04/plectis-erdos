#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression contract for release-gate subprocess environment isolation."""

from __future__ import annotations

import inspect
import json
import os
import subprocess
import sys
import tempfile
import threading
from pathlib import Path
from unittest.mock import patch

import check_release


def require(condition: bool, message: str) -> None:
    """Keep environment-isolation failures active when run with ``python -O``."""
    if not condition:
        raise AssertionError(message)


def main() -> int:
    source = inspect.getsource(check_release)
    require(
        "primary_source_disposition_check = subprocess.run(" not in source,
        "primary-source disposition gate invokes raw subprocess.run",
    )
    require(
        "proof_cockpit_check = subprocess.run(" not in source,
        "proof-cockpit gate invokes raw subprocess.run",
    )
    require(
        "_read_safe_bytes" in inspect.getsource(check_release.read)
        and "_read_safe_bytes" in inspect.getsource(check_release.file_digest)
        and "safe_release_path" in inspect.getsource(check_release._read_safe_bytes),
        "release artifact readers bypass the in-checkout path guard",
    )
    check_release.read.cache_clear()
    cached_path = check_release.ROOT / "README.md"
    with patch.object(
        check_release,
        "_read_safe_bytes",
        wraps=check_release._read_safe_bytes,
    ) as admitted_read:
        first = check_release.read(cached_path)
        second = check_release.read(cached_path)
    require(first == second, "release snapshot cache changed decoded content")
    require(
        admitted_read.call_count == 1,
        "release snapshot cache repeated path admission for one input",
    )
    check_release.read.cache_clear()
    hostile_environment = {
        "GIT_DIR": "/private/wrong-git-dir",
        "GIT_WORK_TREE": "/private/wrong-work-tree",
        "GIT_INDEX_FILE": "/private/wrong-index",
        "GIT_NAMESPACE": "wrong-namespace",
        "GIT_REPLACE_REF_BASE": "refs/replacements/wrong",
        "GIT_OBJECT_DIRECTORY": "/private/wrong-objects",
        "GIT_ALTERNATE_OBJECT_DIRECTORIES": "/private/wrong-alternates",
        "GIT_COMMON_DIR": "/private/wrong-common",
        "PYTHONHOME": "/private/wrong-python-home",
        "PYTHONPATH": "/private/wrong-python-path",
        "PYTHONOPTIMIZE": "2",
        "LC_ALL": "C",
        "LANG": "C",
        "LANGUAGE": "C",
        "PATH": "/private/wrong-bin",
    }
    with tempfile.TemporaryDirectory() as raw:
        with patch.dict(os.environ, hostile_environment, clear=False):
            sanitized = check_release.clean_environment()
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
            ):
                require(key not in sanitized, f"release environment retained {key}")
            require(sanitized["PATH"] == os.defpath, "release environment did not pin PATH")
            require(sanitized["LC_ALL"] == "C.UTF-8", "release environment did not pin LC_ALL")
            require(sanitized["LANG"] == "C.UTF-8", "release environment did not pin LANG")
            require(sanitized["LANGUAGE"] == "C.UTF-8", "release environment did not pin LANGUAGE")
            require(sanitized["GIT_CONFIG_NOSYSTEM"] == "1", "system Git configuration was not disabled")
            require(sanitized["GIT_ASKPASS"] == "/bin/false", "Git credential prompting was not disabled")
            child = check_release.run(
                [
                    sys.executable,
                    "-c",
                    "import json, os; print(json.dumps({k: os.environ[k] for k in "
                    "('GIT_DIR', 'GIT_NAMESPACE', 'GIT_REPLACE_REF_BASE', "
                    "'PYTHONPATH', 'PYTHONHOME', 'PYTHONOPTIMIZE', 'LC_ALL', "
                    "'LANG', 'LANGUAGE', 'PATH') "
                    "if k in os.environ}))",
                ],
                cwd=Path(raw),
                capture_output=True,
                text=True,
                check=False,
            )
            require(child.returncode == 0, "sanitized release child process failed")
            require(
                json.loads(child.stdout)
                == {
                    "LC_ALL": "C.UTF-8",
                    "LANG": "C.UTF-8",
                    "LANGUAGE": "C.UTF-8",
                    "PATH": os.defpath,
                },
                "sanitized release child inherited ambient execution state",
            )

        private = Path(raw) / "private"
        private.mkdir()
        (private / "secret.txt").write_text("outside release\n", encoding="utf-8")
        docs = Path(raw) / "docs"
        docs.mkdir()
        (docs / "linked").symlink_to(private, target_is_directory=True)
        fifo = Path(raw) / "release.fifo"
        os.mkfifo(fifo)
        original_root = check_release.ROOT
        check_release.ROOT = Path(raw)
        try:
            try:
                check_release.safe_release_path(docs / "linked" / "secret.txt")
            except check_release.UnsafeReleasePath:
                pass
            else:
                require(
                    False,
                    "release gate followed a symlinked parent directory",
                )
            require(
                not check_release.release_file_exists(
                    docs / "linked" / "secret.txt"
                ),
                "metadata-only release file checks followed a symlink",
            )
            require(
                check_release.release_file_exists(private / "secret.txt"),
                "metadata-only release file check rejected a regular file",
            )
            with patch.object(check_release, "safe_release_path", return_value=fifo):
                try:
                    check_release.read_bytes(fifo)
                except check_release.UnsafeReleasePath as error:
                    require(
                        "regular file" in str(error),
                        f"special release reader returned an unexpected error: {error}",
                    )
                else:
                    require(False, "special release reader was accepted")

            raced_parent = Path(raw) / "input-parent"
            raced_parent.mkdir()
            original_parent = Path(raw) / "input-parent-original"
            outside = Path(raw) / "outside"
            outside.mkdir()
            raced_input = raced_parent / "descriptor.json"
            raced_input.write_text("inside\n", encoding="utf-8")
            (outside / raced_input.name).write_text("outside\n", encoding="utf-8")
            original_open = check_release.os.open

            def swap_parent(
                path: Path,
                flags: int,
                mode: int = 0o777,
                *,
                dir_fd: int | None = None,
            ) -> int:
                if dir_fd is not None and Path(path).name == raced_input.name:
                    raced_parent.rename(original_parent)
                    raced_parent.symlink_to(outside, target_is_directory=True)
                if dir_fd is not None:
                    return original_open(path, flags, mode, dir_fd=dir_fd)
                return original_open(path, flags, mode)

            with patch.object(check_release.os, "open", side_effect=swap_parent):
                observed = check_release.read_bytes(raced_input)
            require(
                observed == b"inside\n",
                "release reader followed a swapped parent directory",
            )
            require(
                (original_parent / raced_input.name).is_file(),
                "release reader did not use the held parent descriptor",
            )
        finally:
            check_release.ROOT = original_root

        with patch.object(
            check_release,
            "_SUBPROCESS_RUN",
            return_value=subprocess.CompletedProcess(
                ["fixture"], returncode=0, stdout="", stderr=""
            ),
        ) as runner:
            check_release.run(
                ["fixture"],
                cwd=Path(raw),
                capture_output=True,
                text=True,
                check=False,
            )
        require(runner.call_args is not None, "release wrapper did not invoke its subprocess")
        require(
            runner.call_args.kwargs["timeout"] == check_release.SUBPROCESS_TIMEOUT_SECONDS,
            "release wrapper omitted its default subprocess timeout",
        )

    dispatched: list[tuple[str, ...]] = []

    def record_projection(
        args: list[str], **kwargs: object
    ) -> subprocess.CompletedProcess[str]:
        dispatched.append(tuple(args))
        return subprocess.CompletedProcess(args, returncode=0, stdout="current", stderr="")

    check_release._PROJECTION_CHECK_RESULTS = None
    first_builder = check_release.refresh_projections.BUILDERS[0]
    last_builder = check_release.refresh_projections.BUILDERS[-1]
    try:
        with patch.object(check_release, "_SUBPROCESS_RUN", side_effect=record_projection):
            first = check_release.run(
                [sys.executable, str(check_release.ROOT / first_builder), "--check"],
                cwd=check_release.ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
            last = check_release.run(
                [sys.executable, str(check_release.ROOT / last_builder), "--check"],
                cwd=check_release.ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
        require(first.returncode == 0 and last.returncode == 0, "projection batch failed")
        require(
            sorted(Path(args[1]).relative_to(check_release.ROOT).as_posix() for args in dispatched)
            == sorted(check_release.refresh_projections.BUILDERS),
            "release projection batch did not dispatch each authoritative builder once",
        )
        require(
            len(dispatched) == len(check_release.refresh_projections.BUILDERS),
            "release projection result cache repeated a builder",
        )
    finally:
        check_release._PROJECTION_CHECK_RESULTS = None

    independent_dispatches: list[tuple[str, ...]] = []

    def record_independent(
        args: list[str], **kwargs: object
    ) -> subprocess.CompletedProcess[str]:
        independent_dispatches.append(tuple(args))
        return subprocess.CompletedProcess(args, returncode=0, stdout="ok", stderr="")

    independent_commands = {
        "one": [sys.executable, "one.py"],
        "two": [sys.executable, "two.py"],
    }
    with patch.object(check_release, "_SUBPROCESS_RUN", side_effect=record_independent):
        independent_results = check_release.run_independent_checks(independent_commands)
    require(
        set(independent_results) == set(independent_commands),
        "independent release batch lost a named result",
    )
    require(
        sorted(independent_dispatches)
        == sorted(tuple(argv) for argv in independent_commands.values()),
        "independent release batch dropped or repeated a command",
    )

    combined_dispatches: list[tuple[str, ...]] = []

    def record_combined(
        args: list[str], **kwargs: object
    ) -> subprocess.CompletedProcess[str]:
        combined_dispatches.append(tuple(args))
        return subprocess.CompletedProcess(args, returncode=0, stdout="ok", stderr="")

    check_release._PROJECTION_CHECK_RESULTS = None
    with patch.object(check_release, "_SUBPROCESS_RUN", side_effect=record_combined):
        publication_results = check_release.publication_stage_check_results()
    require(
        len(combined_dispatches) == len(check_release.refresh_projections.BUILDERS) + 4,
        "publication-stage pool dropped or repeated a check",
    )
    require(
        len(check_release._PROJECTION_CHECK_RESULTS or {})
        == len(check_release.refresh_projections.BUILDERS),
        "publication-stage pool did not populate the projection result cache",
    )
    require(
        {
            "external_verification_release",
            "note_source",
            "paper_corpus",
            "publication_taxonomy",
        }
        <= publication_results.keys(),
        "publication-stage pool lost a named diagnostic result",
    )
    check_release._PROJECTION_CHECK_RESULTS = None

    release_deferred = threading.Event()
    both_started = threading.Event()
    dispatch_count = 0
    dispatch_lock = threading.Lock()

    def hold_independent(
        args: list[str], **kwargs: object
    ) -> subprocess.CompletedProcess[str]:
        nonlocal dispatch_count
        with dispatch_lock:
            dispatch_count += 1
            if dispatch_count == len(independent_commands):
                both_started.set()
        release_deferred.wait(timeout=2)
        return subprocess.CompletedProcess(args, returncode=0, stdout="ok", stderr="")

    with patch.object(check_release, "_SUBPROCESS_RUN", side_effect=hold_independent):
        executor, futures = check_release.start_independent_checks(independent_commands)
        require(both_started.wait(timeout=2), "deferred checks did not start concurrently")
        require(
            not any(future.done() for future in futures.values()),
            "deferred check launch waited for a result",
        )
        release_deferred.set()
        deferred_results = check_release.finish_independent_checks(executor, futures)
    require(
        set(deferred_results) == set(independent_commands),
        "deferred release batch lost a named result",
    )

    require(
        check_release.ENVIRONMENT_CONTRACT
        == "clean_committed_snapshot_subprocess_environment_v1",
        "release environment contract identifier drifted",
    )
    require(
        "GIT_NAMESPACE" in check_release.SANITIZED_GIT_ENVIRONMENT_KEYS,
        "release environment omitted GIT_NAMESPACE sanitization",
    )
    require(
        "GIT_REPLACE_REF_BASE" in check_release.SANITIZED_GIT_ENVIRONMENT_KEYS,
        "release environment omitted GIT_REPLACE_REF_BASE sanitization",
    )
    require(
        check_release.SUBPROCESS_TIMEOUT_SECONDS
        == check_release.singleflight.DEFAULT_WORKER_TIMEOUT_SECONDS,
        "release subprocess timeout drifted from the shared worker boundary",
    )
    require(
        check_release.PROJECTION_CHECK_WORKERS
        == check_release.refresh_projections.CHECK_WORKERS,
        "release projection batch drifted from the aggregate freshness worker bound",
    )
    require(
        1 <= check_release.RELEASE_CHECK_WORKERS <= 4,
        "release suite batch exceeds its bounded worker policy",
    )
    print(
        "test_check_release_environment: release-gate child processes cannot "
        "inherit caller Git, Python, locale, or PATH state"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
