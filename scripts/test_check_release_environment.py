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
        "primary_source_disposition_check = run(" in source,
        "primary-source disposition gate bypassed the release subprocess wrapper",
    )
    require(
        "primary_source_disposition_check = subprocess.run(" not in source,
        "primary-source disposition gate still invokes raw subprocess.run",
    )
    require(
        "safe_release_path" in inspect.getsource(check_release.read)
        and "safe_release_path" in inspect.getsource(check_release.file_digest),
        "release artifact readers bypass the in-checkout path guard",
    )
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
    print(
        "test_check_release_environment: release-gate child processes cannot "
        "inherit caller Git, Python, locale, or PATH state"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
