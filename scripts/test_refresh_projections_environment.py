#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression contract for projection-refresh subprocess environment isolation."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

import refresh_projections


def require(condition: bool, message: str) -> None:
    """Keep projection-environment failures active when run with ``python -O``."""
    if not condition:
        raise AssertionError(message)


def main() -> int:
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
            sanitized = refresh_projections.clean_environment()
            require(
                all(
                    key not in sanitized
                    for key in hostile_environment
                    if key not in {"LC_ALL", "LANG", "LANGUAGE", "PATH"}
                ),
                "projection environment retained a hostile selector",
            )
            require(
                sanitized["PATH"] == os.defpath,
                "projection environment did not pin PATH",
            )
            require(
                sanitized["LC_ALL"] == "C.UTF-8"
                and sanitized["LANG"] == "C.UTF-8"
                and sanitized["LANGUAGE"] == "C.UTF-8",
                "projection environment did not pin locale",
            )
            child = refresh_projections.run(
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
            )
            require(child.returncode == 0, "projection child process failed")
            require(
                json.loads(child.stdout)
                == {
                    "LC_ALL": "C.UTF-8",
                    "LANG": "C.UTF-8",
                    "LANGUAGE": "C.UTF-8",
                    "PATH": os.defpath,
                },
                "projection child process inherited ambient execution state",
            )
            with patch.object(
                refresh_projections.subprocess,
                "run",
                return_value=subprocess.CompletedProcess(
                    ["fixture"], returncode=0, stdout="", stderr=""
                ),
            ) as runner:
                refresh_projections.run(["fixture"], cwd=Path(raw))
            require(
                runner.call_args.kwargs["timeout"]
                == refresh_projections.SUBPROCESS_TIMEOUT_SECONDS,
                "projection subprocess omitted its timeout",
            )

    require(
        refresh_projections.ENVIRONMENT_CONTRACT
        == "clean_committed_snapshot_subprocess_environment_v1",
        "projection environment contract drifted",
    )
    require(
        "GIT_NAMESPACE" in refresh_projections.SANITIZED_GIT_ENVIRONMENT_KEYS,
        "projection environment no longer sanitizes GIT_NAMESPACE",
    )
    require(
        "GIT_REPLACE_REF_BASE"
        in refresh_projections.SANITIZED_GIT_ENVIRONMENT_KEYS,
        "projection environment no longer sanitizes GIT_REPLACE_REF_BASE",
    )
    require(
        "PYTHONPATH" in refresh_projections.SANITIZED_RUNTIME_ENVIRONMENT_KEYS,
        "projection environment no longer sanitizes PYTHONPATH",
    )
    require(
        refresh_projections.SUBPROCESS_TIMEOUT_SECONDS
        == refresh_projections.singleflight.DEFAULT_WORKER_TIMEOUT_SECONDS,
        "projection subprocess timeout drifted from the shared worker boundary",
    )
    print(
        "test_refresh_projections_environment: projection subprocesses cannot "
        "inherit caller Git, Python, locale, or PATH state and are bounded"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
