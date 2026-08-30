#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression contract for benchmark-packet Git subprocesses."""

from __future__ import annotations

import os
import subprocess
from pathlib import Path
from unittest.mock import patch

import build_benchmark_packet as experiment
import validation_singleflight as singleflight


def require(condition: bool, message: str) -> None:
    """Keep portability failures active when CI invokes Python with ``-O``."""
    if not condition:
        raise AssertionError(message)


def main() -> int:
    completed = subprocess.CompletedProcess(
        ["git"], returncode=0, stdout="ok\n", stderr=""
    )
    hostile = {
        "GIT_DIR": "/foreign/git",
        "GIT_WORK_TREE": "/foreign/worktree",
        "GIT_NAMESPACE": "foreign-namespace",
        "GIT_REPLACE_REF_BASE": "refs/replace/foreign/",
        "PYTHONPATH": "/foreign/python",
        "LANGUAGE": "fr_FR",
    }
    with patch.dict(os.environ, hostile, clear=False):
        expected = singleflight.command_environment()
        with patch.object(
            experiment.subprocess, "run", return_value=completed
        ) as runner:
            result = experiment.git("status", cwd=Path("/benchmark-fixture"))
            experiment._remove_worktree(Path("/benchmark-fixture"))

    require(result == "ok\n", "benchmark Git helper did not return stdout")
    require(len(runner.call_args_list) == 2, "benchmark helpers made an unexpected call count")
    for call in runner.call_args_list:
        require(call.kwargs["env"] == expected, "benchmark Git call drifted from canonical environment")
        require(
            call.kwargs["timeout"] == singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
            "benchmark Git call lost its bounded timeout",
        )
    require(
        all(
            key not in expected
            for key in {
                "GIT_DIR",
                "GIT_WORK_TREE",
                "GIT_NAMESPACE",
                "GIT_REPLACE_REF_BASE",
                "PYTHONPATH",
            }
        ),
        "benchmark Git environment retained caller selectors",
    )
    require(expected["LANGUAGE"] == "C.UTF-8", "benchmark Git locale was not canonicalized")
    require(
        experiment.ENVIRONMENT_CONTRACT == "clean_reproduction_subprocess_environment_v1",
        "benchmark environment contract identifier drifted",
    )
    print("test_build_benchmark_packet_environment: Git calls are isolated and bounded")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
