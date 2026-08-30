#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression contract for the historical bridge subprocess environment."""

from __future__ import annotations

import os
import subprocess
from pathlib import Path
from unittest.mock import patch

import historical_bridge_experiment as experiment
import validation_singleflight as singleflight


def require(condition: bool, message: str) -> None:
    """Keep environment-isolation failures active under ``python -O``."""
    if not condition:
        raise AssertionError(message)


def main() -> int:
    completed = subprocess.CompletedProcess(
        ["fixture"], returncode=0, stdout="", stderr=""
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
        with patch.object(
            experiment.subprocess, "run", return_value=completed
        ) as runner:
            result = experiment._run(
                ["fixture"],
                cwd=Path("/historical-fixture"),
                timeout_seconds=17.0,
            )
    require(result.returncode == 0, "historical fixture subprocess failed")
    require(runner.call_args is not None, "historical fixture did not invoke subprocess")
    call = runner.call_args
    environment = call.kwargs["env"]
    expected = singleflight.command_environment()
    require(environment == expected, "historical fixture environment drifted from the canonical contract")
    sanitized_keys = {
        "GIT_DIR",
        "GIT_WORK_TREE",
        "GIT_NAMESPACE",
        "GIT_REPLACE_REF_BASE",
        "PYTHONPATH",
    }
    require(
        all(key not in environment for key in sanitized_keys),
        "historical fixture retained caller Git or Python selectors",
    )
    require(
        environment["LANGUAGE"] == "C.UTF-8",
        "historical fixture did not use the canonical locale",
    )
    require(call.kwargs["timeout"] == 17.0, "historical fixture timeout was not forwarded")
    require(
        experiment.ENVIRONMENT_CONTRACT == "clean_reproduction_subprocess_environment_v1",
        "historical fixture environment contract identifier drifted",
    )
    print("test_historical_bridge_environment: historical child processes are isolated and bounded")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
