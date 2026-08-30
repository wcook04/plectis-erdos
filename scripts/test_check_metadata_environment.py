#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep the metadata validator independent of ambient checkout state."""

from __future__ import annotations

import os
import subprocess
from pathlib import Path
from unittest.mock import patch

import check_metadata
import validation_singleflight as singleflight


def require(condition: bool, message: str) -> None:
    """Keep the environment contract active when Python is run with -O."""
    if not condition:
        raise AssertionError(message)


def main() -> int:
    hostile_environment = {
        "GIT_DIR": "/private/wrong-git-dir",
        "GIT_NAMESPACE": "refs/namespaces/wrong-release",
        "GIT_REPLACE_REF_BASE": "refs/replace/",
        "PYTHONPATH": "/private/wrong-python-path",
        "LC_ALL": "C",
        "LANG": "C",
        "PATH": "/private/wrong-bin",
    }
    fake_executable = "/opt/release-venv/bin/cffconvert"
    with patch.dict(os.environ, hostile_environment, clear=False):
        with patch.object(
            check_metadata.shutil, "which", return_value=fake_executable
        ):
            with patch.object(
                check_metadata.subprocess,
                "run",
                return_value=subprocess.CompletedProcess([], 0),
            ) as run:
                require(check_metadata.main() == 0, "metadata checker failed")

    command, = run.call_args.args
    require(
        command == [fake_executable, "--validate"],
        "metadata checker invoked the wrong command",
    )
    kwargs = run.call_args.kwargs
    require(kwargs["cwd"] == check_metadata.ROOT, "metadata checker cwd drifted")
    require(
        kwargs["timeout"] == singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
        "metadata checker lost its subprocess timeout",
    )
    sanitized = kwargs["env"]
    for key in (
        "GIT_DIR",
        "GIT_NAMESPACE",
        "GIT_REPLACE_REF_BASE",
        "PYTHONPATH",
    ):
        require(key not in sanitized, f"ambient {key} leaked into validator")
    require(sanitized["LC_ALL"] == "C.UTF-8", "canonical LC_ALL was not set")
    require(sanitized["LANG"] == "C.UTF-8", "canonical LANG was not set")
    require(
        sanitized["PATH"].split(os.pathsep)[0] == str(Path(fake_executable).parent),
        "validator executable directory was not preserved",
    )
    require(
        sanitized["GIT_CONFIG_NOSYSTEM"] == "1",
        "system Git configuration was not disabled",
    )
    require(
        sanitized["GIT_NO_REPLACE_OBJECTS"] == "1",
        "Git replacement objects were not disabled",
    )

    require(
        check_metadata.ENVIRONMENT_CONTRACT
        == "clean_committed_snapshot_subprocess_environment_v1",
        "metadata environment contract drifted",
    )
    print(
        "test_check_metadata_environment: cffconvert runs with a clean snapshot "
        "environment and a bounded subprocess"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
