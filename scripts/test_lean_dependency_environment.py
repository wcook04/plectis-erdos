#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression contract for dependency-bootstrap subprocess environment isolation."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

import build_lean_dependency_index
import validation_singleflight


def require(condition: bool, message: str) -> None:
    """Keep dependency-environment failures active when run with ``python -O``."""
    if not condition:
        raise AssertionError(message)


def main() -> int:
    hostile_environment = {
        "GIT_DIR": "/private/wrong-git-dir",
        "GIT_WORK_TREE": "/private/wrong-work-tree",
        "GIT_INDEX_FILE": "/private/wrong-index",
        "GIT_NAMESPACE": "wrong-namespace",
        "GIT_REPLACE_REF_BASE": "refs/replacements/wrong",
        "PYTHONPATH": "/private/wrong-python-path",
        "LC_ALL": "C",
        "LANG": "en_US.UTF-8",
        "LANGUAGE": "fr_FR",
    }
    with tempfile.TemporaryDirectory() as raw:
        with patch.dict(os.environ, hostile_environment, clear=False):
            sanitized = validation_singleflight.command_environment()
            require(
                all(
                    key not in sanitized
                    for key in hostile_environment
                    if key not in {"LC_ALL", "LANG", "LANGUAGE"}
                ),
                "dependency environment retained a hostile selector",
            )
            require(
                sanitized["LC_ALL"] == "C.UTF-8",
                "dependency environment lost canonical LC_ALL",
            )
            require(
                sanitized["LANG"] == "C.UTF-8",
                "dependency environment lost canonical LANG",
            )
            child = build_lean_dependency_index.run(
                [
                    sys.executable,
                    "-c",
                    "import json, os; print(json.dumps({k: os.environ[k] for k in "
                    "('GIT_DIR', 'GIT_NAMESPACE', 'GIT_REPLACE_REF_BASE', 'PYTHONPATH', "
                    "'LC_ALL', 'LANG', 'LANGUAGE', 'PATH') "
                    "if k in os.environ}))",
                ],
                cwd=Path(raw),
                capture_output=True,
                text=True,
                check=False,
            )
            require(child.returncode == 0, "dependency child process failed")
            child_environment = json.loads(child.stdout)
            require(
                child_environment == {
                    "LC_ALL": "C.UTF-8",
                    "LANG": "C.UTF-8",
                    "LANGUAGE": "C.UTF-8",
                    "PATH": os.pathsep.join(
                        (str(build_lean_dependency_index.TOOLCHAIN_BIN), os.defpath)
                    ),
                },
                "dependency child process inherited a hostile selector or lost elan",
            )
            with patch.object(
                build_lean_dependency_index.subprocess,
                "run",
                return_value=subprocess.CompletedProcess(["fixture"], 0),
            ) as runner:
                observed = build_lean_dependency_index.run(
                    ["fixture"], cwd=Path(raw), check=False
                )
            require(observed.returncode == 0, "dependency run helper failed")
            kwargs = runner.call_args.kwargs
            expected_environment = validation_singleflight.command_environment()
            expected_environment["PATH"] = os.pathsep.join(
                (str(build_lean_dependency_index.TOOLCHAIN_BIN), os.defpath)
            )
            require(
                kwargs["env"] == expected_environment,
                "dependency run helper drifted from the canonical environment",
            )
            require(
                kwargs["timeout"]
                == validation_singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
                "dependency run helper lost its bounded timeout",
            )

    require(
        build_lean_dependency_index.ENVIRONMENT_CONTRACT
        == "clean_committed_snapshot_subprocess_environment_v1",
        "dependency environment contract drifted",
    )
    print(
        "test_lean_dependency_environment: dependency-bootstrap child processes "
        "cannot inherit caller Git or Python selectors"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
