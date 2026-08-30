#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression contract for release-gate subprocess environment isolation."""

from __future__ import annotations

import json
import os
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
    with tempfile.TemporaryDirectory() as raw:
        with patch.dict(os.environ, hostile_environment, clear=False):
            sanitized = check_release.clean_environment()
            require(
                all(key not in sanitized for key in hostile_environment),
                "release environment retained a hostile Git selector",
            )
            child = check_release.run(
                [
                    sys.executable,
                    "-c",
                    "import json, os; print(json.dumps({k: os.environ[k] for k in "
                    "('GIT_DIR', 'GIT_NAMESPACE', 'GIT_REPLACE_REF_BASE') "
                    "if k in os.environ}))",
                ],
                cwd=Path(raw),
                capture_output=True,
                text=True,
                check=False,
            )
            require(child.returncode == 0, "sanitized release child process failed")
            require(
                json.loads(child.stdout) == {},
                "sanitized release child inherited a Git selector",
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
    print(
        "test_check_release_environment: release-gate child processes cannot "
        "inherit caller Git selectors"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
