#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression contract for projection-refresh subprocess environment isolation."""

from __future__ import annotations

import json
import os
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
    }
    with tempfile.TemporaryDirectory() as raw:
        with patch.dict(os.environ, hostile_environment, clear=False):
            sanitized = refresh_projections.clean_environment()
            require(
                all(key not in sanitized for key in hostile_environment),
                "projection environment retained a hostile Git selector",
            )
            child = refresh_projections.run(
                [
                    sys.executable,
                    "-c",
                    "import json, os; print(json.dumps({k: os.environ[k] for k in "
                    "('GIT_DIR', 'GIT_NAMESPACE', 'GIT_REPLACE_REF_BASE') "
                    "if k in os.environ}))",
                ],
                cwd=Path(raw),
            )
            require(child.returncode == 0, "projection child process failed")
            require(
                json.loads(child.stdout) == {},
                "projection child process inherited a hostile Git selector",
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
    print(
        "test_refresh_projections_environment: projection subprocesses cannot "
        "inherit caller Git selectors"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
