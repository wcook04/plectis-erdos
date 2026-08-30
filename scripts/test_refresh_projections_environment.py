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
            assert all(key not in sanitized for key in hostile_environment)
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
            assert child.returncode == 0
            assert json.loads(child.stdout) == {}

    assert refresh_projections.ENVIRONMENT_CONTRACT == (
        "clean_committed_snapshot_subprocess_environment_v1"
    )
    assert "GIT_NAMESPACE" in refresh_projections.SANITIZED_GIT_ENVIRONMENT_KEYS
    assert "GIT_REPLACE_REF_BASE" in refresh_projections.SANITIZED_GIT_ENVIRONMENT_KEYS
    print(
        "test_refresh_projections_environment: projection subprocesses cannot "
        "inherit caller Git selectors"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
