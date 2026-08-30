#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep the cache-warm workflow on the canonical clean command contract."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / ".github" / "workflows" / "lean-cache-warm.yml"
EXPECTED_ENVIRONMENT = {
    "GIT_CONFIG_NOSYSTEM": '"1"',
    "GIT_CONFIG_GLOBAL": "/dev/null",
    "GIT_OPTIONAL_LOCKS": '"0"',
    "GIT_NO_REPLACE_OBJECTS": '"1"',
    "GIT_PAGER": "cat",
    "GIT_TERMINAL_PROMPT": '"0"',
    "GIT_ASKPASS": "/bin/false",
    "GIT_DIR": '""',
    "GIT_WORK_TREE": '""',
    "GIT_INDEX_FILE": '""',
    "GIT_NAMESPACE": '""',
    "GIT_REPLACE_REF_BASE": '""',
    "GIT_OBJECT_DIRECTORY": '""',
    "GIT_ALTERNATE_OBJECT_DIRECTORIES": '""',
    "GIT_COMMON_DIR": '""',
    "LC_ALL": "C.UTF-8",
    "LANG": "C.UTF-8",
    "LANGUAGE": "C.UTF-8",
    "PYTHONHASHSEED": '"0"',
    "PYTHONNOUSERSITE": '"1"',
    "PYTHONDONTWRITEBYTECODE": '"1"',
    "PYTHONUTF8": '"1"',
}


def require(condition: bool, message: str) -> None:
    """Keep workflow portability failures active under ``python -O``."""
    if not condition:
        raise AssertionError(message)


def main() -> int:
    workflow = WORKFLOW.read_text(encoding="utf-8")
    warm_job = re.search(
        r"(?ms)^  warm:\n(?P<body>.*?)(?=^  \S|\Z)", workflow
    )
    require(warm_job is not None, "cache-warm workflow lost its warm job")
    body = warm_job.group("body")
    require("    env:\n" in body, "cache-warm job lost its environment contract")
    for key, value in EXPECTED_ENVIRONMENT.items():
        require(
            re.search(rf"(?m)^      {re.escape(key)}: {re.escape(value)}$", body)
            is not None,
            f"cache-warm job lost canonical environment entry {key}",
        )
    require(
        re.search(r"(?m)^    timeout-minutes: 180$", body) is not None,
        "cache-warm job lost its resource boundary",
    )
    require(
        len(re.findall(r"uses:[^\n]*@[0-9a-f]{40}(?:\s|#|$)", body)) == 2,
        "cache-warm actions are not pinned to immutable revisions",
    )
    print("test_lean_cache_warm_environment: cache-warm commands are isolated and pinned")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
