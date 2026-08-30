#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep the cache-warm workflow on the canonical clean command contract."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / ".github" / "workflows" / "lean-cache-warm.yml"
SETUP_PYTHON_ACTION = "actions/setup-python@5fda3b95a4ea91299a34e894583c3862153e4b97"
EXPECTED_ENVIRONMENT = {
    "GIT_CONFIG_NOSYSTEM": '"1"',
    "GIT_CONFIG_GLOBAL": "/dev/null",
    "GIT_OPTIONAL_LOCKS": '"0"',
    "GIT_NO_REPLACE_OBJECTS": '"1"',
    "GIT_PAGER": "cat",
    "GIT_TERMINAL_PROMPT": '"0"',
    "GIT_ASKPASS": "/bin/false",
    "GIT_TRACE": '""',
    "GIT_TRACE2": '""',
    "GIT_TRACE_PACKET": '""',
    "GIT_TRACE_PERFORMANCE": '""',
    "GIT_TRACE_SETUP": '""',
    "GIT_TRACE_CURL": '""',
    "GIT_TRACE2_EVENT": '""',
    "GIT_TRACE2_PERF": '""',
    "GIT_SSH": '""',
    "GIT_SSH_COMMAND": '""',
    "GIT_SSH_VARIANT": '""',
    "GIT_EXTERNAL_DIFF": '""',
    "GIT_DIFF_OPTS": '""',
    "GIT_EDITOR": '""',
    "GIT_SEQUENCE_EDITOR": '""',
    "GIT_MERGE_AUTOEDIT": '""',
    "GIT_DIR": '""',
    "GIT_WORK_TREE": '""',
    "GIT_INDEX_FILE": '""',
    "GIT_NAMESPACE": '""',
    "GIT_REPLACE_REF_BASE": '""',
    "GIT_OBJECT_DIRECTORY": '""',
    "GIT_ALTERNATE_OBJECT_DIRECTORIES": '""',
    "GIT_COMMON_DIR": '""',
    "GIT_CEILING_DIRECTORIES": '""',
    "GIT_DISCOVERY_ACROSS_FILESYSTEM": '""',
    "PYTHONHOME": '""',
    "PYTHONPATH": '""',
    "PYTHONSTARTUP": '""',
    "PYTHONUSERBASE": '""',
    "PYTHONBREAKPOINT": '""',
    "PYTHONWARNINGS": '""',
    "PYTHONOPTIMIZE": '""',
    "PATH": "/usr/local/bin:/usr/bin:/bin",
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
    environment = dict(
        re.findall(r"(?m)^      ([A-Z][A-Z0-9_]+): (.+)$", body)
    )
    require(
        environment == EXPECTED_ENVIRONMENT,
        "cache-warm job environment drifted from the canonical exact key set",
    )
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
        body.count(SETUP_PYTHON_ACTION) == 1,
        "cache-warm job must install the pinned Python action exactly once",
    )
    require(
        body.count('python-version: "3.12.9"') == 1,
        "cache-warm job must install Python 3.12.9 exactly once",
    )
    require(
        body.count("cache: false") == 1,
        "cache-warm job must not use an implicit setup-python cache",
    )
    require(
        len(re.findall(r"uses:[^\n]*@[0-9a-f]{40}(?:\s|#|$)", body)) == 3,
        "cache-warm actions are not pinned to immutable revisions",
    )
    print("test_lean_cache_warm_environment: cache-warm commands are isolated and pinned")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
