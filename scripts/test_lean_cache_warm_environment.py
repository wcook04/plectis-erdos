#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep the post-merge Lean workflows on the canonical clean command contract.

Two workflows run on main after a merge: the cache warm and the paper-coverage
build. Neither is a required check, so a pull request never runs them; each
runs this test as its first step instead.
"""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / ".github" / "workflows" / "lean-cache-warm.yml"
COVERAGE_WORKFLOW = ROOT / ".github" / "workflows" / "lean-coverage-build.yml"
SETUP_PYTHON_ACTION = "actions/setup-python@5fda3b95a4ea91299a34e894583c3862153e4b97"
EXPECTED_ENVIRONMENT = {
    "GIT_CONFIG_NOSYSTEM": '"1"',
    "GIT_CONFIG_GLOBAL": "/tmp/plectis-ci-empty.gitconfig",
    "GIT_OPTIONAL_LOCKS": '"0"',
    "GIT_NO_REPLACE_OBJECTS": '"1"',
    "GIT_NAMESPACE": '""',
    "GIT_REPLACE_REF_BASE": '""',
    "GIT_PAGER": "cat",
    "GIT_TERMINAL_PROMPT": '"0"',
    "GIT_ASKPASS": "/bin/false",
    "GIT_TRACE2": '""',
    "GIT_TRACE2_EVENT": '""',
    "GIT_TRACE2_PERF": '""',
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


def check_post_merge_job(
    path: Path,
    job: str,
    label: str,
    *,
    timeout_minutes: int,
    pinned_actions: int,
    environment_test_step: str,
) -> tuple[str, str]:
    """Check one single-job post-merge workflow; return its text and job body."""
    workflow = path.read_text(encoding="utf-8")
    match = re.search(
        rf"(?ms)^  {re.escape(job)}:\n(?P<body>.*?)(?=^  \S|\Z)", workflow
    )
    require(match is not None, f"{label} workflow lost its {job} job")
    body = match.group("body") if match is not None else ""
    require("    env:\n" in body, f"{label} job lost its environment contract")
    environment = dict(
        re.findall(r"(?m)^      ([A-Z][A-Z0-9_]+): (.+)$", body)
    )
    require(
        environment == EXPECTED_ENVIRONMENT,
        f"{label} job environment drifted from the canonical exact key set",
    )
    for key, value in EXPECTED_ENVIRONMENT.items():
        require(
            re.search(rf"(?m)^      {re.escape(key)}: {re.escape(value)}$", body)
            is not None,
            f"{label} job lost canonical environment entry {key}",
        )
    require(
        re.search(rf"(?m)^    timeout-minutes: {timeout_minutes}$", body) is not None,
        f"{label} job lost its resource boundary",
    )
    require(
        body.count(SETUP_PYTHON_ACTION) == 1,
        f"{label} job must install the pinned Python action exactly once",
    )
    require(
        body.count('python-version: "3.12.9"') == 1,
        f"{label} job must install Python 3.12.9 exactly once",
    )
    require(
        f"- name: {environment_test_step}" in body,
        f"{label} job must test its own command environment first",
    )
    setup_step = body[
        body.index("- name: Install the pinned Python runtime") :
        body.index(f"- name: {environment_test_step}")
    ]
    require(
        "cache:" not in setup_step,
        f"{label} setup-python step must not request a package-manager cache",
    )
    require(
        len(re.findall(r"uses:[^\n]*@[0-9a-f]{40}(?:\s|#|$)", body)) == pinned_actions,
        f"{label} actions are not pinned to immutable revisions",
    )
    require(
        len(re.findall(r"uses:", body)) == pinned_actions,
        f"{label} job uses an action that is not pinned to an immutable revision",
    )
    require(
        re.search(r"(?m)^  cancel-in-progress: false$", workflow) is not None,
        f"a later main push must not cancel an in-flight {label} run",
    )
    return workflow, body


def main() -> int:
    _, warm_body = check_post_merge_job(
        WORKFLOW,
        "warm",
        "cache-warm",
        timeout_minutes=180,
        pinned_actions=3,
        environment_test_step="Test cache-warm command environment",
    )
    require(
        "Detect Lean-affecting changes" in warm_body,
        "cache-warm must classify Lean-affecting pushes before warming",
    )

    coverage, coverage_body = check_post_merge_job(
        COVERAGE_WORKFLOW,
        "coverage",
        "coverage-build",
        timeout_minutes=240,
        pinned_actions=5,
        environment_test_step="Test post-merge workflow command environment",
    )
    triggers = coverage[coverage.index("\non:\n") : coverage.index("\nconcurrency:\n")]
    # A path filter, so that every run that starts compiles the whole target
    # set; a skip decided inside the job would let a documentation-only push
    # replace a pending Lean run in the concurrency queue.
    require(
        "\n    paths:\n" in triggers,
        "coverage-build must filter pushes by Lean input paths",
    )
    require(
        "Detect Lean-affecting changes" not in coverage_body,
        "coverage-build must not skip its build inside the job",
    )
    require(
        "pull_request" not in triggers,
        "coverage-build must stay off the pull-request path",
    )
    print(
        "test_lean_cache_warm_environment: post-merge Lean workflows are "
        "isolated and pinned"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
