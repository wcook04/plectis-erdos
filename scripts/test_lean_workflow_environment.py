#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep the required Lean workflow on the canonical command environment."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / ".github" / "workflows" / "lean.yml"
WARM_WORKFLOW = ROOT / ".github" / "workflows" / "lean-cache-warm.yml"
SETUP_PYTHON_ACTION = "actions/setup-python@5fda3b95a4ea91299a34e894583c3862153e4b97"
PINNED_PYTHON_VERSION = 'python-version: "3.12.9"'
PINNED_PYTHON_JOBS = ("build", "external-verification", "release-surfaces")
REQUIRED_KEYS = {
    "GIT_CONFIG_NOSYSTEM",
    "GIT_CONFIG_GLOBAL",
    "GIT_OPTIONAL_LOCKS",
    "GIT_NO_REPLACE_OBJECTS",
    "GIT_ASKPASS",
    "GIT_NAMESPACE",
    "GIT_REPLACE_REF_BASE",
    "PYTHONHOME",
    "PYTHONPATH",
    "PYTHONOPTIMIZE",
    "PATH",
    "LC_ALL",
    "LANG",
    "PYTHONHASHSEED",
    "PYTHONNOUSERSITE",
    "PYTHONDONTWRITEBYTECODE",
    "PYTHONUTF8",
}


def require(condition: bool, message: str) -> None:
    """Keep workflow portability failures active under ``python -O``."""
    if not condition:
        raise AssertionError(message)


def workflow_environment(path: Path) -> dict[str, str]:
    workflow = path.read_text(encoding="utf-8")
    match = re.search(r"(?ms)^env:\n(?P<body>.*?)(?=^jobs:\n)", workflow)
    indent = "  "
    if match is None:
        match = re.search(
            r"(?ms)^  warm:\n.*?^    env:\n(?P<body>.*?)(?=^    steps:\n)",
            workflow,
        )
        indent = "      "
    require(match is not None, f"{path.name} lost its workflow environment")
    body = match.group("body")
    return dict(
        re.findall(rf"(?m)^{re.escape(indent)}([A-Z][A-Z0-9_]+): (.+)$", body)
    )


def job_body(workflow: str, job: str) -> str:
    match = re.search(rf"(?ms)^  {re.escape(job)}:\n(?P<body>.*?)(?=^  \S|\Z)", workflow)
    require(match is not None, f"Lean workflow lost the {job} job")
    return match.group("body") if match is not None else ""


def require_pinned_python(workflow: str) -> None:
    for job in PINNED_PYTHON_JOBS:
        body = job_body(workflow, job)
        setup_steps = re.findall(
            rf"(?ms)^      - name: Install the pinned Python runtime\n"
            rf"(?P<body>.*?)(?=^      - |\Z)",
            body,
        )
        require(
            len(setup_steps) == 1,
            f"{job} must install the pinned Python action exactly once",
        )
        setup_body = setup_steps[0] if setup_steps else ""
        require(
            setup_body.count(SETUP_PYTHON_ACTION) == 1,
            f"{job} must install the pinned Python action exactly once",
        )
        require(
            setup_body.count(PINNED_PYTHON_VERSION) == 1,
            f"{job} must install Python 3.12.9 exactly once",
        )
        # setup-python's `cache` input names a package manager (pip, pipenv,
        # poetry); it is not a boolean, and `cache: false` makes the action fail
        # with "Caching for 'false' is not supported". The property is that the
        # step enables no dependency cache at all, and setup-python caches
        # nothing unless a provider is named, so the check is that none is.
        require(
            "cache:" not in setup_body,
            f"{job} must not use an implicit setup-python cache",
        )


def main() -> int:
    environment = workflow_environment(WORKFLOW)
    warm_environment = workflow_environment(WARM_WORKFLOW)
    require(
        environment == warm_environment,
        "lean.yml and lean-cache-warm.yml have divergent command environments",
    )
    require(
        REQUIRED_KEYS <= environment.keys(),
        "Lean workflow environment lost a required Git/Python portability key",
    )
    for key in ("GIT_NAMESPACE", "GIT_REPLACE_REF_BASE"):
        require(
            environment[key] == '""',
            f"Lean workflow environment must clear {key}",
        )
    workflow = WORKFLOW.read_text(encoding="utf-8")
    require_pinned_python(workflow)
    require(
        re.search(r"(?m)^    env:\n", workflow) is None,
        "a Lean job added a job-level environment that could override the baseline",
    )
    print("test_lean_workflow_environment: Lean jobs share the isolated command environment")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
