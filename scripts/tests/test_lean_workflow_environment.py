#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep the required Lean workflow on the canonical command environment."""

from __future__ import annotations

import _test_bootstrap  # noqa: F401

import ast
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = ROOT / ".github" / "workflows" / "lean.yml"
WARM_WORKFLOW = ROOT / ".github" / "workflows" / "lean-cache-warm.yml"
COVERAGE_WORKFLOW = ROOT / ".github" / "workflows" / "lean-coverage-build.yml"
# Single-job post-merge workflows carry the baseline on their one job.
POST_MERGE_JOBS = ("warm", "coverage")
SETUP_PYTHON_ACTION = "actions/setup-python@5fda3b95a4ea91299a34e894583c3862153e4b97"
PINNED_PYTHON_VERSION = 'python-version: "3.12.9"'
PINNED_PYTHON_JOBS = ("build", "external-verification", "release-surfaces")
PINNED_VALIDATOR_PATH_EXPORT = (
    "python_bin_dir=\"$(python3 -c 'import os, sys; "
    "print(os.path.dirname(sys.executable))')\"\n"
    '          echo "$python_bin_dir" >> "$GITHUB_PATH"'
)
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
        jobs = "|".join(re.escape(job) for job in POST_MERGE_JOBS)
        match = re.search(
            rf"(?ms)^  (?:{jobs}):\n.*?^    env:\n(?P<body>.*?)(?=^    steps:\n)",
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


def require_release_validator_path(workflow: str) -> None:
    """Keep pinned console scripts reachable after the isolated PATH reset."""
    release_body = job_body(workflow, "release-surfaces")
    install_match = re.search(
        r"(?ms)^      - name: Install metadata validators\n"
        r"(?P<body>.*?)(?=^      - |\Z)",
        release_body,
    )
    require(
        install_match is not None,
        "release-surfaces lost the metadata-validator install step",
    )
    install_body = install_match.group("body") if install_match is not None else ""
    require(
        install_body.count(PINNED_VALIDATOR_PATH_EXPORT) == 1,
        "release-surfaces must export setup-python's executable directory exactly once",
    )


def evaluate_condition(expression: str, values: dict[str, object]) -> bool:
    """Evaluate the supported boolean subset, refusing unknown expressions."""
    rendered = expression
    for key, value in values.items():
        rendered = rendered.replace(key, repr(value))
    rendered = rendered.replace("&&", " and ").replace("||", " or ")
    rendered = re.sub(r"!(?!=)", "not ", rendered).strip()
    tree = ast.parse(rendered, mode="eval")
    allowed = (ast.Expression, ast.BoolOp, ast.UnaryOp, ast.Compare,
               ast.Constant, ast.And, ast.Or, ast.Not, ast.Eq, ast.NotEq)
    require(all(isinstance(node, allowed) for node in ast.walk(tree)),
            "unsupported CI scheduling expression")
    return bool(eval(compile(tree, "<CI condition>", "eval"), {"__builtins__": {}}))


def require_evidence_before_expensive_jobs(workflow: str) -> None:
    """Only explicit recovery may bypass stale evidence, never a PR."""
    gate = job_body(workflow, "change_scope")
    steps = re.split(r"(?m)^      - ", gate)[1:]
    evidence = [s for s in steps if "run: python3 scripts/refresh_projections.py --preflight" in s]
    require(len(evidence) == 1, "classification must run exactly one committed-evidence gate")
    condition = re.search(r"(?m)^        if: \$\{\{ (.+) \}\}$", evidence[0])
    require(condition is not None, "evidence recovery condition is missing")
    for event in ("pull_request", "push", "workflow_dispatch"):
        for scope in ("", "all", "external-verification-only", "release-surfaces-only", "dependency-index-refresh"):
            actual = evaluate_condition(condition.group(1), {
                "github.event_name": event, "inputs.scope": scope,
            })
            require(actual == (event != "workflow_dispatch" or scope != "dependency-index-refresh"),
                    f"evidence gate schedules incorrectly: {event}/{scope}")
    for name in ("build", "external-verification", "release-surfaces"):
        body = job_body(workflow, name)
        needs = re.search(r"(?m)^    needs: (.+)$", body)
        require(needs is not None and "change_scope" in needs.group(1).strip("[]").split(", "),
                f"{name} can bypass the evidence gate")
    require("--full-check" in job_body(workflow, "build"), "cheap freshness replaced Lean export")


def require_release_before_expensive_jobs(workflow: str) -> None:
    """Evaluate the actual job conditions across failed and selective runs.

    GitHub implicitly requires successful dependencies unless an expression
    contains a status function. Only the explicit replay-only dispatch may
    accept the intentionally skipped release job.
    """
    release = job_body(workflow, "release-surfaces")
    require("needs: change_scope" in release,
            "release checks must remain independent of expensive jobs")
    for job in ("build", "external-verification"):
        body = job_body(workflow, job)
        needs = re.search(r"(?m)^    needs: \[([^\]]+)\]$", body)
        require(needs is not None, f"{job} must declare its release dependency")
        require(set(x.strip() for x in needs.group(1).split(",")) ==
                {"change_scope", "release-surfaces"},
                f"{job} must await classification and release checks")
        condition = re.search(r"(?m)^    if: \$\{\{ (.+) \}\}$", body)
        require(condition is not None, f"{job} lost its scope condition")
        expression = condition.group(1)
        for event, scope, result, cancelled, corpus_only, expected in (
            ("pull_request", "", "success", False, "false", True),
            ("pull_request", "", "failure", False, "false", False),
            ("pull_request", "", "skipped", False, "false", False),
            ("pull_request", "", "cancelled", False, "false", False),
            ("pull_request", "", "success", True, "false", False),
            ("pull_request", "", "success", False, "true", job == "build"),
            ("workflow_dispatch", "all", "success", False, "false", True),
            ("workflow_dispatch", "all", "failure", False, "false", False),
            ("workflow_dispatch", "release-surfaces-only", "success", False, "false", False),
            ("workflow_dispatch", "external-verification-only", "skipped", False, "false",
             job == "external-verification"),
            ("workflow_dispatch", "external-verification-only", "failure", False, "false", False),
            ("workflow_dispatch", "external-verification-only", "skipped", True, "false", False),
            ("workflow_dispatch", "dependency-index-refresh", "skipped", False, "false", job == "build"),
            ("workflow_dispatch", "dependency-index-refresh", "failure", False, "false", False),
            ("workflow_dispatch", "dependency-index-refresh", "skipped", True, "false", False),
            ("pull_request", "dependency-index-refresh", "skipped", False, "false", False),
        ):
            for change_result in ("success", "failure", "skipped", "cancelled"):
                values = {
                    "github.event_name": event,
                    "inputs.scope": scope,
                    "needs.change_scope.result": change_result,
                    "needs.change_scope.outputs.erdos1041_corpus_only": corpus_only,
                    "needs.release-surfaces.result": result,
                    "cancelled()": cancelled,
                }
                actual = evaluate_condition(expression, values)
                if "cancelled()" not in expression:
                    actual = actual and result == "success" and change_result == "success" and not cancelled
                require(actual == (expected and change_result == "success"),
                        f"{job} schedules incorrectly: {event}/{scope}/{result}, "
                        f"cancelled={cancelled}, corpus_only={corpus_only}, classification={change_result}")


def main() -> int:
    environment = workflow_environment(WORKFLOW)
    warm_environment = workflow_environment(WARM_WORKFLOW)
    require(
        environment == warm_environment,
        "lean.yml and lean-cache-warm.yml have divergent command environments",
    )
    require(
        environment == workflow_environment(COVERAGE_WORKFLOW),
        "lean.yml and lean-coverage-build.yml have divergent command environments",
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
    require_release_validator_path(workflow)
    require_evidence_before_expensive_jobs(workflow)
    require_release_before_expensive_jobs(workflow)
    require(
        re.search(r"(?m)^    env:\n", workflow) is None,
        "a Lean job added a job-level environment that could override the baseline",
    )
    print("test_lean_workflow_environment: Lean jobs share the isolated command environment")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
