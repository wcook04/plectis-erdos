#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial contract for the read-only public research-return intake.

The workflow invokes this file before it exercises any return data.  Keep the
checker standard-library-only and static: it must be able to establish the
runner, permission, checkout, and issue-form boundary from a clean clone
without importing the research-return implementation or installing packages.
"""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / ".github" / "workflows" / "research-return.yml"
ISSUE_FORM = ROOT / ".github" / "ISSUE_TEMPLATE" / "research_return.yml"
CHECKOUT_SHA = "3d3c42e5aac5ba805825da76410c181273ba90b1"
SETUP_PYTHON_SHA = "5fda3b95a4ea91299a34e894583c3862153e4b97"

# What the workflow must pin. The path-valued GIT_* selectors are deliberately
# absent: an empty string is a value, not an absence, and git rejects it for a
# path ("fatal: The empty string is not a valid path"), so pinning GIT_DIR: ""
# and its neighbours made actions/checkout fail before any repository content
# existed. GIT_CONFIG_GLOBAL is a writable neutral file rather than /dev/null,
# because checkout writes safe.directory into the global config and git 2.55
# needs a lock, which /dev/null cannot take. FORBIDDEN_ENV below keeps both
# forms from coming back.
FORBIDDEN_ENV = (
    'GIT_CONFIG_GLOBAL: "/dev/null"',
    'GIT_DIR: ""',
    'GIT_WORK_TREE: ""',
    'GIT_INDEX_FILE: ""',
    'GIT_COMMON_DIR: ""',
    'GIT_OBJECT_DIRECTORY: ""',
    'GIT_ALTERNATE_OBJECT_DIRECTORIES: ""',
    'GIT_CEILING_DIRECTORIES: ""',
    'GIT_NAMESPACE: ""',
    'GIT_REPLACE_REF_BASE: ""',
)


REPRODUCIBILITY_ENV = (
    'GIT_TRACE2: ""',
    'GIT_TRACE2_EVENT: ""',
    'GIT_TRACE2_PERF: ""',
    'GIT_CONFIG_NOSYSTEM: "1"',
    'GIT_OPTIONAL_LOCKS: "0"',
    'GIT_NO_REPLACE_OBJECTS: "1"',
    'GIT_TERMINAL_PROMPT: "0"',
    'GIT_ASKPASS: "/bin/false"',
    'GIT_PAGER: "cat"',
    'PYTHONPATH: ""',
    'PYTHONHOME: ""',
    'PYTHONSTARTUP: ""',
    'PYTHONUSERBASE: ""',
    'PYTHONBREAKPOINT: ""',
    'PYTHONWARNINGS: ""',
    'PYTHONOPTIMIZE: ""',
    'PYTHONNOUSERSITE: "1"',
    'PYTHONDONTWRITEBYTECODE: "1"',
    'PYTHONHASHSEED: "0"',
    'PYTHONUTF8: "1"',
    'PATH: "/usr/local/bin:/usr/bin:/bin"',
    'LC_ALL: "C.UTF-8"',
    'LANG: "C.UTF-8"',
    'LANGUAGE: "C.UTF-8"',
    'GIT_CONFIG_NOSYSTEM: "1"',
    'GIT_PAGER: "cat"',
)

REQUIRED_COMMANDS = (
    "python3 scripts/test_research_return_workflow.py",
    "python3 -O scripts/test_research_return_workflow.py",
    "python3 scripts/test_contribution_entry.py",
    "python3 -O scripts/test_contribution_entry.py",
    "python3 scripts/test_research_contribution_recognition.py",
    "python3 -O scripts/test_research_contribution_recognition.py",
    "python3 scripts/check_research_contribution_recognition.py",
    "python3 -O scripts/check_research_contribution_recognition.py",
    "python3 scripts/test_research_contributions_result_classes.py",
    "python3 -O scripts/test_research_contributions_result_classes.py",
    "python3 scripts/test_research_contributions_output_safety.py",
    "python3 -O scripts/test_research_contributions_output_safety.py",
    "python3 scripts/test_research_contributions_source_safety.py",
    "python3 -O scripts/test_research_contributions_source_safety.py",
    "python3 scripts/test_research_contributions_symlink_safety.py",
    "python3 -O scripts/test_research_contributions_symlink_safety.py",
    "python3 scripts/test_research_contributions_committed_sources.py",
    "python3 -O scripts/test_research_contributions_committed_sources.py",
    "python3 scripts/test_validate_research_return.py",
    "python3 -O scripts/test_validate_research_return.py",
    "python3 scripts/test_continue_research.py",
    "python3 -O scripts/test_continue_research.py",
    "python3 scripts/test_query_route_memory.py",
    "python3 -O scripts/test_query_route_memory.py",
    "python3 scripts/test_accept_research_return.py",
    "python3 -O scripts/test_accept_research_return.py",
    "python3 scripts/test_research_contributions.py",
    "python3 -O scripts/test_research_contributions.py",
    "python3 scripts/build_research_contributions.py --check",
    "python3 -O scripts/build_research_contributions.py --check",
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def workflow_errors(text: str) -> list[str]:
    """Return actionable failures for the workflow's trust boundary."""
    errors: list[str] = []
    for event in ("pull_request", "push", "workflow_dispatch"):
        if re.search(rf"(?m)^  {event}:\s*$", text) is None:
            errors.append(f"workflow is missing the {event} event")
    for unsafe_event in ("pull_request_target", "issues", "issue_comment"):
        if re.search(rf"(?m)^  {unsafe_event}:\s*$", text):
            errors.append(f"workflow must not automate {unsafe_event}")

    if "permissions:\n  contents: read\n" not in text:
        errors.append("workflow must keep top-level contents read permission")
    if re.search(r"(?m)^\s+[A-Za-z_-]+:\s*write\s*$", text) or "write-all" in text:
        errors.append("workflow must not request write permission")
    if text.count("persist-credentials: false") != 1:
        errors.append("checkout must disable credential persistence exactly once")
    if text.count("fetch-depth: 0") != 1:
        errors.append("accepted-receipt ancestry validation requires full Git history")
    if text.count("filter: blob:none") != 1:
        errors.append("full-history checkout must defer unneeded historical blobs")
    if text.count("cancel-in-progress: true") != 1:
        errors.append("workflow must cancel an older run for the same ref")

    actions = re.findall(r"(?m)^\s*uses:\s*([^@\s]+)@([^\s#]+)", text)
    if not actions:
        errors.append("workflow has no declared action")
    for action, revision in actions:
        if re.fullmatch(r"[0-9a-f]{40}", revision) is None:
            errors.append(f"action {action} is not pinned to a full commit")
    if f"actions/checkout@{CHECKOUT_SHA}" not in text:
        errors.append("workflow lost the repository-pinned checkout action")
    if text.count(f"actions/setup-python@{SETUP_PYTHON_SHA}") != 1:
        errors.append("workflow must use the canonical pinned setup-python action exactly once")

    timeout = re.search(r"(?m)^\s*timeout-minutes:\s*(\d+)\s*$", text)
    if timeout is None or int(timeout.group(1)) > 15:
        errors.append("workflow must retain a bounded timeout of at most 15 minutes")
    if text.count("  validate:\n") != 1:
        errors.append("workflow must contain exactly one validation job")
    if text.count("runs-on: ubuntu-24.04") != 1:
        errors.append("workflow must use exactly one pinned runner image")

    for command in REQUIRED_COMMANDS:
        if text.count(command) != 1:
            errors.append(f"workflow must run exactly once: {command}")
    for forbidden in FORBIDDEN_ENV:
        if forbidden in text:
            errors.append(f"workflow reintroduced a setting that breaks checkout: {forbidden}")
    if "GIT_CONFIG_GLOBAL:" in text and 'GIT_CONFIG_GLOBAL: "/dev' in text:
        errors.append("GIT_CONFIG_GLOBAL must name a writable file, not a device")
    for setting in REPRODUCIBILITY_ENV:
        if text.count(setting) != 1:
            errors.append(f"workflow must pin runner state exactly once: {setting}")
    for forbidden in ("secrets.", "pip install", "curl ", "wget ", "gh ", "actions/cache"):
        if forbidden in text:
            errors.append(f"workflow contains forbidden external-capability marker {forbidden!r}")
    if "test ! -e return.json && ! -e route-memory.json" not in text:
        errors.append("workflow must reject transient return artifacts on main")
    if "github.event_name == 'pull_request'" not in text:
        errors.append("return.json validation must remain pull-request scoped")
    return errors


def issue_form_errors(text: str) -> list[str]:
    """Require public intake to carry machine-readable, reviewable evidence."""
    errors: list[str] = []
    required_markers = (
        "id: return_json",
        "render: json",
        "scripts/validate_research_return.py",
        "--require-submitted --check-git",
        "id: route_memory_json",
        "--require-route-memory-receipt",
        "id: formal_navigation",
        "id: correction_lineage",
        "id: public_safety",
        "id: acceptance_boundary",
    )
    for marker in required_markers:
        if marker not in text:
            errors.append(f"issue form is missing required marker {marker!r}")
    if text.count("    id: return_json") != 1:
        errors.append("issue form must have exactly one machine-readable return field")
    if text.count("    id: route_memory_json") != 1:
        errors.append("issue form must have exactly one route-memory field")
    if "ai_workflow" in text:
        errors.append("issue form must not expose a private repository dependency")
    return errors


def issue_form_link_errors(text: str) -> list[str]:
    """Require every relative issue-form link to resolve in a clean clone."""
    errors: list[str] = []
    for link in re.findall(r"\]\(([^)]+)\)", text):
        target_ref = link.split("#", 1)[0]
        if not target_ref or "://" in target_ref:
            continue
        target = (ISSUE_FORM.parent / target_ref).resolve()
        if not target.is_file():
            errors.append(f"issue form link does not resolve: {link}")
    return errors


def require_rejection(mutated: str, marker: str) -> None:
    errors = workflow_errors(mutated)
    require(errors and any(marker in error for error in errors), f"mutation was accepted: {marker}")


def main() -> int:
    require(WORKFLOW.is_file(), f"missing workflow: {WORKFLOW}")
    require(ISSUE_FORM.is_file(), f"missing issue form: {ISSUE_FORM}")
    workflow = WORKFLOW.read_text(encoding="utf-8")
    issue_form = ISSUE_FORM.read_text(encoding="utf-8")
    require(not workflow_errors(workflow), "live research-return workflow violates its contract")
    require(not issue_form_errors(issue_form), "live research-return issue form violates its contract")
    require(not issue_form_link_errors(issue_form), "live research-return issue form has a dead local link")

    require_rejection(workflow.replace(CHECKOUT_SHA, "v4", 1), "not pinned to a full commit")
    require_rejection(workflow.replace("contents: read", "contents: write", 1), "write permission")
    require_rejection(
        workflow.replace("persist-credentials: false", "persist-credentials: true", 1),
        "credential persistence",
    )
    require_rejection(workflow.replace("fetch-depth: 0", "fetch-depth: 1", 1), "full Git history")
    require_rejection(workflow.replace("cancel-in-progress: true", "cancel-in-progress: false", 1), "cancel")
    require_rejection(workflow.replace("  pull_request:\n", "  issues:\n", 1), "issues")
    require_rejection(
        workflow.replace("python3 -O scripts/test_research_return_workflow.py", "python3 -c 'pass'", 1),
        "test_research_return_workflow.py",
    )
    require_rejection(workflow + "\n# actions/cache\n", "actions/cache")

    print(
        "research-return workflow contract: green; "
        f"{len(REQUIRED_COMMANDS)} required consumers, "
        f"{len(REPRODUCIBILITY_ENV)} environment pins, 8 adversarial mutations rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
