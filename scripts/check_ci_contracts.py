#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Run the cold build/workflow contracts used by publication and CI.

These suites use temporary fixtures and mocks; they never provision Lean.
Adding an expensive-job test without registering it here fails before any
cache restore or compilation. Both ordinary and optimized Python must pass.
"""
from __future__ import annotations

import re
import shlex
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import validation_singleflight as singleflight

ROOT = Path(__file__).resolve().parents[1]
TESTS = (
    "test_check_axiom_audit.py",
    "test_dependency_lock_contract.py",
    "test_lean_fast_build.py",
    "test_lean_dependency_environment.py",
    "test_lean_dependency_index_cache.py",
    "test_lean_workflow_environment.py",
    "test_lean_cache_warm_environment.py",
    "test_external_verification.py",
    "test_external_verification_release.py",
    "test_erdos249_totient_kernel_comparator.py",
    "test_refresh_projections_coverage.py",
    "test_run_release_check.py",
    "test_check_release_ref.py",
    "test_check_push.py",
    "test_ci_contracts.py",
    "test_ci_release.py",
    "test_check_release_environment.py",
)
WORKFLOW_JOBS = {
    "lean.yml": ("build", "external-verification"),
    "lean-cache-warm.yml": ("warm",),
    "lean-coverage-build.yml": ("coverage",),
}
TIMEOUT_SECONDS = 120
WORKERS = 2


def workflow_tests(workflow: str, jobs: tuple[str, ...]) -> set[str]:
    """Inspect literal Python test commands, failing closed on new syntax.

    This is deliberately a bounded workflow reader, not a YAML/shell
    interpreter. It never executes workflow text or imports its test modules.
    """
    result: set[str] = set()
    for job in jobs:
        match = re.search(rf"(?ms)^  {re.escape(job)}:\n(.*?)(?=^  \S|\Z)", workflow)
        if match is None:
            raise ValueError(f"missing workflow job: {job}")
        for line in match.group(1).splitlines():
            command = line.strip().removeprefix("- ").removeprefix("run: ")
            if not re.match(r"python(?:3(?:\.\d+)?)?\s", command):
                continue
            if "test_" not in command:
                continue
            words = shlex.split(command, comments=True)
            if not any("test_" in word for word in words[1:]):
                continue
            args = words[1:]
            if args and args[0] == "-O":
                args = args[1:]
            if len(args) == 1 and re.fullmatch(r"scripts/test_\w+\.py", args[0]):
                result.add(Path(args[0]).name)
            else:
                raise ValueError(f"unregistered test invocation syntax in {job}: {command}")
    return result


def coverage_errors(root: Path = ROOT, tests: tuple[str, ...] = TESTS) -> list[str]:
    import check_ci_release
    errors = check_ci_release.registry_errors()
    if root == ROOT:
        errors += check_ci_release.workflow_errors((root / ".github/workflows/lean.yml").read_text())
    if len(tests) != len(set(tests)):
        errors.append("CI contract registry repeats a test")
    for test in tests:
        if not (root / "scripts" / test).is_file():
            errors.append(f"missing CI contract: scripts/{test}")
    for workflow, jobs in WORKFLOW_JOBS.items():
        try:
            discovered = workflow_tests((root / ".github/workflows" / workflow).read_text(), jobs)
            for test in sorted(discovered - set(tests)):
                errors.append(f"{workflow} runs {test} after admission but local preflight omits it; register it in check_ci_contracts.TESTS")
        except (OSError, ValueError) as exc:
            errors.append(str(exc))
    return errors


def run_test(test: str, optimized: bool, *, root: Path = ROOT,
             timeout: float = TIMEOUT_SECONDS) -> tuple[str, str | None]:
    label = test + (" (-O)" if optimized else "")
    argv = [sys.executable, *(["-O"] if optimized else []), str(root / "scripts" / test)]
    try:
        result = singleflight.run_bounded(argv, cwd=root, env=singleflight.command_environment(),
                                text=True, capture_output=True, timeout=timeout)
        if result.returncode:
            detail = (result.stdout + "\n" + result.stderr).strip()[-6000:]
            return label, f"exit {result.returncode}\n{detail}"
    except (OSError, subprocess.TimeoutExpired) as exc:
        return label, str(exc)
    return label, None


def run_suite(tests: tuple[str, ...] = TESTS, *, root: Path = ROOT,
              timeout: float = TIMEOUT_SECONDS) -> int:
    # Collect every failure; one broken assertion must not conceal the rest.
    commands = [(test, optimized) for test in tests for optimized in (False, True)]
    with ThreadPoolExecutor(max_workers=WORKERS) as pool:
        results = list(pool.map(lambda pair: run_test(*pair, root=root, timeout=timeout), commands))
    failures = [(name, error) for name, error in results if error is not None]
    for name, error in failures:
        print(f"FAIL {name}: {error}", flush=True)
    print(f"CI contracts: {len(results) - len(failures)}/{len(results)} passed", flush=True)
    return int(bool(failures))


def main() -> int:
    errors = coverage_errors()
    if errors:
        for error in errors:
            print(f"CI contract coverage: {error}", file=sys.stderr)
        return 1
    return run_suite()


if __name__ == "__main__":
    raise SystemExit(main())
