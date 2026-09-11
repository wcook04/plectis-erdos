#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Aggregate test runner must retain a failing child's exit status and stderr."""

from __future__ import annotations

import inspect
import subprocess
import sys

import check_release


CHILD_SCRIPT = (
    "import sys\n"
    "print('child-stdout-should-not-hide-failure')\n"
    "print('child-diagnostic-fixture', file=sys.stderr)\n"
    "sys.exit(7)\n"
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> int:
    source = inspect.getsource(check_release)
    require("2>/dev/null" not in source, "release runner still discards stderr")
    require("| tail" not in source, "release runner still truncates child output in a pipe")

    results = check_release.run_independent_checks(
        {
            "deliberately_failing_child": [
                sys.executable,
                "-c",
                CHILD_SCRIPT,
            ]
        }
    )
    child = results["deliberately_failing_child"]
    require(child.returncode == 7, f"child exit 7 was lost: {child.returncode}")
    require(
        "child-diagnostic-fixture" in (child.stderr or ""),
        f"child stderr was discarded: {child.stderr!r}",
    )
    failures = check_release.failed_independent_checks(results)
    require(failures, "aggregate runner treated a failing child as success")
    require(
        any(
            "deliberately_failing_child" in row
            and "exit 7" in row
            and "child-diagnostic-fixture" in row
            for row in failures
        ),
        f"aggregate runner did not identify the failing child: {failures}",
    )

    hidden = subprocess.run(
        ["bash", "--noprofile", "--norc", "-c", "python3 -c 'import sys; sys.exit(7)' 2>/dev/null | tail -20"],
        capture_output=True,
        text=True,
        check=False,
    )
    require(
        hidden.returncode == 0,
        "control pipeline unexpectedly preserved the child exit; the regression fixture drifted",
    )
    require(
        child.returncode != hidden.returncode,
        "production runner still matches the concealing pipeline",
    )

    print(
        "test_release_child_status: failing child exit 7 is retained and named; "
        "the no-pipefail pipeline is not used"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
