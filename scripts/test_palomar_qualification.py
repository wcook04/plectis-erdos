#!/usr/bin/env python3
"""Focused contract tests for the local Palomar qualification product."""

from __future__ import annotations

import copy
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

import check_palomar_qualification as checker


ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "scripts" / "check_palomar_qualification.py"


def expect_unsafe(path: Path, root: Path, label: str) -> None:
    try:
        checker.safe_text(path, root=root)
    except checker.UnsafeQualificationInput:
        return
    raise AssertionError(f"qualification input escaped safe boundary: {label}")


def test_safe_input_boundary() -> None:
    with tempfile.TemporaryDirectory(prefix="palomar-input-") as raw_workspace:
        workspace = Path(raw_workspace)
        regular = workspace / "regular.txt"
        regular.write_text("qualification input\n", encoding="utf-8")
        if checker.safe_text(regular, root=workspace) != "qualification input\n":
            raise AssertionError("qualification regular-file input was not read")

        directory = workspace / "directory"
        directory.mkdir()
        expect_unsafe(directory, workspace, "directory")

        symlink = workspace / "symlink.txt"
        symlink.symlink_to(regular)
        expect_unsafe(symlink, workspace, "symlink")

        if hasattr(os, "mkfifo"):
            fifo = workspace / "fifo"
            os.mkfifo(fifo)
            expect_unsafe(fifo, workspace, "FIFO")


def run_checker(*extra: str) -> dict:
    result = subprocess.run(
        [sys.executable, str(CHECKER), "--json", *extra],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    return json.loads(result.stdout)


def test_normal_and_optimised_checker_agree() -> None:
    normal = run_checker()
    optimised = subprocess.run(
        [sys.executable, "-O", str(CHECKER), "--json"],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    assert optimised.returncode == 0, optimised.stdout + optimised.stderr
    assert json.loads(optimised.stdout) == normal
    assert normal["ok"] is True
    assert normal["decision"] == "NOT_READY"


def test_full_current_roster_and_eight_problem_crosswalk() -> None:
    showcase = json.loads((ROOT / "docs/PALOMAR_RESULT_SHOWCASE.json").read_text())
    names = [
        name
        for row in showcase["frontier_by_problem"]
        for name in row["comparator_declarations"]
    ]
    assert len(names) == 31
    assert len(names) == len(set(names))
    assert [row["problem"] for row in showcase["frontier_by_problem"]] == [68, 243, 249, 251, 257, 269, 1041, 1049]
    assert showcase["candidate_selection"]["declaration"] in names
    assert showcase["candidate_selection"]["family_id"] == "pairwise_coprime_support"


def test_adversarial_roster_drop_is_not_silently_accepted() -> None:
    showcase = json.loads((ROOT / "docs/PALOMAR_RESULT_SHOWCASE.json").read_text())
    comparator = json.loads(
        subprocess.check_output(["git", "show", "HEAD:verification/comparator.json"], cwd=ROOT)
    )
    reconciliation = json.loads((ROOT / "docs/PALOMAR_POLICY_RECONCILIATION.json").read_text())
    damaged = copy.deepcopy(showcase)
    damaged["frontier_by_problem"][0]["comparator_declarations"].pop()
    source = CHECKER.read_text()
    namespace: dict = {}
    exec(compile(source, str(CHECKER), "exec"), namespace)
    errors = namespace["roster_errors"](ROOT, comparator, damaged, reconciliation)
    assert errors
    assert any("crosswalk" in error for error in errors)


if __name__ == "__main__":
    test_safe_input_boundary()
    test_normal_and_optimised_checker_agree()
    test_full_current_roster_and_eight_problem_crosswalk()
    test_adversarial_roster_drop_is_not_silently_accepted()
    print("palomar qualification tests: ok")
