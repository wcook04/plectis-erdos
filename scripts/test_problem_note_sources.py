#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial fixtures for the problem-note source and coverage contract."""

from __future__ import annotations

import json
import os
import tempfile
from pathlib import Path
from unittest.mock import patch

import check_problem_note_sources as scanner
from check_problem_note_sources import (
    declarations_in,
    declares_at,
    linked_declaration_keys,
    required_note_declaration_failures,
    source_pin_failure,
    validated_coverage_floor,
)

ROOT = Path(__file__).resolve().parent.parent


def require(condition: bool, message: str) -> None:
    """Keep the environment contract active when Python is run with -O."""
    if not condition:
        raise AssertionError(message)


def test_worktree_source_reader_boundary() -> None:
    """Worktree note inputs must be regular, in-checkout UTF-8 files."""
    with tempfile.TemporaryDirectory(prefix="problem-note-source-safety-") as raw:
        root = Path(raw) / "checkout"
        outside = Path(raw) / "outside"
        root.mkdir()
        outside.mkdir()
        regular = root / "note.tex"
        regular.write_text("note\n", encoding="utf-8")
        original_root = scanner.ROOT
        scanner.ROOT = root
        try:
            require(
                scanner.safe_worktree_text(regular) == "note\n",
                "regular note source did not load",
            )
            linked = root / "linked.tex"
            linked.symlink_to(outside / "note.tex")
            try:
                scanner.safe_worktree_text(linked)
            except scanner.UnsafeSourceInput as error:
                require("symbolic link" in str(error), str(error))
            else:
                raise AssertionError("note source reader followed a symlink")

            if hasattr(os, "mkfifo"):
                fifo = root / "note.fifo"
                os.mkfifo(fifo)
                try:
                    scanner.safe_worktree_text(fifo)
                except scanner.UnsafeSourceInput as error:
                    require("regular file" in str(error), str(error))
                else:
                    raise AssertionError("note source reader opened a FIFO")
        finally:
            scanner.ROOT = original_root


def test_comment_injection_is_not_a_declaration() -> None:
    source = """\
/-!
theorem linked
/- nested comment
theorem linked
-/
-/
-- theorem linked
theorem live : True := by
  trivial
"""
    assert declarations_in(source) == ["live"]


def test_split_declaration_head_resolves_at_keyword_line() -> None:
    lines = ["theorem", "    splitHead", "    : True := by", "  trivial"]
    assert declares_at(lines, 0, "splitHead")
    assert not declares_at(lines, 0, "otherHead")


def test_wrong_module_name_collision_is_not_coverage() -> None:
    note = r"\lref{Erdos257/Other.lean}{10}{sharedName}"
    linked = linked_declaration_keys(note)
    assert ("ErdosProblems/Erdos257/Other.lean", "sharedName") in linked
    assert ("ErdosProblems/Erdos257/Headline.lean", "sharedName") not in linked


def test_missing_required_anchor_is_rejected() -> None:
    row = {
        "problem_id": "synthetic",
        "principal_module": "ErdosProblems.Synthetic.Headline",
        "companion_modules": [],
        "required_note_declarations": [
            {
                "module": "ErdosProblems.Synthetic.Headline",
                "declaration": "headline",
            }
        ],
    }
    current = {("ErdosProblems/Synthetic/Headline.lean", "headline")}
    wrong_module_link = {("ErdosProblems/Synthetic/Other.lean", "headline")}
    failures = required_note_declaration_failures(
        row, current, wrong_module_link
    )
    assert failures == [
        "synthetic: note does not link required headline declaration "
        "ErdosProblems/Synthetic/Headline.lean::headline"
    ]


def test_invalid_coverage_floor_is_rejected() -> None:
    for value in (None, True, "0.6", 0, -0.1, 1.1, float("inf"), float("nan")):
        floor, failures = validated_coverage_floor(
            {"note_coverage_floor": value}
        )
        assert floor is None
        assert failures
    floor, failures = validated_coverage_floor({"note_coverage_floor": 0.6})
    assert floor == 0.6
    assert failures == []


def test_erdos257_headline_anchors_are_required() -> None:
    index = json.loads(
        (ROOT / "docs" / "problem_index_source.json").read_text(encoding="utf-8")
    )
    row = next(
        problem
        for problem in index["problems"]
        if problem["problem_id"] == "erdos_257"
    )
    anchors = {
        (anchor["module"], anchor["declaration"])
        for anchor in row["required_note_declarations"]
    }
    assert anchors == {
        (
            "ErdosProblems.Erdos257.MersenneSubseriesRigidity",
            "selectedMersenneTail_lt_weight",
        ),
        (
            "ErdosProblems.Erdos257.MersenneSubseriesRigidity",
            "supportedMersenneDigitValue_injective",
        ),
        (
            "ErdosProblems.Erdos257.MersenneSubseriesRigidity",
            "volume_supportedMersenneAchievementSet_dichotomy",
        ),
    }


def test_mismatched_note_commitshort_is_rejected() -> None:
    note = r"""
\renewcommand{\commit}{76b5b0a7ed5da7ebf3b9ed3bfd2fb480b6c38ee0}
\renewcommand{\commitshort}{08d83b6689c8}
"""
    assert source_pin_failure(
        "paper/synthetic.tex",
        note,
        "571ec44f2aad2a1497098971a91858f527038b55",
        "571ec44f2aad",
    ) == (
        "paper/synthetic.tex: displayed \\commitshort 08d83b6689c8 "
        "does not match the effective \\commit prefix 76b5b0a7ed5d"
    )


def test_commit_override_without_matching_short_is_rejected() -> None:
    note = r"\renewcommand{\commit}{599f7e50a15b288f27f9b57ece16fdd396cb6d76}"
    assert source_pin_failure(
        "paper/synthetic.tex",
        note,
        "571ec44f2aad2a1497098971a91858f527038b55",
        "571ec44f2aad",
    ) == (
        "paper/synthetic.tex: displayed \\commitshort 571ec44f2aad "
        "does not match the effective \\commit prefix 599f7e50a15b"
    )


def test_git_snapshot_reads_use_clean_bounded_environment() -> None:
    hostile_environment = {
        "GIT_DIR": "/private/wrong-git-dir",
        "GIT_NAMESPACE": "refs/namespaces/wrong-release",
        "GIT_REPLACE_REF_BASE": "refs/replace/",
        "PYTHONPATH": "/private/wrong-python-path",
        "LC_ALL": "C",
        "LANG": "C",
        "PATH": "/private/wrong-bin",
    }
    completed = scanner.subprocess.CompletedProcess(
        ["git", "show"], 0, stdout="theorem linked : True\n", stderr=""
    )
    with patch.dict(os.environ, hostile_environment, clear=False):
        with patch.object(scanner.subprocess, "run", return_value=completed) as run:
            lines = scanner.snapshot_lines(
                "a" * 40, "ErdosProblems/Synthetic.lean", {}
            )

    require(lines == ["theorem linked : True"], "Git snapshot output was not returned")
    require(len(run.call_args_list) == 1, "Git snapshot read was not exercised")
    kwargs = run.call_args.kwargs
    sanitized = kwargs["env"]
    for key in ("GIT_DIR", "GIT_NAMESPACE", "GIT_REPLACE_REF_BASE", "PYTHONPATH"):
        require(key not in sanitized, f"ambient {key} leaked into Git snapshot read")
    require(sanitized["LC_ALL"] == "C.UTF-8", "canonical locale missing")
    require(sanitized["LANG"] == "C.UTF-8", "canonical LANG missing")
    require(sanitized["PATH"] == os.defpath, "ambient PATH leaked into Git snapshot read")
    require(
        kwargs["timeout"] == scanner.singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
        "Git snapshot read timeout drifted",
    )
    require(
        scanner.ENVIRONMENT_CONTRACT
        == "clean_committed_snapshot_subprocess_environment_v1",
        "problem-note environment contract drifted",
    )


def main() -> int:
    test_worktree_source_reader_boundary()
    test_comment_injection_is_not_a_declaration()
    test_split_declaration_head_resolves_at_keyword_line()
    test_wrong_module_name_collision_is_not_coverage()
    test_missing_required_anchor_is_rejected()
    test_invalid_coverage_floor_is_rejected()
    test_erdos257_headline_anchors_are_required()
    test_mismatched_note_commitshort_is_rejected()
    test_commit_override_without_matching_short_is_rejected()
    test_git_snapshot_reads_use_clean_bounded_environment()
    print(
        "test_problem_note_sources: comment injection, split heads, module "
        "collisions, required anchors, invalid floors, and mismatched source "
        "pins rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
