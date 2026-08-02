#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial fixtures for the problem-note source and coverage contract."""

from __future__ import annotations

import json
from pathlib import Path

from check_problem_note_sources import (
    declarations_in,
    linked_declaration_keys,
    required_note_declaration_failures,
    source_pin_failure,
    validated_coverage_floor,
)

ROOT = Path(__file__).resolve().parent.parent


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


def main() -> int:
    test_comment_injection_is_not_a_declaration()
    test_wrong_module_name_collision_is_not_coverage()
    test_missing_required_anchor_is_rejected()
    test_invalid_coverage_floor_is_rejected()
    test_erdos257_headline_anchors_are_required()
    test_mismatched_note_commitshort_is_rejected()
    test_commit_override_without_matching_short_is_rejected()
    print(
        "test_problem_note_sources: comment injection, module collisions, "
        "required anchors, invalid floors, and mismatched source pins rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
