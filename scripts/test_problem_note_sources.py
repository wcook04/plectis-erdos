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


def test_relocated_owner_keeps_the_immutable_paper_anchor() -> None:
    row = {
        "problem_id": "synthetic", "principal_module": "ErdosProblems.Synthetic.Core",
        "required_note_declarations": [{"module": "ErdosProblems.Synthetic.Old",
            "current_module": "ErdosProblems.Synthetic.Core", "declaration": "headline"}],
    }
    current = {("ErdosProblems/Synthetic/Core.lean", "headline")}
    linked = {("ErdosProblems/Synthetic/Old.lean", "headline")}
    require(not required_note_declaration_failures(row, current, linked),
            "explicit relocation lost the historical citation")
    require(bool(required_note_declaration_failures(row, set(), linked)),
            "missing current declaration accepted")
    require(bool(required_note_declaration_failures(row, current, current)),
            "current source cannot substitute for the actual paper citation")
    row["required_note_declarations"][0]["current_module"] = "ErdosProblems.Unowned.Core"
    require(bool(required_note_declaration_failures(row, current, linked)),
            "relocation outside indexed problem accepted")


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


def test_git_snapshot_batch_uses_one_clean_bounded_process() -> None:
    first = ("a" * 40, "ErdosProblems/First.lean")
    second = ("b" * 40, "ErdosProblems/Missing.lean")
    first_blob = b"theorem first : True\n"

    def fake_run(args, input=None, **kwargs):
        require(args[:2] == ["git", "cat-file"], f"unexpected git argv {args!r}")
        body = b""
        for raw in (input or b"").split(b"\n"):
            if not raw:
                continue
            spec = raw.decode()
            _commit, _, path = spec.partition(":")
            if path == "ErdosProblems/First.lean":
                body += f"{'1' * 40} blob {len(first_blob)}\n".encode()
                body += first_blob + b"\n"
            else:
                body += spec.encode() + b" missing\n"
        return scanner.subprocess.CompletedProcess(
            args, 0, stdout=body, stderr=b""
        )

    cache: dict[tuple[str, str], list[str]] = {}
    with patch.object(scanner.subprocess, "run", side_effect=fake_run) as run:
        scanner.snapshot_lines_batch([first, second, first], cache)
    require(cache[first] == ["theorem first : True"], "batch lost a Git blob")
    require(cache[second] == [], "batch did not type a missing Git blob")
    require(len(run.call_args_list) == 1, "batch repeated the Git process")
    kwargs = run.call_args.kwargs
    require(
        kwargs["env"] == scanner.singleflight.command_environment(),
        "batch environment drifted",
    )
    require(
        kwargs["timeout"] == scanner.singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
        "batch Git timeout drifted",
    )


def test_nested_layout_snapshot_falls_back_from_identity_path() -> None:
    nested_blob = "theorem nested : True\n"
    calls: list[str] = []

    def fake_run(args, **kwargs):
        spec = args[2] if len(args) > 2 else ""
        calls.append(spec)
        if spec.endswith("lean/ErdosProblems/Nested.lean"):
            return scanner.subprocess.CompletedProcess(
                args, 0, stdout=nested_blob, stderr=""
            )
        return scanner.subprocess.CompletedProcess(
            args, 128, stdout="", stderr="missing"
        )

    with patch.object(scanner.subprocess, "run", side_effect=fake_run):
        lines = scanner.snapshot_lines(
            "c" * 40, "ErdosProblems/Nested.lean", {}
        )
    require(lines == ["theorem nested : True"], "nested layout blob was not used")
    require(
        any(spec.endswith("lean/ErdosProblems/Nested.lean") for spec in calls),
        "nested storage path was never queried",
    )


def test_explicit_immutable_headline_links_require_exact_source() -> None:
    note = (r"\href{https://github.com/wcook04/plectis-erdos/blob/" + "a" * 40
            + r"/lean/ErdosProblems/Synthetic/Headline.lean\#L1}"
            + r"{\texttt{checked\_headline}}")
    key = ("ErdosProblems/Synthetic/Headline.lean", "checked_headline")
    with patch.object(scanner, "snapshot_lines", return_value=["theorem checked_headline : True := by trivial"]):
        require(key in linked_declaration_keys(note), "exact immutable link not recognized")
        require(key not in linked_declaration_keys(note.replace("L1", "L8")), "wrong line counted")
        require(key not in linked_declaration_keys(note.replace("wcook04/", "other/")), "foreign repository counted")
        require(key not in linked_declaration_keys(note.replace("a" * 40, "main")), "moving ref counted")
        require(key not in linked_declaration_keys("% " + note), "commented link counted")
    with patch.object(scanner, "snapshot_lines", return_value=[]):
        require(key not in linked_declaration_keys(note), "missing snapshot counted")
    with patch.object(scanner, "snapshot_lines", return_value=["/- theorem checked_headline : True -/"]):
        require(key not in linked_declaration_keys(note), "commented declaration counted")


def test_printed_links_are_checked_exactly_as_rendered() -> None:
    commit, ledger = "a" * 40, "b" * 40
    note = (
        r"\renewcommand{\commit}{" + commit + "}\n"
        r"\lword{Erdos243/Tail.lean}{3}{tail}{the tail}" "\n"
        r"\mref{Erdos249257/Old.lean}{4}{old}" "\n"
        r"\lproof{ErdosProblems/Erdos243/Tail.lean}{5}{tail}" "\n"
        r"\iffalse \lrefx{Erdos243/Hidden.lean}{1}{hidden} \ifx\a\b x\fi \fi" "\n"
        r"% \lword{Erdos243/Commented.lean}{1}{c}{c}" "\n"
    )
    targets, problems = scanner.rendered_link_targets(note, "c" * 40, ledger, "ErdosProblems")
    require(problems == [], f"unexpected problems {problems!r}")
    require((commit, "ErdosProblems/Erdos243/Tail.lean") in targets, "\\lword not rendered under \\PX")
    require((commit, "Erdos249257/Old.lean") in targets, "\\mref not rendered repository-relative")
    require(
        (ledger, "lean/ErdosProblems/Erdos243/Tail.lean") in targets,
        "\\lproof not rendered under lean/ at the ledger pin",
    )
    require(
        not any("Hidden" in path or "Commented" in path for _commit, path in targets),
        "a link TeX never prints was checked",
    )
    moved = note.replace("\n", "\n\\renewcommand{\\PX}{lean/ErdosProblems}\n", 1)
    relocated, _ = scanner.rendered_link_targets(moved, "c" * 40, ledger, "ErdosProblems")
    require(
        (commit, "lean/ErdosProblems/Erdos243/Tail.lean") in relocated,
        "a note's \\PX override was ignored",
    )
    _targets, foreign = scanner.rendered_link_targets(
        r"\renewcommand{\repobase}{https://example.org/\commit}", commit, ledger, "ErdosProblems"
    )
    require(bool(foreign), "an unrecognised \\repobase override passed silently")


def test_printed_path_absent_at_pin_fails_with_relocation_hint() -> None:
    commit = "a" * 40
    note = r"\renewcommand{\commit}{" + commit + r"}\lword{Erdos243/Tail.lean}{3}{tail}{the tail}"

    def fake_text(path):
        return r"\newcommand{\PX}{ErdosProblems}" if path == scanner.PREAMBLE else note

    # The pinned snapshot holds the file only under lean/, as 3d6d938d did for #243.
    def fake_present(keys):
        return {key for key in keys if key[1].startswith("lean/")}

    with patch.object(scanner, "ledger_sources", return_value=["paper/synthetic.tex"]), \
            patch.object(scanner, "safe_worktree_text", side_effect=fake_text), \
            patch.object(scanner, "objects_present", side_effect=fake_present):
        failures, checked = scanner.rendered_link_failures(commit, None)
    require(checked == 1, f"expected one printed URL, got {checked}")
    require(
        len(failures) == 1 and "404" in failures[0] and "under lean/" in failures[0],
        f"a printed 404 was not reported with its fix: {failures!r}",
    )


def test_late_pin_links_are_checked_at_their_own_pin() -> None:
    commit, late = "a" * 40, "d" * 40
    late_pin = (
        r"\newcommand{\latecommit}{" + late + "}\n"
        r"\newcommand{\laterepobase}{https://github.com/wcook04/plectis-erdos/blob/\latecommit}" "\n"
    )
    note = (
        r"\renewcommand{\commit}{" + commit + "}\n"
        + late_pin
        + r"\href{\laterepobase/lean/ErdosProblems/Erdos243/Late.lean\#L7}{a late theorem}" "\n"
        r"\lean{Late.thm}{lean/ErdosProblems/Erdos249/\allowbreak LateToo.lean:9}" "\n"
        r"\lean{Old.thm}{Erdos249257/Old.lean:4}" "\n"
        r"\iffalse \href{\laterepobase/lean/Hidden.lean}{hidden} \fi" "\n"
        r"% \href{\laterepobase/lean/Commented.lean}{commented}" "\n"
    )
    targets, problems = scanner.rendered_link_targets(note, "c" * 40, None, "ErdosProblems")
    require(problems == [], f"unexpected problems {problems!r}")
    require(
        (late, "lean/ErdosProblems/Erdos243/Late.lean") in targets,
        "a \\laterepobase link was not rendered at \\latecommit",
    )
    require(
        (late, "lean/ErdosProblems/Erdos249/LateToo.lean") in targets,
        "a lean/ \\lean target was not rendered at \\latecommit",
    )
    require(
        not any("Old" in path for pin, path in targets if pin == late),
        "a \\lean target without the lean/ prefix was sent to \\latecommit",
    )
    require(
        not any("Hidden" in path or "Commented" in path for _pin, path in targets),
        "a late link TeX never prints was checked",
    )
    _targets, unpinned = scanner.rendered_link_targets(
        r"\href{\laterepobase/lean/X.lean}{x}", commit, None, "ErdosProblems"
    )
    require(bool(unpinned), "a late link without \\latecommit passed silently")
    foreign_pin = late_pin.replace("https://github.com/wcook04/plectis-erdos/blob", "https://example.org")
    _targets, foreign = scanner.rendered_link_targets(
        foreign_pin + r"\href{\laterepobase/lean/X.lean}{x}", commit, None, "ErdosProblems"
    )
    require(bool(foreign), "an unrecognised \\laterepobase passed silently")

    def fake_text(path):
        return r"\newcommand{\PX}{ErdosProblems}" if path == scanner.PREAMBLE else note

    # Every path exists at the ordinary pin; none exists at \latecommit.
    def fake_present(keys):
        return {key for key in keys if key[0] != late}

    with patch.object(scanner, "ledger_sources", return_value=["paper/synthetic.tex"]), \
            patch.object(scanner, "safe_worktree_text", side_effect=fake_text), \
            patch.object(scanner, "objects_present", side_effect=fake_present):
        failures, checked = scanner.rendered_link_failures(commit, None)
    require(checked == 2, f"expected two printed late URLs, got {checked}")
    require(
        len(failures) == 1 and late[:12] in failures[0] and "404" in failures[0],
        f"a late link absent at \\latecommit was not reported: {failures!r}",
    )


def main() -> int:
    test_printed_links_are_checked_exactly_as_rendered()
    test_printed_path_absent_at_pin_fails_with_relocation_hint()
    test_late_pin_links_are_checked_at_their_own_pin()
    test_explicit_immutable_headline_links_require_exact_source()
    test_worktree_source_reader_boundary()
    test_comment_injection_is_not_a_declaration()
    test_split_declaration_head_resolves_at_keyword_line()
    test_wrong_module_name_collision_is_not_coverage()
    test_missing_required_anchor_is_rejected()
    test_invalid_coverage_floor_is_rejected()
    test_relocated_owner_keeps_the_immutable_paper_anchor()
    test_erdos257_headline_anchors_are_required()
    test_mismatched_note_commitshort_is_rejected()
    test_commit_override_without_matching_short_is_rejected()
    test_git_snapshot_reads_use_clean_bounded_environment()
    test_git_snapshot_batch_uses_one_clean_bounded_process()
    test_nested_layout_snapshot_falls_back_from_identity_path()
    print(
        "test_problem_note_sources: comment injection, split heads, module "
        "collisions, required anchors, invalid floors, and mismatched source "
        "pins rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
