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


def test_standalone_semantic_word_bodies_keep_their_actual_pin_and_prefix() -> None:
    commit, literal, fallback = "a" * 40, "b" * 40, "c" * 40
    for command in ("newcommand", "renewcommand"):
        note = (
            "\\" + command + r"{\commit}{" + commit + "}\n"
            + "\\" + command + r"{\PX}{lean/ErdosProblems}" "\n"
            + "\\" + command + r"{\repobase}{https://github.com/wcook04/plectis-erdos/blob/\commit}" "\n"
            + r"\lref{Synthetic/A.lean}{1}{a}" "\n"
            + r"\newcommand{\lword}[4]{\href{\repobase/ErdosProblems/#1\#L#2}{#4}}" "\n"
            + r"\lword{Synthetic/B.lean}{2}{b}{body}" "\n"
            + r"\newcommand{\mword}[4]{\href{https://github.com/wcook04/plectis-erdos/blob/"
            + literal + r"/#1\#L#2}{#4}}" "\n"
            + r"\mword{Erdos249257/C.lean}{3}{c}{literal body}"
        )
        targets, problems = scanner.rendered_link_targets(note, fallback, None, "WrongDefault")
        require(not problems, repr(problems))
        require((commit, "lean/ErdosProblems/Synthetic/A.lean") in targets, "local pin/PX ignored")
        require((commit, "ErdosProblems/Synthetic/B.lean") in targets, "actual word body prefix ignored")
        require((literal, "Erdos249257/C.lean") in targets, "literal word-body pin ignored")
        require(not any(pin == fallback for pin, _path in targets), "standalone body uses inherited pin")
    foreign = r"\newcommand{\lword}[4]{\href{https://example.org/#1\#L#2}{#4}}\lword{X.lean}{1}{x}{x}"
    _targets, problems = scanner.rendered_link_targets(foreign, fallback, None, "ErdosProblems")
    require(bool(problems), "foreign semantic word body passed silently")
    foreign_base = r"\newcommand{\repobase}{https://example.org/\commit}\lref{X.lean}{1}{x}"
    _targets, problems = scanner.rendered_link_targets(foreign_base, fallback, None, "ErdosProblems")
    require(bool(problems), "foreign standalone source base passed silently")


def test_standalone_word_body_nonexistent_pin_or_path_is_rejected() -> None:
    existing, absent = "a" * 40, "b" * 40
    for pin, path in ((absent, "ErdosProblems/Exists.lean"), (existing, "ErdosProblems/Missing.lean")):
        note = (r"\newcommand{\lword}[4]{\href{https://github.com/wcook04/plectis-erdos/blob/"
                + pin + r"/ErdosProblems/#1\#L#2}{#4}}\lword{"
                + path.removeprefix("ErdosProblems/") + r"}{1}{target}{target}")
        def fake_text(source):
            return r"\newcommand{\PX}{Erdos249257}" if source == scanner.PREAMBLE else note
        def fake_present(keys):
            return {key for key in keys if key == (existing, "ErdosProblems/Exists.lean")}
        with patch.object(scanner, "ledger_sources", return_value=["paper/synthetic.tex"]), \
                patch.object(scanner, "safe_worktree_text", side_effect=fake_text), \
                patch.object(scanner, "objects_present", side_effect=fake_present):
            failures, checked = scanner.rendered_link_failures(existing, None)
        require(checked >= 1 and bool(failures), "missing body pin/path passed")
        require(any("404" in row and pin[:12] in row for row in failures), repr(failures))


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


def test_margin_marks_reach_their_declarations_only_for_marked_results() -> None:
    evidence = {"papers": [
        {"paper_id": "note-a", "results": [
            {"label": "visible", "lean": {"mark": "lean", "declarations": [
                {"name": "Erdos249257.Outer.inner_lemma", "path": "lean/Erdos249257/Mod.lean"}]}},
            {"label": "unmarked", "lean": {"mark": None, "declarations": [
                {"name": "Erdos249257.unmarked", "path": "lean/Erdos249257/Mod.lean"}]}},
        ]},
        {"paper_id": "note-b", "results": [
            {"lean": {"mark": "lean", "declarations": [
                {"name": "Erdos249257.other", "path": "lean/Erdos249257/Mod.lean"}]}},
        ]},
    ]}
    note = r"\input{evidence/note-a}\label{visible}\label{unmarked}"
    with patch.object(scanner, "safe_worktree_text", return_value=r"\DeclareResultEvidence{visible}{Lean}{proof}{comparison}"):
        keys = scanner.margin_mark_declaration_keys(
            "paper/x/note-a.tex", evidence, note_text=note, native_validated=True
        )
    relative = scanner.library_relative("Erdos249257/Mod.lean")
    require((relative, "Outer.inner_lemma") in keys and (relative, "inner_lemma") in keys,
            f"a marked declaration was not reached under its declared name: {sorted(keys)}")
    require((relative, "unmarked") not in keys, "a result without a mark reached its declaration")
    require((relative, "other") not in keys, "another paper's mark counted for this note")


def test_visible_registered_companion_reachability() -> None:
    """A route must be invoked visibly, registered, and local to this problem."""
    contract = {"artifacts": [
        {"artifact_class": "mathematical_companion", "source_path": "paper/x/record.tex",
         "rendered_path": "paper/x/record.pdf"},
        {"artifact_class": "mathematical_companion", "source_path": "paper/y/other.tex",
         "rendered_path": "paper/y/other.pdf"},
    ]}
    helper = r"\newcommand{\longrecord}[2]{\href{record.pdf\##1}{#2}}"
    with patch.object(scanner, "safe_worktree_text", return_value=json.dumps(contract)):
        source = "paper/x/note.tex"
        require(scanner.reachable_companion_sources(source, helper+r"\longrecord{guide}{proof}")
                == ["paper/x/record.tex"], "invoked local record helper was not followed")
        require(scanner.reachable_companion_sources(source, r"\papersectionlink{record.pdf}{guide}{proof}")
                == ["paper/x/record.tex"], "shared section helper was not followed")
        for text in ["record.pdf", helper,
                     r"\newcommand{\optional}[1][default]{\href{record.pdf}{#1}}",
                     r"\def\unused#1{\href{record.pdf}{#1}}",
                     helper+r"\iffalse\longrecord{guide}{proof}\fi",
                     helper+"\n% \\longrecord{guide}{proof}\n",
                     r"\href{unregistered.pdf}{proof}",
                     r"\href{../y/other.pdf}{proof}"]:
            require(not scanner.reachable_companion_sources(source, text),
                    f"unlinked, unused, hidden or unrelated record counted: {text}")


def test_reached_authored_coordinates_use_the_companion_pin() -> None:
    short_pin, record_pin = "a"*40, "b"*40
    note = r"\href{record.pdf}{proof}"
    record = (r"\renewcommand{\commit}{"+record_pin+r"}"+
              r"\lword{Synthetic/Headline.lean}{1}{headline}{proof}")
    key = ("ErdosProblems/Synthetic/Headline.lean", "headline")
    with patch.object(scanner, "reachable_companion_sources", return_value=["paper/x/record.tex"]), \
         patch.object(scanner, "safe_worktree_text", return_value=record), \
         patch.object(scanner, "snapshot_lines", return_value=["theorem headline : True := by trivial"]) as snapshots:
        keys, failures = scanner.reachable_note_declaration_keys(
            "paper/x/note.tex", note, {}, short_pin, native_validated=False)
        require(key in keys and not failures, "valid companion coordinate was not reached")
        require(snapshots.call_args.args[0] == record_pin, "companion inherited the short-paper pin")
    with patch.object(scanner, "reachable_companion_sources", return_value=["paper/x/record.tex"]), \
         patch.object(scanner, "safe_worktree_text", return_value=record), \
         patch.object(scanner, "snapshot_lines", return_value=["theorem unrelated : True := by trivial"]):
        keys, failures = scanner.reachable_note_declaration_keys(
            "paper/x/note.tex", note, {}, short_pin, native_validated=False)
        require(key not in keys and failures, "invalid companion coordinate conferred coverage")


def test_generated_reach_requires_actual_labels_and_native_currency() -> None:
    evidence = {"papers": [{"paper_id": "note", "results": [
        {"label": "result", "lean": {"declarations": [
            {"name": "ErdosProblems.Synthetic.support", "path": "lean/ErdosProblems/Synthetic.lean"}]}}
    ]}]}
    note = r"\input{evidence/note}\label{result}"
    generated = r"\DeclareResultEvidence{result}{Lean}{proof}{comparison}"
    key = ("ErdosProblems/Synthetic.lean", "support")
    with patch.object(scanner, "safe_worktree_text", return_value=generated):
        def keys(text: str, valid: bool):
            return scanner.margin_mark_declaration_keys(
                "paper/x/note.tex", evidence, note_text=text, native_validated=valid)
        require(key in keys(note, True), "actual declared native label required an obsolete mark flag")
        require(not keys(note, False), "stale or incomplete native evidence counted")
        require(not keys(r"\label{result}", True), "unloaded generated evidence counted")
        require(not keys(r"\input{evidence/note}\iffalse\label{result}\fi", True),
                "unrendered result label counted")
    with patch.object(scanner, "safe_worktree_text", return_value=r"\DeclareResultEvidence{other}"):
        require(not scanner.margin_mark_declaration_keys(
            "paper/x/note.tex", evidence, note_text=note, native_validated=True),
            "an undeclared result acquired support from JSON alone")
    for generated in [r"\DeclareResultEvidence{result}{}{proof}{}",
                      r"\DeclareResultEvidence{result}{Lean}{}{}",
                      r"\iffalse\DeclareResultEvidence{result}{Lean}{proof}{}\fi"]:
        with patch.object(scanner, "safe_worktree_text", return_value=generated):
            require(not scanner.margin_mark_declaration_keys(
                "paper/x/note.tex", evidence, note_text=note, native_validated=True),
                "an empty or hidden generated marker conferred coverage")
    import check_lean_paper_propagation as propagation
    with patch.object(propagation, "read_json", return_value={}), \
         patch.object(propagation, "LeanSources", return_value=object()), \
         patch.object(propagation, "evaluate") as evaluate:
        evaluate.return_value.failed.return_value = True
        require(not scanner.native_evidence_valid(), "a failed native currency gate was accepted")


def test_native_currency_rejects_stale_map_and_sidecar() -> None:
    """A passing propagation ledger cannot bless stale generated evidence."""
    import check_lean_paper_propagation as propagation
    import paper_evidence as owner
    from test_paper_evidence import Fixture, commit_all, write

    with tempfile.TemporaryDirectory(prefix="problem-note-evidence-currency-") as raw:
        fixture = Fixture(Path(raw))
        fixture.materialise()
        problems = owner.Problems()
        evidence = owner.resolve(fixture.root, owner.Repo(fixture.corpus), None, None,
                                 problems, require_relations=False)
        require(not problems.items, f"invalid native evidence fixture: {problems.items}")
        for rel, text in owner.outputs(fixture.root, evidence, "d"*40).items():
            write(fixture.root, rel, text)
        # Records do not contain their own pin: commit them first, then bind
        # the generated reader links to that real immutable snapshot.
        record_pin = commit_all(fixture.root, "evidence records")
        config_path = fixture.root / owner.CONFIG
        config = json.loads(config_path.read_text())
        config["record_commit"] = record_pin
        config_path.write_text(json.dumps(config), encoding="utf-8")
        for rel, text in owner.outputs(fixture.root, evidence, record_pin).items():
            write(fixture.root, rel, text)

        with patch.object(scanner, "ROOT", fixture.root), \
             patch.object(propagation, "read_json", return_value={}), \
             patch.object(propagation, "LeanSources", return_value=object()), \
             patch.object(propagation, "evaluate") as evaluate:
            evaluate.return_value.failed.return_value = False
            require(scanner.native_evidence_valid(), "current native evidence did not pass without PDFs")

            map_path = fixture.root / owner.EVIDENCE_MAP
            current_map = map_path.read_text(encoding="utf-8")
            stale = json.loads(current_map)
            stale["papers"][0]["results"][0]["lean"]["declarations"][0]["name"] = "Syn.forged"
            map_path.write_text(json.dumps(stale, indent=1)+"\n", encoding="utf-8")
            require(not scanner.native_evidence_valid(),
                    "a forged declaration for a real declared label passed a current ledger")
            map_path.write_text(current_map, encoding="utf-8")

            sidecar = fixture.root / owner.SIDECAR_DIR / (evidence["papers"][0]["paper_id"]+".tex")
            current_sidecar = sidecar.read_text(encoding="utf-8")
            sidecar.write_text(current_sidecar.replace("{Lean}", "{Lean-stale}", 1), encoding="utf-8")
            require(not scanner.native_evidence_valid(),
                    "a stale declared margin passed a current ledger and evidence map")
            sidecar.write_text(current_sidecar, encoding="utf-8")
            require(scanner.native_evidence_valid(), "restored generated evidence did not pass")


def test_worded_pinned_link_reaches_the_declaration_at_its_line() -> None:
    note = (r"\href{https://github.com/wcook04/plectis-erdos/blob/" + "a" * 40
            + r"/lean/ErdosProblems/Synthetic/Headline.lean\#L2}{the measure dichotomy}")
    key = ("ErdosProblems/Synthetic/Headline.lean", "worded_headline")
    source = ["-- header", "theorem worded_headline : True := by trivial"]
    with patch.object(scanner, "snapshot_lines", return_value=source):
        require(key in linked_declaration_keys(note), "a worded pinned link was not resolved")
        require(key not in linked_declaration_keys(note.replace("L2", "L1")),
                "a worded link to a line without a declaration counted")
        require(key not in linked_declaration_keys(note.replace("a" * 40, "main")), "moving ref counted")
    with patch.object(scanner, "snapshot_lines", return_value=["-- header", "-- theorem worded_headline"]):
        require(key not in linked_declaration_keys(note), "a commented declaration counted")


def main() -> int:
    test_printed_links_are_checked_exactly_as_rendered()
    test_standalone_semantic_word_bodies_keep_their_actual_pin_and_prefix()
    test_standalone_word_body_nonexistent_pin_or_path_is_rejected()
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
    test_margin_marks_reach_their_declarations_only_for_marked_results()
    test_visible_registered_companion_reachability()
    test_reached_authored_coordinates_use_the_companion_pin()
    test_generated_reach_requires_actual_labels_and_native_currency()
    test_native_currency_rejects_stale_map_and_sidecar()
    test_worded_pinned_link_reaches_the_declaration_at_its_line()
    print(
        "test_problem_note_sources: comment injection, split heads, module "
        "collisions, required anchors, invalid floors, and mismatched source "
        "pins rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
