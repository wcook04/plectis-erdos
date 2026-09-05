#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression test for pinned reasoning-paper Lean source coordinates."""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch


SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

import refresh_reasoning_source_coordinates as coordinates  # noqa: E402
import validation_singleflight as singleflight  # noqa: E402


def require(condition: bool, message: str) -> None:
    """Keep source-coordinate portability checks active under ``python -O``."""
    if not condition:
        raise AssertionError(message)


def run_git(root: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
        env=singleflight.command_environment(),
        timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
    )
    return result.stdout.strip()


def check_comment_projection() -> None:
    source = (
        'def visible := 1 -- def lineHidden := 2\n'
        '/- outer /- nested -/ def blockHidden := 3 -/\n'
        'def quoted := "/- string content stays -/"\n'
        'def escaped := "quote: \\" -- still in string" -- hidden again\n'
    )
    projected = coordinates.strip_lean_comments(source)
    require(len(projected) == len(source), "comment projection changed source offsets")
    require(
        [index for index, char in enumerate(projected) if char == "\n"]
        == [index for index, char in enumerate(source) if char == "\n"],
        "comment projection changed source lines",
    )
    require("def visible" in projected, "comment projection removed Lean code")
    require("lineHidden" not in projected, "line-comment content survived")
    require("blockHidden" not in projected, "nested block-comment content survived")
    require("string content stays" in projected, "string content was treated as a comment")
    require("still in string" in projected, "escaped quote ended a string early")
    require("hidden again" not in projected, "comment after escaped string survived")


def main() -> int:
    check_comment_projection()
    with tempfile.TemporaryDirectory(prefix="reasoning-coordinate-test-") as temporary:
        root = Path(temporary)
        run_git(root, "init", "--quiet")
        run_git(root, "config", "user.name", "Coordinate Test")
        run_git(root, "config", "user.email", "coordinate-test@example.invalid")
        reviewed_source = root / "Erdos249257" / "Sample.lean"
        problem_source = root / "ErdosProblems" / "Erdos68" / "Sample.lean"
        reviewed_source.parent.mkdir(parents=True)
        problem_source.parent.mkdir(parents=True)
        source_text = (
            "namespace Sample\n\n"
            "/-- The declaration under test. -/\n"
            "theorem pinnedDeclaration : True := by trivial\n\n"
            "end Sample\n"
        )
        reviewed_source.write_text(source_text, encoding="utf-8")
        problem_source.write_text(source_text, encoding="utf-8")
        run_git(root, "add", "Erdos249257/Sample.lean", "ErdosProblems/Erdos68/Sample.lean")
        run_git(root, "commit", "--quiet", "-m", "first pin")
        first_pin = run_git(root, "rev-parse", "HEAD")
        reviewed_source.write_text("\n" + source_text, encoding="utf-8")
        run_git(root, "add", "Erdos249257/Sample.lean")
        run_git(root, "commit", "--quiet", "-m", "second pin")
        second_pin = run_git(root, "rev-parse", "HEAD")

        parts_dirs = tuple(
            root / "paper" / "reasoning-parts" / problem
            for problem in ("erdos68", "erdos249")
        )
        for directory, command, pin in (
            (parts_dirs[0], "renewcommand", first_pin),
            (parts_dirs[1], "newcommand", second_pin),
        ):
            directory.mkdir(parents=True)
            (directory / "preamble.tex").write_text(
                rf"\{command}{{\commit}}{{{pin}}}" + "\n", encoding="utf-8"
            )
        note_named = root / "paper" / "shared-note.tex"
        note_named.write_text(
            rf"\renewcommand{{\commit}}{{{first_pin}}}" + "\n"
            + r"\lref{Erdos68/Sample.lean}{1}{pinnedDeclaration}" + "\n",
            encoding="utf-8",
        )
        named = parts_dirs[1] / "part.tex"
        named.write_text(
            r"\lean{Sample.pinnedDeclaration}{Sample.lean:1}" + "\n",
            encoding="utf-8",
        )
        locations = parts_dirs[1] / "locations.tex"
        locations.write_text(
            r"\lean{}{Sample.lean:3} "
            r"\lean{Sample.lean}{Sample.lean:1-5}" + "\n",
            encoding="utf-8",
        )

        original_root = coordinates.ROOT
        original_papers = coordinates.assembler.PAPERS
        coordinates.ROOT = root
        coordinates.assembler.PAPERS = {
            "68": {"directory": parts_dirs[0], "note_source": note_named},
            "249": {"directory": parts_dirs[1]},
        }
        try:
            hostile_environment = {
                "GIT_DIR": "/private/wrong-git-dir",
                "GIT_NAMESPACE": "wrong-namespace",
                "GIT_REPLACE_REF_BASE": "refs/replacements/wrong",
                "PYTHONPATH": "/private/wrong-python-path",
            }
            original_subprocess_run = subprocess.run
            with patch.dict(os.environ, hostile_environment, clear=False), patch.object(
                coordinates.subprocess,
                "run",
                wraps=original_subprocess_run,
            ) as run_child:
                rendered, declarations, authored_locations, resolved_pins = coordinates.render_all()
            batch_calls = [
                call
                for call in run_child.call_args_list
                if call.args and call.args[0] == ["git", "cat-file", "--batch"]
            ]
            require(len(batch_calls) == 2, "each distinct pin did not use one Git batch")
            require(
                resolved_pins == (first_pin, second_pin),
                "per-paper source pins drifted",
            )
            require(declarations == 2, "unexpected declaration count")
            require(authored_locations == 2, "unexpected authored location count")
            require(
                r"{Sample.lean:5}" in rendered[named],
                "named declaration coordinate was not refreshed",
            )
            require(
                r"{Erdos68/Sample.lean}{4}{pinnedDeclaration}" in rendered[note_named],
                "problem-note declaration coordinate was not refreshed",
            )
            require(
                rendered[locations] == locations.read_text(encoding="utf-8"),
                "authored location citation was rewritten",
            )

            named.write_text(rendered[named], encoding="utf-8")
            rendered_again, _, _, _ = coordinates.render_all()
            require(
                rendered_again[named] == named.read_text(encoding="utf-8"),
                "coordinate rendering was not idempotent",
            )
            stable_ns = 1_700_000_000_000_000_000
            os.utime(named, ns=(stable_ns, stable_ns))
            with patch.object(
                sys,
                "argv",
                ["refresh_reasoning_source_coordinates.py", "--write"],
            ):
                require(coordinates.main() == 0, "unchanged reasoning writer failed")
            require(
                named.stat().st_mtime_ns == stable_ns,
                "unchanged reasoning coordinate output was rewritten",
            )

            named.write_text(
                r"\lean{missingDeclaration}{Sample.lean:4}" + "\n",
                encoding="utf-8",
            )
            try:
                coordinates.render_all()
            except coordinates.CoordinateError as exc:
                require(
                    "missingDeclaration" in str(exc),
                    "missing declaration failure did not identify the declaration",
                )
            else:
                raise AssertionError("missing declaration citation was accepted")
        finally:
            coordinates.ROOT = original_root
            coordinates.assembler.PAPERS = original_papers

    print(
        "test_reasoning_source_coordinates: stale declarations refresh to the pinned "
        "line at each paper pin, problem-note links are covered, authored locations "
        "survive, and missing declarations fail"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
