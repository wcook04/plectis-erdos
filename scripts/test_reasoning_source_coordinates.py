#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression test for pinned reasoning-paper Lean source coordinates."""

from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

import refresh_reasoning_source_coordinates as coordinates  # noqa: E402


def run_git(root: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip()


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="reasoning-coordinate-test-") as temporary:
        root = Path(temporary)
        run_git(root, "init", "--quiet")
        run_git(root, "config", "user.name", "Coordinate Test")
        run_git(root, "config", "user.email", "coordinate-test@example.invalid")
        source = root / "Erdos249257" / "Sample.lean"
        source.parent.mkdir(parents=True)
        source.write_text(
            "namespace Sample\n\n"
            "/-- The declaration under test. -/\n"
            "theorem pinnedDeclaration : True := by trivial\n\n"
            "end Sample\n",
            encoding="utf-8",
        )
        run_git(root, "add", "Erdos249257/Sample.lean")
        run_git(root, "commit", "--quiet", "-m", "pin source")
        pin = run_git(root, "rev-parse", "HEAD")

        parts_dirs = tuple(
            root / "paper" / "reasoning-parts" / problem
            for problem in ("erdos249", "erdos257")
        )
        for directory in parts_dirs:
            directory.mkdir(parents=True)
            (directory / "preamble.tex").write_text(
                rf"\newcommand{{\commit}}{{{pin}}}" + "\n",
                encoding="utf-8",
            )
        named = parts_dirs[0] / "part.tex"
        named.write_text(
            r"\lean{Sample.pinnedDeclaration}{Sample.lean:1}" + "\n",
            encoding="utf-8",
        )
        locations = parts_dirs[1] / "part.tex"
        locations.write_text(
            r"\lean{}{Sample.lean:3} "
            r"\lean{Sample.lean}{Sample.lean:1-4}" + "\n",
            encoding="utf-8",
        )

        original_root = coordinates.ROOT
        original_parts_dirs = coordinates.PARTS_DIRS
        coordinates.ROOT = root
        coordinates.PARTS_DIRS = parts_dirs
        try:
            rendered, declarations, authored_locations, resolved_pin = (
                coordinates.render_all()
            )
            assert resolved_pin == pin
            assert declarations == 1
            assert authored_locations == 2
            assert r"{Sample.lean:4}" in rendered[named]
            assert rendered[locations] == locations.read_text(encoding="utf-8")

            named.write_text(rendered[named], encoding="utf-8")
            rendered_again, _, _, _ = coordinates.render_all()
            assert rendered_again[named] == named.read_text(encoding="utf-8")

            named.write_text(
                r"\lean{missingDeclaration}{Sample.lean:4}" + "\n",
                encoding="utf-8",
            )
            try:
                coordinates.render_all()
            except coordinates.CoordinateError as exc:
                assert "missingDeclaration" in str(exc)
            else:
                raise AssertionError("missing declaration citation was accepted")
        finally:
            coordinates.ROOT = original_root
            coordinates.PARTS_DIRS = original_parts_dirs

    print(
        "test_reasoning_source_coordinates: stale declarations refresh to the pinned "
        "line, authored locations survive, and missing declarations fail"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
