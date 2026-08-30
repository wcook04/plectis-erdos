#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression test for immutable-ref source resolution in the release gate."""

from __future__ import annotations

import os
import subprocess
import tempfile
from unittest import mock
from pathlib import Path

import check_release
import validation_singleflight as singleflight


def git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
        env=check_release.clean_environment(),
        timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
    ).stdout.strip()


def commit(root: Path, message: str) -> str:
    git(root, "add", ".")
    git(root, "commit", "-qm", message)
    return git(root, "rev-parse", "HEAD")


def require(condition: bool, message: str) -> None:
    """Keep source-identity regressions active when run with ``python -O``."""
    if not condition:
        raise AssertionError(message)


def check_git_fixture_environment() -> None:
    """Temporary Git fixtures must ignore caller selectors and remain bounded."""
    completed = subprocess.CompletedProcess(
        ["git"], returncode=0, stdout="fixture\n", stderr=""
    )
    hostile = {
        key: f"/foreign/{key.lower()}"
        for key in check_release.SANITIZED_GIT_ENVIRONMENT_KEYS
    }
    with mock.patch.dict(os.environ, hostile, clear=False):
        with mock.patch.object(subprocess, "run", return_value=completed) as run_mock:
            require(git(Path("/fixture"), "rev-parse", "HEAD") == "fixture", "fixture Git read failed")
    call = run_mock.call_args
    require(call is not None, "fixture Git helper did not invoke subprocess")
    environment = call.kwargs["env"]
    require(
        all(key not in environment for key in check_release.SANITIZED_GIT_ENVIRONMENT_KEYS),
        "fixture Git helper retained inherited Git selectors",
    )
    require(
        call.kwargs["timeout"] == singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
        "fixture Git helper omitted the shared timeout",
    )


def main() -> int:
    """A later worktree file must not satisfy a historical source reference."""
    check_git_fixture_environment()
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        git(root, "init", "-q")
        git(root, "config", "user.email", "release-test@example.invalid")
        git(root, "config", "user.name", "Release source identity test")
        (root / "Erdos249257").mkdir()
        root_source = "import Erdos249257.Stable\n"
        stable_source = "theorem stable : True := True.intro\n"
        (root / "Erdos249257.lean").write_text(
            root_source, encoding="utf-8"
        )
        (root / "Erdos249257" / "Stable.lean").write_text(
            stable_source, encoding="utf-8"
        )
        old_ref = commit(root, "old formal source")
        (root / "Erdos249257" / "PostRef.lean").write_text(
            "theorem postRefOnly : True := True.intro\n", encoding="utf-8"
        )
        new_ref = commit(root, "new worktree source")

        original_root = check_release.ROOT
        check_release.ROOT = root
        try:
            cache: dict[tuple[str, str | None], list[str] | None] = {}
            require(
                check_release.module_lines(cache, "Erdos249257/PostRef.lean", old_ref)
                is None,
                "later module was visible at the old formal-source reference",
            )
            new_lines = check_release.module_lines(cache, "Erdos249257/PostRef.lean", new_ref)
            require(new_lines is not None, "later module was not visible at the new reference")
            require(
                check_release.name_at_line(new_lines, "postRefOnly", 1),
                "later module declaration was not found at its new reference",
            )
            matches_old, old_detail = check_release.formal_source_matches_current_lean_tree(old_ref)
            require(not matches_old, "old formal-source reference matched the later tree")
            require(
                "differ from formal-source checkpoint" in old_detail,
                "old-reference mismatch did not identify checkpoint drift",
            )
            matches_new, new_detail = check_release.formal_source_matches_current_lean_tree(new_ref)
            require(matches_new, "new formal-source reference did not match its tree")
            require(new_detail == "", "new formal-source reference reported unexpected drift")

            (root / "Erdos249257.lean").write_text(
                "import Erdos249257.PostRef\n", encoding="utf-8"
            )
            matches_changed_root, changed_root_detail = (
                check_release.formal_source_matches_current_lean_tree(new_ref)
            )
            require(
                not matches_changed_root,
                "changed root file was accepted at the immutable source reference",
            )
            require(
                "differ from formal-source checkpoint" in changed_root_detail,
                "changed root mismatch did not identify checkpoint drift",
            )
            (root / "Erdos249257.lean").write_text(
                root_source, encoding="utf-8"
            )

            (root / "Erdos249257" / "Stable.lean").unlink()
            matches_with_deletion, deletion_detail = (
                check_release.formal_source_matches_current_lean_tree(new_ref)
            )
            require(
                not matches_with_deletion,
                "deleted source file was accepted at the immutable source reference",
            )
            require(
                "differ from formal-source checkpoint" in deletion_detail,
                "deletion mismatch did not identify checkpoint drift",
            )
            (root / "Erdos249257" / "Stable.lean").write_text(
                stable_source, encoding="utf-8"
            )

            (root / "Erdos249257" / "Untracked.lean").write_text(
                "theorem untracked : True := True.intro\n", encoding="utf-8"
            )
            matches_with_untracked, untracked_detail = (
                check_release.formal_source_matches_current_lean_tree(new_ref)
            )
            require(
                not matches_with_untracked,
                "untracked source file was accepted at the immutable source reference",
            )
            require(
                "Untracked.lean" in untracked_detail,
                "untracked-source mismatch did not name the unexpected file",
            )
        finally:
            check_release.ROOT = original_root

    print(
        "test_release_source_identity: pinned source rejects later modules, "
        "root edits, deletions, and untracked Lean files"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
