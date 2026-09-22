#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Full-source discovery must not silently pick old vs new corpus layouts."""

from __future__ import annotations

import shutil
import subprocess
import tempfile
from pathlib import Path

from lean_source import (
    LAYOUT_HISTORICAL_ROOT,
    LAYOUT_NESTED,
    LAYOUT_TRUNCATED_READER,
    LibraryLayoutError,
    checkout_source_relative,
    describe_unindexed_library_sources,
    library_module_id,
    library_source_inventory,
    library_source_paths,
)


LAKEFILE_NESTED = """
name = "erdos249257"
[[lean_lib]]
name = "Erdos249257"
srcDir = "lean"
[[lean_lib]]
name = "ErdosProblems"
srcDir = "lean"
[[lean_lib]]
name = "ExternalVerification"
srcDir = "verification"
"""

LAKEFILE_HISTORICAL = """
name = "erdos249257"
[[lean_lib]]
name = "Erdos249257"
[[lean_lib]]
name = "ErdosProblems"
"""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def write_module(root: Path, relative: str, body: str = "def specimen := 1\n") -> None:
    path = root / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(body, encoding="utf-8")


def git(root: Path, *arguments: str) -> None:
    subprocess.run(
        ["git", "-C", str(root), *arguments],
        check=True,
        capture_output=True,
        env={
            "PATH": "/usr/bin:/bin:/usr/local/bin:/opt/homebrew/bin",
            "HOME": str(root),
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_AUTHOR_NAME": "t",
            "GIT_AUTHOR_EMAIL": "t@example.invalid",
            "GIT_COMMITTER_NAME": "t",
            "GIT_COMMITTER_EMAIL": "t@example.invalid",
        },
    )


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="lean-layout-missing-") as raw:
        root = Path(raw)
        (root / "lakefile.toml").write_text(LAKEFILE_NESTED, encoding="utf-8")
        try:
            library_source_paths(root)
        except LibraryLayoutError as error:
            require("missing" in str(error), str(error))
        else:
            raise AssertionError("missing configured roots returned an empty list")

    with tempfile.TemporaryDirectory(prefix="lean-layout-ambiguous-") as raw:
        root = Path(raw)
        (root / "lakefile.toml").write_text(LAKEFILE_NESTED, encoding="utf-8")
        write_module(root, "Erdos249257/Duplicate.lean", "def specimen := 1\n")
        write_module(root, "lean/Erdos249257/Duplicate.lean", "def specimen := 2\n")
        write_module(root, "lean/Erdos249257.lean")
        write_module(root, "lean/ErdosProblems.lean")
        try:
            library_source_paths(root)
        except LibraryLayoutError as error:
            require("ambiguous" in str(error) or "duplicate" in str(error), str(error))
        else:
            raise AssertionError("duplicate old/new layout was silently reduced")

    with tempfile.TemporaryDirectory(prefix="lean-layout-nested-") as raw:
        root = Path(raw)
        (root / "lakefile.toml").write_text(LAKEFILE_NESTED, encoding="utf-8")
        write_module(root, "lean/Erdos249257.lean")
        write_module(root, "lean/Erdos249257/Only.lean", "def only := 1\n")
        write_module(root, "lean/ErdosProblems.lean")
        write_module(root, "verification/Challenge.lean", "def challenge := 1\n")
        write_module(root, "research/adapters/Adapter.lean", "def adapter := 1\n")
        paths = library_source_paths(root)
        ids = [library_module_id(path, root) for path in paths]
        require(ids.count("Erdos249257.Only") == 1, ids)
        require("Erdos249257" in ids, ids)
        require("ErdosProblems" in ids, ids)
        require(all(not module.startswith("lean.") for module in ids), ids)
        require("Challenge" not in ids and "Adapter" not in ids, ids)
        require(
            checkout_source_relative("Erdos249257/Only.lean", root)
            == "lean/Erdos249257/Only.lean",
            "library identity did not resolve onto nested storage",
        )
        require(
            checkout_source_relative("Challenge.lean", root)
            == "verification/Challenge.lean",
            "verification identity did not resolve onto verification storage",
        )
        require(
            checkout_source_relative("adapters/Adapter.lean", root)
            == "research/adapters/Adapter.lean",
            "adapter identity did not resolve onto research storage",
        )

    with tempfile.TemporaryDirectory(prefix="lean-layout-historical-") as raw:
        root = Path(raw)
        (root / "lakefile.toml").write_text(LAKEFILE_HISTORICAL, encoding="utf-8")
        write_module(root, "Erdos249257.lean")
        write_module(root, "Erdos249257/Only.lean")
        write_module(root, "ErdosProblems.lean")
        paths = library_source_paths(root, layout=LAYOUT_HISTORICAL_ROOT)
        require(
            [path.relative_to(root).as_posix() for path in paths]
            == [
                "Erdos249257.lean",
                "Erdos249257/Only.lean",
                "ErdosProblems.lean",
            ],
            paths,
        )

    with tempfile.TemporaryDirectory(prefix="lean-layout-truncated-") as raw:
        root = Path(raw)
        (root / "lakefile.toml").write_text(LAKEFILE_NESTED, encoding="utf-8")
        write_module(root, "lean/Erdos249257.lean")
        paths = library_source_paths(root, layout=LAYOUT_TRUNCATED_READER)
        require(
            [path.relative_to(root).as_posix() for path in paths] == ["lean/Erdos249257.lean"],
            paths,
        )
        nested = library_source_paths(root, layout=LAYOUT_NESTED)
        require(len(nested) == 1, nested)

    if shutil.which("git") is None:
        print("test_lean_source_layout: git absent; Git-index cases skipped")
        return 0

    with tempfile.TemporaryDirectory(prefix="lean-layout-unindexed-") as raw:
        root = Path(raw).resolve()
        (root / "lakefile.toml").write_text(LAKEFILE_NESTED, encoding="utf-8")
        write_module(root, "lean/Erdos249257.lean", "import Erdos249257.Tracked\n")
        write_module(root, "lean/Erdos249257/Tracked.lean", "def tracked := 1\n")
        write_module(root, "lean/ErdosProblems.lean")
        git(root, "init", "-q")
        git(root, "add", "-A")
        # An untracked sibling and an ignored one: neither exists in any clone.
        write_module(root, "lean/Erdos249257/Untracked.lean", "def untracked := 2\n")
        (root / ".gitignore").write_text("lean/Erdos249257/Ignored.lean\n", encoding="utf-8")
        write_module(root, "lean/Erdos249257/Ignored.lean", "def ignored := 3\n")
        inventory = library_source_inventory(root)
        ids = [library_module_id(path, root) for path in inventory["paths"]]
        require("Erdos249257.Tracked" in ids, ids)
        require("Erdos249257.Untracked" not in ids, ids)
        require("Erdos249257.Ignored" not in ids, ids)
        excluded = sorted(path.relative_to(root).as_posix() for path in inventory["unindexed"])
        require(
            excluded
            == ["lean/Erdos249257/Ignored.lean", "lean/Erdos249257/Untracked.lean"],
            excluded,
        )
        require(
            library_source_paths(root) == inventory["paths"],
            "library_source_paths must be the indexed inventory",
        )
        notice = describe_unindexed_library_sources(root)
        require(notice is not None and "Untracked.lean" in notice, notice)
        # A single git add makes the file part of every clone again.
        git(root, "add", "lean/Erdos249257/Untracked.lean")
        ids = [library_module_id(path, root) for path in library_source_paths(root)]
        require("Erdos249257.Untracked" in ids, ids)

        # A tracked module importing an unindexed one is irreproducible: refuse.
        write_module(root, "lean/Erdos249257/Reachable.lean", "def reachable := 4\n")
        write_module(
            root,
            "lean/Erdos249257/Tracked.lean",
            "import Erdos249257.Reachable\ndef tracked := 1\n",
        )
        try:
            library_source_paths(root)
        except LibraryLayoutError as error:
            require("not in the Git index" in str(error), str(error))
            require("Tracked.lean imports Erdos249257.Reachable" in str(error), str(error))
        else:
            raise AssertionError("indexed module importing an unindexed module was accepted")
        # A commented-out import is prose, not a dependency.
        write_module(
            root,
            "lean/Erdos249257/Tracked.lean",
            "-- import Erdos249257.Reachable\ndef tracked := 1\n",
        )
        require(
            "Erdos249257.Reachable"
            not in [library_module_id(path, root) for path in library_source_paths(root)],
            "commented import must not be treated as reachability",
        )

    print(
        "test_lean_source_layout: missing, duplicate, nested, historical, "
        "and truncated layouts stay distinct; Git-index enumeration excludes "
        "untracked and ignored sources and refuses unindexed imports"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
