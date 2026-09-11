#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Full-source discovery must not silently pick old vs new corpus layouts."""

from __future__ import annotations

import tempfile
from pathlib import Path

from lean_source import (
    LAYOUT_HISTORICAL_ROOT,
    LAYOUT_NESTED,
    LAYOUT_TRUNCATED_READER,
    LibraryLayoutError,
    checkout_source_relative,
    library_module_id,
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

    print(
        "test_lean_source_layout: missing, duplicate, nested, historical, "
        "and truncated layouts stay distinct"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
