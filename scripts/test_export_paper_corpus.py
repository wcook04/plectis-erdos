#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Focused executable-resolution contract for the public paper exporter."""

from __future__ import annotations

import os
from pathlib import Path
from unittest.mock import patch

import export_paper_corpus as exporter


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> int:
    with patch.dict(os.environ, {"PATH": "/untrusted/ambient/bin"}, clear=False):
        pandoc = exporter.resolve_pandoc()
    require(pandoc is not None, "installed Pandoc was not found through trusted paths")
    require(Path(pandoc).is_absolute(), "resolved Pandoc path is not absolute")
    require(
        exporter.resolve_pandoc(pandoc) == pandoc,
        "explicit absolute Pandoc path did not resolve to the same executable",
    )

    environment = exporter._pandoc_environment(pandoc)
    require(
        "/untrusted/ambient/bin" not in environment["PATH"].split(os.pathsep),
        "Pandoc child inherited the ambient executable search path",
    )
    with patch.object(exporter, "_PANDOC_EXECUTABLE", pandoc):
        version = exporter._pandoc(["--version"])
    require(version.startswith("pandoc "), "resolved executable is not Pandoc")

    with (
        patch.object(exporter, "TRUSTED_PANDOC_PATHS", ()),
        patch.object(exporter.shutil, "which", return_value=None),
    ):
        require(exporter.resolve_pandoc() is None, "missing Pandoc was accepted")
        try:
            exporter._pandoc(["--version"])
        except RuntimeError as error:
            require("pandoc is required" in str(error), "missing-Pandoc error lost context")
        else:
            raise AssertionError("Pandoc invocation proceeded without an executable")

    try:
        exporter.resolve_pandoc("relative/pandoc")
    except ValueError as error:
        require("absolute" in str(error), "relative-path rejection lost its reason")
    else:
        raise AssertionError("relative explicit Pandoc path was accepted")

    print("test_export_paper_corpus: trusted Pandoc resolution passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
