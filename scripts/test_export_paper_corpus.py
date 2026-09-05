#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Focused executable-resolution contract for the public paper exporter."""

from __future__ import annotations

import os
import contextlib
import io
from dataclasses import replace
from pathlib import Path
from unittest.mock import patch

import export_paper_corpus as exporter


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> int:
    papers = exporter.papers_for_exported_corpus(check_source_coverage=False)
    native = next(paper for paper in papers if paper.is_native)
    with patch.object(exporter, "resolve_pandoc", side_effect=AssertionError("unexpected Pandoc lookup")), contextlib.redirect_stdout(io.StringIO()) as output:
        require(exporter.main(["--native-targets"]) == 0, "native target route failed")
    require(native.stem in output.getvalue().split(), "native target omitted")
    require(
        set(exporter.native_build_targets("Problem note"))
        == {paper.stem for paper in papers if paper.is_native and paper.form == "Problem note"},
        "note prerequisites must derive from the same registry form",
    )
    for unsafe in (replace(native, pdf="bad;command.pdf"), replace(native, source="paper/other.tex")):
        with patch.object(exporter, "papers_for_exported_corpus", return_value=(unsafe,)):
            try:
                exporter.native_build_targets()
            except ValueError:
                pass
            else:
                raise AssertionError("unsafe or mismatched Make target accepted")
    with patch.object(exporter, "papers_for_exported_corpus", return_value=(native, native)):
        try:
            exporter.native_build_targets()
        except ValueError:
            pass
        else:
            raise AssertionError("duplicate Make targets accepted")
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
