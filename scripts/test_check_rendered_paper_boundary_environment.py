#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Protect reader-facing limits and keep Poppler independent of ambient state."""

from __future__ import annotations

import os
import subprocess
import tempfile
from pathlib import Path
from unittest.mock import patch

import check_rendered_paper_boundary as boundary


def require(condition: bool, message: str) -> None:
    """Keep the external-tool contract active when Python is run with -O."""
    if not condition:
        raise AssertionError(message)


def check_rendered_file_boundary() -> None:
    """Rendered inputs cannot redirect through a symlinked checkout path."""
    with tempfile.TemporaryDirectory(prefix="rendered-boundary-") as raw:
        root = Path(raw) / "checkout"
        outside = Path(raw) / "outside"
        root.mkdir()
        outside.mkdir()
        (outside / "paper.tex").write_text("private paper\n", encoding="utf-8")
        linked = root / "paper.tex"
        linked.symlink_to(outside / "paper.tex")
        original_root = boundary.ROOT
        boundary.ROOT = root
        try:
            try:
                boundary.safe_rendered_file(linked)
            except boundary.UnsafeRenderedInput as error:
                require("symlinked" in str(error), str(error))
            else:
                raise AssertionError("rendered checker followed a symlink")
            regular = root / "regular.pdf"
            regular.write_bytes(b"pdf fixture")
            require(
                boundary.safe_rendered_file(regular) == regular,
                "rendered checker rejected a regular in-root file",
            )

            if hasattr(os, "mkfifo"):
                fifo = root / "fifo.tex"
                os.mkfifo(fifo)
                try:
                    boundary.safe_rendered_text(fifo)
                except boundary.UnsafeRenderedInput as error:
                    require("regular file" in str(error), str(error))
                else:
                    raise AssertionError("rendered checker opened a FIFO input")
        finally:
            boundary.ROOT = original_root


def check_unified_systems_limits() -> None:
    """Scope/benefit promotions and displaced limits must fail the current profile.

    These excerpts come from the accepted native systems PDF. Poppler is mocked
    here so the negative fixtures also run in the stdlib-only release gate.
    The full rendered check separately verifies the actual PDF and page bands.
    """
    pages = {
        1: """Publishing Mathematical Results from a Lean Repository
Evidence, exposition and revision in eight Erdős problems.
For each mathematical problem, Plectis keeps the question, prior sources,
computations, proofs and unresolved steps together.
A historical test rejected nine of ten false edits but accepted a false claim
of completion.""",
        6: """Lean verifies that a proof establishes the formal statement written
in the source. Comparator adds a separately stated challenge and a check of its
selected Lean implementation under the permitted axioms.
The protocol distinguishes contributor and reviewer roles but does not require
a second independent mathematician. No independent human mathematical review
of the corpus is recorded.
Source-frozen editorial refinement
We freeze the selected manuscripts, their required input files, coverage ledger and audit
rules under a manifest of their exact bytes.
In either case the integrating reviewer decides whether the mathematics and
its description remain faithful.""",
        7: """It neither applies the proposal nor executes returned programs.
This procedure supplies no measurement of reader benefit or autonomous discovery.
An open route for contributions.""",
        8: """Two entry routes and three possible review outcomes.
Repository adoption applies to mathematical and methodological contributions;
it establishes neither independent review nor acceptance by the wider
mathematical community.
The historical publication-evidence record reports that nine of the
ten deliberately false edits were rejected and one escaped.""",
        9: """The contributor and reviewer were the same agent.
The receipt records no public pull request, human review or independent outside clone replay.
No comparative reader result is reported.""",
        10: """Transfer to unseen mathematics and understanding by
independent human readers are unresolved.
Openness alone does not equalise resources or resolve conflicts and appeals.
Broad mathematical acceptance is exogenous to this repository and cannot be
granted by its maintainer.
This paper reports no new Lean or Comparator execution.""",
        11: """The initial unified manuscript was prepared from the frozen packet,
a local integration commit rather than public main.""",
    }
    pdf = boundary.ROOT / "paper/systems/claim-faithful-publication-systems-paper.pdf"

    def check(candidate: dict[int, str]) -> list[str]:
        def render(_pdf, _tool, first, last):
            return " ".join(candidate.get(page, "") for page in range(first, last + 1))
        with patch.object(boundary, "unified_systems_profile", return_value=True):
            with patch.object(boundary, "rendered_pages", side_effect=render):
                return boundary.first_minute_errors(pdf, "fixture-pdftotext")

    require(check(pages) == [], "accepted systems excerpts fail the reader contract")
    mutations = (
        (1, "accepted a false claim\nof completion", "detected every false claim", "false claim of completion"),
        (8, "nine of the\nten deliberately false edits were rejected and one escaped", "all ten deliberately false edits were rejected", "nine of the ten deliberately false edits"),
        (6, "the integrating reviewer decides", "the automated checker decides", "integrating reviewer decides"),
        (7, "no measurement of reader benefit", "a measurement of reader benefit", "no measurement of reader benefit"),
        (7, "neither applies the proposal nor executes", "applies the proposal and executes", "neither applies the proposal nor executes"),
        (10, "understanding by", "speed of", "transfer to unseen mathematics and understanding by"),
        (10, "independent human readers are unresolved", "independent human readers are fully understood", "independent human readers are unresolved"),
        (10, "exogenous to this repository and cannot be", "supplied by this repository and can be", "acceptance is exogenous"),
        (9, "No comparative reader result is reported", "A comparative reader result is established", "no comparative reader result"),
        (6, "does not require\na second independent mathematician", "requires a second independent mathematician", "does not require a second independent mathematician"),
        (9, "The contributor and reviewer were the same agent", "The contributor and reviewer were independent people", "contributor and reviewer were the same agent"),
    )
    for page, old, new, missing in mutations:
        require(old in pages[page], f"negative fixture target missing: {old}")
        changed = dict(pages)
        changed[page] = changed[page].replace(old, new, 1)
        errors = check(changed)
        require(any(missing in error for error in errors), f"claim promotion escaped: {new}")
    moved = dict(pages)
    moved[12] = moved.pop(8)
    require(
        any("pages 8-9" in error and "nine of the ten" in error for error in check(moved)),
        "historical limit outside its reviewed page band was accepted",
    )


def main() -> int:
    check_rendered_file_boundary()
    check_unified_systems_limits()
    hostile_environment = {
        "GIT_DIR": "/private/wrong-git-dir",
        "GIT_NAMESPACE": "refs/namespaces/wrong-release",
        "GIT_REPLACE_REF_BASE": "refs/replace/",
        "PYTHONPATH": "/private/wrong-python-path",
        "LC_ALL": "C",
        "LANG": "C",
        "PATH": "/private/wrong-bin",
    }
    pdftotext = "/opt/poppler/bin/pdftotext"
    pdftohtml = "/opt/poppler/bin/pdftohtml"
    pdf = boundary.ROOT / "paper" / "archive" / "erdos249-257-main-paper.pdf"
    completed = [
        subprocess.CompletedProcess([], 0, stdout="plain text\n"),
        subprocess.CompletedProcess([], 0, stdout=""),
        subprocess.CompletedProcess([], 0, stdout="page text\n"),
    ]
    with patch.dict(os.environ, hostile_environment, clear=False):
        with patch.object(boundary.subprocess, "run", side_effect=completed) as run:
            require(
                boundary.rendered_text(pdf, pdftotext) == "plain text\n",
                "pdftotext output was not returned",
            )
            require(
                boundary.rendered_hrefs(pdf, pdftohtml) == set(),
                "pdftohtml output was not parsed",
            )
            require(
                boundary.rendered_pages(pdf, pdftotext, 1, 2)
                == "page text\n",
                "paged pdftotext output was not returned",
            )

    require(len(run.call_args_list) == 3, "all Poppler calls were not exercised")
    for call in run.call_args_list:
        kwargs = call.kwargs
        sanitized = kwargs["env"]
        for key in (
            "GIT_DIR",
            "GIT_NAMESPACE",
            "GIT_REPLACE_REF_BASE",
            "PYTHONPATH",
        ):
            require(key not in sanitized, f"ambient {key} leaked into Poppler")
        require(sanitized["LC_ALL"] == "C.UTF-8", "canonical locale missing")
        require(sanitized["LANG"] == "C.UTF-8", "canonical LANG missing")
        require(
            sanitized["PATH"].split(os.pathsep)[0] == "/opt/poppler/bin",
            "Poppler executable directory was not preserved",
        )
        require(
            kwargs["timeout"] == boundary.EXTERNAL_TOOL_TIMEOUT_SECONDS,
            "Poppler timeout drifted",
        )

    require(
        boundary.ENVIRONMENT_CONTRACT
        == "clean_committed_snapshot_subprocess_environment_v1",
        "rendered-paper environment contract drifted",
    )
    print(
        "test_check_rendered_paper_boundary_environment: Poppler checks use a "
        "clean snapshot environment and bounded subprocesses; systems scope "
        "and benefit promotions are rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
