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
    """Reject semantic promotions and misplaced limits; allow repagination.

    Fixed excerpts from the October 2026 manuscript are independent of the
    production contract. Mock extraction keeps these negative tests stdlib-only.
    """
    abstract = """A Repository-Based System for Research and Publication
Architecture, evidence and iteration in a Lean research repository
The public prototype brings questions, sources, proofs, computations and failed approaches together in eight problem collections.
Researchers and agents choose the work.
A historical author-run test rejected nine of ten false edits and accepted one false completion claim.
Reader benefit, discovery rate and adoption by independent laboratories remain unmeasured."""
    sections = [
        """2 A repository organised around problems
Files store the research state.
Freshness checks detect disagreement; builders regenerate views. Neither adopts a claim.
agent_entry.py maps a stated task to instructions.
paper_evidence.py locates each registered support.
paper_claim_evidence.py derives status and gap reports.
The maintainer reviews scope, attribution and unresolved obligations before adoption.""",
        """3 Worked case: reviewing an explanation
Rebinding can remove that warning without repairing the claim.
Review must compare the wording with the cited statements.
The claim remains unproved.""",
        """4 Proof and publication checks
The publication audit checks the full registered list even when one declaration suffices for a particular clause.
That checks the record; it adds no mathematical hypothesis.
Lean verifies that a proof establishes the formal statement written in the source.
Comparator adds a separately stated challenge.
The protocol does not technically force a second independent mathematician.
No independent human mathematical review of the corpus is recorded.""",
        """5 Publication and revision
The exchange freezes selected manuscripts, required inputs, coverage records and audit rules under a manifest of their file digests.
Both routes return proposed changes for the same review of mathematical scope, wording and credit.
It neither applies changes nor executes returned programs.
The procedure itself measures neither reader benefit nor autonomous discovery.""",
        """6 An open route for contributions
Adoption establishes neither independent review nor wider acceptance.
Ordinary issues and pull requests need not become journal events.""",
        """7 Recorded observations
Nine of the ten deliberately false edits were rejected and one escaped.
The edits were authored by the checker’s author.
The other nine edits were not rerun.
It supplies no post-repair ten-of-ten result.
The contributor and reviewer were the same agent.
The receipt records no public pull request, human review or independent outside clone replay.
There is no comparative reader result.""",
        """8 Related work
This is not a general incremental scheduler.""",
        """9 Limits
Transfer to unseen mathematics and understanding by independent readers require direct evaluation.
Openness alone does not equalise resources.
Repository adoption cannot confer acceptance by the wider mathematical community.""",
        """A Reading the materials and reproducing checks
A local integration commit rather than public main.
No new Lean or Comparator run was performed for this revision.
It supports document checks, not a full Lean, Comparator or release rerun.""",
        """B The mathematical example: a criterion for irrationality""",
    ]
    pdf = boundary.ROOT / "paper/systems/claim-faithful-publication-systems-paper.pdf"

    def check(candidate: list[str], front: str = abstract) -> list[str]:
        text = "\f".join([front, *candidate])
        with patch.object(boundary, "unified_systems_profile", return_value=True):
            with patch.object(boundary, "rendered_pages", return_value=front):
                with patch.object(boundary, "rendered_text", return_value=text):
                    return boundary.first_minute_errors(pdf, "fixture-pdftotext")

    require(check(sections) == [], "accepted excerpts fail the reader contract")
    require(check(sections, abstract.replace("accepted one false completion claim",
            "detected every false completion claim")), "abstract promotion escaped")
    mutations = (
        (1, "without repairing the claim", "while repairing the claim"),
        (1, "The claim remains unproved", "The claim is disproved"),
        (4, "neither independent review nor wider acceptance", "independent review and wider acceptance"),
        (2, "the full registered list", "any one declaration"),
        (2, "adds no mathematical hypothesis", "adds a mathematical hypothesis"),
        (2, "does not technically force", "requires"),
        (2, "No independent human mathematical review", "Independent human mathematical review"),
        (3, "the same review of mathematical scope, wording and credit", "automatic acceptance"),
        (3, "neither applies changes nor executes", "applies changes and executes"),
        (3, "measures neither reader benefit nor autonomous discovery", "measures reader benefit and autonomous discovery"),
        (5, "Nine of the ten deliberately false edits were rejected and one escaped", "All ten deliberately false edits were rejected"),
        (5, "no post-repair ten-of-ten result", "a post-repair ten-of-ten result"),
        (5, "were the same agent", "were independent people"),
        (5, "no comparative reader result", "a comparative reader result"),
        (7, "require direct evaluation", "have been demonstrated"),
        (7, "cannot confer acceptance", "confers acceptance"),
        (8, "local integration commit rather than public main", "public main"),
        (8, "No new Lean or Comparator run", "A new Lean and Comparator run"),
        (8, "not a full Lean, Comparator or release rerun", "a full Lean, Comparator and release rerun"),
    )
    for index, old, new in mutations:
        require(old in sections[index], f"negative fixture target missing: {old}")
        changed = list(sections)
        changed[index] = changed[index].replace(old, new, 1)
        require(check(changed), f"claim promotion escaped: {new}")

    # Figures can move complete sections without changing their obligations.
    repaginated = ["", *sections]
    require(check(repaginated) == [], "benign figure repagination was rejected")
    moved = list(sections)
    limit = "No new Lean or Comparator run was performed for this revision."
    moved[8] = moved[8].replace(limit, "")
    moved[7] += "\n" + limit
    require(any("no new lean or comparator run" in error for error in check(moved)),
            "a limit in the wrong section satisfied the reproduction boundary")
    oversized = list(sections)
    oversized[5] += "\f" * 4
    require(any("exceeds 3 pages" in error for error in check(oversized)),
            "an unbounded observations section was accepted")
    duplicate = list(sections)
    duplicate[5] += "\n7 Recorded observations"
    require(any("ambiguous" in error for error in check(duplicate)),
            "ambiguous section delimiter was accepted")


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
