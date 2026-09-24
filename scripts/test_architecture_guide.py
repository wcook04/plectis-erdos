#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial fixtures for the newcomer architecture guide."""

from __future__ import annotations

import re
import os
import subprocess
import tempfile
from pathlib import Path
from unittest.mock import patch

import check_architecture_guide as checker
import check_release


def assert_rejected(text: str, label: str) -> None:
    try:
        checker.validate_guide(text)
    except AssertionError:
        return
    raise AssertionError(f"architecture-guide mutation escaped: {label}")


def assert_paper_rejected(text: str, label: str) -> None:
    try:
        checker.validate_systems_paper(text)
    except AssertionError:
        return
    raise AssertionError(f"systems-paper mutation escaped: {label}")


def reflow_tolerant_replace(source: str, phrase: str, replacement: str) -> str:
    """Replace prose even when LaTeX source rewraps it across lines."""
    pattern = r"\s+".join(re.escape(word) for word in phrase.split())
    return re.sub(pattern, lambda _match: replacement, source, count=1)


def check_safe_input_boundary() -> None:
    with tempfile.TemporaryDirectory(prefix="architecture-input-") as raw_workspace:
        workspace = Path(raw_workspace)
        regular = workspace / "regular.txt"
        regular.write_text("architecture input\n", encoding="utf-8")
        assert checker.safe_architecture_text(regular, root=workspace) == (
            "architecture input\n"
        )

        directory = workspace / "directory"
        directory.mkdir()
        try:
            checker.safe_architecture_text(directory, root=workspace)
        except checker.UnsafeArchitectureInput:
            pass
        else:
            raise AssertionError("architecture directory input escaped the regular-file boundary")

        symlink = workspace / "symlink.txt"
        symlink.symlink_to(regular)
        try:
            checker.safe_architecture_text(symlink, root=workspace)
        except checker.UnsafeArchitectureInput:
            pass
        else:
            raise AssertionError("architecture symlink input escaped the no-follow boundary")

        if hasattr(os, "mkfifo"):
            fifo = workspace / "fifo"
            os.mkfifo(fifo)
            try:
                checker.safe_architecture_text(fifo, root=workspace)
            except checker.UnsafeArchitectureInput:
                pass
            else:
                raise AssertionError("architecture FIFO input escaped the non-blocking boundary")


def check_public_root_inventory() -> None:
    with tempfile.TemporaryDirectory(prefix="public-root-layout-") as raw:
        root = Path(raw)
        def git(*args):
            return subprocess.run(["git", "-C", str(root), *args], check=True,
                                  capture_output=True, env=check_release.clean_environment())
        git("init", "-q")
        (root / ".gitignore").write_text("tmp/\nstate/\n.validation-singleflight/\n")
        (root / "README.md").write_text("Public entry\n")
        git("add", ".gitignore", "README.md")
        for name in ("tmp", "state", ".validation-singleflight"):
            (root / name).mkdir()
            (root / name / "local.json").write_text("{}\n")
        def errors():
            with patch.object(check_release, "ROOT", root), patch.object(check_release, "ERRORS", []):
                check_release.check_root_layout()
                return list(check_release.ERRORS)
        assert not errors(), "ignored local caches were treated as published documents"
        (root / "DUPLICATE.md").write_text("Unclassified candidate\n")
        assert any("DUPLICATE.md" in error for error in errors())
        (root / "DUPLICATE.md").unlink()
        git("add", "-f", "state/local.json")
        assert any("state" in error for error in errors()), "ignore rule hid a staged public file"
        git("rm", "--cached", "state/local.json")
        (root / "ErdosProblems").mkdir()
        (root / "ErdosProblems" / "Loose.lean").write_text("def x := 1\n")
        assert any("loose corpus" in error for error in errors())


def main() -> int:
    check_public_root_inventory()
    check_safe_input_boundary()
    guide = checker.GUIDE.read_text(encoding="utf-8")
    readme = checker.README.read_text(encoding="utf-8")
    agents = checker.AGENTS.read_text(encoding="utf-8")
    paper_readme = checker.PAPER_README.read_text(encoding="utf-8")
    systems_paper = checker.SYSTEMS_PAPER.read_text(encoding="utf-8")

    checker.validate_guide(guide)
    checker.validate_systems_paper(systems_paper)
    checker.validate_entry_links(readme, agents, paper_readme, guide)
    checks = 3

    contract = checker.json.loads(
        checker.safe_architecture_text(checker.PUBLICATION_CONTRACT)
    )
    systems_paper_budget = (
        checker.SYSTEMS_PAPER_BASE_BYTES
        + checker.SYSTEMS_PAPER_BYTES_PER_ARTIFACT * len(contract["artifacts"])
    )
    assert len(systems_paper.encode("utf-8")) <= systems_paper_budget

    mutations = (
        (
            reflow_tolerant_replace(
                guide, checker.external_status_boundary(), ""
            ),
            "open-problem boundary removed",
        ),
        (
            reflow_tolerant_replace(
                guide,
                "reviewed claim registry covers #68, #243, #249, #251, #257, #269, #1041 and #1049",
                "reviewed claim registry covers #249 and #257",
            ),
            "obsolete two-problem registry scope restored",
        ),
        (
            guide.replace("#1049.", "#1049 and #9999.", 1),
            "unregistered problem added to reviewed scope",
        ),
        (
            guide.replace("comparator_assurance", "unrelated_route"),
            "Comparator inspection route removed",
        ),
        (
            guide.replace("palomar_qualification", "unrelated_route"),
            "Palomar qualification route removed",
        ),
        (
            guide.replace("Lean decides whether a formal proof", "Software decides"),
            "formal-check decision blurred",
        ),
        (
            guide.replace("A mathematician decides whether the public wording", ""),
            "human semantic review removed",
        ),
        (
            guide.replace("does not prove that every important sentence was selected", ""),
            "coverage ceiling removed",
        ),
        (
            reflow_tolerant_replace(
                guide,
                "The archived combined #249/#257 PDF is not a default reading route.",
                "The combined #249/#257 PDF is the default reading route.",
            ),
            "retired combined manuscript restored as default gateway",
        ),
        (
            guide.replace("## A complete example", "## Internal record"),
            "worked-example section removed",
        ),
        (guide + "\nM8 achieved 9/10.\n", "evaluation shorthand introduced"),
    )
    for mutated, label in mutations:
        assert_rejected(mutated, label)
        checks += 1

    paper_mutations = (
        (
            systems_paper.replace(
                r"\section{A problem-sized world}",
                r"\section{Background}",
            ),
            "real architecture section removed",
        ),
        (
            systems_paper.replace("docs/claims.json", "a claim file"),
            "real claim owner hidden",
        ),
        (
            systems_paper.replace("Comparator-checked", "Independently verified"),
            "review-enforcement boundary inflated",
        ),
        (
            systems_paper + "\nThe M8 score was 9/10 across 5,207 checks.\n",
            "private evaluation shorthand reintroduced",
        ),
        (
            reflow_tolerant_replace(
                systems_paper,
                "% BEGIN generated_semantic_coverage_macros",
                "% semantic coverage macros removed",
            ),
            "semantic-corpus builder boundary removed",
        ),
        (
            reflow_tolerant_replace(
                systems_paper,
                "semantic single-flight queue",
                "ordinary build command",
            ),
            "Lean queue architecture removed",
        ),
        (
            reflow_tolerant_replace(
                systems_paper,
                "The records treat negative results as outputs",
                "The records keep only successful results",
            ),
            "negative-results thesis removed",
        ),
        (
            reflow_tolerant_replace(
                systems_paper,
                "does not technically force a second independent mathematician",
                "guarantees a second independent mathematician",
            ),
            "single-maintainer review ceiling inflated",
        ),
        (
            systems_paper.replace(
                "https://github.com/wcook04/plectis-erdos",
                "https://github.com/wcook04/plectis-lean-erdos249-257",
            ),
            "repository links use a retired repository name",
        ),
        (
            systems_paper.replace(
                r"\repolink{docs/ARCHITECTURE.md}{docs/ARCHITECTURE.md}",
                r"\repolink{ARCHITECTURE.md}{ARCHITECTURE.md}",
            ),
            "inspection route points to a missing repository file",
        ),
    )
    for mutated, label in paper_mutations:
        assert mutated != systems_paper, (
            f"systems-paper mutation fixture became a no-op: {label}"
        )
        assert_paper_rejected(mutated, label)
        checks += 1

    overflow = systems_paper + "x" * (
        systems_paper_budget - len(systems_paper.encode("utf-8")) + 1
    )
    assert_paper_rejected(
        overflow,
        "publication-scaled architecture budget exceeded",
    )
    checks += 1

    try:
        checker.validate_entry_links(
            readme.replace(
                "](docs/ARCHITECTURE.md)",
                "](missing-architecture.md)",
            ),
            agents,
            paper_readme,
            guide,
        )
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("README architecture entry-link deletion escaped")

    try:
        checker.validate_entry_links(
            reflow_tolerant_replace(
                readme,
                checker.external_status_boundary(),
                "A conditional producer would be required",
            ),
            agents,
            paper_readme,
            guide,
        )
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("README private first-impression phrase escaped")

    try:
        checker.validate_entry_links(
            readme,
            agents,
            paper_readme.replace(
                "repository layout, sources of truth, build path, and release\n"
                "infrastructure",
                "specialist systems case study",
            ),
            guide,
        )
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("paper architecture-role deletion escaped")

    try:
        checker.validate_entry_links(
            readme,
            agents,
            paper_readme,
            guide.replace(
                "claim-faithful-publication-systems-paper.pdf",
                "systems-paper.pdf",
            ),
        )
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("architecture systems-paper link deletion escaped")

    try:
        checker.validate_entry_links(
            readme,
            agents,
            paper_readme,
            guide.replace("You do not need to know Lean", "Start by learning Lean"),
        )
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("architecture no-Lean entry boundary deletion escaped")

    print(f"architecture guide tests: {checks} checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
