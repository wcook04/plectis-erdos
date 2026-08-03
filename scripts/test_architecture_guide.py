#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial fixtures for the newcomer architecture guide."""

from __future__ import annotations

import re

import check_architecture_guide as checker


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


def main() -> int:
    guide = checker.GUIDE.read_text(encoding="utf-8")
    readme = checker.README.read_text(encoding="utf-8")
    agents = checker.AGENTS.read_text(encoding="utf-8")
    paper_readme = checker.PAPER_README.read_text(encoding="utf-8")
    systems_paper = checker.SYSTEMS_PAPER.read_text(encoding="utf-8")

    checker.validate_guide(guide)
    checker.validate_systems_paper(systems_paper)
    checker.validate_entry_links(readme, agents, paper_readme)
    checks = 3

    contract = checker.json.loads(
        checker.PUBLICATION_CONTRACT.read_text(encoding="utf-8")
    )
    systems_paper_budget = (
        checker.SYSTEMS_PAPER_BASE_BYTES
        + checker.SYSTEMS_PAPER_BYTES_PER_ARTIFACT * len(contract["artifacts"])
    )
    assert len(systems_paper.encode("utf-8")) <= systems_paper_budget

    mutations = (
        (
            guide.replace(
                "All eight mathematical problems remain open", ""
            ),
            "open-problem boundary removed",
        ),
        (
            reflow_tolerant_replace(
                guide,
                "reviewed claim registry covers #249 and #257",
                "claim registry covers the project",
            ),
            "reviewed-versus-expansion boundary removed",
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
                r"\section{The release workflow}",
                r"\section{Background}",
            ),
            "real architecture section removed",
        ),
        (
            systems_paper.replace("docs/claims.json", "a claim file"),
            "real claim owner hidden",
        ),
        (
            reflow_tolerant_replace(
                systems_paper,
                "does not technically force a second independent mathematician",
                "enforces independent review",
            ),
            "review-enforcement boundary inflated",
        ),
        (
            systems_paper + "\nThe M8 score was 9/10 across 5,207 checks.\n",
            "private evaluation shorthand reintroduced",
        ),
        (
            reflow_tolerant_replace(
                systems_paper,
                "navigation, reading map, code index, machine-readable summary; no authority",
                "orientation, declaration atlas,\\\\\n  machine entry packet",
            ),
            "private diagram labels reintroduced",
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
                "[architecture and repository guide](ARCHITECTURE.md)",
                "architecture notes",
            ),
            agents,
            paper_readme,
        )
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("README architecture entry-link deletion escaped")

    try:
        checker.validate_entry_links(
            readme.replace(
                "All eight problems remain open.",
                "A conditional producer would be required",
            ),
            agents,
            paper_readme,
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
                "architecture\nand access guide",
                "specialist systems case study",
            ),
        )
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("paper architecture-role deletion escaped")

    print(f"architecture guide tests: {checks} checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
