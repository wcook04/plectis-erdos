#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check that the newcomer architecture guide stays concrete and jargon-free."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
GUIDE = ROOT / "ARCHITECTURE.md"
README = ROOT / "README.md"
AGENTS = ROOT / "AGENTS.md"
PAPER_README = ROOT / "paper" / "README.md"
SYSTEMS_PAPER = ROOT / "paper" / "claim-faithful-publication-systems-paper.tex"
SYSTEMS_PDF = ROOT / "claim-faithful-publication-systems-paper.pdf"
MAX_GUIDE_BYTES = 18_000
# Raised from 40_000 (maintainer decision, July 2026) to admit the
# example-instantiated assurance, coverage, and reuse material, then to
# 50_000 for the cold-reader repairs (named equivalence declarations,
# witness glosses, integer-arithmetic detail), then to 52_000 for the
# perimeter-contraction and claim-to-reader-gap material; the budget still
# exists so the paper cannot grow without a deliberate decision.
# Raised again to 52_300 for PDF metadata only: a document language for
# screen readers, keywords, and a numbered outline, matching what the
# mathematics paper already declares. No prose was added and the rendered
# paper is still fourteen pages, so this raise funds metadata, not material.
MAX_SYSTEMS_PAPER_BYTES = 52_300

SECTION_ORDER = (
    "## What this repository is",
    "## The architecture in one page",
    "## Which file is authoritative for what",
    "## Repository map",
    "## A complete example",
    "## What happens when a change is made",
    "## How the checks run",
    "## What the checks do not prove",
    "## Where to start",
)

REQUIRED_ANCHOR_GROUPS = {
    "purpose_and_boundary": (
        "Both mathematical problems remain open",
        "does not claim a solution to either problem",
        "self-contained public release",
    ),
    "three_decisions": (
        "Lean decides whether a formal proof",
        "A mathematician decides whether the public wording",
        "The release program decides whether the files",
    ),
    "authority_owners": (
        "Erdos249257.lean",
        "docs/claims.json",
        "docs/methodology.json",
        "scripts/check_release.py",
        ".github/workflows/lean.yml",
    ),
    "worked_example": (
        "certified_kill_instances",
        "verified finite instance",
        "beyond every fixed cutoff",
    ),
    "validation_split": (
        "lake build",
        "python3 scripts/check_release.py",
        "does not run Lean",
    ),
    "guarantee_ceiling": (
        "does not mean that a program understood every sentence",
        "does not prove that every important sentence was selected",
    ),
}

REQUIRED_PATHS = (
    "Erdos249257.lean",
    "ErdosProblems.lean",
    "docs/claims.json",
    "docs/methodology.json",
    "docs/publication_contract.json",
    "docs/publication_evidence.json",
    "docs/ORIENTATION.md",
    "docs/SOURCE_MAP.md",
    "scripts/check_release.py",
    "scripts/check_cold_clone_comprehension.py",
    ".github/workflows/lean.yml",
    "paper/erdos249-257-main-paper.tex",
)

# These labels belong to the evaluation history or to private agent doctrine.
# A first-principles repository guide has no reason to make a cold reader decode
# them. The full words Type A and Type B are included because they are private
# role labels in the parent workflow, not part of this public Lean project.
BANNED_SHORTHAND = (
    re.compile(r"\bM(?:10|[1-9])\b"),
    re.compile(r"\b9/10\b"),
    re.compile(r"\b5,207\b"),
    re.compile(r"\bMRS\b"),
    re.compile(r"\bquantifier\b", re.IGNORECASE),
    re.compile(r"\bType A\b", re.IGNORECASE),
    re.compile(r"\bType B\b", re.IGNORECASE),
    re.compile(r"\bAccess Skeleton\b", re.IGNORECASE),
    re.compile(r"\bVinum\b", re.IGNORECASE),
)

PAPER_SECTION_ORDER = (
    r"\section{The publication gap}",
    r"\section{The release workflow}",
    r"\section{One claim from Lean theorem to public page}",
    r"\section{What the checks establish}",
    r"\section{A boundary the checklist missed}",
    r"\section{Scope, reuse, and limits}",
    r"\section{Related systems}",
    r"\section{Conclusion}",
    r"\section{Reproducibility}",
)

PAPER_REQUIRED_ANCHOR_GROUPS = {
    "plain_purpose": (
        "Lean verifies that a proof establishes the formal statement written in the source",
        "Both problems remain open",
        "does not claim a solution to either problem",
    ),
    "five_real_parts": (
        "Lean source",
        "maintainer-reviewed claim record",
        "authored public documents",
        "generated indexes and summaries",
        "release program and continuous-integration workflow",
    ),
    "plain_diagram_labels": (
        "reading map, code index",
        "machine-readable summary",
    ),
    "real_owners": (
    "Erdos249257.lean",
    "ErdosProblems.lean",
        "docs/claims.json",
        "docs/publication_contract.json",
        "docs/publication_evidence.json",
        "scripts/check_release.py",
        ".github/workflows/lean.yml",
    ),
    "decision_boundary": (
        "Lean checks the formal proofs",
        "A maintainer reviews what those proofs mean",
        "The release machinery checks that the recorded relationships remain intact",
        "does not technically force a second independent mathematician",
    ),
    "worked_trace": (
        # Pins the worked example to the band the claim record carries, not to a
        # superseded deposit count. The band moved from 28 recorded scales
        # through t = 64 to every scale t <= 82; an anchor naming the old count
        # would enforce an understatement of the checked theorem.
        "Lean has checked a finite certificate at every lcm-diagonal scale",
        "beyond every fixed cutoff",
        "public meaning, not its internal name",
        "certified_kill_instances",
    ),
    "release_flow": (
        "lake build",
        "python3 scripts/check_release.py",
        "two separate jobs",
        "treats that exit as a failing job",
    ),
    "coverage_ceiling": (
        "A boundary the checklist missed",
        "coverage boundary, not a reliability score",
        "only after a person has identified and recorded that relationship",
    ),
    # The three named objects and the passages that instantiate the general
    # machinery on them are load-bearing: losing them returns the paper to a
    # generic systems essay beside a decorative example.
    "worked_example_governs": (
        "No Lean theorem carries the first to the second",
        "Instantiated on the worked example",
        "boundary witness",
        "assurance perimeter",
        "Coverage can also shrink",
    ),
}


def normalise(text: str) -> str:
    return " ".join(text.split())


def normalise_tex(text: str) -> str:
    """Flatten the small subset of TeX used by load-bearing prose anchors."""
    for _ in range(3):
        text = re.sub(
            r"\\(?:textbf|emph|texttt)\{([^{}]*)\}",
            r"\1",
            text,
        )
    text = text.replace(r"\_", "_").replace("{", "").replace("}", "")
    return normalise(text)


def validate_guide(text: str) -> None:
    size = len(text.encode("utf-8"))
    assert size <= MAX_GUIDE_BYTES, (
        f"ARCHITECTURE.md is {size} bytes (budget {MAX_GUIDE_BYTES})"
    )

    positions = [text.find(heading) for heading in SECTION_ORDER]
    assert all(position >= 0 for position in positions), (
        f"architecture guide lost section sequence {SECTION_ORDER}"
    )
    assert positions == sorted(positions), "architecture guide sections are out of order"

    compact = normalise_tex(text)
    for group_id, anchors in REQUIRED_ANCHOR_GROUPS.items():
        for anchor in anchors:
            assert normalise(anchor).casefold() in compact.casefold(), (
                f"architecture guide lost {group_id} anchor {anchor!r}"
            )

    for pattern in BANNED_SHORTHAND:
        assert not pattern.search(text), (
            f"architecture guide exposes private or evaluation shorthand {pattern.pattern!r}"
        )

    for rel in REQUIRED_PATHS:
        assert (ROOT / rel).exists(), f"architecture guide names missing path {rel}"
        assert rel in text, f"architecture guide no longer routes through {rel}"

    for target in re.findall(r"\[[^\]]+\]\(([^)]+)\)", text):
        if target.startswith(("http://", "https://", "#")):
            continue
        path = target.split("#", 1)[0]
        assert (ROOT / path).exists(), f"architecture guide has broken local link {target}"


def validate_systems_paper(text: str) -> None:
    """Keep the PDF source architecture-first rather than experiment-first."""
    size = len(text.encode("utf-8"))
    assert size <= MAX_SYSTEMS_PAPER_BYTES, (
        f"systems architecture paper is {size} bytes "
        f"(budget {MAX_SYSTEMS_PAPER_BYTES})"
    )

    assert (
        "From Lean Proofs to Public Claims" in text
        and "Release checks and trust boundaries in one formal mathematics repository"
        in text
    ), "systems paper lost its plain architecture title"

    positions = [text.find(heading) for heading in PAPER_SECTION_ORDER]
    assert all(position >= 0 for position in positions), (
        f"systems paper lost section sequence {PAPER_SECTION_ORDER}"
    )
    assert positions == sorted(positions), "systems paper sections are out of order"

    compact = normalise_tex(text)
    for group_id, anchors in PAPER_REQUIRED_ANCHOR_GROUPS.items():
        for anchor in anchors:
            assert normalise(anchor).casefold() in compact.casefold(), (
                f"systems paper lost {group_id} anchor {anchor!r}"
            )

    for pattern in BANNED_SHORTHAND:
        assert not pattern.search(text), (
            f"systems paper exposes private or score-like shorthand {pattern.pattern!r}"
        )

    assert len(re.findall(r"\bsentence\b", text, flags=re.IGNORECASE)) <= 4, (
        "systems paper has drifted back to a sentence-centred case study"
    )
    public_meaning = compact.find("public meaning, not its internal name")
    internal_id = compact.find("certified_kill_instances")
    assert 0 <= public_meaning < internal_id, (
        "systems paper exposes its internal claim id before the public meaning"
    )
    assert SYSTEMS_PDF.is_file(), "rendered systems architecture PDF is missing"


def validate_entry_links(readme: str, agents: str, paper_readme: str) -> None:
    readme_prefix = readme.encode("utf-8")[:6_000].decode("utf-8", errors="ignore")
    assert "[architecture and repository guide](ARCHITECTURE.md)" in readme_prefix
    assert (
        "[printable PDF](claim-faithful-publication-systems-paper.pdf)"
        in readme_prefix
    )
    assert "It assumes no Lean or project history" in normalise(readme_prefix)
    for phrase in (
        "conditional producer",
        "unbounded or cofinal supply",
        "lcm-diagonal scales",
        "producer carry",
    ):
        assert phrase not in readme_prefix.casefold(), (
            f"README first impression exposes unexplained phrase {phrase!r}"
        )
    assert "ARCHITECTURE.md" in agents
    assert "plain-language human guide" in agents
    compact_paper_readme = normalise(paper_readme)
    assert "[`ARCHITECTURE.md`](../ARCHITECTURE.md)" in paper_readme
    assert "authored papers with narrower jobs" in compact_paper_readme
    assert "architecture and access guide" in compact_paper_readme
    assert "historical checker example appears only after the architecture" in (
        compact_paper_readme
    )
    for manuscript in (
        "erdos249-257-main-paper.tex",
        "claim-faithful-publication-systems-paper.tex",
    ):
        assert manuscript in paper_readme


def main() -> int:
    validate_guide(GUIDE.read_text(encoding="utf-8"))
    validate_systems_paper(SYSTEMS_PAPER.read_text(encoding="utf-8"))
    validate_entry_links(
        README.read_text(encoding="utf-8"),
        AGENTS.read_text(encoding="utf-8"),
        PAPER_README.read_text(encoding="utf-8"),
    )
    print("architecture guide: first-principles structure and entry links verified")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
