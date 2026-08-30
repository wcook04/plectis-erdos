#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check that the newcomer architecture guide stays concrete and jargon-free."""

from __future__ import annotations

import json
import os
import re
import stat
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
GUIDE = ROOT / "ARCHITECTURE.md"
README = ROOT / "README.md"
AGENTS = ROOT / "AGENTS.md"
PAPER_README = ROOT / "paper" / "README.md"
SYSTEMS_PAPER = ROOT / "paper" / "claim-faithful-publication-systems-paper.tex"
SYSTEMS_PDF = ROOT / "claim-faithful-publication-systems-paper.pdf"
PUBLICATION_CONTRACT = ROOT / "docs" / "publication_contract.json"
MAX_GUIDE_BYTES = 18_000
# Keep the architecture paper bounded without accumulating one-off magic-number
# raises.  Its legitimate explanatory load grows with the canonical publication
# inventory, whose exact membership is independently checked against the build
# and licence manifests.  A stable conceptual base plus a small per-artifact
# allowance therefore scales only when the governed public surface scales.
SYSTEMS_PAPER_BASE_BYTES = 45_000
SYSTEMS_PAPER_BYTES_PER_ARTIFACT = 1_000


class UnsafeArchitectureInput(ValueError):
    """An architecture-check input escaped the checkout or is not a file."""


def safe_architecture_text(path: Path, root: Path = ROOT) -> str:
    """Read one architecture input through a no-follow regular-file descriptor."""
    root = Path(os.path.abspath(root))
    candidate = Path(os.path.abspath(path))
    if candidate != root and root not in candidate.parents:
        raise UnsafeArchitectureInput(f"architecture input escaped checkout: {candidate}")
    current = candidate
    while True:
        if current.is_symlink():
            raise UnsafeArchitectureInput(f"symlinked architecture input: {candidate}")
        if current == root:
            break
        if current.parent == current:
            raise UnsafeArchitectureInput(f"architecture input escaped checkout: {candidate}")
        current = current.parent
    if not candidate.is_file():
        raise UnsafeArchitectureInput(
            f"architecture input is not a regular file: {candidate}"
        )

    flags = os.O_RDONLY | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_NOFOLLOW", 0)
    if hasattr(os, "O_CLOEXEC"):
        flags |= os.O_CLOEXEC
    try:
        descriptor = os.open(candidate, flags)
    except OSError as exc:
        raise UnsafeArchitectureInput(
            f"architecture input could not be opened safely: {candidate}"
        ) from exc
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise UnsafeArchitectureInput(
                f"architecture input is not a regular file: {candidate}"
            )
        chunks: list[bytes] = []
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
        try:
            return b"".join(chunks).decode("utf-8")
        except UnicodeDecodeError as exc:
            raise UnsafeArchitectureInput(
                f"architecture input is not UTF-8: {candidate}"
            ) from exc
    finally:
        os.close(descriptor)

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
        "eight unsolved problems in mathematics",
        "reviewed claim registry covers #249 and #257",
        "All eight mathematical problems remain open",
        "does not claim a solution to any of them",
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
    "paper_lifecycle_boundary": (
        "The eight individual problem papers are the active mathematical routes",
        "archived provenance only, not an active gateway",
        "The archived combined #249/#257 PDF is not a default reading route",
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
        "All eight problems remain open",
        "does not claim a solution to any of them",
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
        # The historical deposits were recorded at 28 breakpoints through
        # t = 64.  The current theorem covers every scale t <= 82, so pin the
        # public semantic boundary rather than a superseded deposit count.
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


def require(condition: bool, message: str) -> None:
    """Enforce a release check even when callers run Python with ``-O``."""
    if not condition:
        raise AssertionError(message)


def validate_guide(text: str) -> None:
    size = len(text.encode("utf-8"))
    require(size <= MAX_GUIDE_BYTES, (
        f"ARCHITECTURE.md is {size} bytes (budget {MAX_GUIDE_BYTES})"
    ))

    positions = [text.find(heading) for heading in SECTION_ORDER]
    require(all(position >= 0 for position in positions), (
        f"architecture guide lost section sequence {SECTION_ORDER}"
    ))
    require(positions == sorted(positions), "architecture guide sections are out of order")

    compact = normalise_tex(text)
    for group_id, anchors in REQUIRED_ANCHOR_GROUPS.items():
        for anchor in anchors:
            require(normalise(anchor).casefold() in compact.casefold(), (
                f"architecture guide lost {group_id} anchor {anchor!r}"
            ))

    for pattern in BANNED_SHORTHAND:
        require(not pattern.search(text), (
            f"architecture guide exposes private or evaluation shorthand {pattern.pattern!r}"
        ))

    for rel in REQUIRED_PATHS:
        require((ROOT / rel).exists(), f"architecture guide names missing path {rel}")
        require(rel in text, f"architecture guide no longer routes through {rel}")

    for target in re.findall(r"\[[^\]]+\]\(([^)]+)\)", text):
        if target.startswith(("http://", "https://", "#")):
            continue
        path = target.split("#", 1)[0]
        require((ROOT / path).exists(), f"architecture guide has broken local link {target}")


def validate_systems_paper(text: str) -> None:
    """Keep the PDF source architecture-first rather than experiment-first."""
    size = len(text.encode("utf-8"))
    contract = json.loads(safe_architecture_text(PUBLICATION_CONTRACT))
    artifact_count = len(contract["artifacts"])
    byte_budget = (
        SYSTEMS_PAPER_BASE_BYTES
        + SYSTEMS_PAPER_BYTES_PER_ARTIFACT * artifact_count
    )
    require(size <= byte_budget, (
        f"systems architecture paper is {size} bytes "
        f"(budget {byte_budget} for {artifact_count} governed artifacts)"
    ))

    require(
        "From Lean Proofs to Public Claims" in text
        and "Release checks and trust boundaries in one formal mathematics repository"
        in text
    , "systems paper lost its plain architecture title")

    positions = [text.find(heading) for heading in PAPER_SECTION_ORDER]
    require(all(position >= 0 for position in positions), (
        f"systems paper lost section sequence {PAPER_SECTION_ORDER}"
    ))
    require(positions == sorted(positions), "systems paper sections are out of order")

    compact = normalise_tex(text)
    for group_id, anchors in PAPER_REQUIRED_ANCHOR_GROUPS.items():
        for anchor in anchors:
            require(normalise(anchor).casefold() in compact.casefold(), (
                f"systems paper lost {group_id} anchor {anchor!r}"
            ))

    for pattern in BANNED_SHORTHAND:
        require(not pattern.search(text), (
            f"systems paper exposes private or score-like shorthand {pattern.pattern!r}"
        ))

    require(len(re.findall(r"\bsentence\b", text, flags=re.IGNORECASE)) <= 4, (
        "systems paper has drifted back to a sentence-centred case study"
    ))
    public_meaning = compact.find("public meaning, not its internal name")
    internal_id = compact.find("certified_kill_instances")
    require(0 <= public_meaning < internal_id, (
        "systems paper exposes its internal claim id before the public meaning"
    ))
    require(SYSTEMS_PDF.is_file(), "rendered systems architecture PDF is missing")


def validate_entry_links(readme: str, agents: str, paper_readme: str) -> None:
    readme_prefix = readme.encode("utf-8")[:6_000].decode("utf-8", errors="ignore")
    require("[architecture and repository guide](ARCHITECTURE.md)" in readme_prefix,
            "README lost the architecture guide entry link")
    require(
        "[printable PDF](claim-faithful-publication-systems-paper.pdf)"
        in readme_prefix
    , "README lost the printable architecture PDF entry link")
    require("It assumes no Lean or project history" in normalise(readme_prefix),
            "README lost the no-history architecture boundary")
    for phrase in (
        "conditional producer",
        "unbounded or cofinal supply",
        "lcm-diagonal scales",
        "producer carry",
    ):
        require(phrase not in readme_prefix.casefold(), (
            f"README first impression exposes unexplained phrase {phrase!r}"
        ))
    require("ARCHITECTURE.md" in agents, "AGENTS lost the architecture guide route")
    require("plain-language human guide" in agents,
            "AGENTS lost the plain-language architecture guide route")
    compact_paper_readme = normalise(paper_readme)
    require("[`ARCHITECTURE.md`](../ARCHITECTURE.md)" in paper_readme,
            "paper README lost the architecture guide route")
    require("authored papers with narrower jobs" in compact_paper_readme,
            "paper README lost the authored-paper boundary")
    require("architecture and access guide" in compact_paper_readme,
            "paper README lost the architecture role")
    require("historical checker example appears only after the architecture" in (
        compact_paper_readme
    ), "paper README moved the historical example ahead of architecture")
    for manuscript in (
        "erdos249-257-main-paper.tex",
        "claim-faithful-publication-systems-paper.tex",
    ):
        require(manuscript in paper_readme,
                f"paper README lost manuscript route {manuscript}")


def main() -> int:
    validate_guide(safe_architecture_text(GUIDE))
    validate_systems_paper(safe_architecture_text(SYSTEMS_PAPER))
    validate_entry_links(
        safe_architecture_text(README),
        safe_architecture_text(AGENTS),
        safe_architecture_text(PAPER_README),
    )
    print("architecture guide: first-principles structure and entry links verified")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
