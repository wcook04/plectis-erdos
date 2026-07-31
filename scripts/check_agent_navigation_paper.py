#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Protect the thesis and evidence boundary of the agent-navigation paper."""

from __future__ import annotations

import hashlib
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / "paper" / "cold-clone-to-proof-receipt.tex"
PAPER_PDF = ROOT / "paper" / "cold-clone-to-proof-receipt.pdf"
ROOT_PDF = ROOT / "cold-clone-to-proof-receipt.pdf"
MAX_SOURCE_BYTES = 55_000

SECTION_ORDER = (
    r"\section{The cold-clone problem}",
    r"\section{A layered mathematical option surface}",
    r"\section{A bounded tour over an unbounded drilldown}",
    r"\section{Crossing from navigation to authority}",
    r"\section{Compilation after comprehension}",
    r"\section{Dogfood receipt}",
    r"\section{Relation to prior work}",
    r"\section{Limits and transfer conditions}",
    r"\section{Authority-preserving agent entry}",
    r"\section{Reproduction routes}",
)

ANCHOR_GROUPS = {
    "scale_and_coverage": (
        "992 Lean modules and 151,761 declarations",
        "9,261 source-resolved nodes and 48,781 direct",
        r"\SemanticAuthoredTheoremLike/\SemanticAuthoredTheoremLike",
        r"\SemanticAuthoredInterpreted\ authored interpretations",
        r"\SemanticDirectEvidence\ direct evidence",
        r"\SemanticContextual\ bounded family context",
        r"\SemanticStructuralOnly\ remain exact source-structural families only",
        "100 claims; 10 programmes; 4 open propositions",
    ),
    "zero_build_tour": (
        "require no Lean build",
        "six-line card",
        "all-problem registry",
        "The route logic names no specimen theorem or module",
        "projection schemas",
        "--vocabulary",
        "executable Rosetta surface",
        "phrase luck",
    ),
    "authority_boundary": (
        "Navigation does not receive proof authority",
        "agent cannot type a verdict into the ledger",
        "claim must cite an accepted probe receipt",
        "Replay reruns every stored probe",
    ),
    "incremental_validation": (
        "modules changed since a Git reference",
        "26 modules in four waves",
        "exact receipt below the ignored Lake cache",
        "explicit full-check mode bypasses it",
        "does not claim that the environment export itself has become incremental",
    ),
    "dogfood_ceiling": (
        "six reasoning notes, one kernel-accepted probe, and two claims",
        "does not establish that the agent's route was optimal",
        "not subjective comprehension",
    ),
    "prior_art": (
        r"\cite{leanblueprint}",
        r"\cite{leanarchitect}",
        r"\cite{carleson}",
        r"\cite{leandojo,pantograph}",
        r"\cite{growingmathlib}",
        r"\cite{leanatlas}",
    ),
    "reproduction": (
        "query_corpus.py --tour --format card",
        "agent_native_corpus_navigation",
        "test_lean_dependency_index_cache.py",
        "build_lean_dependency_index.py --check --full-check",
    ),
}

BANNED = (
    re.compile(r"\b9/10\b"),
    re.compile(r"\b5,207\b"),
    re.compile(r"\bType A\b"),
    re.compile(r"\bType B\b"),
)


def normalise(text: str) -> str:
    for _ in range(3):
        text = re.sub(
            r"\\(?:textbf|emph|texttt|path)\{([^{}]*)\}",
            r"\1",
            text,
        )
    text = text.replace(r"\_", "_").replace("{", "").replace("}", "")
    return re.sub(r"\s+", " ", text)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    source = SOURCE.read_text(encoding="utf-8")
    assert len(source.encode("utf-8")) <= MAX_SOURCE_BYTES
    positions = [source.find(section) for section in SECTION_ORDER]
    assert all(position >= 0 for position in positions), (
        f"agent-navigation paper lost section sequence {SECTION_ORDER}"
    )
    assert positions == sorted(positions), (
        "agent-navigation paper sections are out of order"
    )
    compact = normalise(source)
    for group_id, anchors in ANCHOR_GROUPS.items():
        for anchor in anchors:
            assert normalise(anchor).casefold() in compact.casefold(), (
                f"agent-navigation paper lost {group_id} anchor {anchor!r}"
            )
    for pattern in BANNED:
        match = pattern.search(compact)
        assert match is None, (
            "agent-navigation paper exposes private or inflated shorthand "
            f"{match.group(0)!r}"
        )
    assert ROOT_PDF.is_file(), "root agent-navigation PDF is missing"
    # ``paper/*.pdf`` is deliberately ignored build output.  A fresh clone
    # therefore has the shipped root PDF but no paper-local copy until someone
    # runs the paper Makefile.  Compare the optional build product when it
    # exists without making it a cold-clone prerequisite.
    paper_local_present = PAPER_PDF.is_file()
    if paper_local_present:
        assert sha256(PAPER_PDF) == sha256(ROOT_PDF), (
            "agent-navigation root and paper-local PDFs differ"
        )
    print(
        "agent-navigation paper: thesis, evidence boundary, prior art, "
        "reproduction routes, and shipped PDF verified"
        + (" with paper-local build parity" if paper_local_present else "")
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
