#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Protect the thesis and evidence boundary of the agent-navigation paper."""

from __future__ import annotations

import hashlib
import os
import re
import stat
import sys
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
        "1,019 Lean modules and 153,253 declarations",
        "503 of those modules and 8,171 of those declarations are explicitly marked",
        "counted as formal source and never as separate mathematical claims",
        "Unresolved atlas rows and edge pairs are reported, never treated as independence",
        r"\SemanticAuthoredTheoremLike/\SemanticAuthoredTheoremLike",
        r"\SemanticAuthoredInterpreted\ authored interpretations",
        r"\SemanticDirectEvidence\ direct evidence",
        r"\SemanticContextual\ bounded family context",
        r"\SemanticStructuralOnly\ remain exact source-structural families only",
        "101 claims; 10 programmes; 5 open propositions",
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


class UnsafeAgentNavigationInput(ValueError):
    """An agent-navigation paper input is outside the regular checkout boundary."""


def require(condition: bool, message: str) -> None:
    """Keep the paper contract active when the checker runs with ``python -O``."""
    if not condition:
        raise AssertionError(message)


def _safe_navigation_path(path: Path) -> Path:
    """Reject checkout escapes and symbolic-link path components."""
    root = Path(os.path.abspath(ROOT))
    candidate = Path(os.path.abspath(path))
    current = candidate
    while True:
        if current.is_symlink():
            raise UnsafeAgentNavigationInput(
                f"symlinked agent-navigation input: {candidate}"
            )
        if current == root:
            break
        if current.parent == current:
            raise UnsafeAgentNavigationInput(
                f"agent-navigation input escaped checkout: {candidate}"
            )
        current = current.parent
    return candidate


def safe_read_bytes(path: Path) -> bytes:
    """Read a paper or PDF through a no-follow regular descriptor."""
    candidate = _safe_navigation_path(path)
    if not candidate.is_file():
        raise UnsafeAgentNavigationInput(
            f"agent-navigation input is not a regular file: {candidate}"
        )
    flags = os.O_RDONLY
    flags |= getattr(os, "O_CLOEXEC", 0)
    flags |= getattr(os, "O_NONBLOCK", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(candidate, flags)
    except OSError as exc:
        raise UnsafeAgentNavigationInput(
            f"agent-navigation input could not be opened safely: {candidate}"
        ) from exc
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise UnsafeAgentNavigationInput(
                f"agent-navigation input is not a regular file: {candidate}"
            )
        with os.fdopen(descriptor, "rb") as stream:
            descriptor = -1
            return stream.read()
    finally:
        if descriptor >= 0:
            os.close(descriptor)


def safe_read_text(path: Path) -> str:
    """Read a UTF-8 paper source through the regular-file boundary."""
    return safe_read_bytes(path).decode("utf-8")


def sha256(path: Path) -> str:
    return hashlib.sha256(safe_read_bytes(path)).hexdigest()


def main() -> int:
    try:
        source = safe_read_text(SOURCE)
        root_pdf_digest = sha256(ROOT_PDF)
    except UnsafeAgentNavigationInput as exc:
        print(f"unsafe agent-navigation input: {exc}", file=sys.stderr)
        return 1
    require(len(source.encode("utf-8")) <= MAX_SOURCE_BYTES, "agent-navigation source exceeds its size budget")
    positions = [source.find(section) for section in SECTION_ORDER]
    require(all(position >= 0 for position in positions), (
        f"agent-navigation paper lost section sequence {SECTION_ORDER}"
    ))
    require(positions == sorted(positions), (
        "agent-navigation paper sections are out of order"
    ))
    compact = normalise(source)
    for group_id, anchors in ANCHOR_GROUPS.items():
        for anchor in anchors:
            require(normalise(anchor).casefold() in compact.casefold(), (
                f"agent-navigation paper lost {group_id} anchor {anchor!r}"
            ))
    for pattern in BANNED:
        match = pattern.search(compact)
        require(match is None, (
            "agent-navigation paper exposes private or inflated shorthand "
            f"{match.group(0) if match else '<unknown>'!r}"
        ))
    # ``paper/*.pdf`` is deliberately ignored build output.  A fresh clone
    # therefore has the shipped root PDF but no paper-local copy until someone
    # runs the paper Makefile.  Compare the optional build product when it
    # exists without making it a cold-clone prerequisite.
    try:
        paper_local_digest = sha256(PAPER_PDF)
    except UnsafeAgentNavigationInput:
        paper_local_present = False
    else:
        paper_local_present = True
    if paper_local_present:
        require(paper_local_digest == root_pdf_digest, (
            "agent-navigation root and paper-local PDFs differ"
        ))
    print(
        "agent-navigation paper: thesis, evidence boundary, prior art, "
        "reproduction routes, and shipped PDF verified"
        + (" with paper-local build parity" if paper_local_present else "")
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
