#!/usr/bin/env python3
"""Assure the #1041 bounded-radius concyclic paper boundary."""

from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "paper" / "erdos-1041-lemniscate-newton-flow.tex"
PROOF = ROOT / "research_corpus" / "Erdos1041" / "ConcyclicAlternation.md"
EXACT_CHECK = (
    ROOT
    / "research_corpus"
    / "Erdos1041"
    / "scripts"
    / "check_erdos1041_concyclic_exact_witness.py"
)
NUMERICAL_CHECK = (
    ROOT
    / "research_corpus"
    / "Erdos1041"
    / "scripts"
    / "check_erdos1041_concyclic_alternation.py"
)
PIN = "f214a6b45528dc5eefe20ffadc35f2e981627d4c"


def test_public_corpus_keeps_the_proof_and_both_finite_checks() -> None:
    assert PROOF.is_file()
    assert EXACT_CHECK.is_file()
    assert NUMERICAL_CHECK.is_file()
    proof = PROOF.read_text(encoding="utf-8")
    for fragment in (
        "Theorem C (concyclic alternation)",
        "Lemma S: the chord never beats its own arc",
        "rho <= 2^{-1/n}",
        "Erdős #1041 itself remains open",
    ):
        assert fragment in proof


def test_individual_paper_exposes_the_result_without_formalising_it() -> None:
    paper = PAPER.read_text(encoding="utf-8")
    for fragment in (
        "A bounded-radius concyclic class",
        r"2\rho^n\le1",
        r"2\rho\sin(\pi/n)<2",
        "complete ordinary proof",
        "This is not a Lean theorem",
        "tests finitely many",
        "regression and stress-test evidence",
        "unrestricted concyclic case and Erd\\H{o}s~\\#1041 remain open",
    ):
        assert fragment in paper
    for source in (
        "ConcyclicAlternation.md",
        "check_erdos1041_concyclic_exact_witness.py",
        "check_erdos1041_concyclic_alternation.py",
    ):
        assert f"blob/{PIN}/research_corpus/Erdos1041/" in paper
        assert source in paper


if __name__ == "__main__":
    test_public_corpus_keeps_the_proof_and_both_finite_checks()
    test_individual_paper_exposes_the_result_without_formalising_it()
    print("concyclic alternation paper boundary: ok")
