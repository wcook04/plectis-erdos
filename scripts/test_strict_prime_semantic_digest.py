#!/usr/bin/env python3
"""Check that the strict-prime phase family exposes its source-current spine."""

from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ZONE = ROOT / "docs" / "semantic" / "zones" / "Z08.json"
FRONTIER = ROOT / "docs" / "semantic" / "frontier.json"
ATLAS = ROOT / "docs" / "declaration_atlas.json"
SOURCE = ROOT / "ErdosProblems" / "Erdos249" / "TotientStrictPrimeEscape.lean"
MODULE = "ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def load(path: Path) -> dict:
    with path.open(encoding="utf-8") as stream:
        value = json.load(stream)
    require(isinstance(value, dict), f"expected JSON object: {path}")
    return value


def test_phase_family_is_source_current() -> None:
    zone = load(ZONE)
    load(ATLAS)  # Validate the generated atlas while its owner refreshes coordinates.
    source_lines = SOURCE.read_text(encoding="utf-8").splitlines()
    source_by_name = {
        match.group(2): index
        for index, line in enumerate(source_lines, 1)
        if (match := re.match(r"\s*(def|lemma|theorem)\s+([A-Za-z0-9_]+)\b", line))
    }
    phase = next(
        (
            node
            for node in zone.get("statement_nodes", [])
            if isinstance(node, dict) and node.get("id") == "tail_orbit_initial_phase_normal_form"
        ),
        None,
    )
    barrier = next(
        (
            node
            for node in zone.get("statement_nodes", [])
            if isinstance(node, dict) and node.get("id") == "dyadic_root_blocks_strict_prime_gap"
        ),
        None,
    )
    strict = next(
        (
            node
            for node in zone.get("statement_nodes", [])
            if isinstance(node, dict) and node.get("id") == "strict_prime_escape_socket_implies_249"
        ),
        None,
    )
    require(phase is not None and barrier is not None and strict is not None, "Z08 lost strict-prime phase nodes")

    phase_names = {
        "tailOrbitFirstExp_add",
        "tailOrbitFirstExp_eq_initial_pow_two",
        "naturalPrimeTailOrbitStrictGap_iff_initial_phase",
        "tailOrbitFirstExp_zero_eq_scaled_angle",
        "tailOrbitFirstExp_eq_one_iff_tail_diff_mem_int",
        "cofinally_tailOrbitFirstExp_re_nonpos_of_not_dyadic",
        "TotientTailOrbitCofinalNonpositive",
        "totientTailOrbitCofinalNonpositive_of_irrational",
        "totientTailOrbitCofinalNonpositive_iff_irrational",
    }
    barrier_names = {
        "tailOrbitFirstExp_eq_one_of_le",
        "not_naturalPrimeTailOrbitStrictGap_of_phase_one",
        "not_naturalPrimeTailOrbitStrictGap_of_dyadic_root",
        "exists_tailOrbitFirstExp_zero_pow_two_eq_one_iff_dyadic",
        "tailOrbitFirstExp_zero_pow_two_ne_one_upto_sixteen",
    }
    strict_names = {"naturalPrimeTailOrbitStrictGap_of_cofinal_nonpositive_prime_shift"}

    def check_evidence(node: dict, names: set[str]) -> None:
        rows = {
            row.get("declaration"): row
            for row in node.get("evidence", [])
            if isinstance(row, dict)
        }
        require(names <= set(rows), f"Z08 omitted strict-prime declarations: {sorted(names - set(rows))}")
        for name in sorted(names):
            source_line = source_by_name.get(name)
            require(source_line is not None, f"source lost strict-prime declaration {name}")
            require(
                rows[name].get("module") == MODULE and rows[name].get("line") == source_line,
                f"stale strict-prime coordinate for {name}",
            )

    check_evidence(phase, phase_names)
    check_evidence(barrier, barrier_names)
    check_evidence(strict, strict_names)
    phase_statement = phase.get("canonical_statement", "")
    require("scaled angle" in phase_statement and "integral tail difference" in phase_statement, "phase boundary is incomplete")
    phase_caveat = phase.get("scope_caveat", "")
    require("conditional cofinal nonpositive-phase route" in phase_statement, "phase route boundary is missing")
    require("no real-part gap" in phase_caveat, "phase caveat overclaims a gap")


def test_frontier_names_prime_sampling_boundary() -> None:
    frontier = load(FRONTIER)
    row = next(
        (
            candidate
            for candidate in frontier.get("open_antecedents", [])
            if isinstance(candidate, dict) and candidate.get("id") == "OA249-prime-tail-orbit-escape"
        ),
        None,
    )
    require(row is not None, "frontier lost strict-prime escape row")
    names = {
        evidence.get("declaration")
        for evidence in row.get("mechanism_evidence", [])
        if isinstance(evidence, dict)
    }
    require(
        {
            "tailOrbitFirstExp_zero_eq_scaled_angle",
            "tailOrbitFirstExp_eq_one_iff_tail_diff_mem_int",
            "exists_tailOrbitFirstExp_zero_pow_two_eq_one_iff_dyadic",
            "tailOrbitFirstExp_zero_pow_two_ne_one_upto_sixteen",
            "cofinally_tailOrbitFirstExp_re_nonpos_of_not_dyadic",
            "naturalPrimeTailOrbitStrictGap_of_cofinal_nonpositive_prime_shift",
        }
        <= names,
        "frontier strict-prime mechanism spine is incomplete",
    )
    gap = row.get("gap", "")
    require("still unproduced" in gap and "prime alignment" in gap, "frontier erased strict-prime boundary")


if __name__ == "__main__":
    test_phase_family_is_source_current()
    test_frontier_names_prime_sampling_boundary()
    print("strict-prime semantic digest: ok")
