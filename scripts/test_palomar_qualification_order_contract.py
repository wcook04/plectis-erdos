#!/usr/bin/env python3
"""Order-neutral source-current contracts for Palomar qualification."""

from __future__ import annotations

import copy
import json
import subprocess
from pathlib import Path

import check_palomar_qualification as checker


ROOT = Path(__file__).resolve().parents[1]


def committed_comparator() -> dict:
    return json.loads(
        subprocess.check_output(
            ["git", "show", "HEAD:verification/comparator.json"], cwd=ROOT
        )
    )


def source_showcase() -> dict:
    return json.loads((ROOT / "docs/PALOMAR_RESULT_SHOWCASE.json").read_text())


def source_reconciliation() -> dict:
    return json.loads((ROOT / "docs/PALOMAR_POLICY_RECONCILIATION.json").read_text())


def test_reversed_source_arrays_preserve_identity_contracts() -> None:
    comparator = committed_comparator()
    showcase = source_showcase()
    reconciliation = source_reconciliation()
    assert checker.roster_errors(ROOT, comparator, showcase, reconciliation) == []
    assert checker.candidate_selection_errors(comparator, showcase, ROOT) == []

    reversed_showcase = copy.deepcopy(showcase)
    reversed_showcase["source_authority"]["comparator_roster"].reverse()
    reversed_showcase["frontier_by_problem"].reverse()
    reversed_showcase["candidate_universe"]["declarations"].reverse()
    reversed_showcase["candidate_universe"]["source_review_family_ids"].reverse()
    reversed_showcase["candidate_universe"]["targeted_theorem_forest_discoveries"].reverse()
    reversed_showcase["candidate_value_dispositions"]["eligible_groups"].reverse()
    reversed_showcase["candidate_value_dispositions"]["source_landscape_candidates"].reverse()
    reversed_showcase["candidate_ranking"].reverse()
    reversed_showcase["candidate_screening"].reverse()

    assert checker.roster_errors(ROOT, comparator, reversed_showcase, reconciliation) == []
    assert checker.candidate_selection_errors(comparator, reversed_showcase, ROOT) == []


def test_identity_boundary_and_uniqueness_fail_closed() -> None:
    comparator = committed_comparator()
    showcase = source_showcase()
    reconciliation = source_reconciliation()

    duplicated = copy.deepcopy(showcase)
    duplicated["source_authority"]["comparator_roster"].append(
        duplicated["source_authority"]["comparator_roster"][0]
    )
    assert any(
        "authority roster contains duplicate" in error
        for error in checker.roster_errors(ROOT, comparator, duplicated, reconciliation)
    )

    unbound = copy.deepcopy(showcase)
    unbound["candidate_universe"]["targeted_theorem_forest_discoveries"][0][
        "source_landscape_record"
    ] = "candidate_value_dispositions.source_landscape_candidates[unbound]"
    assert any(
        "wrong source-landscape record" in error
        for error in checker.candidate_selection_errors(comparator, unbound, ROOT)
    )

    boundaryless = copy.deepcopy(showcase)
    boundaryless["candidate_selection"]["open_boundary"] = ""
    assert any(
        "selected candidate lacks exact open_boundary" in error
        for error in checker.candidate_selection_errors(comparator, boundaryless, ROOT)
    )
