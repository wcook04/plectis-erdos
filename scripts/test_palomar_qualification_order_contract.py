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


def source_claims() -> dict:
    return json.loads((ROOT / "docs/claims.json").read_text())


def programme_family_ids(showcase: dict, problem: int) -> list[str]:
    rows = [
        row
        for row in showcase["selection_contract"]["programme_family_order"]
        if row["problem"] == problem
    ]
    assert len(rows) == 1
    return rows[0]["family_ids"]


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


def test_totient_certificate_equivalences_are_deep_metadata_only() -> None:
    showcase = source_showcase()
    claims = source_claims()
    comparator = committed_comparator()
    family_id = "totient_certificate_equivalences"

    family_ids = programme_family_ids(showcase, 249)
    assert family_ids.count(family_id) == 1
    assert (
        family_ids.index("actual_lcm_orbit_separation")
        < family_ids.index("first_harmonic_pivot_decomposition")
        < family_ids.index("strict_prime_tail_orbit_gap")
        < family_ids.index(family_id)
        < family_ids.index("totient_kernel_rank")
        < family_ids.index("totient_carry_anti_compression")
    )

    placements = [
        row
        for row in showcase["selection_contract"]["represented_family_placements"]
        if row["family_id"] == family_id
    ]
    assert len(placements) == 1
    placement = placements[0]
    assert placement["tier_id"] == "deep_mechanism_and_classification"
    assert placement["evidence_status"] == (
        "claims_review_metadata_only_not_comparator_evidence"
    )
    assert "strict-prime producer routes" in placement["relative_judgement"]
    assert "three exact equivalences" in placement["relative_judgement"]
    assert all(
        token in placement["open_boundary"]
        for token in (
            "lcm-diagonal certificate supply",
            "period-multiple kill supply",
            "separated-window pair supply",
            "no unconditional Erdős #249 result",
        )
    )
    assert showcase["candidate_universe"]["source_family_dispositions"][family_id] == (
        "represented"
    )

    relations = [
        row
        for row in showcase["selection_contract"]["family_relations"]
        if row["from_family_id"] == family_id
        or row["to_family_id"] == family_id
    ]
    assert relations == [
        {
            "from_family_id": family_id,
            "relation": "endpoint_normal_form_support_for",
            "to_family_id": "strict_prime_tail_orbit_gap",
            "reason": (
                "Certificate completeness identifies the exact finite endpoint socket "
                "but cannot manufacture the strict-prime route's missing phase-density, "
                "cofinal-prime, or uniform-margin producer."
            ),
        }
    ]

    review_rows = [
        family
        for block in claims["external_verification_packet"]["review_matrix"]
        for family in block["families"]
        if family["id"] == family_id
    ]
    assert len(review_rows) == 1
    review = review_rows[0]
    assert review["evidence_mode"] == "Lean kernel"
    assert review["comparator_disposition"] == (
        "not_selected_deep_certificate_vocabulary"
    )
    assert review["boundary"] == (
        "Equivalent producer statements are as hard as the unresolved target."
    )
    assert len(review["declarations"]) == 3
    assert [row for row in claims["claims"] if row["id"] == family_id] == []
    assert all(
        declaration not in comparator["theorem_names"]
        for declaration in review["declarations"]
    )
    assert not any(
        row.get("family_id") == family_id
        for row in showcase["candidate_ranking"]
    )
    assert not any(
        row.get("family_id") == family_id
        for row in showcase["candidate_screening"]
    )
    assert not any(
        row.get("family_id") == family_id
        for row in showcase["candidate_value_dispositions"][
            "source_landscape_candidates"
        ]
    )

    strict_family_id = "strict_prime_tail_orbit_gap"
    assert family_ids.count(strict_family_id) == 1
    assert sum(
        row.get("family_id") == strict_family_id
        for row in showcase["candidate_ranking"]
    ) == 1
    assert sum(
        row.get("family_id") == strict_family_id
        for row in showcase["candidate_value_dispositions"][
            "source_landscape_candidates"
        ]
    ) == 1
    assert sum(row["id"] == strict_family_id for row in claims["claims"]) == 1
    assert sum(
        family["id"] == strict_family_id
        for block in claims["external_verification_packet"]["review_matrix"]
        for family in block["families"]
    ) == 1

    reordered = copy.deepcopy(showcase)
    reordered["source_authority"]["comparator_roster"].reverse()
    reordered["candidate_universe"]["source_review_family_ids"].reverse()
    reordered["candidate_universe"]["targeted_theorem_forest_discoveries"].reverse()
    reordered["selection_contract"]["family_relations"].reverse()
    reordered["selection_contract"]["represented_family_placements"].reverse()
    assert programme_family_ids(reordered, 249).index(family_id) == family_ids.index(
        family_id
    )


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
