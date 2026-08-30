#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0

import hashlib
import json
from copy import deepcopy
from functools import lru_cache
from unittest.mock import patch

import build_declaration_atlas
import query_semantic
from query_semantic import (
    BUDGET,
    PROBLEMS,
    StaleDeclarationAtlasError,
    build_family_relations_packet,
    cmd_family_relations,
    cmd_problem_registry,
    is_authored_interpretation,
    is_structural_interpretation,
    load_claims,
    load_palomar,
    main,
    encoded_json_bytes,
    problem_for_route,
    problem_scope_matches,
)


ATLAS_FIXTURE_FAMILY = "bounded_rise_coprimality"
ATLAS_FIXTURE_DECLARATION = (
    "ErdosProblems.Erdos243.no_eventuallyBoundedRise_reducedTail"
)
ATLAS_FIXTURE_ROW_ID = (
    "ErdosProblems/Erdos243/ReciprocalTailRigidity.lean:1060:"
    "no_eventuallyBoundedRise_reducedTail"
)
ATLAS_BACKED_FAMILY_COORDINATES = {
    "integral_shift_classification": (
        "ErdosProblems.Erdos251."
        "irrational_initial_iff_all_positive_tailShifts_nonintegral",
        "ErdosProblems/Erdos251/PrimeGapDyadicTail.lean",
        1551,
    ),
    "totient_certificate_equivalences": (
        "Erdos249257.TotientTailPeriodKiller."
        "irrational_totient_series_iff_lcm_diagonal_certificate_supply",
        "Erdos249257/LcmConeFlatness.lean",
        426,
    ),
    "factorial_channel_and_projection_rigidity": (
        "Erdos68.factorialMoment_eq_factorial_pow_mul_channelNumerator_band",
        "ErdosProblems/Erdos68/ChannelBreakpointRigidity.lean",
        71,
    ),
    "newton_value_decay": (
        "ErdosProblems.Erdos1041.newtonFlow_value_hasDerivAt",
        "ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean",
        50,
    ),
    "eventually_periodic_lambert": (
        "Erdos249257.irrational_ratWeightSeries_eventuallyPeriodic",
        "Erdos249257/CertificateKernel.lean",
        12811,
    ),
    "ray_separation": (
        "ErdosProblems.Erdos1041.no_newtonConnection_of_not_samePositiveRay",
        "ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean",
        315,
    ),
    "bounded_rise_coprimality": (
        "ErdosProblems.Erdos243.no_eventuallyBoundedRise_reducedTail",
        "ErdosProblems/Erdos243/ReciprocalTailRigidity.lean",
        1060,
    ),
    "height_fibre_and_shell": (
        "ErdosProblems.Erdos269.finiteSmoothKernelSum_groupedByHeight",
        "ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean",
        406,
    ),
    "totient_shift_propagation": (
        "ErdosProblems.Erdos251.tailShift_integral_totient_of_odd_den",
        "ErdosProblems/Erdos251/PrimeGapDyadicTail.lean",
        877,
    ),
    "totient_lambert_coefficients": (
        "MersenneLambertLadder.tsum_primWeight_div_two_pow_sub_one",
        "Erdos249257/MersenneLambertLadder.lean",
        601,
    ),
    "dyadic_block_alphabet": (
        "ErdosProblems.Erdos269.dyadicBlockBase235_cases",
        "ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean",
        699,
    ),
}


@lru_cache(maxsize=1)
def tracked_declaration_atlas() -> dict:
    return json.loads(
        query_semantic.DECLARATION_ATLAS.read_text(encoding="utf-8")
    )


@lru_cache(maxsize=1)
def atlas_fixture_rows() -> tuple[dict, dict]:
    tracked = tracked_declaration_atlas()
    selected = next(
        row
        for row in tracked["declarations"]
        if row["id"] == ATLAS_FIXTURE_ROW_ID
    )
    decoy = next(
        row
        for row in tracked["declarations"]
        if row["name"] != selected["name"]
    )
    return selected, decoy


def atlas_family_fixture() -> tuple[dict, dict, dict, str]:
    selected, decoy = atlas_fixture_rows()
    fingerprint = "sha256:" + "a" * 64
    atlas = {
        "source_fingerprint": fingerprint,
        "declarations": [dict(decoy), dict(selected)],
    }
    palomar = {
        "selection_contract": {
            "programme_family_order": [
                {"problem": 243, "family_ids": [ATLAS_FIXTURE_FAMILY]}
            ],
            "family_relations": [],
        },
        "candidate_ranking": [],
        "candidate_value_dispositions": {"source_landscape_candidates": []},
    }
    claims = {
        "external_verification_packet": {
            "review_matrix": [
                {
                    "problem": 1049,
                    "families": [
                        {
                            "id": "unrelated_fixture_family",
                            "summary": "unrelated",
                            "boundary": "unrelated boundary",
                            "contribution_class": "fixture",
                            "evidence_mode": "fixture",
                        }
                    ],
                },
                {
                    "problem": 243,
                    "families": [
                        {
                            "id": ATLAS_FIXTURE_FAMILY,
                            "summary": "bounded-rise obstruction",
                            "boundary": (
                                "The required bounded-rise input is not automatic "
                                "for the original sequence."
                            ),
                            "contribution_class": (
                                "locally proved result; novelty unassessed"
                            ),
                            "evidence_mode": "Lean kernel",
                            "declarations": [ATLAS_FIXTURE_DECLARATION],
                        }
                    ],
                },
            ]
        }
    }
    return palomar, claims, atlas, fingerprint


def build_tracked_atlas_family_packet(
    family_id: str,
    *,
    claims: dict | None = None,
) -> dict:
    """Freeze relation tests to one tracked atlas while verifying direct source."""
    atlas = tracked_declaration_atlas()
    with patch(
        "query_semantic.current_declaration_atlas_source_fingerprint",
        return_value=atlas["source_fingerprint"],
    ):
        return build_family_relations_packet(
            load_palomar(),
            claims if claims is not None else load_claims(),
            family_id,
            atlas=atlas,
        )


def test_authored_tier_is_not_inferred_from_statement_node_presence() -> None:
    structural = {
        "statement_node": "structural::abc",
        "interpretation_tier": "source_structural_family",
    }
    assert not is_authored_interpretation(structural)
    assert is_structural_interpretation(structural)


def test_authored_tier_is_explicit() -> None:
    authored = {
        "statement_node": "Z40::material_statement",
        "interpretation_tier": "authored_statement",
    }
    assert is_authored_interpretation(authored)
    assert not is_structural_interpretation(authored)


def test_zone_only_role_is_neither_interpretation_tier() -> None:
    role = {"zone": "Z40", "role": "substrate"}
    assert not is_authored_interpretation(role)
    assert not is_structural_interpretation(role)


def test_problem_registry_is_loaded_from_the_public_problem_index() -> None:
    assert PROBLEMS == ("68", "243", "249", "251", "257", "269", "1041", "1049")


def test_problem_registry_exposes_route_memory_resume_command() -> None:
    captured: dict = {}

    def capture(payload: object) -> int:
        captured["payload"] = payload
        return 0

    class Args:
        problem = None

    with patch("query_semantic.emit", side_effect=capture):
        result = cmd_problem_registry(
            {
                "declaration_roles": [],
                "zones": [],
                "statement_nodes": [],
                "summary": {"per_problem": {}},
            },
            Args(),
        )
    if result != 0:
        raise AssertionError(f"problem registry returned {result}")

    if "payload" not in captured:
        raise AssertionError("problem registry did not emit a packet")
    rows = captured["payload"]["problems"]
    if [row["erdos_number"] for row in rows] != [
        int(problem) for problem in PROBLEMS
    ]:
        raise AssertionError("problem registry selector coverage drifted")
    for row in rows:
        expected = (
            "python3 scripts/query_route_memory.py --problem "
            f"{row['erdos_number']}"
        )
        if row["follow"].get("route_memory") != expected:
            raise AssertionError("problem registry route-memory handoff drifted")


def test_historical_both_scope_does_not_leak_into_every_problem() -> None:
    assert problem_scope_matches("both", "249")
    assert problem_scope_matches("both", "257")
    assert not problem_scope_matches("both", "243")


def test_problem_route_prefers_authored_node_then_zone_then_exact_namespace() -> None:
    corpus = {
        "statement_nodes": [{"id": "Z90::node", "problem": "269"}],
        "zones": [{"zone_id": "Z91", "problem": "251"}],
    }
    assert problem_for_route(
        corpus,
        {
            "statement_node": "Z90::node",
            "zone": "Z91",
            "module": "ErdosProblems/Erdos243/Foo.lean",
        },
    ) == "243"
    assert problem_for_route(
        corpus,
        {
            "statement_node": "Z90::node",
            "zone": "Z91",
            "module": "Erdos249257/Foo.lean",
        },
    ) == "251"
    assert problem_for_route(
        corpus,
        {"statement_node": "Z90::node", "module": "Erdos249257/Foo.lean"},
    ) == "269"
    assert problem_for_route(
        corpus,
        {"module": "ErdosProblems/Erdos9999/Future.lean"},
    ) == "9999"


def test_palomar_relations_expose_249_peers_and_exact_boundaries() -> None:
    packet = build_tracked_atlas_family_packet(
        "first_harmonic_pivot_decomposition"
    )
    assert packet["family"]["source_route"] == "Erdos249257/FirstHarmonicPivot.lean"
    assert packet["family"]["source_declaration"] == (
        "Erdos249257.TotientTailPeriodKiller."
        "irrational_totient_series_of_pivotResidualDecorrelation"
    )
    assert "PivotBudgetAt" in packet["family"]["open_boundary"]
    stronger = [
        row
        for row in packet["relations"]
        if row["authority_rank_relation"] == "stronger_peer"
        if row["peer"]["family_id"] == "actual_lcm_orbit_separation"
    ]
    assert len(stronger) == 1
    assert stronger[0]["relation_class"] == "conditional_peer"
    assert stronger[0]["peer"]["source_route"] == (
        "Erdos249257/TotientActualLcmOrbitSeparation.lean"
    )
    assert "cofinal" in stronger[0]["peer"]["open_boundary"]
    actual_sources = {
        row["source_file"]: row
        for row in stronger[0]["peer"]["source_evidence"]
    }
    assert actual_sources[
        "Erdos249257/TotientActualLcmOrbitSeparation.lean"
    ]["source_anchor"] == "305"
    assert actual_sources[
        "Erdos249257/TotientActualLcmOrbitSign.lean"
    ]["source_anchor"] == "31-278"
    primary_index = stronger[0]["peer"]["primary_source_evidence_index"]
    assert stronger[0]["peer"]["source_evidence"][primary_index] == actual_sources[
        "Erdos249257/TotientActualLcmOrbitSeparation.lean"
    ]

    contrary = build_tracked_atlas_family_packet(
        "fixed_precision_transport_no_go"
    )
    weaker = [
        row
        for row in contrary["relations"]
        if row["authority_rank_relation"] == "weaker_peer"
        if row["peer"]["family_id"] == "actual_foreign_residue_projection"
    ]
    assert len(weaker) == 1
    assert weaker[0]["relation_class"] == "contrary_evidence"
    assert contrary["contrary_evidence_edges"] == [
        {
            "relation": "contrary_evidence_for",
            "relation_class": "contrary_evidence",
            "direction": "outgoing",
            "peer_family_id": "actual_foreign_residue_projection",
            "authority_rank_relation": "weaker_peer",
        }
    ]
    assert contrary["family"]["source_declaration"].endswith(
        "fixedPrecisionTropicalNoGo; "
        "Erdos249257.TotientTailPeriodKiller.vu_step_has_centred_completion; "
        "Erdos249257.TotientTailPeriodKiller.vu_word_has_prefix_locked_completion"
    )
    assert "finite-word" in contrary["family"]["open_boundary"]
    assert all(
        ";" not in command for command in contrary["follow"]["declarations"]
    )
    assert contrary["follow"]["problem_route"].endswith("erdos_249")


def test_support_relation_is_not_misclassified_as_prerequisite() -> None:
    packet = build_tracked_atlas_family_packet(
        "factorial_carry_characterisation"
    )
    support = next(
        row
        for row in packet["support_edges"]
        if row["peer_family_id"] == "factorial_channel_and_projection_rigidity"
    )
    assert support["relation"] == "supports_without_producing"
    assert support["relation_class"] == "support"
    assert packet["prerequisite_edges"] == []


def test_relation_only_metadata_fixture_remains_queryable_without_invented_rank() -> None:
    claims = deepcopy(load_claims())
    for block in claims["external_verification_packet"]["review_matrix"]:
        for family in block["families"]:
            if family["id"] == "totient_certificate_equivalences":
                family.pop("declarations", None)
    packet = build_tracked_atlas_family_packet(
        "totient_certificate_equivalences", claims=claims
    )
    assert packet["family"]["authority_rank"] == {
        "status": "relation_family_not_in_programme_family_order",
        "programme_position": None,
        "basis": (
            "docs/PALOMAR_RESULT_SHOWCASE.json::selection_contract."
            "programme_family_order"
        ),
    }
    assert packet["family"]["problem"] == 249
    assert packet["relations"][0]["peer"]["family_id"] == (
        "strict_prime_tail_orbit_gap"
    )
    assert packet["relations"][0]["authority_rank_relation"] == (
        "not_comparable_unranked_family"
    )
    assert packet["family"]["source_evidence_status"] == (
        "review_metadata_only_no_exact_source_coordinate"
    )
    assert "does not infer a source" in packet["family"][
        "source_authority_boundary"
    ]
    assert packet["family"]["mechanism_status"] == (
        "not_separately_authored_in_current_authority"
    )
    assert packet["follow"]["declarations"] == []


def test_claims_main_result_supplies_exact_source_when_palomar_has_no_source_row() -> None:
    packet = build_tracked_atlas_family_packet(
        "bounded_negative_exclusion"
    )
    family = packet["family"]
    assert family["source_evidence_status"] == "exact_claims_main_result_rows"
    assert family["source_route"] == (
        "ErdosProblems/Erdos243/ReciprocalTailRigidity.lean"
    )
    assert family["source_declaration"] == (
        "ErdosProblems.Erdos243."
        "no_cofinallyBoundedNegative_of_normalizedVanishes"
    )
    assert family["source_evidence"][0]["source_kind"] == "claims_main_result"
    assert family["source_evidence"][0]["hypothesis_projection_status"] == (
        "statement_and_declaration_only_no_separate_hypothesis_list"
    )
    assert family["source_evidence_authorities"] == [
        "docs/claims.json::external_verification_packet.main_results"
    ]
    assert packet["follow"]["declarations"] == sorted(
        packet["follow"]["declarations"]
    )
    assert any(
        command.endswith(
            "ErdosProblems.Erdos243."
            "no_cofinallyBoundedNegative_of_normalizedVanishes"
        )
        for command in packet["follow"]["declarations"]
    )


def test_claims_declaration_resolves_through_current_atlas_and_direct_source() -> None:
    palomar, claims, atlas, fingerprint = atlas_family_fixture()
    with patch(
        "query_semantic.current_declaration_atlas_source_fingerprint",
        return_value=fingerprint,
    ):
        packet = build_family_relations_packet(
            palomar,
            claims,
            ATLAS_FIXTURE_FAMILY,
            atlas=atlas,
        )
    family = packet["family"]
    assert family["source_evidence_status"] == (
        "exact_atlas_declaration_rows_direct_source_verified"
    )
    assert family["source_route"] == (
        "ErdosProblems/Erdos243/ReciprocalTailRigidity.lean"
    )
    assert family["source_anchor"] == "1060"
    assert family["source_declaration"] == ATLAS_FIXTURE_DECLARATION
    assert family["open_boundary"] in family["source_evidence"][0]["limitations"]
    evidence = family["source_evidence"][0]
    assert evidence["source_line"] == 1060
    assert evidence["candidate_id"] == f"atlas:{ATLAS_FIXTURE_ROW_ID}"
    assert evidence["source_kind"] == "claims_declaration_atlas_coordinate"
    assert evidence["atlas_provenance"]["atlas_row_id"] == ATLAS_FIXTURE_ROW_ID
    assert evidence["atlas_provenance"]["atlas_source_fingerprint"] == fingerprint
    assert evidence["atlas_provenance"]["direct_source_head_verified"] is True
    assert evidence["atlas_provenance"]["kind"] == "theorem"
    assert evidence["atlas_provenance"]["signature"].startswith(
        "theorem no_eventuallyBoundedRise_reducedTail"
    )
    assert evidence["atlas_provenance"]["direct_source_sha256"].startswith(
        "sha256:"
    )
    assert packet["follow"]["declarations"] == [
        "python3 scripts/query_corpus.py --declaration "
        + ATLAS_FIXTURE_DECLARATION
    ]
    assert encoded_json_bytes(packet) <= BUDGET


def test_atlas_and_claim_inventory_order_cannot_change_source_evidence() -> None:
    palomar, claims, atlas, fingerprint = atlas_family_fixture()
    reversed_atlas = deepcopy(atlas)
    reversed_atlas["declarations"].reverse()
    reversed_claims = deepcopy(claims)
    reversed_claims["external_verification_packet"]["review_matrix"].reverse()
    with patch(
        "query_semantic.current_declaration_atlas_source_fingerprint",
        return_value=fingerprint,
    ):
        normal = build_family_relations_packet(
            palomar, claims, ATLAS_FIXTURE_FAMILY, atlas=atlas
        )
        reversed_packet = build_family_relations_packet(
            palomar,
            reversed_claims,
            ATLAS_FIXTURE_FAMILY,
            atlas=reversed_atlas,
        )
    assert normal == reversed_packet


def test_stale_atlas_fingerprint_fails_before_emitting_source_evidence() -> None:
    palomar, claims, atlas, _ = atlas_family_fixture()
    current = "sha256:" + "b" * 64
    with patch(
        "query_semantic.current_declaration_atlas_source_fingerprint",
        return_value=current,
    ):
        try:
            build_family_relations_packet(
                palomar,
                claims,
                ATLAS_FIXTURE_FAMILY,
                atlas=atlas,
            )
        except StaleDeclarationAtlasError as error:
            assert error.tracked_fingerprint == atlas["source_fingerprint"]
            assert error.current_fingerprint == current
        else:
            raise AssertionError("stale declaration atlas was accepted")


def test_stale_atlas_coordinate_fails_direct_source_head_verification() -> None:
    palomar, claims, atlas, fingerprint = atlas_family_fixture()
    shifted = deepcopy(atlas)
    selected = next(
        row for row in shifted["declarations"]
        if row["id"] == ATLAS_FIXTURE_ROW_ID
    )
    selected["line"] += 1
    selected["id"] = (
        f"{selected['module']}:{selected['line']}:{selected['name']}"
    )
    with patch(
        "query_semantic.current_declaration_atlas_source_fingerprint",
        return_value=fingerprint,
    ):
        try:
            build_family_relations_packet(
                palomar,
                claims,
                ATLAS_FIXTURE_FAMILY,
                atlas=shifted,
            )
        except StaleDeclarationAtlasError as error:
            assert "direct Lean source" in str(error)
        else:
            raise AssertionError("stale declaration coordinate was accepted")


def test_tampered_atlas_row_fields_fail_direct_source_verification() -> None:
    palomar, claims, atlas, fingerprint = atlas_family_fixture()
    mutations = (
        ("id", "fabricated-row-id"),
        ("kind", "lemma"),
        ("module", "../outside.lean"),
        ("signature", "theorem no_eventuallyBoundedRise_reducedTail : True"),
    )
    for field, value in mutations:
        tampered = deepcopy(atlas)
        selected = next(
            row for row in tampered["declarations"]
            if row["id"] == ATLAS_FIXTURE_ROW_ID
        )
        selected[field] = value
        with patch(
            "query_semantic.current_declaration_atlas_source_fingerprint",
            return_value=fingerprint,
        ):
            try:
                build_family_relations_packet(
                    palomar,
                    claims,
                    ATLAS_FIXTURE_FAMILY,
                    atlas=tampered,
                )
            except StaleDeclarationAtlasError:
                pass
            else:
                raise AssertionError(f"tampered atlas {field} was accepted")


def test_family_relations_cli_reports_stale_atlas_without_partial_evidence() -> None:
    palomar, claims, atlas, _ = atlas_family_fixture()
    captured: dict = {}

    class Args:
        node_id = ATLAS_FIXTURE_FAMILY

    def capture(payload: object) -> int:
        captured["payload"] = payload
        return 0

    with (
        patch("query_semantic.load_palomar", return_value=palomar),
        patch("query_semantic.load_claims", return_value=claims),
        patch("query_semantic.load_declaration_atlas", return_value=atlas),
        patch(
            "query_semantic.current_declaration_atlas_source_fingerprint",
            return_value="sha256:" + "b" * 64,
        ),
        patch("query_semantic.emit", side_effect=capture),
    ):
        assert cmd_family_relations({}, Args()) == 0
    assert captured["payload"]["error"] == (
        "declaration_atlas_evidence_unavailable"
    )
    assert captured["payload"]["source_evidence_emitted"] is False
    assert "source_evidence" not in captured["payload"]
    assert captured["payload"]["tracked_source_fingerprint"] == (
        atlas["source_fingerprint"]
    )
    assert encoded_json_bytes(captured["payload"]) <= BUDGET
    assert all(
        key not in captured["payload"]
        for key in ("source_file", "source_line", "signature", "source_declaration")
    )


def test_existing_exact_family_does_not_duplicate_atlas_source_evidence() -> None:
    palomar = load_palomar()
    claims = load_claims()
    family_id = "strict_prime_tail_orbit_gap"
    claim_row = query_semantic._claims_family_rows(claims)[family_id]
    with patch(
        "query_semantic.load_declaration_atlas",
        side_effect=AssertionError("richer source evidence must stay preferred"),
    ):
        evidence = query_semantic._source_evidence_rows(
            palomar,
            claims,
            family_id,
            claim_row,
            {},
        )
    assert evidence
    assert all(
        row["source_kind"] != "claims_declaration_atlas_coordinate"
        for row in evidence
    )


def test_fast_source_fingerprint_uses_the_builder_framing() -> None:
    path = (
        query_semantic.ROOT
        / "ErdosProblems"
        / "Erdos243"
        / "ReciprocalTailRigidity.lean"
    )
    relative = path.relative_to(query_semantic.ROOT).as_posix()
    text = build_declaration_atlas.safe_atlas_text(path)
    digest = hashlib.sha256()
    digest.update(
        relative.encode("utf-8")
        + b"\0"
        + text.encode("utf-8")
        + b"\0"
    )
    assert build_declaration_atlas.source_fingerprint([path]) == (
        f"sha256:{digest.hexdigest()}"
    )


def test_all_eleven_canonical_backfills_keep_exact_principal_coordinates() -> None:
    palomar = load_palomar()
    claims = load_claims()
    claim_rows = query_semantic._claims_family_rows(claims)
    declaration_names = {
        declaration
        for family_id in ATLAS_BACKED_FAMILY_COORDINATES
        for declaration in claim_rows[family_id].get("declarations", [])
    }
    bare_names = {name.rsplit(".", 1)[-1] for name in declaration_names}
    atlas = {
        "source_fingerprint": "sha256:" + "c" * 64,
        "declarations": [
            row
            for row in tracked_declaration_atlas()["declarations"]
            if row["name"] in bare_names
        ],
    }
    with patch(
        "query_semantic.current_declaration_atlas_source_fingerprint",
        return_value=atlas["source_fingerprint"],
    ):
        for family_id, (
            declaration,
            source_file,
            source_line,
        ) in ATLAS_BACKED_FAMILY_COORDINATES.items():
            assert declaration in claim_rows[family_id].get("declarations", [])
            packet = build_family_relations_packet(
                palomar,
                claims,
                family_id,
                atlas=atlas,
            )
            family = packet["family"]
            assert family["source_evidence_status"] == (
                "exact_atlas_declaration_rows_direct_source_verified"
            )
            matching = [
                row
                for row in family["source_evidence"]
                if row["source_declaration"] == declaration
                and row["source_file"] == source_file
                and row["source_line"] == source_line
            ]
            assert len(matching) == 1
            assert family["open_boundary"] in matching[0]["limitations"]
            assert encoded_json_bytes(packet) <= BUDGET


def test_every_canonical_family_packet_is_bounded_and_boundary_honest() -> None:
    palomar = load_palomar()
    claims = load_claims()
    programme_ids = {
        str(family_id)
        for row in palomar["selection_contract"]["programme_family_order"]
        for family_id in row["family_ids"]
    }
    relation_ids = {
        str(family_id)
        for row in palomar["selection_contract"]["family_relations"]
        for family_id in (row["from_family_id"], row["to_family_id"])
    }
    for family_id in sorted(programme_ids | relation_ids):
        try:
            packet = build_family_relations_packet(palomar, claims, family_id)
        except StaleDeclarationAtlasError as error:
            failure = error.packet(family_id)
            assert failure["source_evidence_emitted"] is False
            assert encoded_json_bytes(failure) <= BUDGET
            continue
        family = packet["family"]
        assert family["open_boundary"]
        assert family["mechanism_status"] in {
            "authored_source_mechanism",
            "ranked_mechanism_judgement",
            "not_separately_authored_in_current_authority",
        }
        assert family["source_evidence_status"] in {
            "exact_palomar_source_rows",
            "exact_claims_main_result_rows",
            "exact_atlas_declaration_rows_direct_source_verified",
            "formal_declarations_only_no_exact_source_coordinate",
            "review_metadata_only_no_exact_source_coordinate",
        }
        if family["source_evidence"]:
            assert all(
                row["source_file"] or row["source_declaration"]
                for row in family["source_evidence"]
            )
        else:
            assert family["source_authority_boundary"]
        assert encoded_json_bytes(packet) <= BUDGET


def test_family_query_resolves_only_the_selected_relation_neighbourhood() -> None:
    palomar = load_palomar()
    claims = load_claims()
    family_id = "first_harmonic_pivot_decomposition"
    required = {family_id}
    for row in palomar["selection_contract"]["family_relations"]:
        endpoints = {str(row["from_family_id"]), str(row["to_family_id"])}
        if family_id in endpoints:
            required.update(endpoints)
    resolved: list[str] = []
    original = query_semantic._family_details

    def capture(key: str, *args, **kwargs) -> dict:
        resolved.append(key)
        return original(key, *args, **kwargs)

    atlas = tracked_declaration_atlas()
    with (
        patch("query_semantic._family_details", side_effect=capture),
        patch(
            "query_semantic.current_declaration_atlas_source_fingerprint",
            return_value=atlas["source_fingerprint"],
        ),
    ):
        build_family_relations_packet(
            palomar, claims, family_id, atlas=atlas
        )
    assert set(resolved) == required
    assert len(resolved) == len(required)


def test_family_relations_project_claim_status_without_inventing_a_rank() -> None:
    packet = build_tracked_atlas_family_packet(
        "conditional_carry_escape"
    )
    family = packet["family"]
    assert family["proof_status"] == (
        "conditional no-go consumer; novelty and significance unassessed"
    )
    assert family["proof_status_authority"].endswith(
        "families[].contribution_class"
    )
    weighted = next(
        row for row in packet["relations"]
        if row["peer"]["family_id"] == "weighted_phase_carry_observer"
    )
    assert weighted["peer"]["proof_status"] == (
        "locally proved result; novelty unassessed"
    )


def test_palomar_relation_and_detail_array_order_cannot_change_authority_rank() -> None:
    palomar = {
        "selection_contract": {
            "programme_family_order": [
                {
                    "problem": 249,
                    "family_ids": ["actual_lcm", "first_harmonic", "fixed", "foreign"],
                },
                {"problem": 257, "family_ids": ["cross_support"]},
            ],
            "family_relations": [
                {
                    "from_family_id": "first_harmonic",
                    "relation": "independent_conditional_endpoint_peer",
                    "to_family_id": "actual_lcm",
                    "reason": "independent endpoint consumers",
                },
                {
                    "from_family_id": "fixed",
                    "relation": "contrary_evidence_for",
                    "to_family_id": "foreign",
                    "reason": "fixed precision does not close global projection",
                },
                {
                    "from_family_id": "cross_support",
                    "relation": "supports_without_producing",
                    "to_family_id": "first_harmonic",
                    "reason": "cross-programme support does not define value order",
                },
            ],
        },
        "candidate_ranking": [
            {
                "rank": 2,
                "family_id": "first_harmonic",
                "declaration": "External.first_harmonic",
                "mechanism_depth_and_natural_friction": "ranked first harmonic mechanism",
            },
            {
                "rank": 1,
                "family_id": "actual_lcm",
                "declaration": "External.actual_lcm",
                "mechanism_depth_and_natural_friction": "ranked actual LCM mechanism",
            },
        ],
        "candidate_value_dispositions": {
            "source_landscape_candidates": [
                {
                    "family_id": "actual_lcm",
                    "candidate_id": "actual_lcm",
                    "comparator_declaration": "External.actual_lcm",
                    "source_declaration": "Source.actual_lcm",
                    "source_file": "Erdos249257/ActualLcm.lean",
                    "source_anchor": "42",
                    "hard_mechanism": "actual LCM mechanism",
                },
                {
                    "family_id": "actual_lcm",
                    "candidate_id": "actual_lcm_sign_support",
                    "source_declaration": "Source.actual_lcm_sign",
                    "source_file": "Erdos249257/ActualLcmSign.lean",
                    "source_anchor": "9-12",
                    "hard_mechanism": "actual LCM sign boundary",
                },
                {
                    "family_id": "first_harmonic",
                    "candidate_id": "first_harmonic",
                    "comparator_declaration": "External.first_harmonic",
                    "source_declaration": "Source.first_harmonic",
                    "source_file": "Erdos249257/FirstHarmonic.lean",
                    "source_anchor": "100",
                    "hard_mechanism": "first harmonic mechanism",
                },
                {
                    "family_id": "fixed",
                    "source_declaration": "Source.fixed",
                    "source_file": "Erdos249257/Fixed.lean",
                    "hard_mechanism": "fixed precision mechanism",
                },
                {
                    "family_id": "foreign",
                    "source_declaration": "Source.foreign",
                    "source_file": "Erdos249257/Foreign.lean",
                    "hard_mechanism": "foreign projection mechanism",
                },
                {
                    "family_id": "cross_support",
                    "source_declaration": "Source.cross_support",
                    "source_file": "Erdos249257/CrossSupport.lean",
                    "hard_mechanism": "cross-programme support mechanism",
                },
            ]
        },
    }
    claims = {
        "external_verification_packet": {
            "review_matrix": [
                {
                    "problem": 249,
                    "families": [
                        {
                            "id": family_id,
                            "summary": f"{family_id} summary",
                            "boundary": f"{family_id} boundary",
                            "contribution_class": f"{family_id} class",
                            "evidence_mode": "fixture",
                            "declarations": [f"Source.{family_id}"],
                        }
                        for family_id in ["actual_lcm", "first_harmonic", "fixed", "foreign"]
                    ]
                },
                {
                    "problem": 257,
                    "families": [
                        {
                            "id": "cross_support",
                            "summary": "cross summary",
                            "boundary": "cross boundary",
                            "contribution_class": "cross class",
                            "evidence_mode": "fixture",
                            "declarations": ["Source.cross_support"],
                        }
                    ],
                },
            ]
        }
    }
    reversed_source = deepcopy(palomar)
    reversed_source["selection_contract"]["programme_family_order"].reverse()
    reversed_source["selection_contract"]["family_relations"].reverse()
    reversed_source["candidate_ranking"].reverse()
    reversed_source["candidate_value_dispositions"][
        "source_landscape_candidates"
    ].reverse()
    reversed_claims = deepcopy(claims)
    reversed_claims["external_verification_packet"]["review_matrix"].reverse()
    for block in reversed_claims["external_verification_packet"]["review_matrix"]:
        block["families"].reverse()

    normal = build_family_relations_packet(palomar, claims, "first_harmonic")
    reversed_packet = build_family_relations_packet(
        reversed_source, reversed_claims, "first_harmonic"
    )
    assert normal == reversed_packet
    assert normal["family"]["authority_rank"]["programme_position"] == 2
    assert "global_position" not in normal["family"]["authority_rank"]
    assert normal["stronger_peers"][0]["peer_family_id"] == "actual_lcm"
    cross = next(
        row for row in normal["relations"]
        if row["peer"]["family_id"] == "cross_support"
    )
    assert cross["authority_rank_relation"] == "not_comparable_cross_programme"
    actual = next(
        row["peer"]
        for row in normal["relations"]
        if row["peer"]["family_id"] == "actual_lcm"
    )
    primary = actual["source_evidence"][actual["primary_source_evidence_index"]]
    assert primary["source_file"] == "Erdos249257/ActualLcm.lean"
    assert primary["source_anchor"] == "42"
    assert normal["family"]["presentation_disposition"] == reversed_packet[
        "family"
    ]["presentation_disposition"]


def test_family_relations_does_not_load_unrelated_semantic_corpus() -> None:
    palomar = {
        "selection_contract": {
            "programme_family_order": [
                {"problem": 249, "family_ids": ["solo"]}
            ],
            "family_relations": [],
        },
        "candidate_ranking": [],
        "candidate_value_dispositions": {
            "source_landscape_candidates": [
                {
                    "family_id": "solo",
                    "candidate_id": "solo",
                    "source_declaration": "Source.solo",
                    "source_file": "Erdos249257/Solo.lean",
                    "source_anchor": "1",
                }
            ]
        },
    }
    claims = {
        "external_verification_packet": {
            "review_matrix": [
                {
                    "problem": 249,
                    "families": [
                        {
                            "id": "solo",
                            "summary": "solo summary",
                            "boundary": "solo boundary",
                            "contribution_class": "fixture",
                            "evidence_mode": "fixture",
                            "declarations": ["Source.solo"],
                        }
                    ],
                }
            ]
        }
    }
    captured: dict = {}

    def capture(payload: object) -> int:
        captured["payload"] = payload
        return 0

    with (
        patch("sys.argv", ["query_semantic.py", "family-relations", "solo"]),
        patch("query_semantic.load", side_effect=AssertionError("must not load")),
        patch("query_semantic.load_palomar", return_value=palomar),
        patch("query_semantic.load_claims", return_value=claims),
        patch("query_semantic.emit", side_effect=capture),
    ):
        assert main() == 0
    assert captured["payload"]["family"]["family_id"] == "solo"


if __name__ == "__main__":
    tests = [
        value
        for name, value in sorted(globals().items())
        if name.startswith("test_") and callable(value)
    ]
    for test in tests:
        test()
    print(f"query semantic tier tests: {len(tests)} passed")
