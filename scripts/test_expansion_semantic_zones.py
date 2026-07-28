#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0

from build_expansion_semantic_zones import role_for_row


def spec() -> dict:
    return {
        "contextual_routes": [
            {
                "modules": {"ErdosProblems/FreePosition/Selected.lean"},
                "target": "free_position_finite_certificates",
                "basis": "digest-bound historical roster membership",
            },
            {
                "modules": {"ErdosProblems/FreePosition/Later.lean"},
                "target": "free_position_later_verified_certificates",
                "basis": "digest-bound later-census membership",
            },
        ],
        "role_prefix": (
            "freeKill",
            "finite_instance",
            "free_position_finite_certificates",
        ),
    }


def test_roster_module_gets_bounded_contextual_route() -> None:
    helper = {
        "name": "prime_selected_101",
        "module": "ErdosProblems/FreePosition/Selected.lean",
        "line": 10,
    }
    role = role_for_row(spec(), helper, {})
    assert role["role"] == "substrate"
    assert role["statement_node"] == "free_position_finite_certificates"
    assert role["routing_origin"] == "authored_contextual_certificate_substrate"
    assert role["routing_basis_ref"] == "free_position_finite_certificates"


def test_later_module_routes_to_separate_census_node() -> None:
    later_helper = {
        "name": "prime_later_103",
        "module": "ErdosProblems/FreePosition/Later.lean",
        "line": 11,
    }
    role = role_for_row(spec(), later_helper, {})
    assert role["statement_node"] == "free_position_later_verified_certificates"
    assert (
        role["routing_basis_ref"]
        == "free_position_later_verified_certificates"
    )


def test_unbound_module_stays_outside_both_nodes() -> None:
    unbound_helper = {
        "name": "prime_unbound_107",
        "module": "ErdosProblems/FreePosition/Unbound.lean",
        "line": 12,
    }
    role = role_for_row(spec(), unbound_helper, {})
    assert role == {
        "declaration": "prime_unbound_107",
        "module": "ErdosProblems/FreePosition/Unbound.lean",
        "line": 12,
        "role": "substrate",
    }


def test_public_certificate_prefix_retains_finite_instance_role() -> None:
    certificate = {
        "name": "freeKill_selected",
        "module": "ErdosProblems/FreePosition/Selected.lean",
        "line": 100,
    }
    role = role_for_row(spec(), certificate, {})
    assert role["role"] == "finite_instance"
    assert role["statement_node"] == "free_position_finite_certificates"


def test_promoted_direct_evidence_wins_over_contextual_module_route() -> None:
    promoted = {
        (
            "ErdosProblems/FreePosition/Selected.lean",
            "freeKill_selected",
        ): "specific_certificate_statement",
    }
    certificate = {
        "name": "freeKill_selected",
        "module": "ErdosProblems/FreePosition/Selected.lean",
        "line": 100,
    }
    role = role_for_row(spec(), certificate, promoted)
    assert role["role"] == "finite_instance"
    assert role["statement_node"] == "specific_certificate_statement"
    assert "routing_origin" not in role
    assert "routing_basis_ref" not in role


if __name__ == "__main__":
    tests = [
        value
        for name, value in sorted(globals().items())
        if name.startswith("test_") and callable(value)
    ]
    for test in tests:
        test()
    print(f"expansion semantic zone tests: {len(tests)} passed")
