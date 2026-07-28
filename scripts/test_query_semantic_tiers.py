#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0

from query_semantic import (
    PROBLEMS,
    is_authored_interpretation,
    is_structural_interpretation,
    problem_for_route,
    problem_scope_matches,
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
    assert PROBLEMS == ("243", "249", "251", "257", "269", "1049")


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


if __name__ == "__main__":
    tests = [
        value
        for name, value in sorted(globals().items())
        if name.startswith("test_") and callable(value)
    ]
    for test in tests:
        test()
    print(f"query semantic tier tests: {len(tests)} passed")
