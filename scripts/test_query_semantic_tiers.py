#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0

from query_semantic import (
    is_authored_interpretation,
    is_structural_interpretation,
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


if __name__ == "__main__":
    tests = [
        value
        for name, value in sorted(globals().items())
        if name.startswith("test_") and callable(value)
    ]
    for test in tests:
        test()
    print(f"query semantic tier tests: {len(tests)} passed")
