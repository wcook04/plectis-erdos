#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0

from semantic_family_compiler import (
    compile_source_structural_families,
    normalized_proposition_signature,
    problem_for_module,
)


def row(
    name: str,
    signature: str,
    *,
    module: str = "ErdosProblems/Erdos1049/Foo.lean",
    line: int = 10,
    kind: str = "theorem",
    generated: bool = False,
    docstring: str | None = None,
) -> dict:
    return {
        "id": f"{module}:{line}:{name}",
        "name": name,
        "kind": kind,
        "module": module,
        "line": line,
        "signature": signature,
        "generated_certificate": generated,
        "docstring": docstring,
    }


def test_signature_normalization_removes_name_and_abstracts_numerals() -> None:
    left = normalized_proposition_signature(
        "private theorem prime_cell_101 : Nat.Prime 101"
    )
    right = normalized_proposition_signature(
        "private theorem prime_cell_103 : Nat.Prime 103"
    )
    assert left == right == ": Nat.Prime <num>"


def test_compiler_groups_only_inside_exact_module_and_signature_shape() -> None:
    rows = [
        row("prime_101", "theorem prime_101 : Nat.Prime 101", line=10),
        row("prime_103", "theorem prime_103 : Nat.Prime 103", line=11),
        row(
            "prime_101",
            "theorem prime_101 : Nat.Prime 101",
            module="ErdosProblems/Erdos1049/Other.lean",
            line=10,
        ),
        row("bound_101", "theorem bound_101 : 101 < 200", line=12),
    ]
    nodes, roles = compile_source_structural_families(rows, {})
    assert len(nodes) == 3
    assert len(roles) == 4
    assert sorted(node["member_count"] for node in nodes) == [1, 1, 2]
    assert all(role["statement_node"] for role in roles.values())
    assert all(
        set(evidence) == {"id", "resolved"}
        for node in nodes
        for evidence in node["evidence"]
    )


def test_existing_statement_nodes_win_and_definitions_are_not_promoted() -> None:
    theorem = row("proved", "theorem proved : True")
    definition = row("thing", "def thing : Nat", kind="def", line=11)
    existing = {
        theorem["id"]: {
            "statement_node": "Z99::reviewed",
            "role": "statement",
            "zone": "Z99",
        }
    }
    nodes, roles = compile_source_structural_families(
        [theorem, definition], existing, {theorem["id"]}
    )
    assert nodes == []
    assert roles == {}


def test_direct_evidence_without_a_role_is_not_duplicated_structurally() -> None:
    theorem = row("proved", "theorem proved : True")
    nodes, roles = compile_source_structural_families(
        [theorem], {}, {theorem["id"]}
    )
    assert nodes == []
    assert roles == {}


def test_contextual_authored_route_is_preserved_while_audit_evidence_closes() -> None:
    theorem = row("support", "theorem support : True")
    existing = {
        theorem["id"]: {
            "statement_node": "Z99::reviewed",
            "role": "substrate",
            "zone": "Z99",
        }
    }
    nodes, roles = compile_source_structural_families([theorem], existing)
    assert len(nodes) == 1
    assert nodes[0]["evidence"][0]["id"] == theorem["id"]
    assert roles == {}


def test_generated_declarations_remain_owned_by_generated_manifest() -> None:
    generated = row(
        "cert_7",
        "theorem cert_7 : Certified 7",
        generated=True,
    )
    nodes, roles = compile_source_structural_families([generated], {})
    assert nodes == []
    assert roles == {}


def test_single_source_docstring_is_preserved_without_name_inference() -> None:
    theorem = row(
        "corridor_no_go",
        "theorem corridor_no_go : ¬ Corridor 3 2",
        docstring="The coordinatewise corridor is impossible at base 3/2.",
    )
    nodes, roles = compile_source_structural_families([theorem], {})
    assert nodes[0]["canonical_statement"] == (
        "SOURCE-DOCUMENTED: "
        "The coordinatewise corridor is impossible at base 3/2."
    )
    assert nodes[0]["interpretation_tier"] == "source_structural_family"
    assert roles[theorem["id"]]["routing_origin"] == "source_structural_family"


def test_problem_inference_uses_explicit_namespace_only() -> None:
    assert problem_for_module("ErdosProblems/Erdos243/Tail.lean") == "243"
    assert problem_for_module("ErdosProblems/Erdos9999/Future.lean") == "9999"
    assert problem_for_module("Erdos249257/Shared.lean") == "shared_substrate"
    assert problem_for_module("Mathlib/Data/Nat/Foo.lean") == "shared_substrate"


if __name__ == "__main__":
    tests = [
        value
        for name, value in sorted(globals().items())
        if name.startswith("test_") and callable(value)
    ]
    for test in tests:
        test()
    print(f"semantic family compiler tests: {len(tests)} passed")
