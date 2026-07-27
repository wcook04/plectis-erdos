#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build the source-joined direct dependency index from the Lean environment."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any

import query_corpus


ROOT = Path(__file__).resolve().parent.parent
OUTPUT = ROOT / "docs" / "lean_dependency_index.json"
EXPORTER = ROOT / "scripts" / "export_lean_dependency_edges.lean"
SCHEMA = "erdos249257-lean-dependency-index/1"


def ensure_elaborated_environment() -> None:
    completed = subprocess.run(
        ["lake", "build", "Erdos249257"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if completed.returncode:
        sys.stderr.write(completed.stdout)
        raise RuntimeError(
            f"Lean root build exited {completed.returncode}"
        )


def module_id(path: str) -> str:
    return ".".join(Path(path).with_suffix("").parts)


def export_environment() -> tuple[
    dict[str, str],
    dict[tuple[str, str], set[str]],
    dict[str, int],
]:
    completed = subprocess.run(
        ["lake", "env", "lean", str(EXPORTER)],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode:
        sys.stderr.write(completed.stdout)
        sys.stderr.write(completed.stderr)
        raise RuntimeError(
            f"Lean dependency exporter exited {completed.returncode}"
        )
    return parse_environment_output(completed.stdout)


def parse_environment_output(
    output: str,
) -> tuple[
    dict[str, str],
    dict[tuple[str, str], set[str]],
    dict[str, int],
]:
    nodes: dict[str, str] = {}
    relations: dict[tuple[str, str], set[str]] = defaultdict(set)
    internal_omissions: dict[str, int] = {}
    for line in output.splitlines():
        fields = line.split("\t")
        if fields[0] == "AIW_NODE" and len(fields) == 3:
            _, handle, owner_module = fields
            nodes[handle] = owner_module
        elif fields[0] == "AIW_EDGE" and len(fields) == 6:
            _, source, source_module, target, target_module, relation = fields
            nodes.setdefault(source, source_module)
            nodes.setdefault(target, target_module)
            relations[(source, target)].add(relation)
        elif fields[0] == "AIW_INTERNAL_OMISSION" and len(fields) == 3:
            _, handle, count = fields
            internal_omissions[handle] = int(count)
        elif line.strip():
            raise RuntimeError(f"unexpected Lean exporter output: {line}")
    return nodes, relations, internal_omissions


def build_packet() -> dict[str, Any]:
    ensure_elaborated_environment()
    atlas = query_corpus.load("docs/declaration_atlas.json")
    claims = query_corpus.load("docs/claims.json")
    atlas_rows = [
        row
        for row in query_corpus.atlas_declarations(atlas)
        if query_corpus.declaration_externally_addressable(row)
    ]
    rows_by_environment_identity = {
        (
            query_corpus.qualified_declaration_name(row),
            module_id(row["module"]),
        ): row
        for row in atlas_rows
    }
    environment_nodes, environment_relations, internal_omissions = (
        export_environment()
    )
    resolved_rows = {
        handle: rows_by_environment_identity[(handle, owner_module)]
        for handle, owner_module in environment_nodes.items()
        if (handle, owner_module) in rows_by_environment_identity
    }
    resolved_relations: dict[tuple[str, str], set[str]] = {}
    unresolved_public_edge_count = 0
    for (source, target), relations in environment_relations.items():
        source_row = resolved_rows.get(source)
        target_row = resolved_rows.get(target)
        if source_row is None or target_row is None:
            unresolved_public_edge_count += 1
            continue
        resolved_relations[(source, target)] = relations
    direct_dependency_counts: dict[str, int] = defaultdict(int)
    for source, _ in resolved_relations:
        direct_dependency_counts[source] += 1
    nodes = []
    node_id_by_handle = {
        handle: node_id
        for node_id, handle in enumerate(sorted(resolved_rows))
    }
    for handle, row in sorted(resolved_rows.items()):
        nodes.append(
            {
                "node_id": node_id_by_handle[handle],
                "handle": handle,
                "name": row["name"],
                "declaration_kind": row["kind"],
                "module": row["module"],
                "line": row["line"],
                "source_ref": f"{row['module']}:{row['line']}",
                "direct_dependency_count": direct_dependency_counts[handle],
                "omitted_internal_reference_count": (
                    internal_omissions.get(handle, 0)
                ),
            }
        )
    relation_bits = {"type_reference": 1, "value_reference": 2}
    edges = [
        [
            node_id_by_handle[source],
            node_id_by_handle[target],
            sum(relation_bits[relation] for relation in relations),
        ]
        for (source, target), relations in sorted(
            resolved_relations.items()
        )
    ]
    formal_source = claims["release"]["formal_source"]
    unresolved_atlas_rows = []
    for row in atlas_rows:
        handle = query_corpus.qualified_declaration_name(row)
        atlas_module = module_id(row["module"])
        environment_module = environment_nodes.get(handle)
        if environment_module == atlas_module:
            continue
        unresolved_atlas_rows.append(
            {
                "handle": handle,
                "module": row["module"],
                "line": row["line"],
                "resolution_status": (
                    "loaded_constant_owned_by_different_module"
                    if environment_module is not None
                    else "not_present_in_loaded_root_environment"
                ),
                **(
                    {"environment_owner_module": environment_module}
                    if environment_module is not None
                    else {}
                ),
            }
        )
    unresolved_atlas_status_counts = dict(
        sorted(
            (
                status,
                sum(
                    row["resolution_status"] == status
                    for row in unresolved_atlas_rows
                ),
            )
            for status in {
                row["resolution_status"] for row in unresolved_atlas_rows
            }
        )
    )
    return {
        "schema_version": SCHEMA,
        "kind": "lean_dependency_index",
        "authority_posture": (
            "direct_constant_references_from_elaborated_Lean_types_and_values_"
            "joined_to_source_coordinates_not_a_transitive_proof_explanation"
        ),
        "source_fingerprint": atlas["source_fingerprint"],
        "formal_source": formal_source,
        "environment_validation": {
            "command": "lake build Erdos249257",
            "posture": (
                "incremental_root_build_precedes_environment_export_so_"
                "source_fingerprint_and_loaded_olean_state_are_current"
            ),
        },
        "operational_posture": (
            "offline_full_environment_build_artifact_not_query_time_work"
        ),
        "coverage": {
            "effective_atlas_declaration_count": len(
                query_corpus.atlas_declarations(atlas)
            ),
            "externally_addressable_atlas_declaration_count": len(atlas_rows),
            "environment_public_corpus_constant_count": len(environment_nodes),
            "source_resolved_node_count": len(nodes),
            "environment_direct_reference_pair_count": len(
                environment_relations
            ),
            "source_resolved_direct_edge_count": len(edges),
            "unresolved_public_edge_count": unresolved_public_edge_count,
            "omitted_internal_reference_count": sum(
                internal_omissions.values()
            ),
            "unresolved_atlas_declaration_count": len(unresolved_atlas_rows),
            "unresolved_atlas_declaration_status_counts": (
                unresolved_atlas_status_counts
            ),
        },
        "unresolved_atlas_declarations": unresolved_atlas_rows,
        "edge_relation_bit_legend": {
            "1": "type_reference",
            "2": "value_reference",
        },
        "nodes": nodes,
        "edges": edges,
        "validation": "python3 scripts/build_lean_dependency_index.py --check",
    }


def encoded(packet: dict[str, Any]) -> str:
    return json.dumps(
        packet,
        ensure_ascii=False,
        separators=(",", ":"),
    ) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    packet = build_packet()
    content = encoded(packet)
    if args.check:
        if not OUTPUT.is_file() or OUTPUT.read_text(encoding="utf-8") != content:
            print(f"stale Lean dependency index: {OUTPUT}", file=sys.stderr)
            return 1
        print(
            "Lean dependency index: PASS "
            f"({packet['coverage']['source_resolved_node_count']} nodes, "
            f"{packet['coverage']['source_resolved_direct_edge_count']} edges)"
        )
        return 0
    OUTPUT.write_text(content, encoding="utf-8")
    print(
        f"wrote {OUTPUT} "
        f"({packet['coverage']['source_resolved_node_count']} nodes, "
        f"{packet['coverage']['source_resolved_direct_edge_count']} edges)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
