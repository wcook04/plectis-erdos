#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build the source-joined direct dependency index from the Lean environment."""

from __future__ import annotations

import argparse
import hashlib
import inspect
import json
import os
import subprocess
import stat
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any

import query_corpus
import validation_singleflight as singleflight


ROOT = Path(__file__).resolve().parent.parent
OUTPUT = ROOT / "docs" / "lean_dependency_index.json"
EXPORTER = ROOT / "scripts" / "export_lean_dependency_edges.lean"
SCHEMA = "erdos249257-lean-dependency-index/3"
LEAN_ROOT_TARGETS = ("Erdos249257", "ErdosProblems")
LEAN_FAST_BUILD = ROOT / "scripts" / "lean_fast_build.py"
CHECK_RECEIPT = ROOT / ".lake" / "aiw" / "lean_dependency_index_check.json"
CHECK_RECEIPT_SCHEMA = "erdos249257-lean-dependency-index-check/1"
ENVIRONMENT_CONTRACT = "clean_committed_snapshot_subprocess_environment_v1"
# The global single-flight environment deliberately strips ambient PATH.  The
# documented elan install is the one deterministic toolchain location that
# this builder must add back before launching Lake or Lean.
TOOLCHAIN_BIN = Path.home() / ".elan" / "bin"
CHECK_INPUT_FILES = (
    "docs/declaration_atlas.json",
    "docs/generated_certificate_manifest.json",
    "lake-manifest.json",
    "lakefile.toml",
    "lean-toolchain",
    "scripts/build_declaration_atlas.py",
    "scripts/build_lean_dependency_index.py",
    "scripts/export_lean_dependency_edges.lean",
    "scripts/lean_fast_build.py",
)
QUERY_CORPUS_DEPENDENCY_HELPERS = (
    "atlas_declarations",
    "declaration_externally_addressable",
    "lean_code_projection",
    "module_namespace_events",
    "qualified_declaration_name",
)


class UnsafeDependencyInput(ValueError):
    """A dependency-index input is outside its root or is not a regular file."""


def safe_dependency_path(path: Path, root: Path | None = ROOT) -> Path:
    """Resolve a dependency input without following checkout symlinks."""
    candidate = Path(os.path.abspath(path))
    if root is not None:
        root = Path(os.path.abspath(root))
        if candidate != root and root not in candidate.parents:
            raise UnsafeDependencyInput(f"dependency input escaped checkout: {candidate}")
        current = candidate
        while True:
            if current.is_symlink():
                raise UnsafeDependencyInput(f"symlinked dependency input: {candidate}")
            if current == root:
                break
            if current.parent == current:
                raise UnsafeDependencyInput(f"dependency input escaped checkout: {candidate}")
            current = current.parent
    if not candidate.is_file():
        raise UnsafeDependencyInput(
            f"dependency input is not a regular file: {candidate}"
        )
    return candidate


def safe_dependency_bytes(path: Path, root: Path | None = ROOT) -> bytes:
    """Read a dependency input through a no-follow regular-file descriptor."""
    candidate = safe_dependency_path(path, root=root)
    flags = os.O_RDONLY | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_NOFOLLOW", 0)
    if hasattr(os, "O_CLOEXEC"):
        flags |= os.O_CLOEXEC
    try:
        descriptor = os.open(candidate, flags)
    except OSError as exc:
        raise UnsafeDependencyInput(
            f"dependency input could not be opened safely: {candidate}"
        ) from exc
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise UnsafeDependencyInput(
                f"dependency input is not a regular file: {candidate}"
            )
        chunks: list[bytes] = []
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                return b"".join(chunks)
            chunks.append(chunk)
    finally:
        os.close(descriptor)


def safe_dependency_text(path: Path, root: Path | None = ROOT) -> str:
    """Decode one dependency input read through its safe descriptor."""
    candidate = Path(os.path.abspath(path))
    try:
        return safe_dependency_bytes(path, root=root).decode("utf-8")
    except UnicodeDecodeError as exc:
        raise UnsafeDependencyInput(
            f"dependency input is not UTF-8: {candidate}"
        ) from exc


def run(*args: Any, **kwargs: Any) -> subprocess.CompletedProcess[str]:
    """Run dependency-bootstrap commands without ambient state or hangs."""
    environment = singleflight.command_environment()
    environment["PATH"] = os.pathsep.join((str(TOOLCHAIN_BIN), environment["PATH"]))
    kwargs["env"] = environment
    kwargs.setdefault("timeout", singleflight.GIT_COMMAND_TIMEOUT_SECONDS)
    return subprocess.run(*args, **kwargs)


def sha256_text(content: str) -> str:
    return f"sha256:{hashlib.sha256(content.encode('utf-8')).hexdigest()}"


def check_input_paths(root: Path = ROOT) -> list[Path]:
    """Return every source that can change the elaborated dependency packet."""
    paths = [root / relative for relative in CHECK_INPUT_FILES]
    for library_root in LEAN_ROOT_TARGETS:
        paths.append(root / f"{library_root}.lean")
        paths.extend(sorted((root / library_root).rglob("*.lean")))
    return sorted(set(paths))


def semantic_check_inputs(root: Path = ROOT) -> list[tuple[str, bytes]]:
    """Project large shared owners to the exact values this builder consumes."""
    claims = json.loads(
        safe_dependency_text(root / "docs" / "claims.json", root=root)
    )
    formal_source = json.dumps(
        claims["release"]["formal_source"],
        ensure_ascii=False,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")
    helper_sources = "\n\n".join(
        inspect.getsource(getattr(query_corpus, name))
        for name in QUERY_CORPUS_DEPENDENCY_HELPERS
    )
    suppressed_rows = json.dumps(
        sorted(query_corpus.SUPPRESSED_DECLARATION_ATLAS_ROWS),
        ensure_ascii=False,
        separators=(",", ":"),
    )
    return [
        ("docs/claims.json::release.formal_source", formal_source),
        (
            "scripts/query_corpus.py::dependency_helpers",
            f"{helper_sources}\n{suppressed_rows}\n".encode("utf-8"),
        ),
    ]


def check_input_fingerprint(root: Path = ROOT) -> str:
    """Hash path identities and bytes, including the complete supported roots."""
    digest = hashlib.sha256()
    for path in check_input_paths(root):
        if not path.is_file():
            raise RuntimeError(
                f"Lean dependency verification input is missing: {path}"
            )
        relative = path.relative_to(root).as_posix()
        digest.update(relative.encode("utf-8"))
        digest.update(b"\0")
        digest.update(safe_dependency_bytes(path, root=root))
        digest.update(b"\0")
    for identity, payload in semantic_check_inputs(root):
        digest.update(identity.encode("utf-8"))
        digest.update(b"\0")
        digest.update(payload)
        digest.update(b"\0")
    return f"sha256:{digest.hexdigest()}"


def receipt_matches(
    receipt: dict[str, Any],
    *,
    input_fingerprint: str,
    output_digest: str,
) -> bool:
    return (
        receipt.get("schema") == CHECK_RECEIPT_SCHEMA
        and receipt.get("builder_schema") == SCHEMA
        and receipt.get("input_fingerprint") == input_fingerprint
        and receipt.get("output_digest") == output_digest
    )


def load_cached_check(
    *,
    root: Path = ROOT,
    output: Path = OUTPUT,
    receipt_path: Path = CHECK_RECEIPT,
) -> dict[str, Any] | None:
    """Return a receipt only when the verified inputs and output are exact."""
    if not output.is_file() or not receipt_path.is_file():
        return None
    try:
        receipt = json.loads(safe_dependency_text(receipt_path, root=None))
    except (json.JSONDecodeError, OSError):
        return None
    content = safe_dependency_text(output, root=None)
    if not receipt_matches(
        receipt,
        input_fingerprint=check_input_fingerprint(root),
        output_digest=sha256_text(content),
    ):
        return None
    return receipt


def write_check_receipt(
    content: str,
    packet: dict[str, Any],
    *,
    input_fingerprint: str,
    root: Path = ROOT,
    receipt_path: Path = CHECK_RECEIPT,
) -> None:
    coverage = packet["coverage"]
    receipt = {
        "schema": CHECK_RECEIPT_SCHEMA,
        "builder_schema": SCHEMA,
        "input_fingerprint": input_fingerprint,
        "output_digest": sha256_text(content),
        "source_fingerprint": packet["source_fingerprint"],
        "source_resolved_node_count": coverage[
            "source_resolved_node_count"
        ],
        "source_resolved_direct_edge_count": coverage[
            "source_resolved_direct_edge_count"
        ],
        "verification_posture": (
            "full_supported_root_build_and_elaborated_environment_export_"
            "matched_the_committed_index"
        ),
    }
    receipt_path.parent.mkdir(parents=True, exist_ok=True)
    temporary = receipt_path.with_suffix(".tmp")
    temporary.write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(receipt_path)


def ensure_elaborated_environment() -> None:
    completed = run(
        [
            sys.executable,
            str(LEAN_FAST_BUILD),
            "--lake-staleness",
            *LEAN_ROOT_TARGETS,
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if completed.returncode:
        sys.stderr.write(completed.stdout)
        raise RuntimeError(
            f"bounded Lean root build exited {completed.returncode}"
        )


def module_id(path: str) -> str:
    return ".".join(Path(path).with_suffix("").parts)


def export_environment() -> tuple[
    dict[str, str],
    dict[tuple[str, str], set[str]],
    dict[str, int],
    dict[str, dict[str, Any]],
]:
    completed = run(
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
    dict[str, dict[str, Any]],
]:
    nodes: dict[str, str] = {}
    relations: dict[tuple[str, str], set[str]] = defaultdict(set)
    internal_omissions: dict[str, int] = {}
    type_shapes: dict[str, dict[str, Any]] = {}
    for line in output.splitlines():
        fields = line.split("\t")
        if fields[0] == "AIW_NODE" and len(fields) == 3:
            _, handle, owner_module = fields
            nodes[handle] = owner_module
        elif fields[0] == "AIW_TYPE_SHAPE" and len(fields) == 4:
            _, handle, binder_count, conclusion_head = fields
            type_shapes.setdefault(
                handle,
                {"conclusion_symbols": set(), "binders": {}},
            ).update(
                {
                    "binder_count": int(binder_count),
                    "conclusion_head": conclusion_head,
                }
            )
        elif fields[0] == "AIW_BINDER_SHAPE" and len(fields) == 7:
            (
                _,
                handle,
                binder_index,
                binder_name,
                binder_info,
                is_proposition,
                type_head,
            ) = fields
            type_shapes.setdefault(
                handle,
                {"conclusion_symbols": set(), "binders": {}},
            )["binders"][int(binder_index)] = {
                "name": binder_name,
                "binder_info": binder_info,
                "is_proposition": is_proposition == "true",
                "type_head": type_head,
                "type_symbols": set(),
            }
        elif fields[0] == "AIW_BINDER_REF" and len(fields) == 4:
            _, handle, binder_index, reference = fields
            shape = type_shapes.setdefault(
                handle,
                {"conclusion_symbols": set(), "binders": {}},
            )
            binder = shape["binders"].setdefault(
                int(binder_index),
                {"type_symbols": set()},
            )
            binder["type_symbols"].add(reference)
        elif fields[0] == "AIW_CONCLUSION_REF" and len(fields) == 3:
            _, handle, reference = fields
            type_shapes.setdefault(
                handle,
                {"conclusion_symbols": set(), "binders": {}},
            )["conclusion_symbols"].add(reference)
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
    return nodes, relations, internal_omissions, type_shapes


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
    (
        environment_nodes,
        environment_relations,
        internal_omissions,
        environment_type_shapes,
    ) = export_environment()
    loaded_library_roots = {
        root
        for root in LEAN_ROOT_TARGETS
        if any(
            owner_module == root
            or owner_module.startswith(f"{root}.")
            for owner_module in environment_nodes.values()
        )
    }
    missing_library_roots = set(LEAN_ROOT_TARGETS) - loaded_library_roots
    if missing_library_roots:
        raise RuntimeError(
            "Lean dependency exporter omitted supported library roots: "
            f"{sorted(missing_library_roots)}"
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
    theorem_kinds = {"theorem", "lemma", "corollary", "proposition"}
    affordance_handles = [
        handle
        for handle, row in sorted(resolved_rows.items())
        if row["kind"] in theorem_kinds
        and handle in environment_type_shapes
    ]
    affordance_binders = {}
    for handle in affordance_handles:
        shape = environment_type_shapes[handle]
        binder_indexes = sorted(shape["binders"])
        if binder_indexes != list(range(shape["binder_count"])):
            raise RuntimeError(
                f"non-contiguous binder export for {handle}: "
                f"{binder_indexes!r}"
            )
        affordance_binders[handle] = [
            shape["binders"][index] for index in binder_indexes
        ]
    affordance_symbols = sorted(
        {
            symbol
            for handle in affordance_handles
            for symbol in (
                environment_type_shapes[handle]["conclusion_head"],
                *environment_type_shapes[handle]["conclusion_symbols"],
                *(
                    binder_symbol
                    for binder in affordance_binders[handle]
                    for binder_symbol in (
                        binder["type_head"],
                        *binder["type_symbols"],
                    )
                ),
            )
        }
    )
    affordance_symbol_ids = {
        symbol: symbol_id
        for symbol_id, symbol in enumerate(affordance_symbols)
    }
    affordance_binder_names = sorted(
        {
            binder["name"]
            for handle in affordance_handles
            for binder in affordance_binders[handle]
        }
    )
    affordance_binder_name_ids = {
        name: name_id
        for name_id, name in enumerate(affordance_binder_names)
    }
    binder_info_codes = {
        "explicit": 0,
        "implicit": 1,
        "strict_implicit": 2,
        "instance_implicit": 3,
    }
    affordance_rows = [
        [
            node_id_by_handle[handle],
            environment_type_shapes[handle]["binder_count"],
            affordance_symbol_ids[
                environment_type_shapes[handle]["conclusion_head"]
            ],
            sorted(
                affordance_symbol_ids[symbol]
                for symbol in environment_type_shapes[handle][
                    "conclusion_symbols"
                ]
            ),
            [
                [
                    affordance_binder_name_ids[binder["name"]],
                    binder_info_codes[binder["binder_info"]],
                    binder["is_proposition"],
                    affordance_symbol_ids[binder["type_head"]],
                    sorted(
                        affordance_symbol_ids[symbol]
                        for symbol in binder["type_symbols"]
                    ),
                ]
                for binder in affordance_binders[handle]
            ],
        ]
        for handle in affordance_handles
    ]
    affordance_binder_count = sum(
        len(binders) for binders in affordance_binders.values()
    )
    affordance_proposition_binder_count = sum(
        binder["is_proposition"]
        for binders in affordance_binders.values()
        for binder in binders
    )
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
            "command": "lake build Erdos249257 ErdosProblems",
            "posture": (
                "both_supported_compact_roots_are_built_before_environment_"
                "export_so_source_fingerprint_and_loaded_olean_state_are_current"
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
            "loaded_library_roots": sorted(loaded_library_roots),
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
            "source_resolved_formal_type_affordance_count": len(
                affordance_rows
            ),
            "formal_type_affordance_symbol_count": len(
                affordance_symbols
            ),
            "formal_type_affordance_binder_name_count": len(
                affordance_binder_names
            ),
            "formal_type_affordance_binder_count": (
                affordance_binder_count
            ),
            "formal_type_affordance_proposition_binder_count": (
                affordance_proposition_binder_count
            ),
        },
        "unresolved_atlas_declarations": unresolved_atlas_rows,
        "edge_relation_bit_legend": {
            "1": "type_reference",
            "2": "value_reference",
        },
        "formal_type_affordances": {
            "authority_posture": (
                "conclusion_shape_from_elaborated_Lean_types_for_navigation_"
                "and_candidate_ranking_not_unification_or_applicability_proof"
            ),
            "row_layout": [
                "node_id",
                "forall_binder_count",
                "conclusion_head_symbol_id",
                "conclusion_symbol_ids",
                "binder_rows",
            ],
            "binder_row_layout": [
                "binder_name_id",
                "binder_info_code",
                "is_proposition",
                "type_head_symbol_id",
                "type_symbol_ids",
            ],
            "binder_info_code_legend": {
                "0": "explicit",
                "1": "implicit",
                "2": "strict_implicit",
                "3": "instance_implicit",
            },
            "symbol_table": affordance_symbols,
            "binder_name_table": affordance_binder_names,
            "rows": affordance_rows,
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
    parser.add_argument(
        "--full-check",
        action="store_true",
        help="ignore an exact cached receipt and rerun the Lean exporter",
    )
    args = parser.parse_args()
    if args.full_check and not args.check:
        parser.error("--full-check requires --check")
    if args.check and not args.full_check:
        cached = load_cached_check()
        if cached is not None:
            print(
                "Lean dependency index: PASS cached "
                f"({cached['source_resolved_node_count']} nodes, "
                f"{cached['source_resolved_direct_edge_count']} edges)"
            )
            return 0
    initial_input_fingerprint = check_input_fingerprint()
    packet = build_packet()
    content = encoded(packet)
    if check_input_fingerprint() != initial_input_fingerprint:
        print(
            "Lean dependency verification inputs changed during the full "
            "environment check; rerun against a stable snapshot",
            file=sys.stderr,
        )
        return 2
    if args.check:
        if not OUTPUT.is_file() or OUTPUT.read_text(encoding="utf-8") != content:
            print(f"stale Lean dependency index: {OUTPUT}", file=sys.stderr)
            return 1
        write_check_receipt(
            content,
            packet,
            input_fingerprint=initial_input_fingerprint,
        )
        print(
            "Lean dependency index: PASS "
            f"({packet['coverage']['source_resolved_node_count']} nodes, "
            f"{packet['coverage']['source_resolved_direct_edge_count']} edges)"
        )
        return 0
    OUTPUT.write_text(content, encoding="utf-8")
    write_check_receipt(
        content,
        packet,
        input_fingerprint=initial_input_fingerprint,
    )
    print(
        f"wrote {OUTPUT} "
        f"({packet['coverage']['source_resolved_node_count']} nodes, "
        f"{packet['coverage']['source_resolved_direct_edge_count']} edges)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
