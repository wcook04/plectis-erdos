#!/usr/bin/env python3
"""Read-only manifest-to-corpus navigation map for the Lean corpus."""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path
from typing import Any

from script_catalog import _normalize_problem_id, catalog


FRONTIER_IDENTIFIER_PREVIEW_LIMIT = 4
ENTRY_SCHEMA = "lean_corpus_entry_v0"
PROJECT_ROUTE_PREFIX = "formal_math/erdos257_period_noncollapse"
SOURCE_KINDS = ("lean", "markdown", "script")


def _manifest(project_root: Path) -> list[dict[str, Any]]:
    path = project_root / "ErdosProblems" / "assimilation_manifest.json"
    payload = json.loads(path.read_text(encoding="utf-8"))
    problems = payload.get("problems") if isinstance(payload, dict) else None
    if not isinstance(problems, list) or not all(isinstance(problem, dict) for problem in problems):
        raise ValueError("manifest problems must be a list of objects")
    return problems


def entry_card(project_root: Path) -> dict[str, Any]:
    """Return a compact first-contact card without opening any research packet.

    This is deliberately smaller than the manifest navigation map. It gives a
    new agent the stable problem identifiers and command families that lead to
    owner surfaces, leaving packet fields, source trees, and computations
    unopened until a problem is selected.
    """

    problem_choices = []
    for row in _manifest(project_root):
        if not isinstance(row.get("id"), str) or not row["id"]:
            continue
        lean_module = row.get("lean_module")
        choice = {
            "problem_id": row["id"],
            "owner_directory": row.get("directory"),
            "research_packet": row.get("packet"),
            "supported_lean_module": lean_module,
        }
        if isinstance(lean_module, str) and lean_module:
            choice["focused_lean_build_plan"] = (
                f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/lean_fast_build.py "
                f"--plan {lean_module}"
            )
        problem_choices.append(choice)
    problem_ids = [row["problem_id"] for row in problem_choices]
    return {
        "schema_version": ENTRY_SCHEMA,
        "kind": "lean_corpus_entry",
        "boundary": (
            "First-contact routing only; no research packet is opened, no computation "
            "is run, and no mathematical status is inferred."
        ),
        "summary": {
            "problem_count": len(problem_ids),
            "problem_ids": problem_ids,
        },
        "problem_choices": problem_choices,
        "recommended_routes": {
            "choose_problem_from_compact_packet_metadata": "all_problem_frontier_overview",
            "map_corpus_source_shape_before_opening_a_problem": "all_problem_source_topology",
            "locate_cross_problem_computation_families": "cross_problem_computation_overview",
            "inspect_cross_problem_mathematical_connections": (
                "global_mathematical_connection_index"
            ),
            "inspect_corpus_structure_before_mutation": "corpus_structure_check",
            "inspect_supported_aggregate_assumptions": "aggregate_axiom_audit_plan",
            "plan_selected_problem_lean_validation": (
                "problem_choices[].focused_lean_build_plan"
            ),
            "inspect_declared_corpus_scripts_for_a_selected_problem": (
                "explicit_corpus_computation_routes_template"
            ),
            "inspect_papers_comparators_or_research_for_a_selected_problem": (
                "problem_cockpit_template"
            ),
            "route_an_incoming_research_return_for_a_selected_problem": (
                "assimilation_surface_template"
            ),
            "inspect_one_large_source_kind_without_dumping_all_paths": (
                "bounded_source_inventory_template"
            ),
        },
        "routes": {
            "problem_cockpit_template": (
                "./repo-python -m system.lib.mathematical_working_memory "
                "--query 'Erdos #<number>' --problem-cockpit --context-budget 12000"
            ),
            "assimilation_surface_template": (
                f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/assimilation_surface.py "
                "--problem <number>"
            ),
            "all_problem_frontier": (
                f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/corpus_navigation.py "
                "--frontier-summary --json"
            ),
            "all_problem_frontier_overview": (
                f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/corpus_navigation.py "
                "--frontier-overview --json"
            ),
            "selected_problem_frontier_template": (
                f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/corpus_navigation.py "
                "--problem erdos_<number> --frontier-summary --json"
            ),
            "cross_problem_computation_overview": (
                "./repo-python -m system.lib.formal_math_probe_registry --overview"
            ),
            "global_mathematical_connection_index": (
                "./repo-python -m system.lib.mathematical_working_memory --mode global "
                "--query 'Lean corpus connection index' --context-budget 12000"
            ),
            "corpus_structure_check": (
                f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/"
                "check_problem_corpus_index.py --json"
            ),
            "release_aggregate_build_plan": (
                f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/lean_fast_build.py "
                "--plan ErdosProblems.Root"
            ),
            "aggregate_axiom_audit_plan": (
                f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/lean_fast_build.py "
                "--plan ErdosProblems.AxiomAudit"
            ),
            "explicit_corpus_computation_routes_template": (
                f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/corpus_computation_routes.py "
                "--problem erdos_<number> --json"
            ),
            "source_topology_template": (
                f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/corpus_navigation.py "
                "--problem erdos_<number> --source-summary --json"
            ),
            "bounded_source_inventory_template": (
                f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/corpus_navigation.py "
                "--problem erdos_<number> --source-paths --source-kind markdown "
                "--source-path-limit 40 --json"
            ),
            "all_problem_source_topology": (
                f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/corpus_navigation.py "
                "--source-overview --json"
            ),
        },
        "first_action": (
            "Choose one listed problem id, then replace <number> in "
            "problem_cockpit_template before reading a packet or source tree. For Lean "
            "validation, use that choice's focused_lean_build_plan first; reserve "
            "release_aggregate_build_plan for the separate integration gate."
        ),
    }


def _research_packet(project_root: Path, packet_ref: object) -> dict[str, Any]:
    """Read one manifest-owned research packet for an explicit frontier view."""

    if not isinstance(packet_ref, str) or not packet_ref:
        raise ValueError("manifest row has no research packet path")
    payload = json.loads((project_root / packet_ref).read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"research packet must be a JSON object: {packet_ref}")
    return payload


def _open_producer_ids(packet: dict[str, Any]) -> list[str]:
    """Extract source-declared producer identifiers without reading their claims."""

    producers = packet.get("open_producers")
    if not isinstance(producers, list):
        return []
    identifiers: list[str] = []
    for position, producer in enumerate(producers, start=1):
        if isinstance(producer, dict) and isinstance(producer.get("id"), str):
            identifiers.append(producer["id"])
        elif isinstance(producer, str):
            identifiers.append(producer)
        else:
            identifiers.append(f"<unidentified_open_producer_{position}>")
    return identifiers


def _record_count(packet: dict[str, Any], key: str) -> int | None:
    """Count a packet list or singleton without judging its mathematical weight."""

    value = packet.get(key)
    if value is None:
        return None
    return len(value) if isinstance(value, list) else 1


def _identified_record_ids(packet: dict[str, Any], key: str) -> list[str]:
    """Return only literal ``id`` fields from one packet record list."""

    records = packet.get(key)
    if not isinstance(records, list):
        return []
    return [
        record["id"]
        for record in records
        if isinstance(record, dict) and isinstance(record.get("id"), str)
    ]


def _identifier_status(packet: object, field: str) -> str:
    """Say whether a packet field's records carry identifiers.

    Several packets store ``negative_results`` as bare prose strings rather than
    records with an ``id``.  ``_identified_record_ids`` then returns nothing, and
    a reader looking only at ``*_id_count`` sees ``0`` and concludes the packet
    has no such results -- when in fact it may hold the largest refutation set in
    the corpus.  This field distinguishes "none recorded" from "recorded without
    identifiers" so no caller has to infer it from a zero.
    """

    records = packet.get(field) if isinstance(packet, dict) else None
    if not isinstance(records, list) or not records:
        return "no_records"
    identified = sum(
        1
        for record in records
        if isinstance(record, dict) and isinstance(record.get("id"), str)
    )
    if identified == len(records):
        return "all_records_identified"
    if identified == 0:
        return "prose_records_without_identifiers"
    return "mixed_identified_and_prose_records"


def _packet_frontier(
    project_root: Path,
    *,
    packet_ref: object,
    include_all_ids: bool,
) -> dict[str, Any]:
    """Relay compact packet-owned frontier coordinates for corpus navigation."""

    packet = _research_packet(project_root, packet_ref)
    open_producer_ids = _open_producer_ids(packet)
    exact_result_ids = _identified_record_ids(packet, "exact_results")
    negative_result_ids = _identified_record_ids(packet, "negative_results")
    producer_view: dict[str, Any]
    if include_all_ids:
        producer_view = {"open_producer_ids": open_producer_ids}
    else:
        producer_view = {
            "representative_open_producer_ids": open_producer_ids[
                :FRONTIER_IDENTIFIER_PREVIEW_LIMIT
            ],
            "omitted_open_producer_count": max(
                0, len(open_producer_ids) - FRONTIER_IDENTIFIER_PREVIEW_LIMIT
            ),
        }
    exact_result_view: dict[str, Any]
    if include_all_ids:
        exact_result_view = {"exact_result_ids": exact_result_ids}
    else:
        exact_result_view = {
            "representative_exact_result_ids": exact_result_ids[
                :FRONTIER_IDENTIFIER_PREVIEW_LIMIT
            ],
            "omitted_exact_result_id_count": max(
                0, len(exact_result_ids) - FRONTIER_IDENTIFIER_PREVIEW_LIMIT
            ),
        }
    negative_result_view: dict[str, Any]
    if include_all_ids:
        negative_result_view = {"negative_result_ids": negative_result_ids}
    else:
        negative_result_view = {
            "representative_negative_result_ids": negative_result_ids[
                :FRONTIER_IDENTIFIER_PREVIEW_LIMIT
            ],
            "omitted_negative_result_id_count": max(
                0, len(negative_result_ids) - FRONTIER_IDENTIFIER_PREVIEW_LIMIT
            ),
        }
    claim_ceiling = packet.get("claim_ceiling")
    integrity = packet.get("frontier_integrity")
    if not isinstance(integrity, dict):
        integrity = {}
    canonical = integrity.get("canonical_frontier")
    if not isinstance(canonical, dict):
        canonical = {"kind": "declared_target", "producer_ids": []}
    relations = integrity.get("producer_relations")
    if not isinstance(relations, dict):
        relations = {}
    return {
        "packet_title": packet.get("title") if isinstance(packet.get("title"), str) else None,
        "target": packet.get("target") if isinstance(packet.get("target"), dict) else None,
        "canonical_frontier": canonical,
        "producer_relations": relations,
        "open_producer_semantics": "candidate_route_inventory_not_frontier_authority",
        "claim_ceiling_source": (
            f"{packet_ref}::claim_ceiling" if isinstance(claim_ceiling, str) else None
        ),
        "claim_ceiling_character_count": len(claim_ceiling) if isinstance(claim_ceiling, str) else None,
        "open_producer_count": len(open_producer_ids),
        **producer_view,
        "exact_result_id_count": len(exact_result_ids),
        **exact_result_view,
        "negative_result_id_count": len(negative_result_ids),
        "negative_result_record_count": _record_count(packet, "negative_results"),
        "negative_result_identifier_status": _identifier_status(
            packet, "negative_results"
        ),
        **negative_result_view,
        "packet_record_counts": {
            "exact_results": _record_count(packet, "exact_results"),
            "negative_results": _record_count(packet, "negative_results"),
            "source_returns": _record_count(packet, "source_returns"),
            "landed_formal_source": _record_count(packet, "landed_formal_source"),
        },
    }


def _frontier_navigation_routes(problem_id: str, lean_module: object) -> dict[str, str]:
    """Return fixed source-kind routes for a manifest problem without running them."""

    routes = {
        "problem_cockpit": (
            "./repo-python -m system.lib.mathematical_working_memory "
            f"--query 'Erdos #{problem_id.removeprefix('erdos_')}' "
            "--problem-cockpit --context-budget 12000"
        ),
        "assimilation_surface": (
            f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/assimilation_surface.py "
            f"--problem {problem_id.removeprefix('erdos_')}"
        ),
        "packet_frontier": (
            f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/corpus_navigation.py "
            f"--problem {problem_id} --frontier-summary --json"
        ),
        "source_topology": (
            f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/corpus_navigation.py "
            f"--problem {problem_id} --source-summary --json"
        ),
        "source_inventory": (
            f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/corpus_navigation.py "
            f"--problem {problem_id} --source-paths --json"
        ),
        "bounded_source_inventory": (
            f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/corpus_navigation.py "
            f"--problem {problem_id} --source-paths --source-kind markdown "
            "--source-path-limit 40 --json"
        ),
        "packet_bound_computation_coverage": (
            "./repo-python -m system.lib.formal_math_probe_registry "
            f"--problem {problem_id} --coverage"
        ),
        "explicit_corpus_computation_routes": (
            f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/corpus_computation_routes.py "
            f"--problem {problem_id} --json"
        ),
        "corpus_structure_check": (
            f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/"
            "check_problem_corpus_index.py --json"
        ),
        "aggregate_axiom_audit_plan": (
            f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/lean_fast_build.py "
            "--plan ErdosProblems.AxiomAudit"
        ),
    }
    if isinstance(lean_module, str) and lean_module:
        routes["focused_lean_build_plan"] = (
            f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/lean_fast_build.py "
            f"--plan {lean_module}"
        )
    routes["release_aggregate_build_plan"] = (
        f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/lean_fast_build.py "
        "--plan ErdosProblems.Root"
    )
    return routes


def _frontier_overview_entry(
    problem_id: str, packet_frontier: dict[str, Any]
) -> dict[str, Any]:
    """Project packet metadata into one bounded all-problem frontier row."""

    target = packet_frontier.get("target")
    target_status = target.get("status") if isinstance(target, dict) else None
    return {
        "id": problem_id,
        "packet_title": packet_frontier["packet_title"],
        "packet_declared_target_status": target_status,
        "problem_cockpit_command": (
            "./repo-python -m system.lib.mathematical_working_memory "
            f"--query 'Erdos #{problem_id.removeprefix('erdos_')}' "
            "--problem-cockpit --context-budget 12000"
        ),
        "frontier_record_counts": {
            "candidate_routes_not_frontier": packet_frontier["open_producer_count"],
            "exact_result_ids": packet_frontier["exact_result_id_count"],
            "negative_result_ids": packet_frontier["negative_result_id_count"],
            "packet_records": packet_frontier["packet_record_counts"],
        },
        "canonical_frontier": packet_frontier["canonical_frontier"],
        "frontier_detail_command": (
            f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/corpus_navigation.py "
            f"--problem {problem_id} --frontier-summary --json"
        ),
        "source_topology_command": (
            f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/corpus_navigation.py "
            f"--problem {problem_id} --source-summary --json"
        ),
        "bounded_source_inventory_command": (
            f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/corpus_navigation.py "
            f"--problem {problem_id} --source-paths --source-kind markdown "
            "--source-path-limit 40 --json"
        ),
        "explicit_corpus_computation_routes_command": (
            f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/corpus_computation_routes.py "
            f"--problem {problem_id} --json"
        ),
    }


def _staged_paper_tex_paths(project_root: Path) -> dict[str, list[str]]:
    """Return physical staged TeX source routes keyed by Erdős problem id."""

    papers_dir = project_root / "ErdosProblems" / "papers"
    paths_by_problem: dict[str, list[str]] = {}
    if not papers_dir.is_dir():
        return paths_by_problem
    for path in sorted(papers_dir.glob("erdos-*.tex")):
        parts = path.stem.split("-", 2)
        if len(parts) != 3 or parts[0] != "erdos" or not parts[1].isdecimal():
            continue
        problem_id = f"erdos_{int(parts[1])}"
        paths_by_problem.setdefault(problem_id, []).append(path.relative_to(project_root).as_posix())
    return paths_by_problem


def _owner_source_paths(project_root: Path, directory: object, suffix: str) -> list[str]:
    """Return physical source paths of one kind below a manifest owner directory."""

    if not isinstance(directory, str):
        return []
    owner_directory = project_root / directory
    if not owner_directory.is_dir():
        return []
    return [
        path.relative_to(project_root).as_posix()
        for path in sorted(owner_directory.rglob(f"*{suffix}"))
        if path.is_file()
    ]


def _module_source_path(project_root: Path, module: object) -> str | None:
    """Resolve one declared Lean module to its physical source path, if present."""

    if not isinstance(module, str) or not module:
        return None
    parts = module.split(".")
    if not all(
        part and part not in {".", ".."} and "/" not in part and "\\" not in part
        for part in parts
    ):
        return None
    path = project_root.joinpath(*parts).with_suffix(".lean")
    return path.relative_to(project_root).as_posix() if path.is_file() else None


def _source_summary(
    project_root: Path,
    *,
    directory: object,
    lean_module: object,
    companion_modules: list[str],
    problem_script_paths: list[str],
) -> dict[str, Any]:
    """Summarize one problem's own files plus manifest-declared companions.

    Historical compatibility modules can live outside the physical problem
    directory. The manifest declares those source routes, whereas a recursive
    owner-directory listing deliberately does not. Keep both categories
    visible without inspecting theorem bodies or inferring status.
    """

    owner_directory = directory.rstrip("/") if isinstance(directory, str) else ""
    owner_prefix = owner_directory + "/" if owner_directory else ""
    companion_sources: list[dict[str, str | None]] = []
    for module in companion_modules:
        source_path = _module_source_path(project_root, module)
        companion_sources.append(
            {
                "module": module,
                "path": source_path,
                "relative_to_problem_owner": (
                    "missing_source"
                    if source_path is None
                    else (
                        "within_problem_directory"
                        if source_path.startswith(owner_prefix)
                        else "outside_problem_directory"
                    )
                ),
            }
        )

    return {
        "owner_directory_source_counts": {
            "lean_source_count": len(_owner_source_paths(project_root, directory, ".lean")),
            "markdown_note_count": len(_owner_source_paths(project_root, directory, ".md")),
            "problem_script_count": len(problem_script_paths),
        },
        "supported_entry_source": {
            "module": lean_module,
            "path": _module_source_path(project_root, lean_module),
        },
        "manifest_companion_lean_sources": companion_sources,
        "boundary": (
            "Filesystem and manifest routing only; source presence and location do "
            "not imply proof status, mathematical relevance, or publication state."
        ),
    }


def _source_overview(
    project_root: Path,
    *,
    directory: object,
    lean_module: object,
    companion_modules: list[str],
    problem_script_paths: list[str],
) -> dict[str, Any]:
    """Compress one source summary into counts suitable for all-problem output."""

    source_summary = _source_summary(
        project_root,
        directory=directory,
        lean_module=lean_module,
        companion_modules=companion_modules,
        problem_script_paths=problem_script_paths,
    )
    companion_location_counts = Counter(
        source["relative_to_problem_owner"]
        for source in source_summary["manifest_companion_lean_sources"]
    )
    return {
        "owner_directory_source_counts": source_summary["owner_directory_source_counts"],
        "supported_entry_source": source_summary["supported_entry_source"],
        "manifest_companion_source_location_counts": dict(
            sorted(companion_location_counts.items())
        ),
    }


def navigation_map(
    project_root: Path,
    *,
    problem: str | None = None,
    include_source_paths: bool = False,
    source_kind: str | None = None,
    source_path_limit: int | None = None,
    include_source_summary: bool = False,
    include_source_overview: bool = False,
    include_frontier_summary: bool = False,
    include_frontier_overview: bool = False,
) -> dict[str, Any]:
    """Join manifest ownership with companion, script, and staged-paper routes.

    The result is a filesystem and manifest navigation surface only. It does
    not run computations or infer mathematical status from their presence.
    Its optional frontier view relays source-authored packet fields unchanged;
    it does not rank problems or interpret those fields as progress.
    """

    selected_problem_id = _normalize_problem_id(problem) if problem is not None else None
    problems = _manifest(project_root)
    known_problem_ids = {
        row["id"] for row in problems if isinstance(row.get("id"), str) and row["id"]
    }
    if selected_problem_id is not None and selected_problem_id not in known_problem_ids:
        raise ValueError(f"unknown manifest problem id: {selected_problem_id}")
    if include_source_paths and selected_problem_id is None:
        raise ValueError("source-path inventory requires --problem")
    if source_kind is not None and not include_source_paths:
        raise ValueError("source-kind requires --source-paths")
    if source_kind is not None and source_kind not in SOURCE_KINDS:
        raise ValueError(f"unknown source kind: {source_kind}")
    if source_path_limit is not None and not include_source_paths:
        raise ValueError("source-path-limit requires --source-paths")
    if source_path_limit is not None and source_kind is None:
        raise ValueError("source-path-limit requires --source-kind")
    if source_path_limit is not None and source_path_limit < 1:
        raise ValueError("source-path-limit must be positive")
    if include_source_summary and selected_problem_id is None:
        raise ValueError("source summary requires --problem")
    if include_frontier_summary and include_frontier_overview:
        raise ValueError("frontier summary and frontier overview are alternative views")

    catalog_entries = catalog(project_root)["scripts"]
    scripts_by_problem = Counter(
        entry["problem_id"] for entry in catalog_entries if entry["problem_id"] is not None
    )
    script_paths_by_problem: dict[str, list[str]] = {}
    for entry in catalog_entries:
        entry_problem_id = entry["problem_id"]
        if entry_problem_id is not None:
            script_paths_by_problem.setdefault(entry_problem_id, []).append(entry["path"])
    paper_tex_paths_by_problem = _staged_paper_tex_paths(project_root)
    rows: list[dict[str, Any]] = []
    packet_frontiers: list[dict[str, Any]] = []
    frontier_overview_rows: list[dict[str, Any]] = []
    for row in problems:
        problem_id = row.get("id")
        if not isinstance(problem_id, str) or (selected_problem_id is not None and problem_id != selected_problem_id):
            continue
        companion_modules = row.get("companion_modules")
        companion_modules = (
            companion_modules
            if isinstance(companion_modules, list) and all(isinstance(module, str) for module in companion_modules)
            else []
        )
        directory = row.get("directory")
        owner_namespace = directory.replace("/", ".") + "." if isinstance(directory, str) else None
        owner_namespace_companion_module_count = sum(
            owner_namespace is not None and module.startswith(owner_namespace)
            for module in companion_modules
        )
        entry = {
            "id": problem_id,
            "directory": directory,
            "packet": row.get("packet"),
            "lean_module": row.get("lean_module"),
            "companion_module_count": len(companion_modules),
            "owner_namespace_companion_module_count": owner_namespace_companion_module_count,
            "outside_problem_namespace_companion_module_count": (
                len(companion_modules) - owner_namespace_companion_module_count
            ),
            "problem_owned_script_count": scripts_by_problem[problem_id],
            "staged_paper_tex_paths": paper_tex_paths_by_problem.get(problem_id, []),
        }
        if selected_problem_id is not None:
            entry["problem_navigation_routes"] = _frontier_navigation_routes(
                problem_id, row.get("lean_module")
            )
        if include_source_paths:
            source_paths_by_kind = {
                "lean": _owner_source_paths(project_root, directory, ".lean"),
                "markdown": _owner_source_paths(project_root, directory, ".md"),
                "script": script_paths_by_problem.get(problem_id, []),
            }
            if source_kind is None:
                entry["lean_source_paths"] = source_paths_by_kind["lean"]
                entry["markdown_note_paths"] = source_paths_by_kind["markdown"]
                entry["problem_script_paths"] = source_paths_by_kind["script"]
            else:
                paths = source_paths_by_kind[source_kind]
                displayed_paths = (
                    paths if source_path_limit is None else paths[:source_path_limit]
                )
                entry["source_inventory"] = {
                    "kind": source_kind,
                    "paths": displayed_paths,
                    "total_path_count": len(paths),
                    "omitted_path_count": len(paths) - len(displayed_paths),
                }
        if include_source_summary:
            entry["source_summary"] = _source_summary(
                project_root,
                directory=directory,
                lean_module=row.get("lean_module"),
                companion_modules=companion_modules,
                problem_script_paths=script_paths_by_problem.get(problem_id, []),
            )
            entry["problem_cockpit_command"] = (
                "./repo-python -m system.lib.mathematical_working_memory "
                f"--query 'Erdos #{problem_id.removeprefix('erdos_')}' "
                "--problem-cockpit --context-budget 12000"
            )
            entry["source_inventory_command"] = (
                f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/corpus_navigation.py "
                f"--problem {problem_id} --source-paths --json"
            )
            entry["bounded_source_inventory_commands"] = {
                kind: (
                    f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/corpus_navigation.py "
                    f"--problem {problem_id} --source-paths --source-kind {kind} "
                    "--source-path-limit 40 --json"
                )
                for kind in SOURCE_KINDS
            }
        if include_source_overview:
            entry["source_overview"] = _source_overview(
                project_root,
                directory=directory,
                lean_module=row.get("lean_module"),
                companion_modules=companion_modules,
                problem_script_paths=script_paths_by_problem.get(problem_id, []),
            )
            entry["source_topology_command"] = (
                f"./repo-python {PROJECT_ROUTE_PREFIX}/scripts/corpus_navigation.py "
                f"--problem {problem_id} --source-summary --json"
            )
        if include_frontier_summary or include_frontier_overview:
            packet_frontier = _packet_frontier(
                project_root,
                packet_ref=row.get("packet"),
                include_all_ids=selected_problem_id is not None,
            )
            packet_frontiers.append(packet_frontier)
            if include_frontier_summary:
                entry["packet_frontier"] = packet_frontier
                routes = entry.get("problem_navigation_routes") or _frontier_navigation_routes(
                    problem_id, row.get("lean_module")
                )
                entry["frontier_drilldown_command"] = routes["problem_cockpit"]
                entry["frontier_navigation_routes"] = routes
            else:
                frontier_overview_rows.append(
                    _frontier_overview_entry(problem_id, packet_frontier)
                )
        rows.append(entry)

    filters = {
        "problem_id": selected_problem_id,
        "source_paths": include_source_paths,
        "source_summary": include_source_summary,
        "source_overview": include_source_overview,
    }
    if include_frontier_summary:
        filters["frontier_summary"] = True
    if include_frontier_overview:
        filters["frontier_overview"] = True
    if source_kind is not None:
        filters["source_kind"] = source_kind
    if source_path_limit is not None:
        filters["source_path_limit"] = source_path_limit
    summary = {
        "problem_count": len(rows),
        "problem_owned_script_count": sum(row["problem_owned_script_count"] for row in rows),
        "companion_module_count": sum(row["companion_module_count"] for row in rows),
        "owner_namespace_companion_module_count": sum(
            row["owner_namespace_companion_module_count"] for row in rows
        ),
        "outside_problem_namespace_companion_module_count": sum(
            row["outside_problem_namespace_companion_module_count"] for row in rows
        ),
        "staged_paper_tex_source_count": sum(len(row["staged_paper_tex_paths"]) for row in rows),
    }
    if include_source_overview:
        source_overviews = [row["source_overview"] for row in rows]
        companion_location_counts: Counter[str] = Counter()
        for source_overview in source_overviews:
            companion_location_counts.update(
                source_overview["manifest_companion_source_location_counts"]
            )
        summary["source_overview"] = {
            "owner_directory_source_counts": {
                key: sum(
                    source_overview["owner_directory_source_counts"][key]
                    for source_overview in source_overviews
                )
                for key in ("lean_source_count", "markdown_note_count", "problem_script_count")
            },
            "supported_entry_source_count": sum(
                source_overview["supported_entry_source"]["path"] is not None
                for source_overview in source_overviews
            ),
            "manifest_companion_source_location_counts": dict(
                sorted(companion_location_counts.items())
            ),
        }
    if include_frontier_summary or include_frontier_overview:
        if include_frontier_overview:
            summary = {"problem_count": len(rows)}
        summary["frontier_packet_count"] = len(packet_frontiers)
        summary["open_producer_count"] = sum(
            packet_frontier["open_producer_count"] for packet_frontier in packet_frontiers
        )
        summary["exact_result_id_count"] = sum(
            packet_frontier["exact_result_id_count"] for packet_frontier in packet_frontiers
        )
        summary["negative_result_id_count"] = sum(
            packet_frontier["negative_result_id_count"] for packet_frontier in packet_frontiers
        )
        summary["packet_record_totals"] = {
            key: sum(
                packet_frontier["packet_record_counts"].get(key) or 0
                for packet_frontier in packet_frontiers
            )
            for key in (
                ("exact_results", "negative_results", "source_returns", "landed_formal_source")
                if include_frontier_overview
                else ("source_returns", "landed_formal_source")
            )
        }
        summary["packet_record_field_presence_counts"] = {
            key: sum(
                packet_frontier["packet_record_counts"].get(key) is not None
                for packet_frontier in packet_frontiers
            )
            for key in (
                "exact_results",
                "negative_results",
                "source_returns",
                "landed_formal_source",
            )
        }

    if include_frontier_overview:
        rows = frontier_overview_rows

    return {
        "schema_version": "lean_corpus_navigation_map_v0",
        "kind": "lean_corpus_navigation_map",
        "boundary": "manifest and filesystem navigation only; computations are not run and no mathematical status is inferred",
        "filters": filters,
        "summary": summary,
        "problems": rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--project-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="Lean project root (defaults to this script's parent)",
    )
    parser.add_argument("--problem", help="restrict to one manifest problem, for example 257 or erdos_257")
    parser.add_argument(
        "--entry",
        action="store_true",
        help="emit the compact first-contact card without opening research packets",
    )
    parser.add_argument(
        "--source-paths",
        action="store_true",
        help="include exact Lean, Markdown, and problem-owned script paths; requires --problem",
    )
    parser.add_argument(
        "--source-kind",
        choices=SOURCE_KINDS,
        help="restrict --source-paths to one kind: lean, markdown, or script",
    )
    parser.add_argument(
        "--source-path-limit",
        type=int,
        help="maximum paths in a selected --source-kind inventory; requires --source-paths",
    )
    parser.add_argument(
        "--source-summary",
        action="store_true",
        help="include compact owner counts and manifest-declared companion Lean routes; requires --problem",
    )
    parser.add_argument(
        "--source-overview",
        action="store_true",
        help="include compact all-problem source counts and companion-location categories",
    )
    parser.add_argument(
        "--frontier-summary",
        action="store_true",
        help=(
            "include packet-owned target, open-producer, and record-count coordinates; "
            "all-problem output is compact and --problem shows every producer id"
        ),
    )
    parser.add_argument(
        "--frontier-overview",
        action="store_true",
        help=(
            "emit one compact packet-metadata row per problem without target statements "
            "or identifier previews"
        ),
    )
    parser.add_argument("--json", action="store_true", help="emit the full deterministic JSON map")
    args = parser.parse_args()

    try:
        project_root = args.project_root.resolve()
        if args.entry:
            if (
                args.problem
                or args.source_paths
                or args.source_kind
                or args.source_path_limit is not None
                or args.source_summary
                or args.source_overview
                or args.frontier_summary
                or args.frontier_overview
            ):
                parser.error("--entry cannot be combined with problem or detail-selection flags")
            payload = entry_card(project_root)
        else:
            payload = navigation_map(
                project_root,
                problem=args.problem,
                include_source_paths=args.source_paths,
                source_kind=args.source_kind,
                source_path_limit=args.source_path_limit,
                include_source_summary=args.source_summary,
                include_source_overview=args.source_overview,
                include_frontier_summary=args.frontier_summary,
                include_frontier_overview=args.frontier_overview,
            )
    except (OSError, ValueError, json.JSONDecodeError) as error:
        parser.error(str(error))
    if args.json or args.entry:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(json.dumps(payload["summary"], indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
