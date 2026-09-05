#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Project the complete result-family order into the eight paper pairs.

Mathematical statements and evidence modes come from ``docs/claims.json``.
The qualitative display bands come from the canonical Palomar showcase and are
projected to ``docs/family-display-order.jsonl``.  ``paper-result-integration-source.json`` owns only the independent
short/long publication placement.  The generated JSON and TeX fragments are
therefore routing/exposition projections, never proof or promotion authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import Counter
from pathlib import Path
from typing import Any

from result_atoms import load_result_atoms, validate_result_atoms
from lean_source import lean_code_without_comments_and_strings
from build_comparator_replay_portfolio import build_portfolio


ROOT = Path(__file__).resolve().parent.parent
CLAIMS = ROOT / "docs" / "claims.json"
ATLAS = ROOT / "docs" / "declaration_atlas.json"
PALOMAR = ROOT / "docs" / "PALOMAR_RESULT_SHOWCASE.json"
PLACEMENT_SOURCE = ROOT / "paper" / "paper-result-integration-source.json"
OUTPUT = ROOT / "paper" / "paper-result-integration.json"
PUBLIC_ORDER = ROOT / "docs" / "family-display-order.jsonl"
RESULT_ATOMS = ROOT / "docs" / "result-atoms.jsonl"

DISPLAY_BANDS = (
    "front_door",
    "major_result",
    "mechanism",
    "frontier",
    "technical_support",
)

FRAGMENTS = {
    68: ROOT / "paper" / "reasoning-parts" / "erdos68" / "family_catalogue.tex",
    243: ROOT / "paper" / "reasoning-parts" / "erdos243" / "family_catalogue.tex",
    249: ROOT / "paper" / "reasoning-parts" / "erdos249" / "a249_family_catalogue.tex",
    251: ROOT / "paper" / "reasoning-parts" / "erdos251" / "family_catalogue.tex",
    257: ROOT / "paper" / "reasoning-parts" / "erdos257" / "a257_family_catalogue.tex",
    269: ROOT / "paper" / "reasoning-parts" / "erdos269" / "family_catalogue.tex",
    1041: ROOT / "paper" / "reasoning-parts" / "erdos1041" / "family_catalogue.tex",
    1049: ROOT / "paper" / "reasoning-parts" / "erdos1049" / "family_catalogue.tex",
}


class IntegrationError(RuntimeError):
    """The result-family and paper-placement surfaces do not close."""


def digest(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise IntegrationError(f"{path} is not a JSON object")
    return value


def public_evidence_mode(value: str) -> str:
    """Render configured Comparator selection without inventing a receipt."""
    return value.replace(
        "Lean kernel plus Comparator",
        "Lean kernel; Comparator-selected",
    )


def flatten_claim_families(claims: dict[str, Any]) -> dict[tuple[int, str], dict[str, Any]]:
    try:
        rows = claims["external_verification_packet"]["review_matrix"]
    except (KeyError, TypeError) as exc:
        raise IntegrationError("docs/claims.json has no review_matrix") from exc
    families: dict[tuple[int, str], dict[str, Any]] = {}
    for problem_row in rows:
        problem = int(problem_row["problem"])
        for family in problem_row["families"]:
            key = (problem, family["id"])
            if key in families:
                raise IntegrationError(f"duplicate claim family {key}")
            families[key] = family
    return families


def build_comparator_assurance(
    claims: dict[str, Any],
    claim_families: dict[tuple[int, str], dict[str, Any]],
) -> tuple[dict[tuple[int, str], dict[str, Any]], dict[str, Any], Path]:
    """Join reviewed families to the existing Comparator interface roster.

    ``main_results`` is the registered-claim subset. Comparator may also carry
    executable interfaces that deliberately have no registered-claim status;
    those are linked to a family only when their theorem leaf uniquely matches
    a declaration already owned by that family.
    """
    packet = claims.get("external_verification_packet", {})
    comparator = packet.get("comparator", {})
    config_rel = comparator.get("config")
    if not isinstance(config_rel, str) or not config_rel:
        raise IntegrationError("claims packet has no Comparator config path")
    config_path = ROOT / config_rel
    config = load_json(config_path)
    theorem_names = config.get("theorem_names")
    if not isinstance(theorem_names, list) or not all(
        isinstance(name, str) and name for name in theorem_names
    ):
        raise IntegrationError("Comparator theorem_names must be a nonempty string array")
    if len(theorem_names) != len(set(theorem_names)):
        raise IntegrationError("Comparator theorem_names contains duplicates")
    theorem_roster = set(theorem_names)

    main_results = packet.get("main_results")
    if not isinstance(main_results, list):
        raise IntegrationError("claims packet has no main_results array")
    registered_by_family: dict[tuple[int, str], list[dict[str, Any]]] = {}
    registered_wrappers: set[str] = set()
    for result in main_results:
        if not isinstance(result, dict):
            raise IntegrationError("main_results rows must be objects")
        key = (int(result["problem"]), str(result["review_family"]))
        if key not in claim_families:
            raise IntegrationError(f"Comparator main result has unknown family {key}")
        wrapper = str(result["wrapper_declaration"])
        if wrapper not in theorem_roster:
            raise IntegrationError(
                f"registered Comparator wrapper is absent from theorem roster: {wrapper}"
            )
        if wrapper in registered_wrappers:
            raise IntegrationError(f"duplicate registered Comparator wrapper: {wrapper}")
        registered_wrappers.add(wrapper)
        registered_by_family.setdefault(key, []).append(
            {
                "id": result["id"],
                "registration_status": "registered_claim_interface",
                "original_declaration": result["original_declaration"],
                "wrapper_declaration": wrapper,
                "statement": result["statement"],
                "boundary": result["boundary"],
            }
        )

    declaration_leaf_owners: dict[str, list[tuple[tuple[int, str], str]]] = {}
    for key, family in claim_families.items():
        for declaration in family.get("declarations", []):
            declaration_leaf_owners.setdefault(
                str(declaration).rsplit(".", 1)[-1], []
            ).append((key, str(declaration)))

    unregistered = [name for name in theorem_names if name not in registered_wrappers]
    unregistered_by_family: dict[tuple[int, str], list[dict[str, Any]]] = {}
    unassociated_unregistered: list[str] = []
    for wrapper in unregistered:
        owners = declaration_leaf_owners.get(wrapper.rsplit(".", 1)[-1], [])
        if len(owners) != 1:
            unassociated_unregistered.append(wrapper)
            continue
        key, original = owners[0]
        unregistered_by_family.setdefault(key, []).append(
            {
                "id": None,
                "registration_status": "unregistered_executable_interface",
                "original_declaration": original,
                "wrapper_declaration": wrapper,
                "statement": None,
                "boundary": (
                    "Executable Comparator interface only; it is not included among "
                    "the repository-registered selected result interfaces."
                ),
            }
        )

    assurances: dict[tuple[int, str], dict[str, Any]] = {}
    status_counts: Counter[str] = Counter()
    family_linked_interface_count = 0
    for key, family in claim_families.items():
        disposition = family.get("comparator_disposition")
        if not isinstance(disposition, str) or not disposition:
            raise IntegrationError(f"claim family has no Comparator disposition: {key}")
        interfaces = [
            *registered_by_family.get(key, []),
            *unregistered_by_family.get(key, []),
        ]
        if disposition.startswith("targeted"):
            if not interfaces:
                raise IntegrationError(
                    f"targeted Comparator family has no executable interface: {key}"
                )
            status = "exact_selected_interface"
        elif disposition.startswith("represented_by"):
            status = "represented_by_selected_interface"
        elif disposition.startswith("not_selected"):
            status = "not_selected_for_comparator"
        elif disposition.startswith("not_applicable"):
            status = "not_applicable_to_comparator"
        else:
            raise IntegrationError(
                f"unknown Comparator disposition for {key}: {disposition}"
            )
        if interfaces and status != "exact_selected_interface":
            raise IntegrationError(
                f"non-targeted family unexpectedly owns Comparator interface: {key}"
            )
        registered_count = sum(
            row["registration_status"] == "registered_claim_interface"
            for row in interfaces
        )
        assurances[key] = {
            "status": status,
            "disposition": disposition,
            "registered_interface_count": registered_count,
            "executable_interface_count": len(interfaces),
            "selected_interfaces": interfaces,
            "config": config_rel,
            "query": "python3 scripts/query_corpus.py --route comparator_assurance",
            "authority_boundary": packet.get("boundary"),
        }
        status_counts[status] += 1
        family_linked_interface_count += len(interfaces)

    summary = {
        "classified_family_count": len(assurances),
        "registered_selected_interface_count": len(main_results),
        "comparator_theorem_count": len(theorem_names),
        "family_linked_executable_interface_count": family_linked_interface_count,
        "unregistered_executable_interface_count": len(unregistered),
        "unassociated_unregistered_interface_count": len(unassociated_unregistered),
        "unassociated_unregistered_interfaces": unassociated_unregistered,
        "family_status_counts": dict(sorted(status_counts.items())),
    }
    return assurances, summary, config_path


def discover_per_entry_comparator_portfolio() -> dict[str, Any]:
    """Inventory current in-tree Palomar-style packages without blessing them.

    The old outbound repository used one Comparator configuration per entry.
    Canonical Plectis retains the Challenge/Solution mathematics, but a source
    move does not transfer a commit-bound Comparator receipt. This inventory is
    therefore a replay queue, not another proof or claim authority.
    """
    aggregate = build_portfolio(ROOT)
    aggregate_by_package = {row.name: row for row in aggregate.packages}
    packages: list[dict[str, Any]] = []
    digest_input = bytearray()
    lake_targets = set(
        re.findall(
            r'^name\s*=\s*"([^"]+)"',
            (ROOT / "lakefile.toml").read_text(encoding="utf-8"),
            flags=re.MULTILINE,
        )
    )
    for challenge in sorted(ROOT.glob("ExternalVerification*/Challenge.lean")):
        if challenge.parent.name == "ExternalVerification":
            continue
        solution = challenge.with_name("Solution.lean")
        axiom_audit = challenge.with_name("AxiomAudit.lean")
        if not solution.is_file():
            raise IntegrationError(
                f"per-entry Comparator Challenge has no Solution: {challenge}"
            )
        if challenge.parent.name not in lake_targets:
            raise IntegrationError(
                "per-entry Comparator package has no named Lake target: "
                f"{challenge.parent.name}"
            )
        aggregate_package = aggregate_by_package.get(challenge.parent.name)
        if aggregate_package is None:
            raise IntegrationError(
                f"per-entry package absent from aggregate authority: {challenge.parent.name}"
            )
        theorem_names = list(aggregate_package.theorem_names)
        rel_challenge = challenge.relative_to(ROOT).as_posix()
        rel_solution = solution.relative_to(ROOT).as_posix()
        for path in (challenge, solution):
            digest_input.extend(path.relative_to(ROOT).as_posix().encode("utf-8"))
            digest_input.extend(b"\0")
            digest_input.extend(path.read_bytes())
            digest_input.extend(b"\0")
        packages.append(
            {
                "package_id": challenge.parent.name,
                "challenge": rel_challenge,
                "solution": rel_solution,
                "lake_target": challenge.parent.name,
                "axiom_audit": (
                    axiom_audit.relative_to(ROOT).as_posix()
                    if axiom_audit.is_file()
                    else None
                ),
                "interface_count": len(theorem_names),
                "interface_names": theorem_names,
                "interface_leaf_names": [name.rsplit(".", 1)[-1] for name in theorem_names],
                "assurance_status": "needs_current_commit_bound_comparator_replay",
            }
        )
    aggregate_config_path = ROOT / "verification" / "comparator-replay-candidate.json"
    aggregate_membership_path = ROOT / "verification" / "comparator-replay-membership.json"
    aggregate_config = load_json(aggregate_config_path)
    aggregate_membership = load_json(aggregate_membership_path)
    claim_coverage = aggregate.registered_claim_coverage
    if aggregate_membership.get("registered_claim_coverage") != claim_coverage:
        raise IntegrationError("registered-claim transport projection is stale")
    family_coverage = aggregate_membership.get("result_family_coverage", {})
    if aggregate_config.get("theorem_names") != list(aggregate.theorem_names):
        raise IntegrationError(
            "aggregate Comparator replay config differs from current package discovery"
        )
    if {row.name for row in aggregate.packages} != {
        row["package_id"] for row in packages
    }:
        raise IntegrationError(
            "aggregate Comparator replay packages differ from paper integration"
        )
    execution_counts = family_coverage.get("execution_classification_counts", {})
    if (
        family_coverage.get("schema")
        != "plectis.comparator-result-family-coverage/1"
        or family_coverage.get("registered_family_count")
        != family_coverage.get("classified_family_count")
        or sum(execution_counts.values())
        != family_coverage.get("registered_family_count")
    ):
        raise IntegrationError(
            "aggregate Comparator result-family coverage is incomplete"
        )
    return {
        "portfolio_id": "dynamic_comparator_replay_candidate",
        "status": "needs_current_commit_bound_comparator_replay",
        "package_count": len(packages),
        "interface_count": len(aggregate.theorem_names),
        "source_digest": "sha256:" + hashlib.sha256(digest_input).hexdigest(),
        "packages": packages,
        "aggregate_config": aggregate_config_path.relative_to(ROOT).as_posix(),
        "aggregate_config_digest": digest(aggregate_config_path),
        "aggregate_membership": aggregate_membership_path.relative_to(ROOT).as_posix(),
        "aggregate_membership_digest": digest(aggregate_membership_path),
        "registered_claim_coverage": {
            **{key: claim_coverage[key] for key in (
                "registry_authority", "registry_digest", "registered_claim_count",
                "classified_claim_count", "classification_counts", "formal_claim_count",
                "linked_transport_claim_count", "missing_formal_transport_count",
                "complete_formal_transport_coverage", "boundary",
            )},
            "source": "verification/comparator-replay-membership.json::registered_claim_coverage",
            "atom_level_coverage": "not_asserted_by_family_membership",
        },
        "result_family_coverage": {
            "registered_family_count": family_coverage[
                "registered_family_count"
            ],
            "classified_family_count": family_coverage[
                "classified_family_count"
            ],
            "execution_classification_counts": execution_counts,
            "family_linked_current_interface_count": family_coverage[
                "family_linked_current_interface_count"
            ],
            "family_linked_replay_candidate_interface_count": family_coverage[
                "family_linked_replay_candidate_interface_count"
            ],
            "boundary": (
                "Every registered family has either an executable Challenge package "
                "or an explicit disposition-backed non-executable reason. This is "
                "coverage metadata, not a Comparator run or review receipt."
            ),
        },
        "aggregate_challenge_module": aggregate_config["challenge_module"],
        "aggregate_solution_module": aggregate_config["solution_module"],
        "aggregate_projection_status": "current_replay_candidate_config",
        "generation_check": "python3 scripts/build_comparator_replay_portfolio.py --check",
        "focused_test": "python3 scripts/test_comparator_replay_portfolio.py",
        "replay_route": "docs/EXTERNAL_VERIFICATION_REPLAY.md",
        "historical_external_execution": "docs/PALOMAR_EXTERNAL_EXECUTION.json",
        "boundary": (
            "These in-tree Challenge/Solution pairs preserve the former Palomar "
            "per-entry portfolio. A current aggregate Comparator config is generated "
            "dynamically from every eligible package; the propositions remain replay "
            "candidates until a green commit-bound Comparator receipt exists. "
            "Historical success does not transfer."
        ),
    }


def load_order(palomar: dict[str, Any]) -> list[dict[str, Any]]:
    rows = palomar.get("family_display_order")
    if not isinstance(rows, list):
        raise IntegrationError(
            "docs/PALOMAR_RESULT_SHOWCASE.json has no family_display_order array"
        )
    if not all(isinstance(row, dict) for row in rows):
        raise IntegrationError("Palomar family_display_order rows must be objects")
    rows = list(rows)
    rows.sort(key=lambda row: int(row["global_display_order"]))
    return rows


def render_order(rows: list[dict[str, Any]]) -> str:
    return "".join(
        json.dumps(row, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n"
        for row in rows
    )


def declaration_index(atlas: dict[str, Any]) -> dict[str, dict[str, Any]]:
    """Return only declaration leaf names that are unique across the atlas."""
    candidates: dict[str, list[dict[str, Any]]] = {}
    for row in atlas.get("declarations", []):
        candidates.setdefault(str(row["name"]), []).append(row)
    return {name: rows[0] for name, rows in candidates.items() if len(rows) == 1}


def latex_text(value: object) -> str:
    text = str(value)
    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
        "ℕ": r"\ensuremath{\mathbb{N}}",
        "ℤ": r"\ensuremath{\mathbb{Z}}",
        "ℚ": r"\ensuremath{\mathbb{Q}}",
        "ℝ": r"\ensuremath{\mathbb{R}}",
        "₀": r"\ensuremath{_{0}}",
        "·": r"\ensuremath{\mathbin{\cdot}}",
        "→": r"\ensuremath{\to}",
        "↦": r"\ensuremath{\mapsto}",
        "∈": r"\ensuremath{\in}",
        "∉": r"\ensuremath{\notin}",
        "−": r"\ensuremath{-}",
        "√": r"\ensuremath{\surd}",
        "≠": r"\ensuremath{\ne}",
        "≤": r"\ensuremath{\le}",
        "≥": r"\ensuremath{\ge}",
        "∞": r"\ensuremath{\infty}",
        "π": r"\ensuremath{\pi}",
        "ρ": r"\ensuremath{\rho}",
        "μ": r"\ensuremath{\mu}",
    }
    return "".join(replacements.get(char, char) for char in text)


def family_title(family_id: str) -> str:
    return family_id.replace("_", " ").capitalize()


def build() -> tuple[dict[str, Any], dict[Path, str], str]:
    claims = load_json(CLAIMS)
    atlas = load_json(ATLAS)
    palomar = load_json(PALOMAR)
    placement = load_json(PLACEMENT_SOURCE)
    claim_families = flatten_claim_families(claims)
    comparator_assurance, comparator_summary, comparator_config_path = (
        build_comparator_assurance(claims, claim_families)
    )
    per_entry_comparator = discover_per_entry_comparator_portfolio()
    order = load_order(palomar)
    order_projection = render_order(order)
    atlas_by_leaf = declaration_index(atlas)
    atom_rows = load_result_atoms(RESULT_ATOMS)
    # Validate atoms against the authored Palomar order selected above, not the
    # previous generated JSONL. This lets one owner build add/reorder a family
    # atomically instead of deadlocking on its own stale projection.
    atom_summary = validate_result_atoms(
        atom_rows,
        claims,
        family_display_order=order,
    )
    if atom_summary["zero_family_ids"]:
        raise IntegrationError(
            "every public result family must contain at least one atom; missing="
            f"{atom_summary['zero_family_ids']}"
        )
    paper_problems = tuple(sorted(FRAGMENTS))

    family_total = len(claim_families)
    if not family_total or len(order) != family_total:
        raise IntegrationError(
            "claim and display-order family populations differ: "
            f"{family_total} and {len(order)}"
        )
    positions = [int(row["global_display_order"]) for row in order]
    if positions != list(range(1, family_total + 1)):
        raise IntegrationError("global display positions are not contiguous")
    order_keys = {
        (int(row["erdos_number"]), row["family_id"])
        for row in order
    }
    if order_keys != set(claim_families):
        missing = sorted(set(claim_families) - order_keys)
        extra = sorted(order_keys - set(claim_families))
        raise IntegrationError(f"family order mismatch; missing={missing}, extra={extra}")
    band_counts = Counter(row["display_band"]["band"] for row in order)
    unknown_bands = sorted(set(band_counts) - set(DISPLAY_BANDS))
    if unknown_bands:
        raise IntegrationError(
            f"display order uses unknown bands: {unknown_bands}"
        )
    promoted = sum(row["editorial_disposition"] == "promote" for row in order)

    placement_problems = placement.get("problems", {})
    if tuple(sorted(int(key) for key in placement_problems)) != paper_problems:
        raise IntegrationError("paper placement does not cover every configured problem paper")

    families: list[dict[str, Any]] = []
    problems: list[dict[str, Any]] = []
    fragments: dict[Path, str] = {}
    total_short = 0

    for problem in paper_problems:
        problem_id = f"erdos_{problem}"
        placement_row = placement_problems[str(problem)]
        short_ids = tuple(placement_row["short_family_ids"])
        problem_rows = [row for row in order if int(row["erdos_number"]) == problem]
        problem_keys = {row["family_id"] for row in problem_rows}
        unknown_short = sorted(set(short_ids) - problem_keys)
        if unknown_short:
            raise IntegrationError(f"problem {problem} has unknown short families: {unknown_short}")
        total_short += len(short_ids)

        rendered_rows: list[str] = [
            "\\clearpage\n",
            f"\\section{{Complete result-family map}}\\label{{sec:erdos-{problem}-complete-family-map}}\n\n",
            "This section places every registered family for this problem in the shared "
            f"{family_total}-family reader order.  The five display bands control exposition only; "
            f"the separate promotion state currently covers {promoted} families and is reported "
            "but does not hide or "
            "strengthen any family.  Mathematical statements and evidence modes come "
            "from the public claim registry.  Across all eight problems the public "
            f"result-atom catalog contains {atom_summary['total']} exact packet "
            f"coordinates; this problem contributes {atom_summary['problem_counts'][problem_id]}.  "
            "Catalog rows expose bounded statement excerpts plus full-source digests, "
            "not a claim that every complete packet statement is reproduced here.\n\n",
        ]

        for row in problem_rows:
            key = (problem, row["family_id"])
            claim = claim_families[key]
            family_comparator = comparator_assurance[key]
            admitted = row["family_id"] in short_ids
            declarations = claim.get("declarations", [])
            declaration_bindings = []
            for declaration in declarations:
                atlas_row = atlas_by_leaf.get(str(declaration).rsplit(".", 1)[-1])
                binding = {
                    "declaration": declaration,
                    "binding_status": (
                        "resolved_in_canonical_declaration_atlas"
                        if atlas_row is not None
                        else "unresolved_in_canonical_declaration_atlas"
                    ),
                    "source_currentness": "not_asserted_by_this_projection",
                }
                if atlas_row is not None:
                    binding.update(
                        {
                            "atlas_id": atlas_row["id"],
                            "module": atlas_row["module"],
                            "line": atlas_row["line"],
                            "kind": atlas_row["kind"],
                        }
                    )
                declaration_bindings.append(binding)
            family = {
                "problem_id": problem_id,
                "erdos_number": problem,
                "family_id": row["family_id"],
                "global_display_order": row["global_display_order"],
                "display_band": row["display_band"],
                "editorial_disposition": row["editorial_disposition"],
                "claim_summary": claim.get("summary"),
                "contribution_class": claim.get("contribution_class"),
                "evidence_mode": public_evidence_mode(claim.get("evidence_mode", "")),
                "declarations": declarations,
                "declaration_bindings": declaration_bindings,
                "result_binding": {
                    "family_key": row["object_key"],
                    "formal_promotion": row["editorial_disposition"] == "promote",
                    "public_result_id": None,
                    "public_dossier": None,
                    "status": (
                        "promoted_family_pending_public_result_identity_and_dossier"
                        if row["editorial_disposition"] == "promote"
                        else "visible_family_not_formally_promoted"
                    ),
                },
                "result_atoms": {
                    "count": atom_summary["family_counts"][row["family_id"]],
                    "catalog": "docs/result-atoms.jsonl",
                    "query": (
                        "python3 scripts/query_corpus.py --family-atoms "
                        f"{row['family_id']}"
                    ),
                    "statement_scope": (
                        "bounded_excerpts_plus_full_source_statement_digests"
                    ),
                },
                "comparator_assurance": family_comparator,
                "exact_boundary": claim.get("boundary"),
                "paper_placement": {
                    "long_form": "include",
                    "short_form": "include" if admitted else "long_form_only",
                    "short_form_basis": (
                        "selected by the independent short-form mathematical admission gate"
                        if admitted
                        else "complete context, equivalence, routine identity, support mechanism, or lower-priority boundary retained in the long record"
                    ),
                    "short_paper": placement_row["short_paper"],
                    "long_paper": placement_row["long_paper"],
                },
                "authority_refs": {
                    "claim_family": (
                        "docs/claims.json::external_verification_packet.review_matrix"
                        f"[problem={problem}].families[id={row['family_id']}]"
                    ),
                    "display_order": (
                        "docs/PALOMAR_RESULT_SHOWCASE.json::family_display_order"
                        f"[object_key={row['object_key']}]"
                    ),
                    "declaration_atlas": "docs/declaration_atlas.json",
                    "comparator": (
                        "docs/claims.json::external_verification_packet.main_results"
                    ),
                    "comparator_config": "verification/comparator.json",
                },
            }
            families.append(family)

            band = row["display_band"]["band"].replace("_", " ")
            disposition = row["editorial_disposition"].replace("_", " ")
            placement_sentence = (
                "This family is also admitted to the short note."
                if admitted
                else "This family remains in the complete long record and is not a short-note headline."
            )
            family_atom_count = atom_summary["family_counts"][row["family_id"]]
            atom_population_sentence = (
                f"{family_atom_count} of {atom_summary['total']} public coordinates. "
                "The public atom catalog groups them under this family."
                if family_atom_count
                else (
                    f"0 of {atom_summary['total']} public coordinates.  The family "
                    "remains visible because atom population does not govern family visibility."
                )
            )
            comparator_sentence = (
                family_comparator["status"].replace("_", " ")
                + f"; {family_comparator['executable_interface_count']} executable "
                + "interface(s), "
                + f"{family_comparator['registered_interface_count']} "
                + "repository-registered selected result interface(s)."
            )
            rendered_rows.extend(
                [
                    f"\\subsection{{{latex_text(family_title(row['family_id']))}}}\n",
                    f"\\textbf{{Reader position.}} {row['global_display_order']} of {family_total}; "
                    f"display band: {latex_text(band)}.  Formal editorial disposition: "
                    f"{latex_text(disposition)}.  These are separate classifications.\n\n",
                    f"\\textbf{{Reader entry.}} {latex_text(row['display_band']['reader_hook'])}\n\n",
                    f"{latex_text(claim.get('summary', ''))}\n\n",
                    f"\\textbf{{Authority and reach.}} {latex_text(public_evidence_mode(claim.get('evidence_mode', '')))}; "
                    f"{latex_text(claim.get('contribution_class', ''))}.\n\n",
                    f"\\textbf{{Exact boundary.}} {latex_text(claim.get('boundary', ''))}\n\n",
                    f"\\textbf{{Result-atom population.}} {atom_population_sentence}\n\n",
                    f"\\textbf{{Comparator assurance.}} {latex_text(comparator_sentence)}\n\n",
                    f"\\textbf{{Publication placement.}} {placement_sentence}\n\n",
                ]
            )
            if declarations:
                rendered_rows.append("\\begin{itemize}\n")
                for declaration in declarations:
                    rendered_rows.append(
                        f"  \\item \\nolinkurl{{{declaration}}}\n"
                    )
                rendered_rows.append("\\end{itemize}\n\n")

        fragments[FRAGMENTS[problem]] = "".join(rendered_rows)
        problems.append(
            {
                "problem_id": problem_id,
                "erdos_number": problem,
                "short_paper": placement_row["short_paper"],
                "long_paper": placement_row["long_paper"],
                "long_family_count": len(problem_rows),
                "short_family_count": len(short_ids),
                "long_family_ids_in_reader_order": [row["family_id"] for row in problem_rows],
                "short_family_ids": list(short_ids),
                "result_atom_count": atom_summary["problem_counts"][problem_id],
                "long_form_coverage_complete": True,
            }
        )

    output = {
        "schema": "plectis.paper-result-integration/2",
        "status": "complete_public_projection",
        "release_ready": True,
        "authority_boundary": placement["authority_boundary"],
        "assurance_portfolios": {
            "release_selected": {
                "status": "current_release_comparator_roster",
                "config": "verification/comparator.json",
                "registered_selected_interface_count": comparator_summary[
                    "registered_selected_interface_count"
                ],
                "theorem_count": comparator_summary["comparator_theorem_count"],
                "family_classification": "families[].comparator_assurance",
            },
            "dynamic_comparator_replay_candidate": per_entry_comparator,
        },
        "policies": {
            "long_form": placement["long_form_policy"],
            "short_form": placement["short_form_policy"],
            "display_vs_promotion": "Display band orders exposition; formal promotion remains a separate state and does not control visibility.",
            "palomar_vs_comparator": (
                "Palomar supplies qualitative reader order and display bands. "
                "Comparator checks exact separately declared Lean propositions and "
                "the configured axiom budget. Neither confers novelty, significance, "
                "peer review, or an open-problem solution. Result atoms inherit their "
                "family's Comparator classification; they do not each require a "
                "duplicated challenge theorem."
            ),
            "source_currentness": {
                "posture": "not_asserted_by_this_projection",
                "delta_sensitive_problems": ["erdos_251", "erdos_269", "erdos_1041", "erdos_1049"],
                "rule": "Atlas resolution is a declaration/source locator only. Newly reported source deltas require their owning canonical refresh and receipt before any currentness claim.",
            },
        },
        "inputs": {
            "claims": {"path": "docs/claims.json", "digest": digest(CLAIMS)},
            "declaration_atlas": {
                "path": "docs/declaration_atlas.json",
                "digest": digest(ATLAS),
                "source_fingerprint": atlas.get("source_fingerprint"),
            },
            "palomar_showcase": {
                "path": "docs/PALOMAR_RESULT_SHOWCASE.json",
                "digest": digest(PALOMAR),
                "selector": "family_display_order",
            },
            "placement": {
                "path": "paper/paper-result-integration-source.json",
                "digest": digest(PLACEMENT_SOURCE),
            },
            "family_order": {
                "path": "docs/family-display-order.jsonl",
                "digest": "sha256:" + hashlib.sha256(order_projection.encode("utf-8")).hexdigest(),
                "visibility": "public_generated_projection",
            },
            "result_atoms": {
                "path": "docs/result-atoms.jsonl",
                "digest": digest(RESULT_ATOMS),
                "statement_scope": (
                    "bounded_excerpts_plus_full_source_statement_digests"
                ),
            },
            "comparator": {
                "path": str(comparator_config_path.relative_to(ROOT)),
                "digest": digest(comparator_config_path),
                "registered_claim_source": (
                    "docs/claims.json::external_verification_packet.main_results"
                ),
            },
        },
        "counts": {
            "problem_count": len(paper_problems),
            "family_count": family_total,
            "long_form_routed_family_count": family_total,
            "short_form_admitted_family_count": total_short,
            "formal_promotion_count": promoted,
            "result_atom_count": atom_summary["total"],
            "populated_family_count": atom_summary["populated_family_count"],
            "zero_atom_family_count": len(atom_summary["zero_family_ids"]),
            "comparator_classified_family_count": comparator_summary[
                "classified_family_count"
            ],
            "comparator_registered_selected_interface_count": comparator_summary[
                "registered_selected_interface_count"
            ],
            "comparator_theorem_count": comparator_summary[
                "comparator_theorem_count"
            ],
            "comparator_family_linked_executable_interface_count": comparator_summary[
                "family_linked_executable_interface_count"
            ],
            "comparator_unregistered_executable_interface_count": comparator_summary[
                "unregistered_executable_interface_count"
            ],
            "comparator_unassociated_unregistered_interface_count": comparator_summary[
                "unassociated_unregistered_interface_count"
            ],
            "comparator_family_status_counts": comparator_summary[
                "family_status_counts"
            ],
            "result_atoms_with_inherited_comparator_classification": atom_summary[
                "total"
            ],
            "dynamic_comparator_replay_package_count": per_entry_comparator[
                "package_count"
            ],
            "dynamic_comparator_replay_interface_count": per_entry_comparator[
                "interface_count"
            ],
            "comparator_executable_family_count": per_entry_comparator[
                "result_family_coverage"
            ]["execution_classification_counts"][
                "has_executable_challenge_package"
            ],
            "comparator_intentionally_non_executable_family_count": per_entry_comparator[
                "result_family_coverage"
            ]["execution_classification_counts"]["intentionally_non_executable"],
            "result_atom_interpretation_state_counts": atom_summary[
                "state_counts"
            ],
            "band_counts": {
                band: band_counts.get(band, 0) for band in DISPLAY_BANDS
            },
            "missing_long_form_route_count": 0,
            "duplicate_long_form_route_count": 0,
        },
        "problems": problems,
        "families": families,
        "validation": {
            "write": "python3 scripts/build_paper_result_integration.py --write",
            "check": "python3 scripts/build_paper_result_integration.py --check",
            "long_form_coverage": (
                f"Every one of the {family_total} family keys occurs once and only "
                "once in a problem long-form route."
            ),
            "source_currentness_boundary": "Declaration bindings locate claim-declared names in the canonical atlas; this projection does not independently assert source currentness.",
            "comparator_coverage": (
                f"All {family_total} families and all {atom_summary['total']} result "
                "atoms resolve to one explicit Comparator classification; the "
                f"registered selected interface count remains {len(claims['external_verification_packet']['main_results'])}."
            ),
        },
    }
    return output, fragments, order_projection


def render_json(value: dict[str, Any]) -> str:
    return json.dumps(value, indent=2, ensure_ascii=False) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--write", action="store_true")
    action.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        output, fragments, order_projection = build()
    except (IntegrationError, OSError, KeyError, TypeError, ValueError) as exc:
        print(f"build_paper_result_integration: {exc}", file=sys.stderr)
        return 2

    expected = {PUBLIC_ORDER: order_projection, OUTPUT: render_json(output), **fragments}
    stale = [
        path
        for path, content in expected.items()
        if not path.is_file() or path.read_text(encoding="utf-8") != content
    ]
    if args.check:
        if stale:
            print(
                "paper result integration is stale: "
                + ", ".join(str(path.relative_to(ROOT)) for path in stale),
                file=sys.stderr,
            )
            return 1
        print(
            "paper result integration current: "
            f"{output['counts']['long_form_routed_family_count']}/"
            f"{output['counts']['family_count']} long-form families, "
            f"{output['counts']['short_form_admitted_family_count']} short-form admissions, "
            "family-order visibility=public_generated_projection"
        )
        return 0

    # Match the repository's projection-builder convention: no option writes,
    # while --write remains an explicit compatibility spelling.
    for path, content in expected.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.is_file() or path.read_text(encoding="utf-8") != content:
            path.write_text(content, encoding="utf-8")
    print(
        "wrote paper result integration: "
        f"{output['counts']['long_form_routed_family_count']}/"
        f"{output['counts']['family_count']} long-form families, "
        f"{output['counts']['short_form_admitted_family_count']} short-form admissions, "
        "family-order visibility=public_generated_projection"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
