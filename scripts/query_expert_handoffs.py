#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Query exact mathematical and systems handoffs, or validate a human response.

The default is a bounded six-question index.  Open one complete handoff with
``--question QUESTION_ID``; use ``--domain systems`` for the complete
ten-minute reader protocol.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from collections import Counter
from datetime import date
from functools import lru_cache
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parent.parent
FRONTIER = ROOT / "docs" / "semantic" / "frontier.json"
ATLAS = ROOT / "docs" / "declaration_atlas.json"
PROTOCOL = ROOT / "docs" / "expert_review_protocol.json"
PALOMAR = ROOT / "docs" / "PALOMAR_RESULT_SHOWCASE.json"
CLAIMS = ROOT / "docs" / "claims.json"
SCHEMA = "plectis_expert_review_protocol_v1"
MATH_DOMAIN = "mathematics"
SYSTEMS_DOMAIN = "systems"
DOMAINS = (MATH_DOMAIN, SYSTEMS_DOMAIN)
FROZEN_PROBLEMS = frozenset(
    {"68", "243", "249", "251", "257", "269", "1041", "1049"}
)
REQUIRED_QUESTION_FIELDS = (
    "id",
    "domain",
    "classification",
    "status",
    "exact_ask",
    "payoff",
    "boundary",
    "known_obstruction",
    "current_hypothesis",
)
# These are handoff roots, not a ranking.  Their hierarchy, source details,
# contribution class, and sibling order are read at query time from the same
# Claims/Palomar authority used by query_semantic.py.
SEMANTIC_HANDOFF_ROOT_FAMILIES = (
    "small_mismatch_criterion",
    "conditional_carry_escape",
)
THREE_PRIME_LCM_FAMILY = "three_prime_lcm_cells"
RANK_TWO_KERNEL_FAMILY = "rank_two_kernel_no_go"
HEIGHT_FIBRE_FAMILY = "height_fibre_and_shell"
DYADIC_ALPHABET_FAMILY = "dyadic_block_alphabet"
ACTUAL_LCM_SEPARATION_FAMILY = "actual_lcm_orbit_separation"
FIRST_HARMONIC_FAMILY = "first_harmonic_pivot_decomposition"

# Canonical source binding consumed by the three-prime handoff.  These are
# declaration identities, not a positional sample; coordinates and signatures
# are resolved from the declaration atlas and live Lean source at query time.
THREE_PRIME_SOURCE_DECLARATIONS = (
    "smoothPrefixLcm_eq_threePrimeHeight",
    "SameThreePrimeLogCell",
    "threePrimeHeight_eq_of_sameLogCell",
    "smoothPrefixLcm_eq_of_sameLogCell",
    "threePrimeKernelQ_eq_of_sameLogCell",
    "threePrimeHeight_firstLogStep",
    "threePrimeHeight_secondLogStep",
    "threePrimeHeight_thirdLogStep",
    "smoothPrefixLcm_firstLogStep",
    "smoothPrefixLcm_secondLogStep",
    "smoothPrefixLcm_thirdLogStep",
    "threePrimePositiveJumpSet_card",
    "threePrimeJumpSetWithOrigin_card",
)


@lru_cache(maxsize=16)
def load_json(path: Path) -> dict[str, Any]:
    """Load one authority document once per query process.

    Expert packets revisit the same large declaration atlas while validating
    every question.  Caching avoids reparsing it dozens of times, while the
    fresh process boundary preserves query-time source/Claims/Palomar reads.
    """
    return json.loads(path.read_text(encoding="utf-8"))


def mathematical_questions() -> list[dict[str, Any]]:
    rows = load_json(FRONTIER).get("expert_questions", [])
    declarations = {
        (row["module"], row["name"]): row
        for row in load_json(ATLAS).get("declarations", [])
    }
    # Coordinates are navigation data, not authored mathematical content.
    # Resolve them from the exhaustive live atlas so every expert-query surface
    # survives harmless source movement in the same way as semantic_corpus.json.
    for question in rows:
        for consumer in question.get("consumer_declarations", []):
            declaration = declarations.get(
                (consumer.get("module"), consumer.get("declaration"))
            )
            if declaration is not None:
                consumer["line"] = declaration["line"]
    return [{"domain": MATH_DOMAIN, **row} for row in rows]


def systems_questions() -> list[dict[str, Any]]:
    return list(load_json(PROTOCOL).get("questions", []))


def all_questions() -> list[dict[str, Any]]:
    return [*mathematical_questions(), *systems_questions()]


def _canonical_family_ranks(palomar: Mapping[str, Any]) -> dict[str, dict[str, int]]:
    """Read only Palomar's within-problem positions; never infer a global rank."""
    programme = palomar.get("selection_contract", {}).get("programme_family_order")
    if not isinstance(programme, list):
        raise ValueError("Palomar selection contract lacks programme_family_order")
    ranks: dict[str, dict[str, int]] = {}
    for programme_row in programme:
        problem = int(programme_row["problem"])
        family_ids = programme_row.get("family_ids")
        if not isinstance(family_ids, list):
            raise ValueError(f"Palomar programme order lacks family_ids for #{problem}")
        for programme_position, raw_family_id in enumerate(family_ids, start=1):
            family_id = str(raw_family_id)
            if family_id in ranks:
                raise ValueError(f"Palomar programme order repeats family {family_id!r}")
            ranks[family_id] = {
                "problem": problem,
                "programme_position": programme_position,
            }
    return ranks


def _claim_family_rows(claims: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    rows: dict[str, dict[str, Any]] = {}
    for block in claims.get("external_verification_packet", {}).get("review_matrix", []):
        for family in block.get("families", []):
            family_id = family.get("id")
            if not family_id:
                continue
            family_id = str(family_id)
            if family_id in rows:
                raise ValueError(f"Claims review matrix repeats family {family_id!r}")
            rows[family_id] = family
    return rows


def _palomar_family_row(palomar: Mapping[str, Any], family_id: str) -> dict[str, Any]:
    candidates = list(palomar.get("candidate_ranking", []))
    candidates.extend(
        palomar.get("candidate_value_dispositions", {}).get(
            "source_landscape_candidates", []
        )
    )
    matches = [row for row in candidates if row.get("family_id") == family_id]
    source_matches = [
        row for row in matches if row.get("source_declaration") or row.get("source_file")
    ]
    if len(source_matches) > 1:
        raise ValueError(
            f"Palomar must expose one exact source row for {family_id!r}; found {len(source_matches)}"
        )
    # A relation may deliberately retain a source-less no-go card. Keep that
    # evidence visible without fabricating a source declaration for it.
    return source_matches[0] if source_matches else {}


def _family_card(
    family_id: str,
    ranks: Mapping[str, Mapping[str, int]],
    palomar: Mapping[str, Any],
    claims: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any]:
    rank = ranks[family_id]
    claim = claims.get(family_id)
    if claim is None:
        raise ValueError(f"Claims review matrix lacks family {family_id!r}")
    source = _palomar_family_row(palomar, family_id)
    return {
        "family_id": family_id,
        "problem": rank["problem"],
        "authority_rank": {
            "programme_position": rank["programme_position"],
            "basis": (
                "docs/PALOMAR_RESULT_SHOWCASE.json::selection_contract."
                "programme_family_order"
            ),
            "boundary": "Within-problem order only; no cross-problem rank is inferred.",
        },
        "proof_status": claim.get("contribution_class"),
        "proof_status_authority": (
            "docs/claims.json::external_verification_packet.review_matrix"
            ".families[].contribution_class"
        ),
        "source_declaration": source.get("source_declaration"),
        "wrapper_declaration": source.get("comparator_declaration"),
        "source_route": source.get("source_file"),
        "source_anchor": source.get("source_anchor"),
        "mechanism": source.get("hard_mechanism"),
        "summary": claim.get("summary") or source.get("statement"),
        "open_boundary": claim.get("boundary"),
        "evidence_mode": claim.get("evidence_mode"),
        "limitations": source.get("limitations", []),
    }


def _relation_class(relation: str) -> str:
    if "contrary" in relation:
        return "natural_friction"
    if "support" in relation or relation == "mechanism_for":
        return "mechanism_support"
    if "peer" in relation:
        return "conditional_peer"
    return "other"


def _family_hierarchy(
    family_id: str,
    ranks: Mapping[str, Mapping[str, int]],
    palomar: Mapping[str, Any],
    claims: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any]:
    rows = []
    for relation in palomar.get("selection_contract", {}).get("family_relations", []):
        source = str(relation.get("from_family_id"))
        target = str(relation.get("to_family_id"))
        if family_id not in {source, target}:
            continue
        peer_id = target if family_id == source else source
        if peer_id not in ranks:
            raise ValueError(f"Palomar relation names unranked family {peer_id!r}")
        rows.append(
            {
                "direction": "outgoing" if family_id == source else "incoming",
                "relation": relation["relation"],
                "relation_class": _relation_class(str(relation["relation"])),
                "reason": relation["reason"],
                "peer": _family_card(peer_id, ranks, palomar, claims),
            }
        )
    rows.sort(
        key=lambda row: (
            row["peer"]["problem"],
            row["peer"]["authority_rank"]["programme_position"],
            row["relation"],
        )
    )
    return {
        "family": _family_card(family_id, ranks, palomar, claims),
        "relations": rows,
        "natural_friction_evidence": [
            row for row in rows if row["relation_class"] == "natural_friction"
        ],
        "follow": {
            "family": f"python3 scripts/query_semantic.py family-relations {family_id}",
            "problem": f"python3 scripts/query_corpus.py --route erdos_{ranks[family_id]['problem']}",
        },
    }


def _live_source_declaration(
    module: str, name: str, atlas: Mapping[str, Any]
) -> dict[str, Any]:
    """Join an atlas signature to the declaration's current source coordinate.

    The atlas supplies the exact checked signature and docstring, while the
    source file remains the coordinate authority.  This keeps a reader packet
    useful when a nearby proof grows without copying a second declaration
    inventory into the handoff script.
    """
    atlas_rows = [
        row
        for row in atlas.get("declarations", [])
        if row.get("module") == module and row.get("name") == name
    ]
    if len(atlas_rows) != 1:
        raise ValueError(
            f"declaration atlas must expose one {module}:{name}; "
            f"found {len(atlas_rows)}"
        )
    source_path = ROOT / module
    if not source_path.is_file():
        raise ValueError(f"source declaration module is missing: {module}")
    declaration_pattern = re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)*"
        r"(?:(?:noncomputable|protected|private)\s+)*"
        r"(?:theorem|lemma|def|abbrev)\s+" + re.escape(name) + r"\b"
    )
    live_line = next(
        (
            line_number
            for line_number, line in enumerate(
                source_path.read_text(encoding="utf-8").splitlines(), start=1
            )
            if declaration_pattern.search(line)
        ),
        None,
    )
    if live_line is None:
        raise ValueError(f"source file lacks declaration {module}:{name}")
    row = atlas_rows[0]
    return {
        "name": name,
        "kind": row.get("kind"),
        "module": module,
        "line": live_line,
        "signature": row.get("signature"),
        "docstring": row.get("docstring"),
        "coordinate_authority": "direct Lean source declaration",
        "signature_authority": "docs/declaration_atlas.json",
    }


def three_prime_lcm_cells_handoff(
    palomar: Mapping[str, Any] | None = None,
    claims: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Expose the exact #269 LCM-cell mechanism as a supporting handoff.

    ``three_prime_lcm_cells`` is a Palomar-screened structure family rather
    than one of the two endpoint roots.  Keep it in the same semantic packet
    as a supporting family, with source declarations resolved from the live
    Lean file and status/boundaries read from Claims.  The cross-family rows
    below are boundary context, not a new Palomar relation or rank store.
    """
    palomar = palomar or load_json(PALOMAR)
    claims_document = claims or load_json(CLAIMS)
    review_rows = _claim_family_rows(claims_document)
    review = review_rows.get(THREE_PRIME_LCM_FAMILY)
    if not isinstance(review, dict):
        raise ValueError("Claims review matrix lacks three_prime_lcm_cells")
    ranks = _canonical_family_ranks(palomar)
    rank = ranks.get(THREE_PRIME_LCM_FAMILY)
    if rank is None:
        raise ValueError("Palomar programme order lacks three_prime_lcm_cells")

    claim_rows = [
        *claims_document.get("claims", []),
        *claims_document.get("external_verification_packet", {}).get(
            "main_results", []
        ),
    ]
    claim = next(
        (
            row
            for row in claim_rows
            if row.get("review_family") == THREE_PRIME_LCM_FAMILY
            or row.get("id") == "three_prime_running_lcm"
        ),
        None,
    )
    if not isinstance(claim, dict):
        raise ValueError("Claims lacks the three_prime_running_lcm source claim")
    source_module = str(claim.get("original_source"))
    atlas = load_json(ATLAS)
    declarations = [
        _live_source_declaration(source_module, name, atlas)
        for name in THREE_PRIME_SOURCE_DECLARATIONS
    ]
    wrapper_name = str(claim.get("wrapper_declaration"))
    wrapper_module = "ExternalVerification/Solution.lean"
    wrapper_pattern = re.compile(
        r"^\s*theorem\s+" + re.escape(wrapper_name.rsplit(".", 1)[-1]) + r"\b"
    )
    wrapper_path = ROOT / wrapper_module
    wrapper_line = next(
        (
            line_number
            for line_number, line in enumerate(
                wrapper_path.read_text(encoding="utf-8").splitlines(), start=1
            )
            if wrapper_pattern.search(line)
        ),
        None,
    )
    if wrapper_line is None:
        raise ValueError(f"source file lacks wrapper declaration {wrapper_name}")

    for neighbour_family in (
        "conditional_carry_escape",
        "weighted_phase_carry_observer",
    ):
        if not isinstance(review_rows.get(neighbour_family), dict):
            raise ValueError(
                "Claims review matrix lacks #269 carry neighbour family "
                f"{neighbour_family}"
            )
    screening = [
        row
        for row in palomar.get("candidate_screening", [])
        if row.get("family_id") == THREE_PRIME_LCM_FAMILY
    ]
    if len(screening) != 1:
        raise ValueError("Palomar must expose one #269 three-prime screening row")

    related_specs = [
        {
            "family_id": "conditional_carry_escape",
            "relation": "open_actual_series_bridge_and_cofinal_escape",
            "relation_class": "boundary_context_not_palomar_edge",
            "reason": (
                "The cell/jump structure is the exact source-side material "
                "an actual-series bridge to the reduced carry would need to "
                "consume; Claims leaves both that bridge and cofinal escape open."
            ),
        },
        {
            "family_id": "weighted_phase_carry_observer",
            "relation": "source_structure_to_weighted_observer_context",
            "relation_class": "boundary_context_not_palomar_edge",
            "reason": (
                "The jump ratios expose the channel bases that a weighted-phase "
                "observer would need, but the weighted route still leaves its "
                "integral quotient coboundary and actual-series bridge open."
            ),
        },
    ]
    related_specs.sort(
        key=lambda row: (
            ranks[row["family_id"]]["problem"],
            ranks[row["family_id"]]["programme_position"],
        )
    )
    related_families = [
        {
            **{key: value for key, value in spec.items() if key != "family_id"},
            "family": _family_card(
                spec["family_id"], ranks, palomar, review_rows
            ),
        }
        for spec in related_specs
    ]

    return {
        "family": {
            "family_id": THREE_PRIME_LCM_FAMILY,
            "problem": rank["problem"],
            "authority_rank": {
                "programme_position": rank["programme_position"],
                "basis": (
                    "docs/PALOMAR_RESULT_SHOWCASE.json::selection_contract."
                    "programme_family_order"
                ),
                "boundary": (
                    "Within-problem order only; no cross-problem rank is inferred."
                ),
            },
            "palomar_disposition": screening[0].get("disposition"),
            "proof_status": review.get("contribution_class"),
            "proof_status_authority": (
                "docs/claims.json::external_verification_packet.review_matrix"
                ".families[three_prime_lcm_cells].contribution_class"
            ),
            "summary": review.get("summary"),
            "boundary": review.get("boundary"),
            "claim_id": claim.get("id"),
        },
        "hard_mechanism": (
            "For pairwise-distinct primes, smoothPrefixLcm_eq_threePrimeHeight "
            "identifies the literal running LCM with the product of the three "
            "maximal pure-power coordinates. SameThreePrimeLogCell fixes all "
            "three logarithmic coordinates, so the height, literal LCM, and "
            "kernel are constant on a cell. A one-coordinate log step multiplies "
            "the height/LCM by its prime, while disjoint positive jump channels "
            "have exactly 3*count values (or 3*count+1 with the common origin)."
        ),
        "source_declarations": declarations,
        "wrapper": {
            "declaration": wrapper_name,
            "module": wrapper_module,
            "line": wrapper_line,
            "source_authority": "direct Lean source declaration",
            "claim_authority": "docs/claims.json::claims[three_prime_running_lcm]",
        },
        "mechanism_cards": [
            {
                "id": "running_lcm_identity",
                "declaration_names": ["smoothPrefixLcm_eq_threePrimeHeight"],
                "wrapper_declaration": wrapper_name,
                "hard_mechanism": (
                    "The three pairwise-distinct prime powers are pairwise coprime; "
                    "their product is both the exact height and the running prefix LCM."
                ),
            },
            {
                "id": "log_cell_constancy",
                "declaration_names": [
                    "SameThreePrimeLogCell",
                    "threePrimeHeight_eq_of_sameLogCell",
                    "smoothPrefixLcm_eq_of_sameLogCell",
                    "threePrimeKernelQ_eq_of_sameLogCell",
                ],
                "hard_mechanism": (
                    "No logarithmic coordinate changes inside a cell, so neither "
                    "the height nor the reciprocal kernel can change there."
                ),
            },
            {
                "id": "coordinate_jumps_and_counts",
                "declaration_names": [
                    "threePrimeHeight_firstLogStep",
                    "threePrimeHeight_secondLogStep",
                    "threePrimeHeight_thirdLogStep",
                    "smoothPrefixLcm_firstLogStep",
                    "smoothPrefixLcm_secondLogStep",
                    "smoothPrefixLcm_thirdLogStep",
                    "threePrimePositiveJumpSet_card",
                    "threePrimeJumpSetWithOrigin_card",
                ],
                "hard_mechanism": (
                    "A single coordinate advance multiplies by its channel prime; "
                    "pairwise-distinct channels remain disjoint, giving the exact "
                    "finite jump cardinalities."
                ),
            },
        ],
        "natural_friction_evidence": [
            review.get("boundary"),
            "The finite cell/jump normal form leaves the infinite producer and "
            "actual-series identification untouched.",
        ],
        "open_producer_boundaries": {
            "actual_series_bridge": (
                "The bridge from the actual three-prime running-LCM series (or "
                "its rationality) to the carry systems consumed by the #269 "
                "conditional routes remains open."
            ),
            "cofinal_escape_producer": (
                "CofinalLocalWindowEscape, the denominator-dependent cofinal "
                "residue-window escape producer, is unproved; finite searches "
                "do not supply it."
            ),
            "endpoint": "Cell structure alone does not prove irrationality.",
        },
        "related_families": related_families,
        "relation_authority": (
            "Family positions and neighbour family cards come from Palomar and "
            "Claims; the two boundary-context labels above are a derived reader "
            "crosswalk, not an insertion-ordered relation store or a new Palomar edge."
        ),
        "authority": {
            "claims": "docs/claims.json::claims[three_prime_running_lcm] and external_verification_packet.review_matrix.families[three_prime_lcm_cells]",
            "palomar": "docs/PALOMAR_RESULT_SHOWCASE.json::candidate_screening and selection_contract.programme_family_order",
            "source": "ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean",
            "wrapper_source": "ExternalVerification/Solution.lean",
        },
        "follow": {
            "family": "python3 scripts/query_semantic.py family-relations three_prime_lcm_cells",
            "problem": "python3 scripts/query_corpus.py --route erdos_269",
        },
    }


def rank_two_kernel_no_go_handoff(
    palomar: Mapping[str, Any] | None = None,
    claims: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Expose the next source-bound #269 finite-kernel no-go consumer."""
    palomar = palomar or load_json(PALOMAR)
    claims_document = claims or load_json(CLAIMS)
    review_rows = _claim_family_rows(claims_document)
    review = review_rows.get(RANK_TWO_KERNEL_FAMILY)
    if not isinstance(review, dict):
        raise ValueError("Claims review matrix lacks rank_two_kernel_no_go")
    ranks = _canonical_family_ranks(palomar)
    rank = ranks.get(RANK_TWO_KERNEL_FAMILY)
    if rank is None:
        raise ValueError("Palomar programme order lacks rank_two_kernel_no_go")
    claim = next(
        (
            row
            for row in claims_document.get("external_verification_packet", {}).get(
                "main_results", []
            )
            if row.get("review_family") == RANK_TWO_KERNEL_FAMILY
        ),
        None,
    )
    if not isinstance(claim, dict):
        raise ValueError("Claims lacks the three_prime_kernel_minor source claim")
    source_module = str(claim.get("original_source"))
    source_names = (
        "kernel_235_origin",
        "kernel_235_two",
        "kernel_235_three",
        "kernel_235_six",
        "kernel_235_not_rankOne",
        "kernel_235_minor_eq_neg_one_fifteen",
    )
    atlas = load_json(ATLAS)
    declarations = [
        _live_source_declaration(source_module, name, atlas)
        for name in source_names
    ]
    wrapper_name = str(claim.get("wrapper_declaration"))
    wrapper_module = "ExternalVerification/Solution.lean"
    wrapper_pattern = re.compile(
        r"^\s*theorem\s+" + re.escape(wrapper_name.rsplit(".", 1)[-1]) + r"\b"
    )
    wrapper_path = ROOT / wrapper_module
    wrapper_line = next(
        (
            line_number
            for line_number, line in enumerate(
                wrapper_path.read_text(encoding="utf-8").splitlines(), start=1
            )
            if wrapper_pattern.search(line)
        ),
        None,
    )
    if wrapper_line is None:
        raise ValueError(f"source file lacks wrapper declaration {wrapper_name}")
    screening = [
        row
        for row in palomar.get("candidate_screening", [])
        if row.get("family_id") == RANK_TWO_KERNEL_FAMILY
    ]
    if len(screening) != 1:
        raise ValueError("Palomar must expose one rank-two screening row")
    canonical_relations = [
        row
        for row in palomar.get("selection_contract", {}).get(
            "family_relations", []
        )
        if row.get("from_family_id") == RANK_TWO_KERNEL_FAMILY
    ]
    canonical_relations.sort(
        key=lambda row: (
            ranks.get(str(row.get("to_family_id")), {}).get("problem", 10**9),
            ranks.get(str(row.get("to_family_id")), {}).get(
                "programme_position", 10**9
            ),
        )
    )
    return {
        "family": {
            "family_id": RANK_TWO_KERNEL_FAMILY,
            "problem": rank["problem"],
            "authority_rank": {
                "programme_position": rank["programme_position"],
                "basis": (
                    "docs/PALOMAR_RESULT_SHOWCASE.json::selection_contract."
                    "programme_family_order"
                ),
                "boundary": (
                    "Within-problem order only; no cross-problem rank is inferred."
                ),
            },
            "palomar_disposition": screening[0].get("disposition"),
            "proof_status": review.get("contribution_class"),
            "proof_status_authority": (
                "docs/claims.json::external_verification_packet.review_matrix"
                ".families[rank_two_kernel_no_go].contribution_class"
            ),
            "summary": review.get("summary"),
            "boundary": review.get("boundary"),
            "claim_id": claim.get("id"),
        },
        "hard_mechanism": (
            "The exact 2,3,5 lattice-kernel fixtures evaluate the origin, pure "
            "2- and 3-channel points, and their mixed point; the cross-product "
            "minor is nonzero (exactly -1/15), so this displayed kernel is not "
            "rank one."
        ),
        "source_declarations": declarations,
        "wrapper": {
            "declaration": wrapper_name,
            "module": wrapper_module,
            "line": wrapper_line,
            "source_authority": "direct Lean source declaration",
            "claim_authority": "docs/claims.json::claims[three_prime_kernel_minor]",
        },
        "natural_friction_evidence": [
            review.get("boundary"),
            "The finite minor rules out a separable shortcut but does not create "
            "a cofinal carry-escape producer.",
        ],
        "open_producer_boundaries": {
            "endpoint": "Failure of rank one does not itself imply irrationality.",
            "conditional_carry": (
                "Palomar’s contrary_evidence_for edge to conditional_carry_escape "
                "does not supply the cofinal residue-window escape or the actual-"
                "series-to-carry bridge."
            ),
        },
        "canonical_relations": canonical_relations,
        "related_families": [
            {
                "family": _family_card(
                    "conditional_carry_escape", ranks, palomar, review_rows
                ),
                "relation": "contrary_evidence_for",
                "relation_class": "canonical_palomar_edge",
                "reason": (
                    "The non-rank-one minor blocks a separable carry shortcut; "
                    "it does not supply conditional carry escape."
                ),
            }
        ],
        "relation_authority": (
            "The family position and contrary-evidence edge are read from Palomar; "
            "source status and the non-implication boundary come from Claims."
        ),
        "authority": {
            "claims": "docs/claims.json::claims[three_prime_kernel_minor] and external_verification_packet.review_matrix.families[rank_two_kernel_no_go]",
            "palomar": "docs/PALOMAR_RESULT_SHOWCASE.json::candidate_screening, selection_contract.programme_family_order, and family_relations",
            "source": "ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean",
            "wrapper_source": "ExternalVerification/Solution.lean",
        },
        "follow": {
            "family": "python3 scripts/query_semantic.py family-relations rank_two_kernel_no_go",
            "problem": "python3 scripts/query_corpus.py --route erdos_269",
        },
    }


def height_fibre_and_shell_handoff(
    palomar: Mapping[str, Any] | None = None,
    claims: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Expose the exact finite height-fibre and shell-bound consumer."""
    palomar = palomar or load_json(PALOMAR)
    claims_document = claims or load_json(CLAIMS)
    review_rows = _claim_family_rows(claims_document)
    review = review_rows.get(HEIGHT_FIBRE_FAMILY)
    if not isinstance(review, dict):
        raise ValueError("Claims review matrix lacks height_fibre_and_shell")
    ranks = _canonical_family_ranks(palomar)
    rank = ranks.get(HEIGHT_FIBRE_FAMILY)
    if rank is None:
        raise ValueError("Palomar programme order lacks height_fibre_and_shell")
    placements = [
        row
        for row in palomar.get("selection_contract", {}).get(
            "represented_family_placements", []
        )
        if row.get("family_id") == HEIGHT_FIBRE_FAMILY
    ]
    if len(placements) != 1:
        raise ValueError("Palomar must expose one height-fibre placement")
    declarations_claimed = review.get("declarations")
    if not isinstance(declarations_claimed, list) or len(declarations_claimed) != 2:
        raise ValueError("Claims height-fibre row must name its two declarations")
    source_module = "ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean"
    source_names = (
        "smoothHeightFiber_kernel_sum",
        "finiteSmoothKernelSum_groupedByHeight",
        "smoothExponentShell_card_quadratic",
    )
    atlas = load_json(ATLAS)
    declarations = [
        _live_source_declaration(source_module, name, atlas)
        for name in source_names
    ]
    claimed_names = {
        str(declaration).rsplit(".", 1)[-1] for declaration in declarations_claimed
    }
    if not claimed_names.issubset(set(source_names)):
        raise ValueError("Claims height-fibre declarations drifted from source")
    return {
        "family": {
            "family_id": HEIGHT_FIBRE_FAMILY,
            "problem": rank["problem"],
            "authority_rank": {
                "programme_position": rank["programme_position"],
                "basis": (
                    "docs/PALOMAR_RESULT_SHOWCASE.json::selection_contract."
                    "programme_family_order"
                ),
                "boundary": (
                    "Within-problem order only; no cross-problem rank is inferred."
                ),
            },
            "palomar_tier": placements[0].get("tier_id"),
            "palomar_judgement": placements[0].get("relative_judgement"),
            "proof_status": review.get("contribution_class"),
            "proof_status_authority": (
                "docs/claims.json::external_verification_packet.review_matrix"
                ".families[height_fibre_and_shell].contribution_class"
            ),
            "summary": review.get("summary"),
            "boundary": review.get("boundary"),
        },
        "hard_mechanism": (
            "The fiber-sum theorem rewrites a finite smooth lattice sum as exact "
            "height multiplicities times reciprocal heights. The grouped-by-height "
            "normal form makes cell constancy usable at finite level, while the "
            "sorted half-open shell theorem bounds each shell multiplicity by a "
            "quadratic function of the exponent budget."
        ),
        "source_declarations": declarations,
        "natural_friction_evidence": [
            review.get("boundary"),
            "The finite normal form controls multiplicity only; it does not create "
            "the missing divisibility bridge to an infinite carry contradiction.",
        ],
        "open_producer_boundaries": {
            "divisibility_bridge": (
                "The fibre and shell bounds do not provide the missing divisibility "
                "bridge from the actual three-prime series to a carry consumer."
            ),
            "endpoint": review.get("boundary"),
        },
        "authority": {
            "claims": "docs/claims.json::external_verification_packet.review_matrix.families[height_fibre_and_shell]",
            "palomar": "docs/PALOMAR_RESULT_SHOWCASE.json::selection_contract.represented_family_placements and programme_family_order",
            "source": source_module,
        },
        "follow": {
            "family": "python3 scripts/query_semantic.py family-relations height_fibre_and_shell",
            "problem": "python3 scripts/query_corpus.py --route erdos_269",
        },
    }


def dyadic_block_alphabet_handoff(
    palomar: Mapping[str, Any] | None = None,
    claims: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Expose the exact finite `{2,3,5}` dyadic-block alphabet consumer."""
    palomar = palomar or load_json(PALOMAR)
    claims_document = claims or load_json(CLAIMS)
    review_rows = _claim_family_rows(claims_document)
    review = review_rows.get(DYADIC_ALPHABET_FAMILY)
    if not isinstance(review, dict):
        raise ValueError("Claims review matrix lacks dyadic_block_alphabet")
    ranks = _canonical_family_ranks(palomar)
    rank = ranks.get(DYADIC_ALPHABET_FAMILY)
    if rank is None:
        raise ValueError("Palomar programme order lacks dyadic_block_alphabet")
    placements = [
        row
        for row in palomar.get("selection_contract", {}).get(
            "represented_family_placements", []
        )
        if row.get("family_id") == DYADIC_ALPHABET_FAMILY
    ]
    if len(placements) != 1:
        raise ValueError("Palomar must expose one dyadic-alphabet placement")
    source_module = "ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean"
    source_names = (
        "dyadicBlockBase235",
        "dyadicBlockBase235_cases",
        "dyadicBlockBase235_mem_interval",
    )
    atlas = load_json(ATLAS)
    declarations = [
        _live_source_declaration(source_module, name, atlas)
        for name in source_names
    ]
    claimed = review.get("declarations")
    if not isinstance(claimed, list) or {
        str(row).rsplit(".", 1)[-1] for row in claimed
    } != {"dyadicBlockBase235_cases"}:
        raise ValueError("Claims dyadic-alphabet declaration drifted from source")
    return {
        "family": {
            "family_id": DYADIC_ALPHABET_FAMILY,
            "problem": rank["problem"],
            "authority_rank": {
                "programme_position": rank["programme_position"],
                "basis": (
                    "docs/PALOMAR_RESULT_SHOWCASE.json::selection_contract."
                    "programme_family_order"
                ),
                "boundary": (
                    "Within-problem order only; no cross-problem rank is inferred."
                ),
            },
            "palomar_tier": placements[0].get("tier_id"),
            "palomar_judgement": placements[0].get("relative_judgement"),
            "proof_status": review.get("contribution_class"),
            "proof_status_authority": (
                "docs/claims.json::external_verification_packet.review_matrix"
                ".families[dyadic_block_alphabet].contribution_class"
            ),
            "summary": review.get("summary"),
            "boundary": review.get("boundary"),
        },
        "hard_mechanism": (
            "The dyadic block definition compresses the internal 3- and 5-power "
            "jumps together with the terminal factor 2. The exact case theorem "
            "reduces every actual radix to the four-symbol alphabet {2, 6, 10, 30}; "
            "the interval theorem supplies the bounded-radix interface consumed "
            "by finite carry checks."
        ),
        "source_declarations": declarations,
        "natural_friction_evidence": [
            review.get("boundary"),
            "A finite radix alphabet constrains local transitions but does not "
            "produce cofinal escape in the actual series.",
        ],
        "open_producer_boundaries": {
            "cofinal_escape": (
                "The finite alphabet does not supply the needed cofinal residue-"
                "window carry escape or an actual-series bridge."
            ),
            "endpoint": review.get("boundary"),
        },
        "authority": {
            "claims": "docs/claims.json::external_verification_packet.review_matrix.families[dyadic_block_alphabet]",
            "palomar": "docs/PALOMAR_RESULT_SHOWCASE.json::selection_contract.represented_family_placements and programme_family_order",
            "source": source_module,
        },
        "follow": {
            "family": "python3 scripts/query_semantic.py family-relations dyadic_block_alphabet",
            "problem": "python3 scripts/query_corpus.py --route erdos_269",
        },
    }


def actual_lcm_orbit_separation_handoff(
    palomar: Mapping[str, Any] | None = None,
    claims: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Expose the highest-ranked remaining #249 orbit-separation consumer."""
    palomar = palomar or load_json(PALOMAR)
    claims_document = claims or load_json(CLAIMS)
    review_rows = _claim_family_rows(claims_document)
    review = review_rows.get(ACTUAL_LCM_SEPARATION_FAMILY)
    if not isinstance(review, dict):
        raise ValueError("Claims review matrix lacks actual_lcm_orbit_separation")
    ranks = _canonical_family_ranks(palomar)
    rank = ranks.get(ACTUAL_LCM_SEPARATION_FAMILY)
    if rank is None:
        raise ValueError("Palomar programme order lacks actual_lcm_orbit_separation")
    claim = next(
        (
            row
            for row in claims_document.get("external_verification_packet", {}).get(
                "main_results", []
            )
            if row.get("review_family") == ACTUAL_LCM_SEPARATION_FAMILY
        ),
        None,
    )
    if not isinstance(claim, dict):
        raise ValueError("Claims lacks the actual-LCM separation source claim")
    source_specs = (
        (
            "Erdos249257/TotientActualLcmOrbitNonintegrality.lean",
            "irrational_totientSeries_iff_actualLcmOrbitNonintegralitySupply",
        ),
        (
            "Erdos249257/TotientActualLcmOrbitNonintegrality.lean",
            "irrational_totientSeries_of_actualLcmOrbitNonintegralitySupply",
        ),
        (
            "Erdos249257/TotientActualLcmOrbitSeparation.lean",
            "actualLcmTailOrbit_eq_scaled_totientSeries_sub_prefix",
        ),
        (
            "Erdos249257/TotientActualLcmOrbitSeparation.lean",
            "actualLcmTailOrbit_sub_rawApprox_eq",
        ),
        (
            "Erdos249257/TotientActualLcmOrbitSeparation.lean",
            "abs_actualLcmTailOrbit_sub_rawApprox_lt",
        ),
        (
            "Erdos249257/TotientActualLcmOrbitSeparation.lean",
            "PowerTwoActualLcmOrbitSeparationSupply",
        ),
        (
            "Erdos249257/TotientActualLcmOrbitSeparation.lean",
            "powerTwoActualPenultimateSignedMarginSupply_of_actualLcmOrbitSeparation",
        ),
        (
            "Erdos249257/TotientActualLcmOrbitSeparation.lean",
            "irrational_totientSeries_of_actualLcmOrbitSeparationSupply",
        ),
        (
            "Erdos249257/TotientActualLcmOrbitSign.lean",
            "actualLcmTailDiff_shift_pos",
        ),
        (
            "Erdos249257/TotientActualLcmOrbitSign.lean",
            "actualLcm_trueEndpointSurvivor_neg",
        ),
        (
            "Erdos249257/TotientActualLcmOrbitSign.lean",
            "actualLcm_integral_forces_topEdgeResidue",
        ),
    )
    atlas = load_json(ATLAS)
    declarations = [
        _live_source_declaration(module, name, atlas)
        for module, name in source_specs
    ]
    ranking_rows = [
        row
        for row in palomar.get("candidate_ranking", [])
        if row.get("family_id") == ACTUAL_LCM_SEPARATION_FAMILY
    ]
    if len(ranking_rows) != 1:
        raise ValueError("Palomar must expose one actual-LCM ranking row")
    canonical_relations = [
        row
        for row in palomar.get("selection_contract", {}).get(
            "family_relations", []
        )
        if row.get("to_family_id") == ACTUAL_LCM_SEPARATION_FAMILY
    ]
    canonical_relations.sort(
        key=lambda row: (
            ranks.get(str(row.get("from_family_id")), {}).get("problem", 10**9),
            ranks.get(str(row.get("from_family_id")), {}).get(
                "programme_position", 10**9
            ),
        )
    )
    return {
        "family": {
            "family_id": ACTUAL_LCM_SEPARATION_FAMILY,
            "problem": rank["problem"],
            "authority_rank": {
                "programme_position": rank["programme_position"],
                "basis": (
                    "docs/PALOMAR_RESULT_SHOWCASE.json::selection_contract."
                    "programme_family_order"
                ),
                "boundary": (
                    "Within-problem order only; no cross-problem rank is inferred."
                ),
            },
            "palomar_selection_status": ranking_rows[0].get("selection_status"),
            "proof_status": review.get("contribution_class"),
            "proof_status_authority": (
                "docs/claims.json::external_verification_packet.review_matrix"
                ".families[actual_lcm_orbit_separation].contribution_class"
            ),
            "summary": review.get("summary"),
            "boundary": review.get("boundary"),
            "claim_id": claim.get("claim_id"),
        },
        "hard_mechanism": (
            "The actual-LCM orbit is identified with a scaled totient series and "
            "a raw adjacent-suffix approximation whose explicit error radius is "
            "strictly controlled. A cofinal 1/32 separation supply therefore "
            "transfers to a signed-margin irrationality consumer; the sign and "
            "top-edge declarations show why positivity alone still leaves a true "
            "negative survivor and a residue strip to exclude."
        ),
        "source_declarations": declarations,
        "wrapper": {
            "declaration": claim.get("wrapper_declaration"),
            "module": "ExternalVerification/Solution.lean",
            "line": next(
                (
                    line_number
                    for line_number, line in enumerate(
                        (ROOT / "ExternalVerification/Solution.lean")
                        .read_text(encoding="utf-8")
                        .splitlines(),
                        start=1,
                    )
                    if re.search(
                        r"^\s*theorem\s+"
                        + re.escape(
                            str(claim.get("wrapper_declaration")).rsplit(".", 1)[-1]
                        )
                        + r"\b",
                        line,
                    )
                ),
                None,
            ),
            "source_authority": "direct Lean source declaration",
            "claim_authority": "docs/claims.json::external_verification_packet.main_results[actual_lcm_orbit_separation]",
        },
        "natural_friction_evidence": [
            review.get("boundary"),
            "The PowerTwoActualLcmOrbitSeparationSupply remains a premise, not a proved producer.",
        ],
        "open_producer_boundaries": {
            "cofinal_separation_supply": (
                "The quantitative 1/32 cofinal separation supply is open and is "
                "stronger than mere non-integrality."
            ),
            "top_edge_exclusion": (
                "Sign positivity and top-edge forcing leave the negative survivor "
                "and punctured/top-edge residue to exclude."
            ),
            "endpoint": "The cofinal supply and the #249 endpoint remain open.",
        },
        "canonical_relations": canonical_relations,
        "related_families": [
            {
                "family": _family_card(
                    str(row["from_family_id"]), ranks, palomar, review_rows
                ),
                "relation": row["relation"],
                "relation_class": "canonical_palomar_edge",
                "reason": row["reason"],
            }
            for row in canonical_relations
        ],
        "relation_authority": (
            "Producer-peer relations and positions come from Palomar; source "
            "status and open boundaries come from Claims and direct Lean declarations."
        ),
        "authority": {
            "claims": "docs/claims.json::external_verification_packet.main_results[actual_lcm_orbit_separation] and review_matrix.families[actual_lcm_orbit_separation]",
            "palomar": "docs/PALOMAR_RESULT_SHOWCASE.json::candidate_ranking, selection_contract.programme_family_order, and family_relations",
            "source": "Erdos249257/TotientActualLcmOrbitSeparation.lean and TotientActualLcmOrbitSign.lean",
            "wrapper_source": "ExternalVerification/Solution.lean",
        },
        "follow": {
            "family": "python3 scripts/query_semantic.py family-relations actual_lcm_orbit_separation",
            "problem": "python3 scripts/query_corpus.py --route erdos_249",
        },
    }


def first_harmonic_pivot_handoff(
    palomar: Mapping[str, Any] | None = None,
    claims: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Expose the exact #249 first-harmonic pivot consumer."""
    palomar = palomar or load_json(PALOMAR)
    claims_document = claims or load_json(CLAIMS)
    review_rows = _claim_family_rows(claims_document)
    review = review_rows.get(FIRST_HARMONIC_FAMILY)
    if not isinstance(review, dict):
        raise ValueError("Claims review matrix lacks first_harmonic_pivot_decomposition")
    ranks = _canonical_family_ranks(palomar)
    rank = ranks.get(FIRST_HARMONIC_FAMILY)
    if rank is None:
        raise ValueError("Palomar programme order lacks first_harmonic_pivot_decomposition")
    claim = next(
        (
            row
            for row in claims_document.get("external_verification_packet", {}).get(
                "main_results", []
            )
            if row.get("review_family") == FIRST_HARMONIC_FAMILY
        ),
        None,
    )
    if not isinstance(claim, dict):
        raise ValueError("Claims lacks the first-harmonic pivot source claim")
    source_module = "Erdos249257/FirstHarmonicPivot.lean"
    source_names = tuple(
        str(declaration).rsplit(".", 1)[-1]
        for declaration in review.get("declarations", [])
    )
    if len(source_names) != 9:
        raise ValueError("Claims first-harmonic row must name nine declarations")
    atlas = load_json(ATLAS)
    declarations = [
        _live_source_declaration(source_module, name, atlas)
        for name in source_names
    ]
    ranking_rows = [
        row
        for row in palomar.get("candidate_ranking", [])
        if row.get("family_id") == FIRST_HARMONIC_FAMILY
    ]
    if len(ranking_rows) != 1:
        raise ValueError("Palomar must expose one first-harmonic ranking row")
    wrapper_name = str(claim.get("wrapper_declaration"))
    wrapper_module = "ExternalVerification/Solution.lean"
    wrapper_pattern = re.compile(
        r"^\s*theorem\s+" + re.escape(wrapper_name.rsplit(".", 1)[-1]) + r"\b"
    )
    wrapper_line = next(
        (
            line_number
            for line_number, line in enumerate(
                (ROOT / wrapper_module).read_text(encoding="utf-8").splitlines(),
                start=1,
            )
            if wrapper_pattern.search(line)
        ),
        None,
    )
    if wrapper_line is None:
        raise ValueError(f"source file lacks wrapper declaration {wrapper_name}")
    canonical_relations = [
        row
        for row in palomar.get("selection_contract", {}).get(
            "family_relations", []
        )
        if row.get("from_family_id") == FIRST_HARMONIC_FAMILY
    ]
    canonical_relations.sort(
        key=lambda row: (
            ranks.get(str(row.get("to_family_id")), {}).get("problem", 10**9),
            ranks.get(str(row.get("to_family_id")), {}).get(
                "programme_position", 10**9
            ),
        )
    )
    return {
        "family": {
            "family_id": FIRST_HARMONIC_FAMILY,
            "problem": rank["problem"],
            "authority_rank": {
                "programme_position": rank["programme_position"],
                "basis": (
                    "docs/PALOMAR_RESULT_SHOWCASE.json::selection_contract."
                    "programme_family_order"
                ),
                "boundary": (
                    "Within-problem order only; no cross-problem rank is inferred."
                ),
            },
            "palomar_selection_status": ranking_rows[0].get("selection_status"),
            "proof_status": review.get("contribution_class"),
            "proof_status_authority": (
                "docs/claims.json::external_verification_packet.review_matrix"
                ".families[first_harmonic_pivot_decomposition].contribution_class"
            ),
            "summary": review.get("summary"),
            "boundary": review.get("boundary"),
            "claim_id": claim.get("claim_id"),
        },
        "hard_mechanism": (
            "Supplier fibres are identified exactly with prime-image fibres, and "
            "the four-term first-harmonic decomposition separates supplier, bad, "
            "non-supplier, and remainder contributions. Under the explicit "
            "PivotBudgetAt and dyadic-room hypotheses these bounds yield the 9X/10 "
            "gap; the DTWPivotResidualDecorrelation consumer then transfers a "
            "cofinal producer to irrationality."
        ),
        "source_declarations": declarations,
        "wrapper": {
            "declaration": wrapper_name,
            "module": wrapper_module,
            "line": wrapper_line,
            "source_authority": "direct Lean source declaration",
            "claim_authority": "docs/claims.json::external_verification_packet.main_results[first_harmonic_pivot_decomposition]",
        },
        "natural_friction_evidence": [
            review.get("boundary"),
            "The finite supplier-isolation counterexample prevents silently "
            "promoting fibre bijections to a prime-distribution theorem.",
        ],
        "open_producer_boundaries": {
            "pivot_budget": (
                "PivotBudgetAt and the dyadic-room inequality are explicit premises; "
                "no decorrelation estimate supplying them is proved."
            ),
            "cofinal_decorrelation": (
                "The cofinal decorrelation producer named "
                "DTWPivotResidualDecorrelation is not proved."
            ),
            "endpoint": "The #249 endpoint remains open.",
        },
        "canonical_relations": canonical_relations,
        "related_families": [
            {
                "family_id": row["to_family_id"],
                "relation": row["relation"],
                "relation_class": "canonical_palomar_edge",
                "reason": row["reason"],
            }
            for row in canonical_relations
        ],
        "relation_authority": (
            "Producer-peer relations and positions come from Palomar; source "
            "status and open premises come from Claims and direct Lean declarations."
        ),
        "authority": {
            "claims": "docs/claims.json::external_verification_packet.main_results[first_harmonic_pivot_decomposition] and review_matrix.families[first_harmonic_pivot_decomposition]",
            "palomar": "docs/PALOMAR_RESULT_SHOWCASE.json::candidate_ranking, selection_contract.programme_family_order, and family_relations",
            "source": source_module,
            "wrapper_source": wrapper_module,
        },
        "follow": {
            "family": "python3 scripts/query_semantic.py family-relations first_harmonic_pivot_decomposition",
            "problem": "python3 scripts/query_corpus.py --route erdos_249",
        },
    }


def semantic_endpoint_handoff_packet() -> dict[str, Any]:
    """Join the expert index to canonical endpoint-facing family packets.

    This reads the same Claims and Palomar source authorities as the semantic
    route. The compact expert route owns no parallel family store, and
    relation-array order never becomes a ranking rule.
    """
    palomar = load_json(PALOMAR)
    claims_document = load_json(CLAIMS)
    claims = _claim_family_rows(claims_document)
    ranks = _canonical_family_ranks(palomar)
    roots = [
        _family_hierarchy(family_id, ranks, palomar, claims)
        for family_id in SEMANTIC_HANDOFF_ROOT_FAMILIES
    ]
    supporting_families = [
        three_prime_lcm_cells_handoff(palomar, claims_document),
        rank_two_kernel_no_go_handoff(palomar, claims_document),
        height_fibre_and_shell_handoff(palomar, claims_document),
        dyadic_block_alphabet_handoff(palomar, claims_document),
        actual_lcm_orbit_separation_handoff(palomar, claims_document),
        first_harmonic_pivot_handoff(palomar, claims_document),
    ]
    supporting_families.sort(
        key=lambda row: (
            row["family"]["problem"],
            row["family"]["authority_rank"]["programme_position"],
        )
    )
    return {
        "question": (
            "Which endpoint-facing checked interfaces, supporting mechanisms, "
            "natural-friction evidence, and unsupplied producers should an "
            "expert inspect next?"
        ),
        "authority_posture": (
            "Derived expert-to-semantic handoff. Family status comes from "
            "Claims and hierarchy comes from Palomar; neither this packet nor "
            "Comparator transport is Lean proof authority."
        ),
        "authority": {
            "claims": (
                "docs/claims.json::external_verification_packet.review_matrix"
            ),
            "palomar": (
                "docs/PALOMAR_RESULT_SHOWCASE.json::selection_contract."
                "programme_family_order and family_relations"
            ),
            "rank_rule": (
                "Canonical within-problem programme position determines "
                "hierarchy; insertion order in a relation array never does."
            ),
        },
        "root_family_ids": list(SEMANTIC_HANDOFF_ROOT_FAMILIES),
        "roots": roots,
        "supporting_families": supporting_families,
        "coverage_boundary": (
            "This route highlights two endpoint-facing roots without replacing "
            "the all-eight-problem semantic registry or subordinate/long-tail "
            "family discovery. It also exposes the source-backed #269 "
            "three-prime structure as supporting context without promoting it "
            "to an endpoint. Use each family follow command and "
            "`python3 scripts/query_semantic.py problem-registry` for that "
            "complete inventory."
        ),
    }


def semantic_endpoint_handoff_route() -> dict[str, Any]:
    """Provide the discoverable narrow command without eagerly loading authority."""
    return {
        "command": "python3 scripts/query_expert_handoffs.py --semantic-handoff",
        "root_family_ids": list(SEMANTIC_HANDOFF_ROOT_FAMILIES),
        "authority_posture": (
            "Query-time Claims/Palomar projection; no second rank store."
        ),
    }


def source_current_supports(row: Mapping[str, Any]) -> list[dict[str, Any]]:
    """Expose source-current supporting declarations without minting a family.

    The strict-prime phase declarations belong inside the already-ranked
    ``strict_prime_tail_orbit_gap`` family.  They make its dynamics and its
    natural obstruction inspectable, but never add an endpoint route or relax
    the unsupplied density/cofinal-prime producers.
    """
    if str(row.get("problem") or "") != "249":
        return []
    claims = load_json(CLAIMS)
    family = next(
        (
            candidate
            for candidate in claims.get("claims", [])
            if candidate.get("id") == "strict_prime_tail_orbit_gap"
        ),
        None,
    )
    if not isinstance(family, dict):
        return []
    review = _claim_family_rows(claims).get("strict_prime_tail_orbit_gap", {})
    if not isinstance(review, dict):
        raise ValueError("Claims review matrix lacks strict_prime_tail_orbit_gap")

    declarations = {
        str(candidate.get("name")): candidate
        for candidate in family.get("declarations", [])
        if isinstance(candidate, dict) and candidate.get("name")
    }
    # This is evidence-role metadata for one source family, not a parallel
    # family, relation, or rank store.  Declarations and coordinates below are
    # re-read from Claims at query time.
    evidence_specs = (
        {
            "name": "tailOrbitFirstExp_succ",
            "relation": "support",
            "relation_class": "existing_family_support_only",
            "evidence_kind": "one_step_squaring",
            "hard_mechanism": (
                "The integer carry increment disappears after exponentiation, "
                "so each next phase is the square of the preceding phase."
            ),
            "evidence_boundary": (
                "This one-step recurrence makes the existing phase mechanism "
                "reviewable; it supplies no density, strict-prime occurrence, "
                "or uniform margin."
            ),
        },
        {
            "name": "tailOrbitFirstExp_add",
            "relation": "support",
            "relation_class": "existing_family_support_only",
            "evidence_kind": "all_times_squaring_orbit",
            "hard_mechanism": (
                "Every later phase is an exact power-of-two iterate of an "
                "earlier phase, so no additional carry information survives "
                "inside the phase orbit."
            ),
            "evidence_boundary": (
                "The all-times orbit formula classifies the route's phase "
                "dynamics only; it does not realize the missing density or "
                "cofinal-prime producer."
            ),
        },
        {
            "name": "naturalPrimeTailOrbitStrictGap_iff_initial_phase",
            "relation": "support",
            "relation_class": "existing_family_support_only",
            "evidence_kind": "initial_phase_equivalence",
            "hard_mechanism": (
                "The prime-index strict-gap predicate is exactly rewritten as "
                "a power-of-two orbit condition on the initial phase for each "
                "shift."
            ),
            "evidence_boundary": (
                "This equivalence locates the same strict-gap burden at an "
                "initial phase; it proves neither a prime occurrence nor a "
                "uniform separation margin."
            ),
        },
        {
            "name": "not_naturalPrimeTailOrbitStrictGap_of_dyadic_root",
            "relation": "contrary_evidence",
            "relation_class": "existing_family_contrary_evidence",
            "evidence_kind": "dyadic_root_obstruction",
            "hard_mechanism": (
                "A dyadic root reaches the absorbing phase 1 after finitely "
                "many squarings, which contradicts the cofinal strict-gap "
                "producer."
            ),
            "evidence_boundary": (
                "This is contrary evidence for the producer only: the source "
                "does not show that an actual totient phase enters a dyadic root."
            ),
        },
        {
            "name": "tailOrbitFirstExp_zero_eq_scaled_angle",
            "relation": "support",
            "relation_class": "existing_family_support_only",
            "evidence_kind": "scaled_angle_normal_form",
            "hard_mechanism": (
                "The initial tail phase is the exponential of the scaled angle "
                "(2^h - 1) times the series, fixing the exact starting point "
                "of the squaring orbit."
            ),
            "evidence_boundary": (
                "The scaled-angle identity supplies an exact coordinate change; "
                "it does not establish irrationality or phase density."
            ),
        },
        {
            "name": "tailOrbitFirstExp_eq_one_iff_tail_diff_mem_int",
            "relation": "support",
            "relation_class": "existing_family_support_only",
            "evidence_kind": "integral_tail_phase_equivalence",
            "hard_mechanism": (
                "Phase 1 is equivalent to an integral actual tail difference, "
                "so the analytic endpoint is expressed in the orbit's exact "
                "integer boundary."
            ),
            "evidence_boundary": (
                "This equivalence translates the endpoint condition; it does "
                "not show that the orbit reaches or avoids phase 1."
            ),
        },
        {
            "name": "exists_tailOrbitFirstExp_zero_pow_two_eq_one_iff_dyadic",
            "relation": "support",
            "relation_class": "existing_family_support_only",
            "evidence_kind": "dyadic_root_characterization",
            "hard_mechanism": (
                "A power-of-two iterate reaches phase 1 exactly when the initial "
                "phase is a dyadic root of unity, identifying the obstruction "
                "class without inventing a new route."
            ),
            "evidence_boundary": (
                "The characterization classifies a possible initial phase; it "
                "does not decide whether the actual series has that phase."
            ),
        },
        {
            "name": "tailOrbitFirstExp_zero_pow_two_ne_one_upto_sixteen",
            "relation": "contrary_evidence",
            "relation_class": "existing_family_contrary_evidence",
            "evidence_kind": "finite_nonroot_prefix",
            "hard_mechanism": (
                "The checked finite prefix excludes phase 1 for the first sixteen "
                "power-of-two iterates in the displayed non-dyadic setup."
            ),
            "evidence_boundary": (
                "Finite non-root evidence rules out only that bounded prefix; it "
                "is not a cofinal producer and does not settle the endpoint."
            ),
        },
        {
            "name": "cofinally_tailOrbitFirstExp_re_nonpos_of_not_dyadic",
            "relation": "support",
            "relation_class": "existing_family_support_only",
            "evidence_kind": "cofinal_nonpositive_phase",
            "hard_mechanism": (
                "A non-dyadic initial phase has cofinally many power-of-two "
                "iterates with nonpositive real part, supplying the sign-side "
                "phase mechanism consumed by the existing conditional family."
            ),
            "evidence_boundary": (
                "The cofinal sign statement still needs the configured density "
                "or prime-index margin to produce a strict endpoint gap."
            ),
        },
        {
            "name": "naturalPrimeTailOrbitStrictGap_of_cofinal_nonpositive_prime_shift",
            "relation": "support",
            "relation_class": "existing_family_support_only",
            "evidence_kind": "prime_shift_bridge",
            "hard_mechanism": (
                "Cofinal nonpositive phase on shifted natural-prime indices "
                "feeds the existing strict-gap predicate through the exact "
                "prime-shift bridge."
            ),
            "evidence_boundary": (
                "The bridge consumes a cofinal prime-shift hypothesis; it does "
                "not prove that hypothesis or the resulting irrationality."
            ),
        },
    )
    source_module = "ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean"
    atlas = load_json(ATLAS)
    result = []
    for spec in evidence_specs:
        declaration = declarations.get(spec["name"])
        if declaration is None:
            raise ValueError(
                "Claims strict-prime family lacks source declaration "
                f"{spec['name']!r}"
            )
        if declaration.get("module") != source_module:
            raise ValueError(
                "Claims strict-prime family routes source declaration outside "
                f"{source_module}: {spec['name']!r}"
            )
        live = _live_source_declaration(source_module, spec["name"], atlas)
        result.append(
            {
                "relation": spec["relation"],
                "relation_class": spec["relation_class"],
                "evidence_kind": spec["evidence_kind"],
                "family_id": "strict_prime_tail_orbit_gap",
                "proof_status": review.get("contribution_class"),
                "proof_status_authority": (
                    "docs/claims.json::external_verification_packet.review_matrix"
                    ".families[strict_prime_tail_orbit_gap].contribution_class"
                ),
                "source_declaration": (
                    f"ErdosProblems.Erdos249.{spec['name']}"
                ),
                "source": {
                    "module": live["module"],
                    "line": live["line"],
                    "signature": live.get("signature"),
                },
                "hard_mechanism": spec["hard_mechanism"],
                "evidence_boundary": spec["evidence_boundary"],
                "natural_friction_evidence": review.get("boundary"),
                "open_producer_boundary": review.get("boundary"),
                "authority": {
                    "declaration": (
                        "docs/claims.json::claims[strict_prime_tail_orbit_gap]"
                    ),
                    "family_boundary": (
                        "docs/claims.json::external_verification_packet.review_matrix"
                        ".families[strict_prime_tail_orbit_gap]"
                    ),
                },
                "follow": (
                    "python3 scripts/query_semantic.py family-relations "
                    "strict_prime_tail_orbit_gap"
                ),
            }
        )
    return result


def route_memory_handoff(row: Mapping[str, Any]) -> dict[str, Any]:
    """Expose a problem-bound resume command without inventing a route.

    Expert questions are research handoffs, not canonical programme routes.
    They therefore carry a selector-only navigation edge; the command must be
    run in the current checkout to resolve route IDs and source digests before
    any resume state is accepted.
    """
    raw_problem = row.get("problem")
    token = str(raw_problem).strip() if isinstance(raw_problem, (str, int)) else ""
    if not re.fullmatch(r"\d+", token) or token not in FROZEN_PROBLEMS:
        return {
            "status": "unbound",
            "bindings": [],
            "authority_posture": "derived_resume_handoff_not_claim_or_proof_authority",
            "boundary": (
                "An expert question is not a canonical programme route; no "
                "resume route was invented."
            ),
            "unbound_reason": (
                "question does not carry one of the frozen public problem selectors"
            ),
        }
    return {
        "status": "unbound",
        "problem_number": int(token),
        "bindings": [],
        "command": f"python3 scripts/query_route_memory.py --problem {token}",
        "authority_posture": "derived_resume_handoff_not_claim_or_proof_authority",
        "identity_contract": (
            "Run the selector command in the current tracked checkout before "
            "resume: it resolves canonical route IDs and current source digests, "
            "and rejects stale or cross-problem packets."
        ),
        "boundary": (
            "This selector is a navigation handoff only; it does not bind an "
            "expert question to a programme route or promote a claim."
        ),
        "unbound_reason": (
            "expert question selects a problem but not a canonical programme "
            "route; no resume route was invented"
        ),
    }


def paper_source_handoff(problem_number: str) -> dict[str, Any]:
    """Expose the exact dedicated-paper source selector for a problem handoff."""
    problem = next(
        (
            row
            for row in load_json(ROOT / "docs" / "problems.json").get(
                "problems", []
            )
            if str(row.get("erdos_number")) == problem_number
        ),
        None,
    )
    paper = problem.get("paper", {}) if isinstance(problem, dict) else {}
    source = paper.get("source") if isinstance(paper, dict) else None
    if not isinstance(source, str) or not source:
        return {
            "status": "unavailable",
            "source": None,
            "command": None,
            "authority_posture": (
                "derived_paper_navigation_not_claim_or_proof_authority"
            ),
            "boundary": (
                "The public problem roster supplies no dedicated paper source; "
                "no paper route was invented."
            ),
        }
    return {
        "status": "bound",
        "source": source,
        "command": f"python3 scripts/query_corpus.py --paper-source {source}",
        "authority_posture": (
            "derived_paper_navigation_not_claim_or_proof_authority"
        ),
        "identity_contract": (
            "The selector resolves the complete exact anchor census for the "
            "dedicated paper in the current tracked checkout."
        ),
        "boundary": (
            "This selector is an exposition-navigation handoff only; it does "
            "not promote a paper anchor into a claim or proof."
        ),
    }


def problem_route_handoff(row: Mapping[str, Any]) -> dict[str, Any]:
    """Expose the canonical problem packet without inventing a programme route."""
    raw_problem = row.get("problem")
    token = str(raw_problem).strip() if isinstance(raw_problem, (str, int)) else ""
    if not re.fullmatch(r"\d+", token) or token not in FROZEN_PROBLEMS:
        return {
            "status": "unbound",
            "authority_posture": (
                "derived_problem_navigation_not_claim_or_proof_authority"
            ),
            "boundary": (
                "The expert question does not select a public problem route; no "
                "problem route was invented."
            ),
            "unbound_reason": (
                "question does not carry one of the frozen public problem selectors"
            ),
        }
    return {
        "status": "bound",
        "problem_number": int(token),
        "command": f"python3 scripts/query_corpus.py --route erdos_{token}",
        "paper_source": paper_source_handoff(token),
        "authority_posture": (
            "derived_problem_navigation_not_claim_or_proof_authority"
        ),
        "identity_contract": (
            "The canonical problem route expands the paper record, every "
            "review-matrix result family, declaration handles where supplied, "
            "and exact open obligations."
        ),
        "boundary": (
            "This problem route is navigation context only; it does not bind an "
            "expert question to a programme route or promote a claim."
        ),
    }


def respondent_view(row: dict[str, Any]) -> dict[str, Any]:
    """Return the handoff without evaluator-only expected answers."""
    if row.get("domain") != SYSTEMS_DOMAIN:
        view = dict(row)
        view["route_memory"] = route_memory_handoff(row)
        view["problem_route"] = problem_route_handoff(row)
        view["source_current_supports"] = source_current_supports(row)
        return view
    return {
        key: value
        for key, value in row.items()
        if key not in {"acceptance", "review_template"}
    }


def compact_respondent_view(row: dict[str, Any]) -> dict[str, Any]:
    """Return enough to choose a handoff before opening its full packet."""
    result = {
        "id": row["id"],
        "domain": row["domain"],
        "problem": row.get("problem"),
        "classification": row["classification"],
        "status": row["status"],
        "exact_ask": row["exact_ask"],
        "boundary": row["boundary"],
        "current_hypothesis": row["current_hypothesis"],
        "hypothesis_confidence": row["hypothesis_confidence"],
        "plausible_alternatives": [
            {
                "id": alternative["id"],
                "statement": alternative["statement"],
            }
            for alternative in row["plausible_alternatives"]
        ],
        "current_evidence": row["current_evidence"],
        "discriminating_evidence": row["discriminating_evidence"],
        "checked_consumers": (
            [
                (
                    f"{consumer['module']}:{consumer['line']}:"
                    f"{consumer['declaration']}"
                )
                for consumer in row.get("consumer_declarations", [])
            ]
            or [row.get("consumer", {}).get("command")]
        ),
        "detail_command": (
            "python3 scripts/query_expert_handoffs.py --question "
            f"{row['id']}"
        ),
    }
    if row.get("domain") == MATH_DOMAIN:
        result["route_memory"] = route_memory_handoff(row)
        result["problem_route"] = problem_route_handoff(row)
        result["source_current_supports"] = source_current_supports(row)
    return result


def protocol_errors() -> list[str]:
    errors: list[str] = []
    protocol = load_json(PROTOCOL)
    frontier = load_json(FRONTIER)
    if protocol.get("schema") != SCHEMA:
        errors.append(f"schema must be {SCHEMA}")

    questions = all_questions()
    ids = [row.get("id") for row in questions]
    duplicates = sorted(qid for qid, count in Counter(ids).items() if count > 1)
    if duplicates:
        errors.append(f"duplicate question ids: {duplicates}")
    if len(mathematical_questions()) != 5:
        errors.append("mathematical handoff count must remain 5")
    if not systems_questions():
        errors.append("at least one systems handoff is required")

    for row in questions:
        qid = str(row.get("id") or "<missing>")
        for field in REQUIRED_QUESTION_FIELDS:
            if not row.get(field):
                errors.append(f"{qid}: missing {field}")
        if row.get("domain") not in DOMAINS:
            errors.append(f"{qid}: unsupported domain {row.get('domain')!r}")
        if row.get("status") != "OPEN":
            errors.append(f"{qid}: status must be OPEN")
        if row.get("hypothesis_confidence") not in {"low", "medium", "high"}:
            errors.append(f"{qid}: invalid hypothesis_confidence")
        alternatives = row.get("plausible_alternatives")
        if not isinstance(alternatives, list) or len(alternatives) < 2:
            errors.append(f"{qid}: invalid plausible_alternatives")
        elif any(not isinstance(item, dict) for item in alternatives):
            errors.append(f"{qid}: invalid plausible_alternatives")
        elif (
            len({item.get("id") for item in alternatives}) != len(alternatives)
            or any(
                any(
                    not item.get(field)
                    for field in ("id", "statement", "consequence")
                )
                for item in alternatives
            )
        ):
            errors.append(f"{qid}: invalid plausible_alternatives")
        for field in ("current_evidence", "discriminating_evidence"):
            evidence = row.get(field)
            if (
                not isinstance(evidence, list)
                or len(evidence) < 2
                or any(not isinstance(item, str) or not item for item in evidence)
            ):
                errors.append(f"{qid}: invalid {field}")
        measured_artifact = row.get("measured_evidence_artifact")
        measurement_check = row.get("measurement_check_command")
        if bool(measured_artifact) != bool(measurement_check):
            errors.append(
                f"{qid}: measured artifact and check command must occur together"
            )
        elif measured_artifact:
            artifact_path = Path(str(measured_artifact))
            if (
                artifact_path.is_absolute()
                or ".." in artifact_path.parts
                or not (ROOT / artifact_path).is_file()
            ):
                errors.append(f"{qid}: measured artifact is not a repository file")
            command_parts = str(measurement_check).split()
            if (
                len(command_parts) != 3
                or command_parts[0] != "python3"
                or not command_parts[1].startswith("scripts/")
                or command_parts[2] != "--check"
                or not (ROOT / command_parts[1]).is_file()
            ):
                errors.append(f"{qid}: invalid measurement check command")

    for row in systems_questions():
        qid = str(row.get("id") or "<missing>")
        template = row.get("input_template")
        acceptance = row.get("acceptance")
        consumer = row.get("consumer")
        if not isinstance(template, dict) or not template:
            errors.append(f"{qid}: missing input_template")
        if not isinstance(acceptance, dict) or not acceptance:
            errors.append(f"{qid}: missing acceptance contract")
        if not isinstance(consumer, dict) or not consumer.get("command"):
            errors.append(f"{qid}: missing executable consumer")
        elif not consumer.get("final_review_command"):
            errors.append(f"{qid}: missing final review consumer")
        if not row.get("verification_command"):
            errors.append(f"{qid}: missing verification_command")
        manual_fields = row.get("manual_review_fields")
        if not isinstance(manual_fields, list) or not manual_fields:
            errors.append(f"{qid}: missing manual_review_fields")
        rubric = row.get("manual_review_rubric")
        review_template = row.get("review_template")
        if not isinstance(rubric, dict) or not rubric:
            errors.append(f"{qid}: missing manual_review_rubric")
        if not isinstance(review_template, dict) or not review_template:
            errors.append(f"{qid}: missing review_template")
        elif isinstance(rubric, dict) and set(
            review_template.get("criteria", {})
        ) != set(rubric):
            errors.append(f"{qid}: review criteria drifted from manual rubric")
        if isinstance(acceptance, dict):
            lattice = frontier.get("demand_lattice", {})
            expected_substantial = lattice.get("counts", {}).get("substantial")
            expected_equivalent = sum(
                len(group.get("members", []))
                for group in lattice.get("classes", [])
                if group.get("equivalent_to_problem") is True
            )
            if acceptance.get("substantial_antecedents") != expected_substantial:
                errors.append(
                    f"{qid}: substantial antecedent count drifted from demand lattice"
                )
            if acceptance.get("equivalent_antecedents") != expected_equivalent:
                errors.append(
                    f"{qid}: endpoint-equivalent count drifted from demand lattice"
                )
    return errors


def _is_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def object_digest(value: Any) -> str:
    payload = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def validate_response(response: Any) -> list[str]:
    errors: list[str] = []
    if not isinstance(response, dict):
        return ["response must be a JSON object"]
    qid = response.get("question_id")
    by_id = {row["id"]: row for row in systems_questions()}
    question = by_id.get(qid)
    if question is None:
        return [f"question_id does not select a systems handoff: {qid!r}"]

    template = question["input_template"]
    missing = sorted(set(template) - set(response))
    extra = sorted(set(response) - set(template))
    if missing:
        errors.append(f"missing fields: {missing}")
    if extra:
        errors.append(f"unknown fields: {extra}")

    acceptance = question["acceptance"]
    elapsed = response.get("elapsed_seconds")
    if not _is_int(elapsed) or elapsed < 0:
        errors.append("elapsed_seconds must be a nonnegative integer")
    elif elapsed > acceptance["maximum_elapsed_seconds"]:
        errors.append(
            "elapsed_seconds exceeds "
            f"{acceptance['maximum_elapsed_seconds']}-second contract"
        )

    expected_scalars = {
        "prior_project_context": acceptance["prior_project_context"],
        "problem_249_status": acceptance["problem_status"],
        "problem_257_status": acceptance["problem_status"],
        "farey_bound_provenance": acceptance["farey_bound_provenance"],
        "farey_numerical_delta": acceptance["farey_numerical_delta"],
        "equivalent_antecedents": acceptance["equivalent_antecedents"],
        "substantial_antecedents": acceptance["substantial_antecedents"],
    }
    if not isinstance(response.get("prior_project_context"), bool):
        errors.append("prior_project_context must be a boolean")
    for field in (
        "farey_numerical_delta",
        "equivalent_antecedents",
        "substantial_antecedents",
    ):
        if not _is_int(response.get(field)):
            errors.append(f"{field} must be an integer")
    for field, expected in expected_scalars.items():
        if response.get(field) != expected:
            errors.append(
                f"{field}: expected {expected!r}, got {response.get(field)!r}"
            )

    minimum = acceptance["minimum_nonrestatement_results_per_problem"]
    for problem in ("249", "257"):
        field = f"nonrestatement_results_{problem}"
        values = response.get(field)
        if not isinstance(values, list) or any(
            not isinstance(value, str) or not value.strip() for value in values
        ):
            errors.append(f"{field} must be an array of nonempty descriptions")
            continue
        if len({value.strip().casefold() for value in values}) < minimum:
            errors.append(f"{field} must name at least {minimum} distinct results")

    paths = response.get("source_paths_used")
    if not isinstance(paths, list) or not paths or any(
        not isinstance(path, str) or not path for path in paths
    ):
        errors.append("source_paths_used must be a nonempty array of paths")
    elif any(
        Path(path).is_absolute()
        or ".." in Path(path).parts
        or not (ROOT / path).is_file()
        for path in paths
    ):
        errors.append("source_paths_used must name existing repository files")

    reviewer = response.get("reviewer_identity")
    if not isinstance(reviewer, str) or not reviewer.strip():
        errors.append("reviewer_identity must be a nonempty string")
    reviewed_at = response.get("reviewed_at")
    if not isinstance(reviewed_at, str):
        errors.append("reviewed_at must be an ISO calendar date")
    else:
        try:
            date.fromisoformat(reviewed_at)
        except ValueError:
            errors.append("reviewed_at must be an ISO calendar date")
    revision = response.get("clone_revision")
    if not isinstance(revision, str) or not re.fullmatch(r"[0-9a-f]{40}", revision):
        errors.append("clone_revision must be a full lowercase commit id")

    confusing = response.get("first_confusing_surface")
    if not isinstance(confusing, str):
        errors.append("first_confusing_surface must be a string")
    verdict = response.get("verdict_summary")
    if not isinstance(verdict, str) or not verdict.strip():
        errors.append("verdict_summary must be a nonempty string")
    return errors


def validate_review(response: Any, review: Any) -> list[str]:
    response_errors = validate_response(response)
    if response_errors:
        return [f"response: {error}" for error in response_errors]
    if not isinstance(review, dict):
        return ["review must be a JSON object"]

    qid = response["question_id"]
    by_id = {row["id"]: row for row in systems_questions()}
    question = by_id[qid]
    template = question["review_template"]
    missing = sorted(set(template) - set(review))
    extra = sorted(set(review) - set(template))
    errors: list[str] = []
    if missing:
        errors.append(f"review missing fields: {missing}")
    if extra:
        errors.append(f"review has unknown fields: {extra}")
    if review.get("question_id") != qid:
        errors.append("review question_id does not match the response")
    if review.get("response_sha256") != object_digest(response):
        errors.append("review response_sha256 does not bind the supplied response")

    evaluator = review.get("evaluator_identity")
    if not isinstance(evaluator, str) or not evaluator.strip():
        errors.append("evaluator_identity must be a nonempty string")
    evaluated_at = review.get("evaluated_at")
    if not isinstance(evaluated_at, str):
        errors.append("evaluated_at must be an ISO calendar date")
    else:
        try:
            date.fromisoformat(evaluated_at)
        except ValueError:
            errors.append("evaluated_at must be an ISO calendar date")

    for field in ("reviewer_provenance_verified", "timing_provenance_verified"):
        if not isinstance(review.get(field), bool):
            errors.append(f"{field} must be a boolean")

    criteria = review.get("criteria")
    expected_criteria = set(question["manual_review_rubric"])
    if not isinstance(criteria, dict) or set(criteria) != expected_criteria:
        errors.append("review criteria must match the manual rubric exactly")
        criteria_values: list[bool] = []
    else:
        criteria_values = list(criteria.values())
        if any(not isinstance(value, bool) for value in criteria_values):
            errors.append("every review criterion must be a boolean")

    notes = review.get("review_notes")
    if not isinstance(notes, str):
        errors.append("review_notes must be a string")
    outcome = review.get("final_outcome")
    if outcome not in {"accepted", "needs_revision"}:
        errors.append("final_outcome must be accepted or needs_revision")
    elif outcome == "accepted":
        if (
            review.get("reviewer_provenance_verified") is not True
            or review.get("timing_provenance_verified") is not True
            or not criteria_values
            or not all(value is True for value in criteria_values)
        ):
            errors.append(
                "accepted outcome requires verified provenance, timing and all criteria"
            )
    elif (
        criteria_values
        and all(value is True for value in criteria_values)
        and review.get("reviewer_provenance_verified") is True
        and review.get("timing_provenance_verified") is True
    ):
        errors.append("needs_revision must identify at least one failed condition")
    elif not isinstance(notes, str) or not notes.strip():
        errors.append("needs_revision requires review_notes")
    return errors


def question_packet(
    domain: str | None, question_id: str | None = None
) -> dict[str, Any]:
    rows = all_questions()
    if domain:
        rows = [row for row in rows if row["domain"] == domain]
    if question_id:
        rows = [row for row in rows if row["id"] == question_id]
        if not rows:
            raise ValueError(f"no expert handoff {question_id!r}")
    full_packet = bool(question_id) or (domain == SYSTEMS_DOMAIN and len(rows) == 1)
    domain_counts = Counter(row["domain"] for row in rows)
    return {
        "question": "exact inputs requested from human experts",
        "rule": (
            "Every row names the requested input, current guess, alternatives, "
            "discriminating evidence, consumer, payoff and boundary."
        ),
        "packet_kind": "full_question" if full_packet else "compact_index",
        "count": len(rows),
        "domain_counts": dict(sorted(domain_counts.items())),
        "semantic_endpoint_handoff": semantic_endpoint_handoff_route(),
        "results": [
            respondent_view(row) if full_packet else compact_respondent_view(row)
            for row in rows
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--domain", choices=DOMAINS)
    parser.add_argument("--question", metavar="QUESTION_ID")
    parser.add_argument("--template", metavar="QUESTION_ID")
    parser.add_argument("--response", type=Path, metavar="RESPONSE.json")
    parser.add_argument("--review-template", metavar="QUESTION_ID")
    parser.add_argument(
        "--review",
        nargs=2,
        type=Path,
        metavar=("RESPONSE.json", "REVIEW.json"),
    )
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--semantic-handoff", action="store_true")
    args = parser.parse_args()

    exclusive = (
        args.question,
        args.template,
        args.response,
        args.review_template,
        args.review,
        args.check,
        args.semantic_handoff,
    )
    if sum(bool(value) for value in exclusive) > 1:
        parser.error(
            "--question, --template, --response, --review-template, --review, "
            "--check and --semantic-handoff are mutually exclusive"
        )

    if args.check:
        errors = protocol_errors()
        if errors:
            for error in errors:
                print(f"FAIL {error}")
            return 1
        print(
            "expert handoff protocol: 5 mathematical questions and "
            f"{len(systems_questions())} systems question(s) verified"
        )
        return 0

    if args.semantic_handoff:
        print(json.dumps(semantic_endpoint_handoff_packet(), indent=1, ensure_ascii=False))
        return 0

    if args.template:
        by_id = {row["id"]: row for row in systems_questions()}
        question = by_id.get(args.template)
        if question is None:
            parser.error("--template must name a systems handoff")
        print(json.dumps(question["input_template"], indent=2, ensure_ascii=False))
        return 0

    if args.review_template:
        by_id = {row["id"]: row for row in systems_questions()}
        question = by_id.get(args.review_template)
        if question is None:
            parser.error("--review-template must name a systems handoff")
        print(json.dumps(question["review_template"], indent=2, ensure_ascii=False))
        return 0

    if args.response:
        response = load_json(args.response)
        errors = validate_response(response)
        receipt = {
            "question_id": response.get("question_id"),
            "response_sha256": object_digest(response),
            "status": (
                "structurally_accepted_pending_content_review"
                if not errors
                else "discrepancies"
            ),
            "errors": errors,
            "manual_review_fields": (
                []
                if errors
                else next(
                    row["manual_review_fields"]
                    for row in systems_questions()
                    if row["id"] == response.get("question_id")
                )
            ),
            "boundary": (
                "This receipt checks scalar and structural fields and lists "
                "free prose for manual review; it does not authenticate the "
                "reviewer, timing, mathematics or priority."
            ),
        }
        print(json.dumps(receipt, indent=2, ensure_ascii=False))
        return 0 if not errors else 1

    if args.review:
        response = load_json(args.review[0])
        review = load_json(args.review[1])
        errors = validate_review(response, review)
        receipt = {
            "question_id": (
                response.get("question_id")
                if isinstance(response, dict)
                else None
            ),
            "response_sha256": object_digest(response),
            "status": (
                review.get("final_outcome")
                if not errors and isinstance(review, dict)
                else "discrepancies"
            ),
            "errors": errors,
            "boundary": (
                "This is a reviewed communication receipt, not a verdict on "
                "mathematical correctness, priority, novelty or either problem."
            ),
        }
        print(json.dumps(receipt, indent=2, ensure_ascii=False))
        return 0 if not errors else 1

    try:
        packet = question_packet(args.domain, args.question)
    except ValueError as error:
        parser.error(str(error))
    print(json.dumps(packet, indent=1, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
