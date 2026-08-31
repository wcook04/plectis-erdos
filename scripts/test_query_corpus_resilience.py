#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Focused checks for semantic query translation and partial-artifact resilience.

Every check here used to fail with the same eight words, "query corpus
resilience invariant", for all 106 of its assertions. That message named no
declaration, no observed value, and no repair, so a red run told a reader only
which line number to go and read. The messages below name the handle under
test, the value that was actually observed, and -- where the failure has a
known cause -- the command that fixes it.
"""

from __future__ import annotations

import json
import re
import tempfile
from collections.abc import Callable
from pathlib import Path
from typing import Any

import query_corpus


DEPENDENCY_INDEX = "docs/lean_dependency_index.json"
DECLARATION_ATLAS = "docs/declaration_atlas.json"
DEPENDENCY_INDEX_REBUILD = "python3 scripts/build_lean_dependency_index.py"

# What each non-available availability value means, so a failure explains the
# state rather than restating it. ``query_corpus.formal_dependency_neighbourhood``
# and its siblings emit exactly these three values.
AVAILABILITY_MEANINGS = {
    "unavailable_or_stale": (
        f"{DEPENDENCY_INDEX} did not load at all, so every neighbourhood, "
        "path, cone and proof plan in the corpus reports itself unavailable. "
        "The index copies its source_fingerprint from the declaration atlas it "
        "was exported against; query_corpus rejects the whole file when that "
        "fingerprint no longer equals the one in "
        f"{DECLARATION_ATLAS}, because the atlas is where the index gets its "
        "source coordinates and stale coordinates would be reported as "
        "elaborated fact"
    ),
    "handle_not_source_resolved": (
        "the index loaded but holds no node for this handle. The declaration "
        "is in the atlas and was not in the elaborated environment the index "
        "was exported from -- which is what a module that reached the root "
        "import closure after the last export looks like"
    ),
    "no_declaration_match": (
        "no declaration in the corpus matched the requested handle at all"
    ),
}


def require(condition: bool, message: str | Callable[[], str]) -> None:
    """Keep resilience checks active when invoked with ``python -O``.

    ``message`` may be a callable so that a diagnosis which costs real work --
    a file read, a projection load -- is paid only when the check fails.
    """
    if not condition:
        raise AssertionError(message() if callable(message) else message)


def observed(value: Any, limit: int = 300) -> str:
    """Render an observed value compactly enough to sit inside a message."""
    try:
        text = json.dumps(value, ensure_ascii=False, sort_keys=True, default=repr)
    except (TypeError, ValueError):
        text = repr(value)
    return text if len(text) <= limit else f"{text[: limit - 1]}..."


def missing(expected: set[str], seen: set[str]) -> str:
    """Name the expected members that are absent, not the whole expectation."""
    return observed(sorted(expected - seen))


def committed_index_fingerprint() -> str:
    """Read the index's own fingerprint without parsing the whole 6 MB file."""
    path = query_corpus.ROOT / DEPENDENCY_INDEX
    try:
        head = path.read_text(encoding="utf-8", errors="replace")[:4096]
    except OSError as error:
        return f"<unreadable: {error}>"
    match = re.search(r'"source_fingerprint"\s*:\s*"([^"]+)"', head)
    return match.group(1) if match else "<not in the first 4 KiB>"


def committed_atlas_fingerprint() -> str:
    """Read the atlas fingerprint the index is required to agree with."""
    try:
        return str(
            query_corpus.load(DECLARATION_ATLAS).get(
                "source_fingerprint", "<absent>"
            )
        )
    except (OSError, ValueError, KeyError) as error:
        return f"<unreadable: {error}>"


def unresolved_witness(handle: str, packet: dict[str, Any], kind: str) -> str:
    """Explain an unresolved formal witness by name, value, and repair."""
    availability = packet.get("availability")
    meaning = AVAILABILITY_MEANINGS.get(
        availability, "unrecognised availability value"
    )
    report = [
        f"{kind} for {handle} reports availability {availability!r} rather "
        f"than 'available': {meaning}.",
    ]
    if availability == "unavailable_or_stale":
        report.append(
            f"{DEPENDENCY_INDEX} carries source_fingerprint "
            f"{committed_index_fingerprint()} and {DECLARATION_ATLAS} carries "
            f"{committed_atlas_fingerprint()}."
        )
        report.append(
            "The index is the stale side: it is exported from an elaborated "
            "Lean environment and can only be regenerated from one. Re-run "
            f"`{DEPENDENCY_INDEX_REBUILD}` in a checkout with a built Lean "
            "toolchain and commit the result alongside the atlas refresh that "
            "moved the fingerprint."
        )
    report.append(f"packet keys: {observed(sorted(packet))}")
    return " ".join(report)


def check_dictionary_budget_and_shape() -> None:
    packet = query_corpus.semantic_dictionary_packet()
    encoded = json.dumps(packet, ensure_ascii=False, separators=(",", ":")).encode(
        "utf-8"
    )
    # The dictionary is a first-contact packet, so it stays small enough to read
    # in one pass. The ceiling was 12,000 for a six-problem corpus; #68 and
    # #1041 add their own routes and the packet is now 12.7 KiB. Raised rather
    # than trimmed: dropping routes to fit would make the dictionary silently
    # incomplete, which is the failure the budget exists to prevent.
    require(
        len(encoded) <= 14_000,
        f"the semantic dictionary packet encodes to {len(encoded)} bytes, over "
        "the 14,000-byte first-contact budget; trim a route's prose rather "
        "than dropping a route, because a silently incomplete dictionary is "
        "the failure this budget exists to prevent",
    )
    operator_ids = {row["id"] for row in packet["operators"]}
    expected_operators = {
        "analogy",
        "digest",
        "falsify",
        "frontier",
        "locate",
        "support",
        "trace",
    }
    require(
        operator_ids == expected_operators,
        f"the semantic dictionary advertises operators {observed(sorted(operator_ids))}; "
        f"missing {observed(sorted(expected_operators - operator_ids))} and "
        f"unexpected {observed(sorted(operator_ids - expected_operators))}",
    )
    require(
        packet["authority_posture"].endswith(
            "not_proof_or_claim_status_authority"
        ),
        "the semantic dictionary authority_posture must end in "
        "'not_proof_or_claim_status_authority' so a first-contact reader "
        "cannot mistake the dictionary for claim authority; it reads "
        f"{observed(packet['authority_posture'])}",
    )
    require(
        packet["schema_version"] == "erdos249257-semantic-dictionary/2",
        "the semantic dictionary schema_version is "
        f"{observed(packet['schema_version'])}, not "
        "'erdos249257-semantic-dictionary/2'; a consumer pinned to the "
        "declared version would read the wrong shape",
    )
    discovery = packet["route_discovery_contract"]
    require(
        discovery["source"].startswith("docs/claims.json::"),
        "the route discovery contract must be sourced from a docs/claims.json "
        f"address so it stays derivable; it reads {observed(discovery['source'])}",
    )
    by_route = {row["route_id"]: row for row in discovery["routes"]}
    navigation_terms = by_route["agent_native_corpus_navigation"]["discovery_terms"]
    require(
        "which paper proofs lack semantic interpretation" in navigation_terms,
        "the agent_native_corpus_navigation route no longer advertises the "
        "'which paper proofs lack semantic interpretation' discovery term, so "
        "the backlog question has no route; its terms are "
        f"{observed(navigation_terms)}",
    )
    vocabulary_ids = {row["id"] for row in packet["vocabulary"]}
    require(
        "semantic_population_backlog" in vocabulary_ids,
        "the dictionary vocabulary has no 'semantic_population_backlog' row, "
        "so the unpopulated-interpretation backlog is undiscoverable; the "
        f"vocabulary ids are {observed(sorted(vocabulary_ids))}",
    )


def check_vocabulary_mismatch_queries() -> None:
    require(
        not query_corpus.SUPPRESSED_DECLARATION_ATLAS_ROWS,
        "query_corpus.SUPPRESSED_DECLARATION_ATLAS_ROWS is non-empty: "
        f"{observed(query_corpus.SUPPRESSED_DECLARATION_ATLAS_ROWS)}. Atlas "
        "rows are suppressed at query time only to hide a parser defect; fix "
        "the atlas builder instead so the suppression list can stay empty",
    )
    for comment_word in ("makes", "invariant"):
        try:
            query_corpus.declaration_packet(comment_word, 1)
        except KeyError:
            pass
        else:
            raise AssertionError(
                f"comment prose must not be queryable as a declaration, but "
                f"--declaration {comment_word!r} resolved to a match; the "
                "atlas parser has started reading docstring words as "
                "declaration heads again"
            )
    prose_declarations = [
        row
        for row in query_corpus.search_packet("makes", 20)["results"]
        if row.get("kind") == "declaration" and row.get("name") == "makes"
    ]
    require(
        not prose_declarations,
        "searching for 'makes' returned it as a declaration: "
        f"{observed(prose_declarations)}; the atlas is carrying comment prose "
        "as declaration rows",
    )
    for wrapped_name in (
        "diagonalAdjacentSuffixResidue_powerTwo_oddDepth_central_iff_halfWordBand",
        "HalfTerminalOnlyScaledVanishingSequence.ofCofinalTerminalOnlyStrip",
    ):
        wrapped = query_corpus.declaration_packet(wrapped_name, 1)
        require(
            wrapped["matches"][0]["name"] == wrapped_name,
            f"a line-wrapped declaration head must still resolve whole: "
            f"--declaration {wrapped_name!r} returned name "
            f"{observed(wrapped['matches'][0]['name'])}, so the atlas stored a "
            "truncated name for a signature the source wrapped across lines",
        )
    terms = query_corpus.search_terms(
        "half_mem_mersenneAchievementSet_of_middleProducerTailEscape"
    )
    expected_terms = {
        "half",
        "mem",
        "mersenne",
        "achievement",
        "set",
        "middle",
        "producer",
        "tail",
        "escape",
    }
    require(
        terms >= expected_terms,
        "splitting 'half_mem_mersenneAchievementSet_of_middleProducerTailEscape' "
        f"lost {missing(expected_terms, terms)}; a Lean name that mixes "
        "snake_case and camelCase must split on both, or an ordinary-language "
        "query can never reach it. Observed terms: "
        f"{observed(sorted(terms))}",
    )
    qualified = query_corpus.declaration_packet(
        "Erdos249257.TotientTailPeriodKiller.fixedPrecisionTropicalNoGo",
        1,
    )
    require(
        qualified["matches"][0]["name"] == "fixedPrecisionTropicalNoGo",
        "a fully qualified query must resolve to the bare declaration name; "
        "'Erdos249257.TotientTailPeriodKiller.fixedPrecisionTropicalNoGo' "
        f"resolved to name {observed(qualified['matches'][0]['name'])}",
    )
    require(
        qualified["matches"][0]["qualified_name"]
        == "Erdos249257.TotientTailPeriodKiller.fixedPrecisionTropicalNoGo",
        "the qualified_name echoed back for "
        "'Erdos249257.TotientTailPeriodKiller.fixedPrecisionTropicalNoGo' is "
        f"{observed(qualified['matches'][0]['qualified_name'])}; the namespace "
        "reconstruction has drifted from the module's namespace events",
    )
    dotted = query_corpus.declaration_packet(
        "BooleanMobiusCarryCertificate.reconstructsSupport",
        1,
    )
    require(
        dotted["matches"][0]["qualified_name"]
        == "Erdos249257.BooleanMobiusCarryCertificate.reconstructsSupport",
        "a dotted structure-field query must still qualify into its enclosing "
        "namespace: 'BooleanMobiusCarryCertificate.reconstructsSupport' "
        f"qualified to {observed(dotted['matches'][0]['qualified_name'])} "
        "rather than 'Erdos249257.BooleanMobiusCarryCertificate."
        "reconstructsSupport'",
    )
    private = query_corpus.declaration_packet("mod_six_cases", 1)
    require(
        not private["matches"][0]["externally_addressable"],
        "'mod_six_cases' is a private proof-local helper and is reported as "
        "externally_addressable="
        f"{observed(private['matches'][0]['externally_addressable'])}; a "
        "reader would be told to `apply` a name that does not resolve outside "
        "its own file",
    )
    private_support = query_corpus.semantic_slice_packet(
        "I need the mod_six_cases theorem",
        4,
    )
    private_candidates = [
        row["qualified_declaration"]
        for row in private_support["operator_synthesis"].get(
            "lean_application_candidates", []
        )
        if row["qualified_declaration"].endswith(".mod_six_cases")
    ]
    require(
        not private_candidates,
        "the support synthesis offered private helpers as application "
        f"candidates: {observed(private_candidates)}; a private declaration "
        "cannot be applied from another module and must not be nominated",
    )
    rank_two = query_corpus.search_packet("is rank two worth pursuing", 5)
    require(
        rank_two["query_interpretation"]["operator"]["id"] == "falsify",
        "'is rank two worth pursuing' should translate to the falsify "
        "operator, because it asks whether a route is already ruled out; it "
        f"translated to {observed(rank_two['query_interpretation']['operator']['id'])}",
    )
    require(
        rank_two["results"][0]["kind"] == "declaration",
        "the first result for 'is rank two worth pursuing' has kind "
        f"{observed(rank_two['results'][0]['kind'])}, not 'declaration'; the "
        "falsify operator must lead with the formal obstruction, not with "
        "prose about it",
    )
    require(
        rank_two["results"][0]["name"]
        == "rank2_kill_sound_but_not_shallower_at_cell",
        "the first result for 'is rank two worth pursuing' is "
        f"{observed(rank_two['results'][0]['name'])}, not "
        "'rank2_kill_sound_but_not_shallower_at_cell', which is the "
        "declaration that actually settles the rank-two question",
    )

    half_value = query_corpus.search_packet(
        "what should I try next for the half value problem", 5
    )
    require(
        half_value["query_interpretation"]["operator"]["id"] == "frontier",
        "'what should I try next for the half value problem' should translate "
        "to the frontier operator; it translated to "
        f"{observed(half_value['query_interpretation']['operator']['id'])}",
    )
    half_value_head = [
        (row["kind"], row.get("id")) for row in half_value["results"][:2]
    ]
    require(
        half_value_head
        == [
            ("reading_route", "erdos257_half_story"),
            ("open_proposition", "remaining_open.half_value_membership"),
        ],
        "a frontier query about the half value should lead with the reading "
        "route and then the open proposition; the first two results are "
        f"{observed(half_value_head)}",
    )

    one_over_twenty_one = query_corpus.search_packet(
        "what is the exact public status of one over twenty one "
        "and what remains to prove",
        5,
    )
    require(
        one_over_twenty_one["query_interpretation"]["operator"]["id"] == "frontier",
        "'what is the exact public status of one over twenty one and what "
        "remains to prove' should translate to the frontier operator; it "
        "translated to "
        f"{observed(one_over_twenty_one['query_interpretation']['operator']['id'])}",
    )
    one_over_twenty_one_head = [
        (row["kind"], row.get("name"))
        for row in one_over_twenty_one["results"][:2]
    ]
    require(
        one_over_twenty_one_head
        == [
            ("declaration", "finiteErdosSum_ne_one_div_twenty_one"),
            ("declaration", "exists_two_primitive23_solutions_mul_ten"),
        ],
        "the 1/21 status query should lead with the two declarations that "
        "carry the result and its multiplicity defect; the first two results "
        f"are {observed(one_over_twenty_one_head)}",
    )
    followup_ids = [
        row["node_id"]
        for row in one_over_twenty_one["query_interpretation"][
            "authored_semantic_followups"
        ]
    ]
    require(
        followup_ids
        == [
            "Z65::one_over_twenty_one_has_no_finite_support_on_ranks_at_least_two",
            "Z65::primitive_23_cone_has_rank_ten_defect_and_recurrent_multiplicity",
        ],
        "the authored semantic follow-ups for the 1/21 status query are "
        f"{observed(followup_ids)}; the two Z65 nodes are what tell a reader "
        "which part of 1/21 is settled and which is not",
    )
    fractional_spelling = query_corpus.search_packet(
        "what is the exact public status of 1/21 and what remains to prove",
        5,
    )
    fractional_head = [
        (row["kind"], row.get("name"))
        for row in fractional_spelling["results"][:2]
    ]
    require(
        fractional_head
        == [
            ("declaration", "finiteErdosSum_ne_one_div_twenty_one"),
            ("declaration", "exists_two_primitive23_solutions_mul_ten"),
        ],
        "'1/21' and 'one over twenty one' must reach the same two "
        "declarations; the numeric spelling returned "
        f"{observed(fractional_head)}",
    )

    fixed_cut_boundary = query_corpus.semantic_slice_packet(
        "Does the public Erdős 257 release claim that a denominator-21 "
        "saturated transition reduces to a zero-pulse skip followed by a "
        "local pulse at most one, or prove 1/21 membership?",
        4,
    )
    require(
        fixed_cut_boundary["query_interpretation"]["operator"]["id"] == "frontier",
        "the denominator-21 boundary question should translate to the "
        "frontier operator, because it asks what the release does and does "
        "not claim; it translated to "
        f"{observed(fixed_cut_boundary['query_interpretation']['operator']['id'])}",
    )
    boundary_cells = [
        (cell["kind"], cell["handle"])
        for cell in fixed_cut_boundary["semantic_cells"]
    ]
    require(
        boundary_cells
        == [
            ("declaration", "finiteErdosSum_ne_one_div_twenty_one"),
            ("declaration", "exists_two_primitive23_solutions_mul_ten"),
            ("claim", "universal_257"),
            (
                "open_proposition",
                "remaining_open.universal_257_all_infinite_supports",
            ),
        ],
        "the denominator-21 boundary slice must carry both declarations, the "
        "universal_257 claim, and the open proposition that marks the limit; "
        f"it carried {observed(boundary_cells)}",
    )
    boundary_open_ids = {
        row["id"]
        for row in fixed_cut_boundary["operator_synthesis"]["exact_open_records"]
    }
    require(
        boundary_open_ids == {"remaining_open.universal_257_all_infinite_supports"},
        "the denominator-21 boundary slice reports open records "
        f"{observed(sorted(boundary_open_ids))}; it must name exactly "
        "'remaining_open.universal_257_all_infinite_supports', so a reader is "
        "told precisely which part is unproved",
    )


def check_witness_carrying_semantic_slices() -> None:
    rank_two = query_corpus.semantic_slice_packet(
        "is rank two worth pursuing", 5
    )
    require(
        rank_two["query_interpretation"]["operator"]["id"] == "falsify",
        "the 'is rank two worth pursuing' slice translated to operator "
        f"{observed(rank_two['query_interpretation']['operator']['id'])}, not "
        "'falsify'",
    )
    rank_handles = [cell["handle"] for cell in rank_two["semantic_cells"]]
    require(
        rank_handles == ["rank2_kill_sound_but_not_shallower_at_cell"],
        "the rank-two falsify slice carries handles "
        f"{observed(rank_handles)}; it must carry exactly "
        "'rank2_kill_sound_but_not_shallower_at_cell', the declaration that "
        "records the obstruction",
    )
    rank_cell = rank_two["semantic_cells"][0]
    require(
        "NOT shallower" in rank_cell["content"]["authored_digest"]["text"],
        "the rank-two digest no longer says the kill is NOT shallower, so the "
        "reader loses the whole point of the obstruction; it reads "
        f"{observed(rank_cell['content']['authored_digest']['text'])}",
    )
    require(
        rank_cell["content"]["formal_witness"]["source_ref"].endswith(
            "LcmConeFlatness.lean:626"
        ),
        "the rank-two formal witness points at "
        f"{observed(rank_cell['content']['formal_witness']['source_ref'])}, "
        "not LcmConeFlatness.lean:626; the source coordinate has drifted from "
        "the declaration it is supposed to pin",
    )
    rank_planes = {row["plane"] for row in rank_cell["typed_provenance"]}
    require(
        rank_planes == {"kernel", "status", "digestion", "navigation"},
        "the rank-two cell carries provenance planes "
        f"{observed(sorted(rank_planes))}; all four of kernel, status, "
        "digestion and navigation must be present or the cell cannot say "
        "which of its parts is proof and which is prose",
    )
    require(
        rank_two["operator_synthesis"]["kind"] == "falsification_synthesis",
        "the rank-two slice synthesised "
        f"{observed(rank_two['operator_synthesis']['kind'])} rather than a "
        "'falsification_synthesis'",
    )

    half_value = query_corpus.semantic_slice_packet(
        "what should I try next for the half value problem", 5
    )
    half_handles = [cell["handle"] for cell in half_value["semantic_cells"]]
    require(
        half_handles
        == ["erdos257_half_story", "remaining_open.half_value_membership"],
        "the half-value frontier slice carries handles "
        f"{observed(half_handles)}; it must carry the reading route and then "
        "the open proposition",
    )
    open_cell = half_value["semantic_cells"][1]
    require(
        open_cell["content"]["open_record"]["statement"]
        == "Decide whether 1/2 lies in the Mersenne achievement set. "
        "Yes refutes universal #257; no closes only this route.",
        "the half-value open record now states "
        f"{observed(open_cell['content']['open_record']['statement'])}; the "
        "authored statement is what keeps 'yes refutes universal #257' and "
        "'no closes only this route' from being read as the same outcome",
    )
    route_cell = half_value["semantic_cells"][0]
    require(
        "neither target membership"
        in route_cell["content"]["programme"]["claim_ceiling"],
        "the half-value reading route's claim ceiling reads "
        f"{observed(route_cell['content']['programme']['claim_ceiling'])}; "
        "without 'neither target membership' the route stops disclaiming the "
        "membership result it does not have",
    )
    half_open_ids = {
        row["id"] for row in half_value["operator_synthesis"]["exact_open_records"]
    }
    require(
        "remaining_open.half_value_membership" in half_open_ids,
        "the half-value slice reports open records "
        f"{observed(sorted(half_open_ids))} and omits "
        "'remaining_open.half_value_membership', the record that says the "
        "question is open",
    )

    one_over_twenty_one = query_corpus.semantic_slice_packet(
        "what is the exact public status of one over twenty one "
        "and what remains to prove",
        5,
    )
    twenty_one_handles = [
        cell["handle"] for cell in one_over_twenty_one["semantic_cells"][:2]
    ]
    require(
        twenty_one_handles
        == [
            "finiteErdosSum_ne_one_div_twenty_one",
            "exists_two_primitive23_solutions_mul_ten",
        ],
        "the 1/21 slice leads with handles "
        f"{observed(twenty_one_handles)} rather than the finite-support "
        "obstruction followed by the multiplicity witness",
    )
    finite_obstruction = one_over_twenty_one["semantic_cells"][0]
    # Same consequence, restated by the source-fidelity pass: the theorem rules
    # finite support out rather than asserting infinite support outright.
    require(
        "rules out finite support"
        in finite_obstruction["content"]["authored_digest"]["text"],
        "the 1/21 digest reads "
        f"{observed(finite_obstruction['content']['authored_digest']['text'])}; "
        "it must say the theorem rules out finite support, because asserting "
        "infinite support outright would overstate what was proved",
    )
    multiplicity_obstruction = one_over_twenty_one["semantic_cells"][1]
    require(
        multiplicity_obstruction["content"]["formal_witness"]["name"]
        == "exists_two_primitive23_solutions_mul_ten",
        "the 1/21 multiplicity cell is witnessed by "
        f"{observed(multiplicity_obstruction['content']['formal_witness']['name'])}, "
        "not by 'exists_two_primitive23_solutions_mul_ten'",
    )

    analogy = query_corpus.semantic_slice_packet(
        "compare half carry compactness with the half achievement set route",
        4,
    )
    require(
        analogy["operator_synthesis"]["formal_bridge_status"] == "not_inferred",
        "the analogy synthesis reports formal_bridge_status "
        f"{observed(analogy['operator_synthesis']['formal_bridge_status'])}; "
        "an analogy between two routes must stay 'not_inferred' or the packet "
        "starts asserting a formal bridge nobody proved",
    )
    require(
        "remaining_open.half_value_membership"
        in analogy["operator_synthesis"]["shared_open_proposition_ids"],
        "the analogy synthesis shares open propositions "
        f"{observed(analogy['operator_synthesis']['shared_open_proposition_ids'])} "
        "and omits 'remaining_open.half_value_membership', which is the open "
        "question the two routes actually have in common",
    )

    support = query_corpus.semantic_slice_packet(
        "which premises let either sharp curvature or exponent only three "
        "transport prove irrationality of the totient series",
        4,
    )
    consumer_names = {
        row["name"]
        for row in support["operator_synthesis"]["checked_consumer_signatures"]
    }
    expected_consumers = {
        "irrational_totientSeries_of_sharpCurvatureSupply",
        "irrational_totient_series_of_exponentOnlyThreeTransportSupply",
    }
    require(
        expected_consumers <= consumer_names,
        "the support synthesis lists checked consumers "
        f"{observed(sorted(consumer_names))} and is missing "
        f"{missing(expected_consumers, consumer_names)}; a 'which premises' "
        "question must show every consumer that would discharge them",
    )
    tactics = {
        row["tactic"]
        for row in support["operator_synthesis"]["lean_application_candidates"]
    }
    expected_tactics = {
        "apply Erdos249257.TotientTailPeriodKiller.irrational_totientSeries_of_sharpCurvatureSupply",
        "apply Erdos249257.ExponentOnlyTransport.irrational_totient_series_of_exponentOnlyThreeTransportSupply",
    }
    require(
        tactics >= expected_tactics,
        "the support synthesis offers tactics "
        f"{observed(sorted(tactics))} and is missing "
        f"{missing(expected_tactics, tactics)}",
    )
    unproved_ids = {
        row["id"] for row in support["operator_synthesis"]["unproved_requirements"]
    }
    require(
        unproved_ids == {"remaining_open.unbounded_certificate_supply"},
        "the support synthesis reports unproved requirements "
        f"{observed(sorted(unproved_ids))}; it must name exactly "
        "'remaining_open.unbounded_certificate_supply', the single premise "
        "neither route supplies",
    )

    trace = query_corpus.semantic_slice_packet(
        "why does fixed precision transport fail", 4
    )
    trace_names = [
        row["name"]
        for row in trace["operator_synthesis"]["source_dependency_candidates"]
    ]
    require(
        trace_names == ["vu_word_has_prefix_locked_completion"],
        "the fixed-precision trace nominates source dependencies "
        f"{observed(trace_names)}; the failure is carried by exactly "
        "'vu_word_has_prefix_locked_completion'",
    )

    module = query_corpus.semantic_slice_packet(
        "where is the module for a direct dyadic curvature certificate", 4
    )
    module_cells = [
        (cell["kind"], cell["handle"]) for cell in module["semantic_cells"]
    ]
    require(
        module_cells == [("module", "Erdos249257.CurvatureCarry")],
        "a 'where is the module' query returned cells "
        f"{observed(module_cells)}; it must resolve to the single module cell "
        "Erdos249257.CurvatureCarry rather than to declarations inside it",
    )
    synopsis = module["semantic_cells"][0]["content"]["module"]["authored_synopsis"]
    require(
        "Curvature carry for the totient tail" in synopsis,
        "the Erdos249257.CurvatureCarry synopsis reads "
        f"{observed(synopsis)}; the authored opening is what tells a reader "
        "what the module is for",
    )


def check_elaborated_dependency_witnesses() -> None:
    # These handles are namespace-qualified, not module-qualified, so they
    # survive a declaration moving between files: the specimen below now lives
    # in Erdos249257/CurvatureCarry.lean rather than TotientTailPeriodKiller
    # .lean, while the Erdos249257.TotientTailPeriodKiller namespace is
    # unchanged. Keep the assertions unconditional -- a committed
    # docs/lean_dependency_index.json older than the Lean tree makes every
    # neighbourhood report itself unavailable, and that is a repository defect
    # the build job fails on, not a state this check should tolerate.
    curvature_handle = (
        "Erdos249257.TotientTailPeriodKiller."
        "irrational_totientSeries_of_sharpCurvatureSupply"
    )
    neighbourhood = query_corpus.formal_dependency_neighbourhood(curvature_handle)
    require(
        neighbourhood["availability"] == "available",
        lambda: unresolved_witness(
            curvature_handle, neighbourhood, "the dependency neighbourhood"
        ),
    )
    dependency_handles = {
        row["handle"] for row in neighbourhood["direct_dependencies"]
    }
    expected_dependencies = {
        "Erdos249257.TotientTailPeriodKiller.SharpCurvatureSupply",
        "Erdos249257.TotientTailPeriodKiller."
        "curvature_notMem_int_of_sharpCurvatureCert",
        "Erdos249257.TotientTailPeriodKiller."
        "rational_totient_series_forces_lcm_cone_flatness",
    }
    require(
        dependency_handles >= expected_dependencies,
        f"the elaborated neighbourhood of {curvature_handle} is missing direct "
        f"dependencies {missing(expected_dependencies, dependency_handles)}; "
        f"it reports {observed(sorted(dependency_handles))}",
    )
    require(
        any(
            path["via"].endswith(".curvature_notMem_int_of_sharpCurvatureCert")
            for path in neighbourhood["two_hop_theorem_paths"]
        ),
        f"no two-hop theorem path out of {curvature_handle} goes via "
        "curvature_notMem_int_of_sharpCurvatureCert; the emitted vias are "
        f"{observed([path['via'] for path in neighbourhood['two_hop_theorem_paths']])}",
    )
    require(
        neighbourhood["authority_posture"].startswith(
            "direct_constant_references_from_elaborated_Lean"
        ),
        "the neighbourhood authority_posture reads "
        f"{observed(neighbourhood['authority_posture'])}; it must open with "
        "'direct_constant_references_from_elaborated_Lean' so a reader cannot "
        "mistake these edges for a transitive proof explanation",
    )
    problem_handle = "ErdosProblems.Erdos243.rawNext_gcd_exact_overlap"
    problem_neighbourhood = query_corpus.formal_dependency_neighbourhood(
        problem_handle
    )
    require(
        problem_neighbourhood["availability"] == "available",
        lambda: unresolved_witness(
            problem_handle,
            problem_neighbourhood,
            "the ErdosProblems dependency neighbourhood",
        ),
    )
    require(
        problem_neighbourhood["source_ref"].startswith(
            "ErdosProblems/Erdos243/DynamicCancellation.lean:"
        ),
        f"{problem_handle} is pinned to source_ref "
        f"{observed(problem_neighbourhood['source_ref'])}, not to a line of "
        "ErdosProblems/Erdos243/DynamicCancellation.lean; the index and the "
        "Lean tree disagree about where this declaration lives",
    )
    declaration = query_corpus.declaration_packet(
        "Erdos249257.integerGreedyRemainder_lt_of_get?_eq_false", 1
    )["matches"][0]
    require(
        declaration["name"] == "integerGreedyRemainder_lt_of_get?_eq_false",
        "a declaration name containing '?' must survive the query round trip; "
        "'Erdos249257.integerGreedyRemainder_lt_of_get?_eq_false' resolved to "
        f"name {observed(declaration['name'])}",
    )
    require(
        declaration["qualified_name"]
        == "Erdos249257.integerGreedyRemainder_lt_of_get?_eq_false",
        "the qualified_name for integerGreedyRemainder_lt_of_get?_eq_false is "
        f"{observed(declaration['qualified_name'])}, not "
        "'Erdos249257.integerGreedyRemainder_lt_of_get?_eq_false'",
    )


def check_multihop_formal_dependency_reasoning() -> None:
    source = (
        "Erdos249257.TotientTailPeriodKiller."
        "irrational_totientSeries_of_sharpCurvatureSupply"
    )
    target = (
        "Erdos249257.TotientTailPeriodKiller."
        "tail_diff_int_of_den_dvd"
    )
    expected_chain = [
        "irrational_totientSeries_of_sharpCurvatureSupply",
        "rational_totient_series_forces_lcm_cone_flatness",
        "eventual_period_of_not_irrational",
        "tail_diff_int_of_den_dvd",
    ]
    path = query_corpus.formal_dependency_path(source, target, 8)
    require(
        path["availability"] == "available",
        lambda: unresolved_witness(
            f"{source} -> {target}", path, "the formal dependency path"
        ),
    )
    require(
        path["hop_count"] == 3,
        f"the dependency path from {source} to {target} has hop_count "
        f"{observed(path['hop_count'])}, not 3; the shortest elaborated route "
        "between these two theorems has changed length",
    )
    path_names = [node["name"] for node in path["nodes"]]
    require(
        path_names == expected_chain,
        f"the dependency path from {source} to {target} runs through "
        f"{observed(path_names)} rather than {observed(expected_chain)}",
    )
    edge_shapes = {
        (edge["authority"], edge["relation"]) for edge in path["edges"]
    }
    require(
        edge_shapes == {("kernel_elaborated_environment", "uses_in_elaborated_value")},
        "every edge on a formal dependency path must be a kernel-elaborated "
        "value reference; the path carries edge (authority, relation) pairs "
        f"{observed(sorted(edge_shapes))}",
    )
    cone = query_corpus.formal_dependency_proof_cone(source, 4, 20)
    require(
        cone["availability"] == "available",
        lambda: unresolved_witness(source, cone, "the formal proof cone"),
    )
    cone_depths = {node["name"]: node["depth"] for node in cone["nodes"]}
    for name, expected_depth in (
        ("rational_totient_series_forces_lcm_cone_flatness", 1),
        ("eventual_period_of_not_irrational", 2),
        ("tail_diff_int_of_den_dvd", 3),
    ):
        require(
            cone_depths[name] == expected_depth,
            f"in the proof cone of {source}, {name} sits at depth "
            f"{observed(cone_depths[name])} rather than {expected_depth}; the "
            "elaborated chain between them has gained or lost a step",
        )
    receipt = cone["omission_receipt"]
    require(
        receipt["reachable_node_count_within_depth"] > receipt["emitted_node_count"],
        "the proof cone emitted "
        f"{observed(receipt['emitted_node_count'])} of "
        f"{observed(receipt['reachable_node_count_within_depth'])} reachable "
        "nodes: the receipt must record a real omission, or a truncated cone "
        "is being presented as if it were complete",
    )
    natural_query = (
        "trace the formal chain from sharp curvature irrationality "
        "to denominator divisibility"
    )
    expected_endpoints = [
        "sharp curvature irrationality",
        "denominator divisibility",
    ]
    natural_endpoints = query_corpus.trace_endpoint_queries(natural_query)
    require(
        natural_endpoints == expected_endpoints,
        f"'{natural_query}' split into endpoints "
        f"{observed(natural_endpoints)} rather than "
        f"{observed(expected_endpoints)}",
    )
    why_query = (
        "why does sharp curvature irrationality ultimately use "
        "denominator divisibility?"
    )
    why_endpoints = query_corpus.trace_endpoint_queries(why_query)
    require(
        why_endpoints == expected_endpoints,
        f"'{why_query}' split into endpoints {observed(why_endpoints)}; the "
        "'why does X ultimately use Y' phrasing must reach the same two "
        f"endpoints as the explicit trace phrasing, {observed(expected_endpoints)}",
    )
    semantic_slice = query_corpus.semantic_slice_packet(natural_query, 20)
    slice_cells = {
        (cell["kind"], cell["handle"])
        for cell in semantic_slice["semantic_cells"]
    }
    require(
        slice_cells
        == {
            ("declaration", "irrational_totientSeries_of_sharpCurvatureSupply"),
            ("declaration", "tail_diff_int_of_den_dvd"),
        },
        "a trace query must carry exactly its two endpoint declarations as "
        f"cells; it carried {observed(sorted(slice_cells))}",
    )
    slice_path_names = [
        node["name"]
        for node in semantic_slice["operator_synthesis"]["formal_dependency_path"][
            "nodes"
        ]
    ]
    require(
        slice_path_names == expected_chain,
        "the trace slice's synthesised dependency path runs through "
        f"{observed(slice_path_names)} rather than {observed(expected_chain)}",
    )


def check_formal_goal_affordance_support() -> None:
    query = (
        "I need to prove totientTail (N + h) - totientTail N is an "
        "integer from a rational totient series; which theorem applies?"
    )
    request = query_corpus.support_goal_request(query)
    require(
        request
        == {
            "goal": "totientTail (N + h) - totientTail N is an integer",
            "context": "a rational totient series",
            "extraction": "ordinary_language_goal_pattern",
        },
        "the ordinary-language goal extractor returned "
        f"{observed(request)}; goal, context and extraction must separate "
        "cleanly or the candidate search is run against the wrong text",
    )
    packet = query_corpus.formal_goal_support_packet(query, 3)
    require(
        packet["availability"] == "available",
        lambda: unresolved_witness(
            request["goal"], packet, "the formal goal support packet"
        ),
    )
    candidate = packet["candidates"][0]
    require(
        candidate["qualified_name"]
        == "Erdos249257.TotientTailPeriodKiller.tail_diff_int_of_den_dvd",
        "the best candidate for an integer-tail goal under a rational totient "
        f"series is {observed(candidate['qualified_name'])}, not "
        "'Erdos249257.TotientTailPeriodKiller.tail_diff_int_of_den_dvd'",
    )
    affordance = candidate["formal_affordance"]
    require(
        affordance["conclusion_head"] == "Membership.mem",
        f"{candidate['qualified_name']} is offered with conclusion_head "
        f"{observed(affordance['conclusion_head'])}; the goal is an integer "
        "membership, so a candidate whose conclusion is not Membership.mem "
        "cannot close it",
    )
    conclusion_symbols = set(affordance["conclusion_symbols"])
    require(
        {"Set.range", "Int.cast"} <= conclusion_symbols,
        f"{candidate['qualified_name']} has conclusion symbols "
        f"{observed(sorted(conclusion_symbols))} and is missing "
        f"{missing({'Set.range', 'Int.cast'}, conclusion_symbols)}, which are "
        "what make the conclusion an integer-range membership",
    )
    require(
        candidate["match_receipt"]["shape_matches"] == ["direct_integer_membership"],
        "the match receipt records shape matches "
        f"{observed(candidate['match_receipt']['shape_matches'])} rather than "
        "exactly ['direct_integer_membership']; the receipt is what says why "
        "this candidate was nominated",
    )
    context_matches = set(candidate["match_receipt"]["formal_context_symbol_matches"])
    require(
        {"rational", "totient"} <= context_matches,
        "the match receipt's context symbols are "
        f"{observed(sorted(context_matches))} and are missing "
        f"{missing({'rational', 'totient'}, context_matches)}; the stated "
        "context 'a rational totient series' has stopped influencing the rank",
    )
    carry_query = (
        "I need to prove totientTail (N + h) - totientTail N is an "
        "integer from a bounded tail carry; which theorem applies?"
    )
    carry_candidate = query_corpus.formal_goal_support_packet(carry_query, 3)[
        "candidates"
    ][0]
    require(
        carry_candidate["qualified_name"]
        == "Erdos249257.tail_diff_mem_int_of_boundedTailCarry",
        "changing the stated context to 'a bounded tail carry' must change "
        f"the winning candidate; it returned {observed(carry_candidate['qualified_name'])} "
        "rather than 'Erdos249257.tail_diff_mem_int_of_boundedTailCarry'",
    )
    carry_context = set(
        carry_candidate["match_receipt"]["formal_context_symbol_matches"]
    )
    require(
        {"bounded", "carry", "tail"} <= carry_context,
        "the bounded-tail-carry receipt's context symbols are "
        f"{observed(sorted(carry_context))} and are missing "
        f"{missing({'bounded', 'carry', 'tail'}, carry_context)}",
    )
    context_free_query = (
        "I need to prove totientTail (N + h) - totientTail N is an "
        "integer; which theorem applies?"
    )
    context_free_candidate = query_corpus.formal_goal_support_packet(
        context_free_query, 3
    )["candidates"][0]
    require(
        context_free_candidate["qualified_name"]
        == "Erdos249257.tail_diff_mem_int_of_boundedTailCarry",
        "with no stated context the goal shape alone must still pick a "
        f"candidate; it picked {observed(context_free_candidate['qualified_name'])} "
        "rather than 'Erdos249257.tail_diff_mem_int_of_boundedTailCarry'",
    )
    require(
        context_free_candidate["match_receipt"]["formal_context_symbol_matches"] == [],
        "a query that states no context must record no context matches; the "
        "receipt claims "
        f"{observed(context_free_candidate['match_receipt']['formal_context_symbol_matches'])}, "
        "which would credit the ranking to context the reader never supplied",
    )
    require(
        candidate["lean_application_candidate"]
        == f"apply {candidate['qualified_name']}",
        "the emitted tactic is "
        f"{observed(candidate['lean_application_candidate'])}; it must be "
        f"'apply {candidate['qualified_name']}' so the reader can paste it",
    )
    semantic_slice = query_corpus.semantic_slice_packet(query, 20)
    slice_cells = [
        (cell["handle"], cell["selection_reason"])
        for cell in semantic_slice["semantic_cells"]
    ]
    require(
        slice_cells == [(candidate["name"], "formal_goal_shape_candidate")],
        "the support slice carries cells "
        f"{observed(slice_cells)}; it must carry exactly "
        f"{observed([(candidate['name'], 'formal_goal_shape_candidate')])}, so "
        "the reason the cell was selected travels with it",
    )
    synthesised = semantic_slice["operator_synthesis"]["formal_goal_support"]
    require(
        synthesised["candidates"][0]["qualified_name"] == candidate["qualified_name"],
        "the slice's synthesised support names "
        f"{observed(synthesised['candidates'][0]['qualified_name'])} while the "
        f"direct packet names {observed(candidate['qualified_name'])}; the two "
        "routes to the same question must agree",
    )
    application = synthesised["application"]
    require(
        application["application_status"]
        == "blocked_by_unmatched_proposition_obligations",
        "the application status is "
        f"{observed(application['application_status'])}; this goal leaves a "
        "divisibility hypothesis unmatched, and reporting anything other than "
        "'blocked_by_unmatched_proposition_obligations' would tell the reader "
        "the tactic closes when it does not",
    )
    unmatched = [
        row["name"]
        for row in application["obligations"]
        if row["status"] == "unmatched_proposition_obligation"
    ]
    require(
        unmatched == ["hdvd"],
        f"the unmatched proposition obligations are {observed(unmatched)}; "
        "exactly 'hdvd' should remain, since that is the divisibility premise "
        "the stated context does not supply",
    )
    plan = query_corpus.formal_proof_plan_packet(query, 20, 4)
    require(
        plan["terminal_candidate"]["name"] == "tail_diff_int_of_den_dvd",
        "the proof plan terminates at "
        f"{observed(plan['terminal_candidate']['name'])} rather than "
        "'tail_diff_int_of_den_dvd'",
    )
    require(
        plan["plan_status"] == "blocked_by_unmatched_proposition_obligations",
        f"the proof plan status is {observed(plan['plan_status'])}; it must "
        "stay 'blocked_by_unmatched_proposition_obligations' while hdvd is "
        "unmatched",
    )
    spine_names = {row["name"] for row in plan["exact_dependency_spine"]["steps"]}
    expected_spine = {
        "two_pow_mul_totient_series_eq",
        "summable_totient_div_two_pow",
    }
    require(
        spine_names >= expected_spine,
        "the proof plan's exact dependency spine is missing "
        f"{missing(expected_spine, spine_names)}; it lists "
        f"{observed(sorted(spine_names))}",
    )
    expected_expansion = {
        "runtime_owner": "scripts/proof_state_compiler.py",
        "pilot_command": "python3 scripts/proof_state_compiler.py --pilot-controls",
        "request_schema": "erdos249257-proof-state-request/1",
        "packet_schema": "erdos249257-proof-state-compilation/1",
        "boundary": (
            "the static proof plan nominates candidates; only the runtime "
            "owner's pinned Lean application receipt can assert that a "
            "candidate produced particular subgoals or closed"
        ),
    }
    require(
        plan["dynamic_transition_expansion"] == expected_expansion,
        "the proof plan's dynamic transition expansion reads "
        f"{observed(plan['dynamic_transition_expansion'], 600)}; it must hand "
        "the reader the runtime owner, its pilot command, both schemas, and "
        "the boundary sentence that keeps a nominated candidate from reading "
        "as a checked one",
    )
    curvature_plan = query_corpus.formal_proof_plan_packet(
        "I need to prove Irrational (∑' n : ℕ, "
        "(Nat.totient n : ℝ) / 2 ^ n) from a SharpCurvatureSupply",
        30,
        4,
    )
    require(
        curvature_plan["terminal_candidate"]["name"]
        == "irrational_totientSeries_of_sharpCurvatureSupply",
        "the SharpCurvatureSupply plan terminates at "
        f"{observed(curvature_plan['terminal_candidate']['name'])} rather than "
        "'irrational_totientSeries_of_sharpCurvatureSupply'",
    )
    require(
        curvature_plan["plan_status"]
        == "all_proposition_obligations_have_context_matches",
        "the SharpCurvatureSupply plan status is "
        f"{observed(curvature_plan['plan_status'])}; this is the case where "
        "the stated context does discharge every proposition obligation, so "
        "it must read 'all_proposition_obligations_have_context_matches'",
    )
    require(
        curvature_plan["application"]["unmatched_proposition_count"] == 0,
        "the SharpCurvatureSupply plan reports "
        f"{observed(curvature_plan['application']['unmatched_proposition_count'])} "
        "unmatched proposition obligations; a plan that claims every "
        "obligation is matched must count zero",
    )
    curvature_spine = {
        row["name"] for row in curvature_plan["exact_dependency_spine"]["steps"]
    }
    expected_curvature_spine = {
        "curvature_notMem_int_of_sharpCurvatureCert",
        "periodLcm_pos",
        "rational_totient_series_forces_lcm_cone_flatness",
    }
    require(
        curvature_spine >= expected_curvature_spine,
        "the SharpCurvatureSupply spine is missing "
        f"{missing(expected_curvature_spine, curvature_spine)}; it lists "
        f"{observed(sorted(curvature_spine))}",
    )
    negation_handle = (
        "Erdos249257.ActualForeignResidueProjection."
        "scaleFullTarget_miss_of_abs_sub_le_of_forall_int"
    )
    negation_affordance = query_corpus.lean_dependency_adjacency()[
        "formal_type_affordances"
    ][negation_handle]
    require(
        negation_affordance["conclusion_head"] == "Not",
        f"{negation_handle} is recorded with conclusion_head "
        f"{observed(negation_affordance['conclusion_head'])}; its statement is "
        "a negation, and a candidate search that thinks otherwise will offer "
        "it for the wrong goals",
    )
    require(
        negation_affordance["forall_binder_count"] == 4,
        f"{negation_handle} is recorded with forall_binder_count "
        f"{observed(negation_affordance['forall_binder_count'])}, not 4",
    )
    require(
        len(negation_affordance["binders"]) == 4,
        f"{negation_handle} declares forall_binder_count "
        f"{observed(negation_affordance['forall_binder_count'])} but carries "
        f"{len(negation_affordance['binders'])} binder rows; the count and the "
        "rows must not disagree",
    )
    binder_names = [row["name"] for row in negation_affordance["binders"]]
    require(
        binder_names == ["H", "D", "hcontrol", "hseparation"],
        f"{negation_handle} has binders {observed(binder_names)} rather than "
        "['H', 'D', 'hcontrol', 'hseparation']; binder names are what let the "
        "application receipt say which obligation is unmatched",
    )


def check_missing_registered_artifact_is_typed_not_fatal() -> None:
    old_root = query_corpus.ROOT
    with tempfile.TemporaryDirectory(prefix="query-corpus-resilience-") as tmp:
        root = Path(tmp)
        (root / "docs").mkdir()
        descriptor = {
            "identity": {
                "content": {
                    "technical_companion": {
                        "source_path": "paper/missing.tex",
                        "source_content_digest": "sha256:missing",
                        "artifact_role": "authored_companion",
                    }
                }
            }
        }
        (root / "docs/corpus_descriptor.json").write_text(
            json.dumps(descriptor), encoding="utf-8"
        )
        try:
            query_corpus.ROOT = root
            query_corpus.load.cache_clear()
            query_corpus.artifact_inventory.cache_clear()
            inventory = query_corpus.artifact_inventory()
        finally:
            query_corpus.ROOT = old_root
            query_corpus.load.cache_clear()
            query_corpus.artifact_inventory.cache_clear()

    expected_inventory = [
        {
            "artifact_id": "technical_companion",
            "artifact_role": "authored_companion",
            "authority_posture": (
                "registered_navigation_artifact_not_proof_authority"
            ),
            "follow": ["--paper-anchor <TeX_label_or_source_ref>"],
            "validation": "python3 scripts/build_corpus_descriptor.py --check",
            "artifact_kind": "authored_paper_source",
            "artifact_handle": "paper/missing.tex",
            "file_path": "paper/missing.tex",
            "fragment": None,
            "content_digest": "sha256:missing",
            "availability": "missing",
            "size_bytes": None,
        }
    ]
    require(
        inventory == expected_inventory,
        "a registered artifact whose file is absent must be inventoried with "
        "availability 'missing' rather than crashing the inventory; the "
        f"inventory came back as {observed(inventory, 800)}",
    )


def check_unavailable_paper_coordinate_is_typed_not_fatal() -> None:
    coordinate = query_corpus.paper_coordinate("sec:missing", {})
    require(
        coordinate is not None,
        "paper_coordinate('sec:missing', {}) returned None; an unresolvable "
        "TeX label must come back as a typed coordinate, because None forces "
        "every caller to guess whether the label is absent or the lookup broke",
    )
    require(
        coordinate["label"] == "sec:missing",
        "the unresolved paper coordinate echoes label "
        f"{observed(coordinate['label'])} instead of the requested "
        "'sec:missing'",
    )
    require(
        coordinate["availability"] == "authored_source_unavailable_in_worktree",
        "the unresolved paper coordinate reports availability "
        f"{observed(coordinate['availability'])}; it must say "
        "'authored_source_unavailable_in_worktree' so the reader knows the "
        "label was not found rather than found and empty",
    )
    require(
        coordinate["source_ref"] is None,
        "the unresolved paper coordinate carries source_ref "
        f"{observed(coordinate['source_ref'])}; an unavailable coordinate must "
        "carry no source reference at all rather than a fabricated one",
    )
    packet = query_corpus.paper_label_packet("res:carrycert")
    require(
        packet["kind"] == "paper_label",
        f"paper_label_packet('res:carrycert') has kind {observed(packet['kind'])}, "
        "not 'paper_label'",
    )
    require(
        packet["paper"]["label"] == "res:carrycert",
        "paper_label_packet('res:carrycert') echoes label "
        f"{observed(packet['paper']['label'])}",
    )
    attached_ids = [claim["id"] for claim in packet["attached_claims"]]
    require(
        "boolean_mobius_carry" in attached_ids,
        "the res:carrycert label is attached to claims "
        f"{observed(attached_ids)} and not to 'boolean_mobius_carry'; the "
        "paper anchor has come unbound from the claim it states",
    )


def main() -> int:
    check_dictionary_budget_and_shape()
    check_vocabulary_mismatch_queries()
    check_witness_carrying_semantic_slices()
    check_elaborated_dependency_witnesses()
    check_multihop_formal_dependency_reasoning()
    check_formal_goal_affordance_support()
    check_missing_registered_artifact_is_typed_not_fatal()
    check_unavailable_paper_coordinate_is_typed_not_fatal()
    print("query corpus semantic-resilience checks: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
