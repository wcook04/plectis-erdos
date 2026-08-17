#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Pure validation and Markdown rendering for the public methodology contract."""

from __future__ import annotations

import json
import re
from copy import deepcopy
from typing import Any


IMPLEMENTED_GUARDS = {
    "release.methodology_schema_and_references",
    "release.claim_transition_requirements",
    "release.methodology_projection_matches_source",
    "release.methodology_routes_exist",
    "release.proof_trust",
}

REQUIRED_IMPORT_CONTRACTS = [
    "docs/claims.json::machine_readable_paper.authority_order",
    "docs/claims.json::status_taxonomy",
    "docs/claims.json::remaining_open_propositions",
    "docs/claims.json::non_claims",
]

MATHEMATICAL_RESEARCH_CYCLE = [
    "open_target",
    "representation",
    "necessary_consequence",
    "proved_reduction",
    "finite_certificate",
    "lean_declaration",
    "remaining_open_proposition",
]

PUBLIC_CLAIM_CYCLE = [
    "lean_declaration",
    "checked_assumptions",
    "reviewed_intended_meaning",
    "public_claim",
    "authored_exposition",
    "generated_projection",
    "public_checkout",
]

REMAINING_OPEN_EFFECTS = {
    "proves",
    "narrows",
    "decomposes",
    "re_expresses",
    "constrains",
}

HUMAN_REVIEW_MODES = {"required", "on_trigger", "not_required"}

PRINCIPLE_GROUPS = {"proving", "publishing", "maintaining"}

# Each local-instance relation names the reference kinds it may carry. An
# instance never becomes evidence for the rule itself; it locates where the
# rule is applied, bounded, enforced, or negatively tested.
LOCAL_INSTANCE_RELATIONS = {
    "illustrates": {"public_claim"},
    "states_limit": {"remaining_open", "non_claim"},
    "enforces": {"validation_guard"},
    "tests_rejection": {"negative_fixture"},
}

# Change classes whose delta alters mathematical semantics; these may never
# downgrade human mathematical review to a trigger.
SEMANTIC_REVIEW_CHANGE_CLASSES = {
    "lean_proposition_changed",
    "assumptions_changed",
    "representation_changed",
    "open_problem_relation_changed",
    "claim_status_changed",
    "authored_exposition_changed",
}

# Forbidden effects that specific change classes must always declare.
REQUIRED_FORBIDDEN_EFFECTS = {
    "proof_body_changed": {"strengthen_public_claim_wording"},
    "finite_certificate_range_changed": {"change_open_target_status", "infer_unbounded_result"},
    "claim_support_linkage_changed": {"strengthen_public_claim_wording", "change_open_target_status"},
}

MUTATION_FIXTURE_IDS = {
    "conditional_reduction_without_remaining_open_proposition",
    "remaining_open_proposition_without_open_status",
    "finite_result_changed_to_open_status",
    "open_target_edge_without_stated_effect",
    "methodology_rule_without_implemented_guard",
    "local_instance_reference_unresolvable",
    "finite_range_forbidden_effects_removed",
    "linkage_correction_forbidden_effects_removed",
    "change_class_without_minimum_evidence",
    "semantic_change_review_downgraded",
    "authority_import_contract_removed",
    "mathematical_research_cycle_reordered",
    "public_claim_cycle_skips_review",
}


def _rule_rows(methodology: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        *methodology.get("method_axioms", []),
        *methodology.get("principles", []),
        *methodology.get("anti_principles", []),
        *methodology.get("transition_contracts", []),
    ]


def validate_contract(claims: dict[str, Any], methodology: dict[str, Any]) -> list[str]:
    """Return every structural contract error without mutating either input."""
    errors: list[str] = []

    if methodology.get("schema") != "erdos249257-methodology/2":
        errors.append("unsupported methodology schema")
    if claims.get("schema") != "erdos249257-claims/3":
        errors.append("claims must use erdos249257-claims/3")

    if not methodology.get("human_preamble"):
        errors.append("methodology needs a human_preamble")
    if not methodology.get("scope"):
        errors.append("methodology needs a scope boundary")
    if not methodology.get("artifact_role"):
        errors.append("methodology needs an artifact_role")
    if not methodology.get("human_capsule"):
        errors.append("methodology needs a human_capsule")
    if methodology.get("imports_contracts") != REQUIRED_IMPORT_CONTRACTS:
        errors.append("methodology imports_contracts must name the exact claims authority surfaces")
    if methodology.get("mathematical_research_cycle") != MATHEMATICAL_RESEARCH_CYCLE:
        errors.append("methodology mathematical_research_cycle must preserve the declared path")
    if methodology.get("public_claim_cycle") != PUBLIC_CLAIM_CYCLE:
        errors.append("methodology public_claim_cycle must preserve review and projection order")

    evidence_classes = set(methodology.get("evidence_classes", {}))
    for evidence_id, evidence in methodology.get("evidence_classes", {}).items():
        for field in ("human_name", "decides", "does_not_decide"):
            if not evidence.get(field):
                errors.append(f"evidence class {evidence_id}: missing {field}")

    mathematical_objects = {
        row.get("id") for row in methodology.get("ontology", {}).get("mathematical_objects", [])
    }
    repository_objects = {
        row.get("id") for row in methodology.get("ontology", {}).get("repository_objects", [])
    }
    object_ids = mathematical_objects | repository_objects
    change_types = set(methodology.get("change_types", []))
    claim_statuses = set(claims.get("status_taxonomy", {}))
    argument_relations = set(
        claims.get("machine_readable_paper", {})
        .get("argument_graph", {})
        .get("edge_semantics", {})
    )

    claims_by_id = {claim.get("id"): claim for claim in claims.get("claims", [])}
    remaining_rows = claims.get("remaining_open_propositions", [])
    remaining_ids = [row.get("id") for row in remaining_rows]
    remaining_id_set = set(remaining_ids)
    non_claim_ids = {row.get("id") for row in claims.get("non_claims", [])}
    guard_id_set = {guard.get("id") for guard in methodology.get("validation_guards", [])}

    rules = _rule_rows(methodology)
    rule_ids = [row.get("id") for row in rules]
    if any(not isinstance(rule_id, str) or not rule_id for rule_id in rule_ids):
        errors.append("every methodology rule and transition needs a non-empty id")
    if len(rule_ids) != len(set(rule_ids)):
        errors.append("methodology rule and transition ids must be unique")

    for row in rules:
        rule_id = row.get("id", "<missing>")
        for field in ("title", "checked_by"):
            if not row.get(field):
                errors.append(f"{rule_id}: missing {field}")
        if rule_id.startswith(("method_axiom.", "principle.", "anti_principle.")):
            for field in ("statement", "evidence_classes", "applies_to", "scope_limit"):
                if not row.get(field):
                    errors.append(f"{rule_id}: missing {field}")
            unknown_evidence = set(row.get("evidence_classes", [])) - evidence_classes
            if unknown_evidence:
                errors.append(f"{rule_id}: unknown evidence classes {sorted(unknown_evidence)}")
            for reference in row.get("applies_to", []):
                kind, separator, value = str(reference).partition(":")
                if not separator:
                    errors.append(f"{rule_id}: malformed applies_to reference {reference!r}")
                elif kind == "object" and value not in object_ids:
                    errors.append(f"{rule_id}: unknown object {value!r}")
                elif kind == "change_type" and value not in change_types:
                    errors.append(f"{rule_id}: unknown change type {value!r}")
                elif kind == "claim_status" and value not in claim_statuses:
                    errors.append(f"{rule_id}: unknown claim status {value!r}")
                elif kind == "argument_relation" and value not in argument_relations:
                    errors.append(f"{rule_id}: unknown argument relation {value!r}")
                elif kind not in {"object", "change_type", "claim_status", "argument_relation"}:
                    errors.append(f"{rule_id}: unknown applies_to reference kind {kind!r}")
        elif rule_id.startswith("transition."):
            for field in ("trigger", "required_evidence_classes", "requirements"):
                if not row.get(field):
                    errors.append(f"{rule_id}: missing {field}")
            unknown_evidence = set(row.get("required_evidence_classes", [])) - evidence_classes
            if unknown_evidence:
                errors.append(f"{rule_id}: unknown evidence classes {sorted(unknown_evidence)}")
        else:
            errors.append(f"{rule_id}: id must use a literal methodology prefix")

        unknown_guards = set(row.get("checked_by", [])) - IMPLEMENTED_GUARDS
        if unknown_guards:
            errors.append(f"{rule_id}: unknown validation guards {sorted(unknown_guards)}")

    for row in methodology.get("method_axioms", []):
        rule_id = row.get("id", "<missing>")
        if not row.get("human_name"):
            errors.append(f"{rule_id}: missing human_name")
        instances = row.get("local_instances", [])
        if not instances:
            errors.append(f"{rule_id}: needs at least one local instance")
        for instance in instances:
            relation = instance.get("relation")
            ref_kind = instance.get("ref_kind")
            ref = instance.get("ref")
            if relation not in LOCAL_INSTANCE_RELATIONS:
                errors.append(f"{rule_id}: unknown local-instance relation {relation!r}")
                continue
            if ref_kind not in LOCAL_INSTANCE_RELATIONS[relation]:
                errors.append(f"{rule_id}: relation {relation!r} does not accept ref_kind {ref_kind!r}")
                continue
            resolved = (
                (ref_kind == "public_claim" and ref in claims_by_id)
                or (ref_kind == "remaining_open" and ref in remaining_id_set)
                or (ref_kind == "non_claim" and ref in non_claim_ids)
                or (ref_kind == "validation_guard" and ref in guard_id_set)
                or (ref_kind == "negative_fixture" and ref in MUTATION_FIXTURE_IDS)
            )
            if not resolved:
                errors.append(f"{rule_id}: local instance {ref_kind} reference {ref!r} does not resolve")

    for row in methodology.get("principles", []):
        if row.get("group") not in PRINCIPLE_GROUPS:
            errors.append(f"{row.get('id', '<missing>')}: principle group must be one of {sorted(PRINCIPLE_GROUPS)}")

    trigger_rows = methodology.get("human_review_triggers", [])
    trigger_ids = {row.get("id") for row in trigger_rows}
    if len(trigger_ids) != len(trigger_rows):
        errors.append("human_review_triggers ids must be unique")
    for row in trigger_rows:
        if not row.get("id") or not row.get("description"):
            errors.append("every human review trigger needs an id and a description")

    effect_rows = methodology.get("forbidden_effect_vocabulary", [])
    effect_ids = {row.get("id") for row in effect_rows}
    if len(effect_ids) != len(effect_rows):
        errors.append("forbidden_effect_vocabulary ids must be unique")
    for row in effect_rows:
        if not row.get("id") or not row.get("description"):
            errors.append("every forbidden effect needs an id and a description")

    class_rows = methodology.get("change_classes", [])
    class_ids = [row.get("id") for row in class_rows]
    if len(class_ids) != len(set(class_ids)):
        errors.append("change_classes ids must be unique")
    if set(class_ids) != change_types:
        errors.append("change_classes must cover the declared change_types exactly")
    for row in class_rows:
        class_id = row.get("id", "<missing>")
        for field in ("summary", "public_consequence"):
            if not row.get(field):
                errors.append(f"{class_id}: missing {field}")
        minimum_evidence = row.get("minimum_evidence", [])
        if not minimum_evidence:
            errors.append(f"{class_id}: change class needs minimum evidence")
        unknown_evidence = set(minimum_evidence) - evidence_classes
        if unknown_evidence:
            errors.append(f"{class_id}: unknown evidence classes {sorted(unknown_evidence)}")
        mode = row.get("human_review")
        triggers = row.get("review_triggers", [])
        if mode not in HUMAN_REVIEW_MODES:
            errors.append(f"{class_id}: human_review must be one of {sorted(HUMAN_REVIEW_MODES)}")
        elif mode == "required":
            if "human_mathematical_review" not in minimum_evidence:
                errors.append(f"{class_id}: required review must appear in minimum evidence")
        elif mode == "on_trigger":
            if not triggers:
                errors.append(f"{class_id}: on_trigger review needs review_triggers")
        else:
            if triggers:
                errors.append(f"{class_id}: not_required review must not carry review_triggers")
            if "human_mathematical_review" in minimum_evidence:
                errors.append(f"{class_id}: not_required review conflicts with review in minimum evidence")
        unknown_triggers = set(triggers) - trigger_ids
        if unknown_triggers:
            errors.append(f"{class_id}: unknown review triggers {sorted(unknown_triggers)}")
        forbidden_effects = row.get("forbidden_effects", [])
        unknown_effects = set(forbidden_effects) - effect_ids
        if unknown_effects:
            errors.append(f"{class_id}: unknown forbidden effects {sorted(unknown_effects)}")
        missing_required = REQUIRED_FORBIDDEN_EFFECTS.get(class_id, set()) - set(forbidden_effects)
        if missing_required:
            errors.append(f"{class_id}: missing required forbidden effects {sorted(missing_required)}")
        if class_id in SEMANTIC_REVIEW_CHANGE_CLASSES and mode != "required":
            errors.append(f"{class_id}: semantic change classes require human mathematical review")

    examples = methodology.get("worked_examples", [])
    if not examples:
        errors.append("worked_examples must contain at least one example")
    example_ids = [example.get("id") for example in examples]
    if len(example_ids) != len(set(example_ids)):
        errors.append("worked_examples ids must be unique")
    for example in examples:
        example_id = example.get("id", "<missing>")
        for field in ("title", "narrative", "claim_ids"):
            if not example.get(field):
                errors.append(f"{example_id}: missing {field}")
        for claim_id in example.get("claim_ids", []):
            if claim_id not in claims_by_id:
                errors.append(f"{example_id}: unknown claim {claim_id!r}")
        for remaining_id in example.get("remaining_open_ids", []):
            if remaining_id not in remaining_id_set:
                errors.append(f"{example_id}: unknown remaining open proposition {remaining_id!r}")

    guards = methodology.get("validation_guards", [])
    guard_ids = [guard.get("id") for guard in guards]
    if set(guard_ids) != IMPLEMENTED_GUARDS or len(guard_ids) != len(set(guard_ids)):
        errors.append("validation_guards must name each implemented release guard exactly once")
    reverse_bindings = {
        guard_id: sorted(
            row.get("id") for row in rules if guard_id in set(row.get("checked_by", []))
        )
        for guard_id in IMPLEMENTED_GUARDS
    }
    for guard in guards:
        guard_id = guard.get("id")
        if not guard.get("description"):
            errors.append(f"{guard_id}: validation guard needs a description")
        if sorted(guard.get("serves", [])) != reverse_bindings.get(guard_id, []):
            errors.append(f"{guard_id}: serves must exactly reverse the rule checked_by bindings")

    if len(remaining_ids) != len(remaining_id_set):
        errors.append("remaining_open_proposition ids must be unique")
    remaining_by_id = {row.get("id"): row for row in remaining_rows}
    for row in remaining_rows:
        row_id = row.get("id", "<missing>")
        if row.get("status") != "open":
            errors.append(f"{row_id}: remaining open proposition status must be open")
        target = claims_by_id.get(row.get("open_target_claim"))
        if target is None or target.get("status") != "open":
            errors.append(f"{row_id}: open_target_claim must name an open claim")
        if not row.get("statement"):
            errors.append(f"{row_id}: missing statement")

    for claim in claims.get("claims", []):
        claim_id = claim.get("id", "<missing>")
        remaining = claim.get("remaining_open_proposition_ids", [])
        unknown = set(remaining) - remaining_id_set
        if unknown:
            errors.append(f"{claim_id}: unknown remaining open propositions {sorted(unknown)}")
        if claim.get("status") == "conditional reduction" and not remaining:
            errors.append(f"{claim_id}: conditional reduction must name a remaining open proposition")
        bounded_domain = claim.get("bounded_domain")
        if claim.get("status") == "verified finite instance" and not bounded_domain:
            errors.append(f"{claim_id}: verified finite instance must state bounded_domain")
        if bounded_domain and claim.get("status") != "verified finite instance":
            errors.append(f"{claim_id}: bounded_domain is only valid for verified finite instance")

    edges = (
        claims.get("machine_readable_paper", {})
        .get("argument_graph", {})
        .get("edges", [])
    )
    for edge in edges:
        if edge.get("relation") != "advances_open_target":
            continue
        source = edge.get("from", "<missing>")
        target_id = edge.get("to")
        target = claims_by_id.get(target_id)
        effect = edge.get("remaining_open_effect")
        if target is None or target.get("status") != "open":
            errors.append(f"argument edge {source}->{target_id}: target must be an open claim")
        if not isinstance(effect, dict):
            errors.append(f"argument edge {source}->{target_id}: missing remaining_open_effect")
            continue
        remaining_id = effect.get("remaining_open_proposition_id")
        remaining_row = remaining_by_id.get(remaining_id)
        if remaining_row is None:
            errors.append(f"argument edge {source}->{target_id}: unknown remaining open proposition")
        elif remaining_row.get("open_target_claim") != target_id:
            errors.append(f"argument edge {source}->{target_id}: remaining open proposition belongs to another target")
        if effect.get("operation") not in REMAINING_OPEN_EFFECTS:
            errors.append(f"argument edge {source}->{target_id}: invalid remaining-open operation")
        if not effect.get("statement"):
            errors.append(f"argument edge {source}->{target_id}: remaining-open effect needs a statement")

    return errors


def render_markdown(methodology: dict[str, Any], claims: dict[str, Any]) -> str:
    """Render the human root document from the machine-readable owner.

    The projection is audience-specific: standing rules with local instances,
    evidence responsibilities, grouped principles, worked examples, the
    change matrix, and rejected inferences. Ontology entries, applicability
    bindings, forbidden-effect fields, and transition contracts stay in the
    machine source and the descriptor capsule.
    """
    claims_by_id = {claim["id"]: claim for claim in claims.get("claims", [])}
    remaining_by_id = {row["id"]: row for row in claims.get("remaining_open_propositions", [])}
    non_claims_by_id = {row["id"]: row for row in claims.get("non_claims", [])}
    evidence_classes = methodology["evidence_classes"]

    # REUSE-IgnoreStart
    lines = [
        "<!-- SPDX-FileCopyrightText: 2026 Will Cook -->",
        "<!-- SPDX-License-Identifier: Apache-2.0 -->",
        "<!-- Generated by scripts/build_methodology.py from docs/methodology.json. Do not edit directly. -->",
        "",
        f"# {methodology['title']}",
        "",
    ]
    # REUSE-IgnoreEnd
    for paragraph in methodology["human_preamble"]:
        lines.extend([paragraph, ""])

    lines.extend(["## Standing rules", ""])
    for index, axiom in enumerate(methodology["method_axioms"], start=1):
        lines.extend([f"### {index}. {axiom['human_name']}", "", axiom["statement"], ""])
        illustrations = [row for row in axiom["local_instances"] if row["relation"] == "illustrates"]
        if illustrations:
            seen = "; ".join(
                f"{claims_by_id[row['ref']]['label']} (`{row['ref']}`)" for row in illustrations
            )
            lines.extend([f"Seen in: {seen}.", ""])
        for row in axiom["local_instances"]:
            if row["relation"] != "states_limit":
                continue
            if row["ref_kind"] == "remaining_open":
                boundary = remaining_by_id[row["ref"]]["statement"]
            else:
                boundary = non_claims_by_id[row["ref"]]["meaning"]
            lines.extend([f"Recorded boundary: {boundary.rstrip('.')} (`{row['ref']}`).", ""])
        lines.extend([f"Limit: {axiom['scope_limit']}", ""])

    lines.extend(["## Evidence responsibilities", ""])
    for evidence in evidence_classes.values():
        label = evidence.get("decides_label", "Decides")
        lines.extend(
            [
                f"### {evidence['human_name']}",
                "",
                f"{label}: {evidence['decides']}",
                "",
                f"Does not decide: {evidence['does_not_decide']}",
                "",
            ]
        )

    lines.extend(
        [
            "## Research and publication paths",
            "",
            "The machine source records two bounded paths. They are navigation and review order, not additional mathematical implications.",
            "",
            "### Mathematical research path",
            "",
            " → ".join(f"`{step}`" for step in methodology["mathematical_research_cycle"]),
            "",
            "A route may stop at any intermediate object. In particular, a necessary consequence, reduction, finite certificate, or Lean declaration does not remove the final remaining-open proposition unless a checked theorem actually does so.",
            "",
            "### Public claim path",
            "",
            " → ".join(f"`{step}`" for step in methodology["public_claim_cycle"]),
            "",
            "This is the authority order for publication. Kernel acceptance precedes assumption review; intended meaning is reviewed before a public claim; authored exposition precedes generated projections; and the public checkout is the final reader-facing surface.",
            "",
        ]
    )

    lines.extend(["## Working principles", ""])
    for group, heading in (("proving", "Proving"), ("publishing", "Publishing"), ("maintaining", "Maintaining")):
        lines.extend([f"### {heading}", ""])
        lines.extend(
            f"- {row['statement']}" for row in methodology["principles"] if row["group"] == group
        )
        lines.append("")

    lines.extend(["## Three examples from this development", ""])
    for example in methodology["worked_examples"]:
        lines.extend([f"### {example['title']}", ""])
        route = example.get("route", [])
        if route:
            lines.append("```text")
            lines.append(route[0])
            lines.extend(f"→ {step}" for step in route[1:])
            lines.extend(["```", ""])
        lines.extend([example["narrative"], ""])
        claim_refs = "; ".join(
            f"{claims_by_id[claim_id]['label']} (`{claim_id}`)" for claim_id in example["claim_ids"]
        )
        lines.extend([f"Claims: {claim_refs}.", ""])
        remaining_refs = example.get("remaining_open_ids", [])
        if remaining_refs:
            lines.extend(["Remaining open: " + "; ".join(f"`{rid}`" for rid in remaining_refs) + ".", ""])

    lines.extend(
        [
            "## Before changing a public claim",
            "",
            "Classify the change first. Each class states its minimum evidence, whether human mathematical review is needed, and the public consequence. The machine source additionally records, for each class, the effects the change must not have.",
            "",
            "| Change | Minimum evidence | Mathematical review | Public consequence |",
            "|---|---|---|---|",
        ]
    )
    for row in methodology["change_classes"]:
        evidence_names = ", ".join(
            evidence_classes[evidence_id]["human_name"] for evidence_id in row["minimum_evidence"]
        )
        if row["human_review"] == "required":
            review = "required"
        elif row["human_review"] == "not_required":
            review = "not required"
        else:
            review = "only when " + " or ".join(
                trigger.replace("_", " ") for trigger in row["review_triggers"]
            )
        lines.append(f"| {row['summary']} | {evidence_names} | {review} | {row['public_consequence']} |")
    lines.append("")

    lines.extend(["## Rejected inferences", ""])
    lines.extend(f"- {row['statement']}" for row in methodology["anti_principles"])
    lines.append("")

    lines.extend(
        [
            "## Authority and machine identifiers",
            "",
            "Lean source checked by the pinned Lean kernel remains proof authority. `docs/claims.json` remains the owner of release identity, claim status, remaining open propositions, and argument relationships. `docs/methodology.json` owns the rules on this page and records, for every rule, its evidence classes, applicability bindings, scope limit, local references, and validation guards. The authored paper remains the owner of mathematical exposition.",
            "",
            "`METHODOLOGY.md` is generated from `docs/methodology.json`; run `python3 scripts/build_methodology.py` after changing the source. `python3 scripts/check_release.py` checks the source schema, typed claim-transition requirements, the change-class matrix, local references, exact Markdown projection, descriptor registration, and entry routes.",
            "",
            "Machine identifiers for the standing rules, in the order the rules appear above:",
            "",
            "```text",
        ]
    )
    for index, axiom in enumerate(methodology["method_axioms"], start=1):
        lines.append(f"{index}. {axiom['human_name']}")
        lines.append(f"   {axiom['id']}")
    lines.append("```")
    lines.extend(
        [
            "",
            "Principles, rejected inferences, change classes, review triggers, forbidden effects, and claim-transition contracts keep their full identifiers and machine fields in `docs/methodology.json`.",
            "",
        ]
    )
    return "\n".join(lines)


def mutation_fixture_errors(claims: dict[str, Any], methodology: dict[str, Any]) -> dict[str, list[str]]:
    """Return validator results for the public failure shapes used by tests."""
    fixtures: dict[str, tuple[dict[str, Any], dict[str, Any]]] = {}

    missing_remaining = deepcopy(claims)
    conditional = next(row for row in missing_remaining["claims"] if row["status"] == "conditional reduction")
    conditional.pop("remaining_open_proposition_ids", None)
    fixtures["conditional_reduction_without_remaining_open_proposition"] = (missing_remaining, methodology)

    unstated_open = deepcopy(claims)
    unstated_open["remaining_open_propositions"][0].pop("status", None)
    fixtures["remaining_open_proposition_without_open_status"] = (unstated_open, methodology)

    finite_promoted = deepcopy(claims)
    finite = next(row for row in finite_promoted["claims"] if row["status"] == "verified finite instance")
    finite["status"] = "open"
    fixtures["finite_result_changed_to_open_status"] = (finite_promoted, methodology)

    edge_without_effect = deepcopy(claims)
    edge = next(
        row
        for row in edge_without_effect["machine_readable_paper"]["argument_graph"]["edges"]
        if row["relation"] == "advances_open_target"
    )
    edge.pop("remaining_open_effect", None)
    fixtures["open_target_edge_without_stated_effect"] = (edge_without_effect, methodology)

    unknown_guard = deepcopy(methodology)
    unknown_guard["method_axioms"][0]["checked_by"] = ["release.not_implemented"]
    fixtures["methodology_rule_without_implemented_guard"] = (claims, unknown_guard)

    unresolvable_reference = deepcopy(methodology)
    unresolvable_reference["method_axioms"][3]["local_instances"][0]["ref"] = "claim_that_does_not_exist"
    fixtures["local_instance_reference_unresolvable"] = (claims, unresolvable_reference)

    forbidden_dropped = deepcopy(methodology)
    finite_class = next(
        row for row in forbidden_dropped["change_classes"] if row["id"] == "finite_certificate_range_changed"
    )
    finite_class["forbidden_effects"] = []
    fixtures["finite_range_forbidden_effects_removed"] = (claims, forbidden_dropped)

    linkage_dropped = deepcopy(methodology)
    linkage_class = next(
        row for row in linkage_dropped["change_classes"] if row["id"] == "claim_support_linkage_changed"
    )
    linkage_class["forbidden_effects"] = []
    fixtures["linkage_correction_forbidden_effects_removed"] = (claims, linkage_dropped)

    evidence_dropped = deepcopy(methodology)
    body_class = next(
        row for row in evidence_dropped["change_classes"] if row["id"] == "proof_body_changed"
    )
    body_class["minimum_evidence"] = []
    fixtures["change_class_without_minimum_evidence"] = (claims, evidence_dropped)

    review_downgraded = deepcopy(methodology)
    proposition_class = next(
        row for row in review_downgraded["change_classes"] if row["id"] == "lean_proposition_changed"
    )
    proposition_class["human_review"] = "on_trigger"
    proposition_class["review_triggers"] = ["claim_text_changed"]
    fixtures["semantic_change_review_downgraded"] = (claims, review_downgraded)

    missing_import = deepcopy(methodology)
    missing_import["imports_contracts"] = missing_import["imports_contracts"][:-1]
    fixtures["authority_import_contract_removed"] = (claims, missing_import)

    reordered_research = deepcopy(methodology)
    reordered_research["mathematical_research_cycle"][1:3] = reversed(
        reordered_research["mathematical_research_cycle"][1:3]
    )
    fixtures["mathematical_research_cycle_reordered"] = (claims, reordered_research)

    skipped_review = deepcopy(methodology)
    skipped_review["public_claim_cycle"].remove("reviewed_intended_meaning")
    fixtures["public_claim_cycle_skips_review"] = (claims, skipped_review)

    if set(fixtures) != MUTATION_FIXTURE_IDS:
        raise AssertionError("mutation fixtures drifted from MUTATION_FIXTURE_IDS")

    return {
        fixture_id: validate_contract(fixture_claims, fixture_methodology)
        for fixture_id, (fixture_claims, fixture_methodology) in fixtures.items()
    }
