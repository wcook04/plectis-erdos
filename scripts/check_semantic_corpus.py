#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Enforce the semantic corpus routing and statement-graph contract.

The point of this checker is that the failure it exists to prevent has already
happened once.  A barrier theorem about the squarefree support was carried to
the edge of publication as closing a family of certificate engines, when a
third and weaker engine existed in the same file that the barrier did not
close.  Nothing in the repository could have caught that, because no surface
recorded which engines existed, which a barrier reached, or which it did not.

So the contract below is not bookkeeping.  Each rule closes one way the corpus
could go back to being legible only by rereading it:

 1. every live declaration has exactly one typed routing receipt;
 2. every declaration presented as a statement names one statement node;
 3. every other declaration has an explicit non-statement role and zone;
 4. every generated declaration is owned by a family with a schema and evidence;
 5. every statement node has resolved evidence, or is explicitly external/open;
 6. every mathematical relation carries an evidence basis;
 7. no declaration belongs silently to neither problem;
 8. nothing in the curated ledger is missing a semantic node;
 9. vocabularies are closed, ids unique, and barriers carry a scope caveat;
10. every expert question names a live open proposition and checked consumer;
11. per-problem counts are emitted by class, provenance and prior-art state;
12. the coverage receipt distinguishes exhaustive routing from selective
    statement-level interpretation.

Run from the repository root:

    python3 scripts/check_semantic_corpus.py
    python3 scripts/check_semantic_corpus.py --counts
"""

from __future__ import annotations

import argparse
import json
import os
from collections import Counter
import stat
from pathlib import Path

from build_semantic_corpus import semantic_input_fingerprint
from semantic_review import REGISTRY as SEMANTIC_REVIEWS
from semantic_review import attached_receipt_errors, formal_source_revision

ROOT = Path(__file__).resolve().parent.parent
CORPUS = ROOT / "docs" / "semantic_corpus.json"
ATLAS = ROOT / "docs" / "declaration_atlas.json"
MANIFEST = ROOT / "docs" / "generated_certificate_manifest.json"
CLAIMS = ROOT / "docs" / "claims.json"
SEMANTIC_DIR = ROOT / "docs" / "semantic"
ZONES_DIR = SEMANTIC_DIR / "zones"

FAILURES: list[str] = []


def check(condition: bool, message: str) -> None:
    if not condition:
        FAILURES.append(message)


class UnsafeSemanticCorpusInput(ValueError):
    """A semantic-corpus input is outside the regular checkout boundary."""


def _safe_semantic_path(path: Path) -> Path:
    """Reject checkout escapes and symbolic-link path components."""
    root = Path(os.path.abspath(ROOT))
    candidate = Path(os.path.abspath(path))
    current = candidate
    while True:
        if current.is_symlink():
            raise UnsafeSemanticCorpusInput(
                f"symlinked semantic-corpus input: {candidate}"
            )
        if current == root:
            break
        if current.parent == current:
            raise UnsafeSemanticCorpusInput(
                f"semantic-corpus input escaped checkout: {candidate}"
            )
        current = current.parent
    return candidate


def safe_read_text(path: Path) -> str:
    """Read a semantic-corpus input through a no-follow regular descriptor."""
    candidate = _safe_semantic_path(path)
    if not candidate.is_file():
        raise UnsafeSemanticCorpusInput(
            f"semantic-corpus input is not a regular file: {candidate}"
        )
    flags = os.O_RDONLY
    flags |= getattr(os, "O_CLOEXEC", 0)
    flags |= getattr(os, "O_NONBLOCK", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(candidate, flags)
    except OSError as exc:
        raise UnsafeSemanticCorpusInput(
            f"semantic-corpus input could not be opened safely: {candidate}"
        ) from exc
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise UnsafeSemanticCorpusInput(
                f"semantic-corpus input is not a regular file: {candidate}"
            )
        with os.fdopen(descriptor, "r", encoding="utf-8") as stream:
            descriptor = -1
            return stream.read()
    finally:
        if descriptor >= 0:
            os.close(descriptor)


def load(path: Path) -> dict:
    return json.loads(safe_read_text(path))


def authored_relation_sources() -> tuple[list[tuple[str, dict]], list[tuple[str, dict]]]:
    """Read the authored relation inputs without assigning significance to order."""
    zones = [
        (path.relative_to(ROOT).as_posix(), load(path))
        for path in sorted(ZONES_DIR.glob("*.json"))
    ]
    relation_lenses = [
        (path.relative_to(ROOT).as_posix(), load(path))
        for path in sorted(SEMANTIC_DIR.glob("relations_*.json"))
    ]
    return zones, relation_lenses


# The builder attaches a validated semantic-review receipt to a relation it
# projects. That receipt is evidence about the relation, never part of it, and
# an author cannot write one into a zone or lens file. Counting it as relation
# content made every reviewed relation report as one omission and one invention
# of itself: eight of each, the same eight edges twice. The receipt is checked
# by semantic_review.py, which strips it from the subject for the same reason.
REVIEW_ATTACHMENT_FIELDS = ("semantic_review",)


def relation_identity(edge: dict) -> str:
    """Use complete authored relation content as an order-independent parity identity."""
    authored = {
        key: value
        for key, value in edge.items()
        if key not in REVIEW_ATTACHMENT_FIELDS
    }
    return json.dumps(authored, sort_keys=True, separators=(",", ":"))


def relation_parity_errors(
    corpus: dict,
    *,
    zones: list[tuple[str, dict]] | None = None,
    relation_lenses: list[tuple[str, dict]] | None = None,
) -> list[str]:
    """Require every surviving authored relation to reach the projection unchanged.

    The generated corpus deliberately drops only relations incident to a node
    explicitly absorbed into a generated family.  Comparing complete relation
    identities, as multisets, preserves basis and any future boundary fields
    while allowing source files and arrays to be reordered.
    """
    if zones is None or relation_lenses is None:
        zones, relation_lenses = authored_relation_sources()

    errors: list[str] = []
    source_nodes: dict[tuple[str, str], str] = {}
    source_locals: dict[str, list[str]] = {}
    for _, zone in zones:
        zone_id = zone.get("zone_id")
        if not isinstance(zone_id, str) or not zone_id:
            errors.append("authored relation source has an invalid zone ID")
            continue
        for node in zone.get("statement_nodes", []):
            local_id = node.get("id") if isinstance(node, dict) else None
            if not isinstance(local_id, str) or not local_id:
                errors.append(f"authored relation source {zone_id} has an invalid node ID")
                continue
            qualified = f"{zone_id}::{local_id}"
            source_nodes[(zone_id, local_id)] = qualified
            source_locals.setdefault(local_id, []).append(qualified)

    generated_nodes = {
        node.get("id")
        for node in corpus.get("statement_nodes", [])
        if isinstance(node, dict) and isinstance(node.get("id"), str)
    }
    absorbed_nodes = {
        row.get("node")
        for row in corpus.get("integrity", {}).get(
            "nodes_absorbed_into_generated_families", []
        )
        if isinstance(row, dict) and isinstance(row.get("node"), str)
    }
    unresolved = corpus.get("integrity", {}).get("unresolved_relation_endpoints", [])
    unresolved = unresolved if isinstance(unresolved, list) else []

    expected: Counter[str] = Counter()

    def append_if_surviving(edge: dict, source_label: str) -> None:
        endpoints = (edge["from"], edge["to"])
        missing = [endpoint for endpoint in endpoints if endpoint not in generated_nodes]
        if not missing:
            expected[relation_identity(edge)] += 1
            return
        unexpected = [endpoint for endpoint in missing if endpoint not in absorbed_nodes]
        if unexpected:
            errors.append(
                f"authored relation {source_label} lost endpoint(s) without generated-family absorption: "
                + ", ".join(sorted(unexpected))
            )

    for source_path, zone in zones:
        zone_id = zone.get("zone_id")
        if not isinstance(zone_id, str):
            continue
        for index, raw_edge in enumerate(zone.get("intra_zone_relations", []), 1):
            if not isinstance(raw_edge, dict):
                errors.append(f"authored relation {source_path}:{index} is not an object")
                continue
            source = source_nodes.get((zone_id, raw_edge.get("from")))
            target = source_nodes.get((zone_id, raw_edge.get("to")))
            if source is None or target is None:
                errors.append(
                    f"authored relation {source_path}:{index} has an endpoint absent from its zone"
                )
                continue
            append_if_surviving(
                {**raw_edge, "from": source, "to": target, "scope": "intra_zone", "zone": zone_id},
                f"{source_path}:{index}",
            )

    def resolve(local_id: object, zone_id: object) -> str | None:
        if not isinstance(local_id, str):
            return None
        if isinstance(zone_id, str):
            return source_nodes.get((zone_id, local_id))
        candidates = source_locals.get(local_id, [])
        return candidates[0] if len(candidates) == 1 else None

    for source_path, lens_payload in relation_lenses:
        lens = lens_payload.get("lens", Path(source_path).stem)
        for index, raw_edge in enumerate(lens_payload.get("edges", []), 1):
            if not isinstance(raw_edge, dict):
                errors.append(f"authored relation {source_path}:{index} is not an object")
                continue
            source = resolve(raw_edge.get("from"), raw_edge.get("from_zone"))
            target = resolve(raw_edge.get("to"), raw_edge.get("to_zone"))
            if source is None or target is None:
                if not any(
                    isinstance(row, dict)
                    and row.get("from") == raw_edge.get("from")
                    and row.get("to") == raw_edge.get("to")
                    and row.get("lens") == lens
                    for row in unresolved
                ):
                    errors.append(
                        f"authored relation {source_path}:{index} is unresolved without a projection receipt"
                    )
                continue
            append_if_surviving(
                {**raw_edge, "from": source, "to": target, "scope": "cross_zone", "lens": lens},
                f"{source_path}:{index}",
            )

    actual = Counter(
        relation_identity(edge)
        for edge in corpus.get("relations", [])
        if isinstance(edge, dict) and edge.get("scope") in {"intra_zone", "cross_zone"}
    )
    missing = expected - actual
    extra = actual - expected
    if missing:
        errors.append(
            f"generated semantic corpus omits {sum(missing.values())} authored relation(s)"
        )
    if extra:
        errors.append(
            f"generated semantic corpus invents {sum(extra.values())} authored relation(s)"
        )
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--counts", action="store_true", help="print the per-problem census")
    args = parser.parse_args()

    if not CORPUS.is_file():
        print("docs/semantic_corpus.json missing; run python3 scripts/build_semantic_corpus.py")
        return 1

    try:
        corpus = load(CORPUS)
        atlas = load(ATLAS)
        manifest = load(MANIFEST)
        claims = load(CLAIMS)
    except UnsafeSemanticCorpusInput as exc:
        print(f"unsafe semantic-corpus input: {exc}")
        return 1
    vocab = corpus["vocabularies"]

    check(
        corpus.get("semantic_input_fingerprint") == semantic_input_fingerprint(),
        "semantic corpus is stale relative to the atlas or authored semantic inputs",
    )
    relation_errors = relation_parity_errors(corpus)
    check(
        not relation_errors,
        "semantic corpus relation parity failed: " + "; ".join(relation_errors[:3]),
    )
    expected_formal_source = {
        key: claims["release"]["formal_source"][key]
        for key in ("ref", "ref_kind", "publication_state")
    }
    actual_formal_source = (
        corpus.get("source_provenance", {}).get("formal_source", {})
    )
    check(
        all(
            actual_formal_source.get(key) == value
            for key, value in expected_formal_source.items()
        ),
        "semantic corpus formal-source provenance differs from docs/claims.json",
    )
    check(
        "source_revision" not in corpus,
        "semantic corpus uses the ambiguous legacy source_revision field",
    )

    nodes = {n["id"]: n for n in corpus["statement_nodes"]}
    roles = {r["id"]: r for r in corpus["declaration_roles"]}
    atlas_rows = {r["id"]: r for r in atlas["declarations"]}

    review_errors = attached_receipt_errors(
        load(SEMANTIC_REVIEWS),
        corpus,
        reviewed_revision=formal_source_revision(claims),
    )
    check(
        not review_errors,
        "semantic review registry is stale or invalid: "
        + "; ".join(review_errors[:3]),
    )
    headline_claim_count = sum(
        1 for claim in claims.get("claims", []) if claim.get("readme_headline")
    )
    coverage = corpus.get("summary", {}).get("coverage", {})
    check(
        coverage.get("readme_headline_claims") == headline_claim_count,
        "semantic corpus headline-claim review census differs from docs/claims.json",
    )
    unreviewed_headlines = corpus.get("integrity", {}).get(
        "readme_headline_claims_without_reviewed_node", []
    )
    check(
        not unreviewed_headlines,
        "README headline claim families lack a digest-reviewed semantic node: "
        + ", ".join(unreviewed_headlines[:4]),
    )

    # 1. every live declaration is routed exactly once.  The merged roles
    # object cannot itself reveal two authored source assignments because the
    # later row would overwrite the first, so the builder records that
    # condition before merging and this checker rejects it explicitly.
    missing = sorted(set(atlas_rows) - set(roles))
    check(
        not missing,
        f"{len(missing)} declaration(s) have no typed semantic route, first: {missing[:3]}",
    )
    duplicate_roles = corpus.get("integrity", {}).get(
        "duplicate_role_assignments", []
    )
    check(
        not duplicate_roles,
        f"{len(duplicate_roles)} declaration(s) have more than one authored routing receipt",
    )
    # A role pointing at a declaration that does not exist is inert: it owns
    # nothing and claims nothing, and the builder drops it.  It is reported
    # rather than failed, because the classifier that wrote it was reading an
    # older atlas that named anonymous instances and matched prose inside
    # docstrings.  Evidence on a statement node is the opposite case -- a node
    # citing a declaration that does not exist is a false claim, and rule 5
    # below fails on it.
    residual = corpus.get("integrity", {}).get("phantom_declaration_references", [])
    if residual:
        print(
            f"note: {len(residual)} inert role reference(s) name no live declaration and were dropped"
        )

    # 2 & 3. Role legality and the explicit statement boundary.  A support
    # lemma may deliberately be routed as substrate without a canonical
    # statement node.  That is zone-level routing, not statement-level
    # interpretation, and the coverage receipt below counts the two separately.
    role_names = set(vocab["declaration_roles"])
    bad_role = [k for k, r in roles.items() if r.get("role") not in role_names]
    check(not bad_role, f"{len(bad_role)} declaration(s) carry an unknown role, first: {bad_role[:3]}")

    dangling = [
        k
        for k, r in roles.items()
        if r.get("statement_node") and r["statement_node"] not in nodes
    ]
    check(
        not dangling,
        f"{len(dangling)} declaration(s) point at a statement node that does not exist, first: {dangling[:3]}",
    )
    missing_zone = [
        key for key, role in roles.items() if not role.get("zone")
    ]
    check(
        not missing_zone,
        f"{len(missing_zone)} declaration(s) have no semantic zone, first: {missing_zone[:3]}",
    )
    routing_basis_catalog = corpus.get("routing_basis_catalog", {})
    unresolved_routing_basis_refs = [
        key
        for key, role in roles.items()
        if role.get("routing_basis_ref")
        and role["routing_basis_ref"] not in routing_basis_catalog
    ]
    check(
        not unresolved_routing_basis_refs,
        (
            f"{len(unresolved_routing_basis_refs)} declaration route(s) name "
            "an absent routing-basis reference"
        ),
    )

    unlinked_statement_roles = [
        k
        for k, r in roles.items()
        if r.get("role") == "statement"
        and not r.get("statement_node")
    ]
    check(
        not unlinked_statement_roles,
        f"{len(unlinked_statement_roles)} declaration(s) claim role 'statement' with no node",
    )
    automatic_inventory_roles = {
        key: role
        for key, role in roles.items()
        if role.get("routing_origin") == "automatic_inventory_fallback"
    }
    malformed_inventory_roles = [
        key
        for key, role in automatic_inventory_roles.items()
        if role.get("role") != "substrate"
        or role.get("statement_node") is not None
        or role.get("zone") != "inventory"
        or not role.get("routing_basis")
    ]
    check(
        not malformed_inventory_roles,
        (
            f"{len(malformed_inventory_roles)} automatic inventory route(s) "
            "claim semantic meaning or lack a routing basis"
        ),
    )
    structural_roles = {
        key: role
        for key, role in roles.items()
        if role.get("routing_origin") == "source_structural_family"
    }
    malformed_structural_roles = [
        key
        for key, role in structural_roles.items()
        if not role.get("statement_node")
        or not role.get("routing_basis")
        or nodes.get(role.get("statement_node"), {}).get("interpretation_tier")
        != "source_structural_family"
    ]
    check(
        not malformed_structural_roles,
        (
            f"{len(malformed_structural_roles)} source-structural route(s) "
            "lack an exact family node or routing basis"
        ),
    )

    # 4. generated provenance is a contract, not a filename pattern
    manifest_paths = {p for f in manifest["families"] for p in f["module_paths"]}
    atlas_generated = {r["module"] for r in atlas["declarations"] if r["generated_certificate"]}
    check(
        atlas_generated <= manifest_paths,
        f"{len(atlas_generated - manifest_paths)} module(s) marked generated in the atlas are absent from the manifest",
    )
    missing_paths = sorted(p for p in manifest_paths if not (ROOT / p).is_file())
    check(not missing_paths, f"manifest lists {len(missing_paths)} module(s) that do not exist: {missing_paths[:3]}")
    for family in manifest["families"]:
        check(
            bool(family.get("provenance_evidence")) and bool(family.get("template_statement")),
            f"generated family {family['id']} lacks provenance evidence or a template statement",
        )

    # 5. statement nodes carry resolved evidence, or say why not
    for nid, node in nodes.items():
        if node.get("logical_class") == "generated_certificate_instance":
            continue
        evidence = node.get("evidence", [])
        external = node.get("prior_art_state") in ("known_classical", "prior_art_found")
        check(
            bool(evidence) or any(e.get("resolved") and e.get("evidence_class") == "ordinary_mathematical_proof" for e in node.get("source_evidence", [])) or external or bool(node.get("open_antecedents")),
            f"statement node {nid} has no evidence declaration and is not marked external or open",
        )
        unresolved = [e for e in evidence if not e.get("resolved")]
        check(
            not unresolved,
            f"statement node {nid} cites {len(unresolved)} declaration(s) not found in the atlas",
        )

    # 6. every mathematical relation has an evidence basis
    relation_names = set(vocab["relations"])
    for edge in corpus["relations"]:
        if edge.get("suppressed_in_views"):
            continue
        check(
            edge.get("relation") in relation_names,
            f"relation {edge.get('relation')!r} is outside the closed vocabulary",
        )
        check(
            bool(edge.get("basis")),
            f"relation {edge.get('from')} -> {edge.get('to')} carries no evidence basis",
        )
        for endpoint in ("from", "to"):
            check(
                edge.get(endpoint) in nodes,
                f"relation endpoint {edge.get(endpoint)!r} is not a statement node",
            )

    # Optional semantic-review receipts are stronger than authorship,
    # confidence, or a nonempty basis.  If present, they are revision- and
    # evidence-bound; absence remains an explicit `not measured` result.
    review_fields = {
        "reviewer",
        "reviewed_revision",
        "reviewed_at",
        "evidence_digest",
        "claim_ceiling",
    }
    for item_id, item in [
        *((nid, node) for nid, node in nodes.items()),
        *(
            (f"{edge.get('from')}->{edge.get('to')}", edge)
            for edge in corpus["relations"]
            if not edge.get("suppressed_in_views")
        ),
    ]:
        receipt = item.get("semantic_review")
        if receipt is None:
            continue
        check(
            isinstance(receipt, dict)
            and review_fields <= set(receipt)
            and all(receipt.get(field) for field in review_fields),
            f"semantic review receipt for {item_id} is not revision- and evidence-bound",
        )

    # 7. nothing silently belongs to neither problem
    problems = set(vocab["problems"])
    unassigned = [nid for nid, n in nodes.items() if n.get("problem") not in problems]
    check(
        not unassigned,
        f"{len(unassigned)} statement node(s) belong to no problem, first: {unassigned[:3]}",
    )

    # 8. the curated ledger is downstream of this graph
    integrity = corpus.get("integrity", {})
    orphaned_claims = integrity.get("curated_claim_declarations_without_node", [])
    check(
        not orphaned_claims,
        f"{len(orphaned_claims)} curated claim declaration(s) have no semantic node, first: {orphaned_claims[:3]}",
    )

    # 9. closed vocabularies, unique ids, scoped barriers
    classes = set(vocab["logical_classes"])
    states = set(vocab["prior_art_states"])
    for nid, node in nodes.items():
        check(node.get("logical_class") in classes, f"node {nid} has class {node.get('logical_class')!r}")
        check(node.get("prior_art_state") in states, f"node {nid} has prior-art state {node.get('prior_art_state')!r}")
        if node.get("logical_class") == "barrier_no_go":
            check(
                bool(node.get("scope_caveat")),
                f"barrier node {nid} does not say what it fails to rule out",
            )
        if node.get("logical_class") == "conditional_implication":
            check(
                bool(node.get("open_antecedents")),
                f"conditional node {nid} names no open antecedent",
            )
    check(
        len(nodes) == len(corpus["statement_nodes"]),
        "statement node ids are not unique",
    )
    multiply_counted_evidence = integrity.get(
        "multi_node_evidence_without_equivalence", []
    )
    check(
        not multiply_counted_evidence,
        (
            f"{len(multiply_counted_evidence)} declaration/node pair(s) reuse one "
            "Lean proposition as distinct statements without an alias, definitional "
            "equivalence, or typed evidence-sharing exception"
        ),
    )

    # 10. expert questions are executable handoffs, not wish-list prose
    expert_questions = corpus.get("frontier", {}).get("expert_questions", [])
    expert_ids = [row.get("id") for row in expert_questions]
    check(
        len(expert_ids) == len(set(expert_ids)),
        "expert question ids are not unique",
    )
    open_ids = {row["id"] for row in claims["remaining_open_propositions"]}
    claim_ids = {row["id"] for row in claims["claims"]}
    expert_classes = {
        "endpoint_equivalent",
        "sufficient_for_erdos_249",
        "sufficient_for_counterexample",
    }
    for row in expert_questions:
        qid = row.get("id", "<missing>")
        check(row.get("problem") in {"249", "257"}, f"expert question {qid} has invalid problem")
        check(
            row.get("classification") in expert_classes,
            f"expert question {qid} has invalid classification",
        )
        check(row.get("status") == "OPEN", f"expert question {qid} is not tagged OPEN")
        check(
            row.get("open_proposition_id") in open_ids,
            f"expert question {qid} names no live open proposition",
        )
        check(
            row.get("source_claim_id") in claim_ids,
            f"expert question {qid} names no live source claim",
        )
        for field in (
            "exact_ask",
            "payoff",
            "boundary",
            "known_obstruction",
            "current_hypothesis",
        ):
            check(bool(row.get(field)), f"expert question {qid} lacks {field}")
        check(
            row.get("hypothesis_confidence") in {"low", "medium", "high"},
            f"expert question {qid} has invalid hypothesis_confidence",
        )
        alternatives = row.get("plausible_alternatives", [])
        alternative_ids = [alternative.get("id") for alternative in alternatives]
        check(
            len(alternatives) >= 2
            and len(alternative_ids) == len(set(alternative_ids)),
            f"expert question {qid} lacks distinct plausible alternatives",
        )
        for alternative in alternatives:
            for field in ("id", "statement", "consequence"):
                check(
                    bool(alternative.get(field)),
                    f"expert question {qid} alternative lacks {field}",
                )
        for field in ("current_evidence", "discriminating_evidence"):
            evidence = row.get(field, [])
            check(
                isinstance(evidence, list)
                and len(evidence) >= 2
                and all(isinstance(item, str) and item for item in evidence),
                f"expert question {qid} lacks typed {field}",
            )
        consumers = row.get("consumer_declarations", [])
        check(bool(consumers), f"expert question {qid} names no checked consumer")
        for consumer in consumers:
            key = (
                f"{consumer.get('module')}:{consumer.get('line')}:"
                f"{consumer.get('declaration')}"
            )
            check(
                key in atlas_rows,
                f"expert question {qid} consumer is absent from the declaration atlas: {key}",
            )
        check(
            row.get("source_claim_id", "") in row.get("verification_command", ""),
            f"expert question {qid} verification command does not select its source claim",
        )
    check(
        bool(corpus.get("frontier", {}).get("expert_question_limits")),
        "expert questions carry no global limits",
    )

    # 12. Coverage is a vector, not one scalar.  Inventory and routing are
    # exhaustive; statement-level interpretation is selective and must be
    # reported as such.  Recompute the counts from the live atlas and receipts
    # so a hand-edited summary cannot upgrade the semantic ceiling.
    coverage_contract = corpus.get("coverage_contract", {})
    check(
        coverage_contract.get("posture")
        == "exhaustive_source_structural_linkage_with_selective_authored_interpretation",
        "semantic corpus does not state the exhaustive-linkage/tiered-interpretation boundary",
    )
    authored_theorem_like = {
        key
        for key, row in atlas_rows.items()
        if not row.get("generated_certificate")
        and row.get("kind") in ("theorem", "lemma")
    }
    node_linked = {
        key for key, role in roles.items() if role.get("statement_node")
    }
    authored_node_linked = authored_theorem_like & node_linked
    authored_zone_only = authored_theorem_like - node_linked
    authored_structural = {
        key
        for key in authored_theorem_like
        if (roles.get(key) or {}).get("interpretation_tier")
        == "source_structural_family"
    }
    authored_statement_interpretation = authored_node_linked - authored_structural
    direct_evidence = set()
    authored_statement_evidence = set()
    structural_family_evidence = set()
    for node in nodes.values():
        for evidence in node.get("evidence", []):
            evidence_id = evidence.get("id")
            if not evidence.get("resolved") or not evidence_id:
                continue
            direct_evidence.add(evidence_id)
            if node.get("interpretation_tier") == "authored_statement":
                authored_statement_evidence.add(evidence_id)
            elif node.get("interpretation_tier") == "source_structural_family":
                structural_family_evidence.add(evidence_id)
    authored_direct_evidence = authored_theorem_like & direct_evidence
    authored_statement_direct_evidence = (
        authored_statement_interpretation & authored_statement_evidence
    )
    authored_statement_contextual_links = (
        authored_statement_interpretation
        - authored_statement_direct_evidence
    )
    summary_coverage = corpus["summary"]["coverage"]
    authored_total = max(1, len(authored_theorem_like))
    expected_coverage = {
        "declarations_owned": len(roles),
        "automatic_inventory_fallback_count": len(automatic_inventory_roles),
        "duplicate_role_assignment_count": len(duplicate_roles),
        "node_linked_declarations": len(node_linked),
        "authored_theorem_like_node_linked": len(authored_node_linked),
        "authored_theorem_like_zone_only": len(authored_zone_only),
        "authored_theorem_like_authored_statement_interpretation": len(
            authored_statement_interpretation
        ),
        "authored_theorem_like_source_structural_family": len(
            authored_structural
        ),
        "authored_theorem_like_authored_statement_direct_evidence": len(
            authored_statement_direct_evidence
        ),
        "authored_theorem_like_authored_statement_contextual_links": len(
            authored_statement_contextual_links
        ),
        "authored_theorem_like_structural_family_direct_evidence": len(
            authored_theorem_like & structural_family_evidence
        ),
        "authored_theorem_like_direct_evidence": len(authored_direct_evidence),
        "authored_theorem_like_contextual_node_links": len(
            authored_statement_contextual_links
        ),
        "curated_claim_declarations_without_node": len(
            integrity.get("curated_claim_declarations_without_node", [])
        ),
        "statement_nodes_with_semantic_review_receipt": sum(
            1 for node in nodes.values() if node.get("semantic_review")
        ),
        "relations_with_semantic_review_receipt": sum(
            1
            for edge in corpus["relations"]
            if not edge.get("suppressed_in_views")
            and edge.get("semantic_review")
        ),
    }
    for field, expected in expected_coverage.items():
        check(
            summary_coverage.get(field) == expected,
            f"coverage receipt field {field} is {summary_coverage.get(field)!r}, expected {expected}",
        )
    expected_fractions = {
        "authored_theorem_like_node_linked_fraction": round(
            len(authored_node_linked) / authored_total, 4
        ),
        "authored_theorem_like_authored_statement_interpretation_fraction": round(
            len(authored_statement_interpretation) / authored_total, 4
        ),
        "authored_theorem_like_authored_statement_direct_evidence_fraction": round(
            len(authored_statement_direct_evidence) / authored_total, 4
        ),
        "authored_theorem_like_direct_evidence_fraction": round(
            len(authored_direct_evidence) / authored_total, 4
        ),
    }
    for field, expected in expected_fractions.items():
        check(
            summary_coverage.get(field) == expected,
            (
                f"coverage receipt field {field} is "
                f"{summary_coverage.get(field)!r}, expected {expected}"
            ),
        )
    check(
        not authored_zone_only,
        (
            f"{len(authored_zone_only)} authored theorem-like declaration(s) "
            "lack a statement node; exact structural-family compilation must "
            "keep this coverage at 100%"
        ),
    )
    check(
        authored_direct_evidence == authored_theorem_like,
        (
            f"{len(authored_theorem_like - authored_direct_evidence)} authored "
            "theorem-like declaration(s) lack exact statement-node evidence"
        ),
    )
    expected_structural_node_count = sum(
        node.get("interpretation_tier") == "source_structural_family"
        for node in nodes.values()
    )
    check(
        corpus["summary"].get("source_structural_family_nodes")
        == expected_structural_node_count,
        "source-structural family node count drifted from live nodes",
    )
    check(
        bool(coverage_contract.get("accuracy_boundary")),
        "coverage receipt omits the mathematical-accuracy boundary",
    )
    check(
        bool(coverage_contract.get("anti_filler")),
        "coverage receipt omits the direct-evidence anti-filler boundary",
    )

    # 11. emit the census
    if args.counts or not FAILURES:
        summary = corpus["summary"]
        print("semantic corpus coverage receipt")
        print(f"  declarations           {summary['declarations']}")
        print(f"    authored             {summary['authored_declarations']}")
        print(f"    generated            {summary['generated_declarations']}")
        print(f"    authored theorem-like{summary['authored_theorem_like']:>6}")
        print(f"  statement nodes        {summary['statement_nodes']}")
        print(f"  relations              {summary['relations']}")
        cov = summary["coverage"]
        print(
            f"  routing                {cov['declarations_owned']}/{summary['declarations']} "
            f"live declarations, {cov['duplicate_role_assignment_count']} duplicate receipts"
        )
        print(
            "  statement-level        "
            f"{cov['authored_theorem_like_node_linked']}/"
            f"{summary['authored_theorem_like']} authored theorem-like declarations "
            f"({cov['authored_theorem_like_node_linked_fraction']:.1%}); "
            f"{cov['authored_theorem_like_zone_only']} zone-routed only"
        )
        print(
            "    authored readings    "
            f"{cov['authored_theorem_like_authored_statement_interpretation']}/"
            f"{summary['authored_theorem_like']} "
            f"({cov['authored_theorem_like_authored_statement_interpretation_fraction']:.1%})"
        )
        print(
            "      direct evidence    "
            f"{cov['authored_theorem_like_authored_statement_direct_evidence']}/"
            f"{summary['authored_theorem_like']} "
            f"({cov['authored_theorem_like_authored_statement_direct_evidence_fraction']:.1%})"
        )
        print(
            "      contextual family  "
            f"{cov['authored_theorem_like_authored_statement_contextual_links']}/"
            f"{summary['authored_theorem_like']}"
        )
        print(
            "    structural families  "
            f"{cov['authored_theorem_like_source_structural_family']}/"
            f"{summary['authored_theorem_like']} across "
            f"{summary['source_structural_family_nodes']} exact signature families"
        )
        print(
            "  direct evidence        "
            f"{cov['authored_theorem_like_direct_evidence']}/"
            f"{summary['authored_theorem_like']} theorem-like declarations "
            f"({cov['authored_theorem_like_direct_evidence_fraction']:.1%}); "
            f"{cov['authored_theorem_like_contextual_node_links']} contextual links"
        )
        print(
            f"  curated ledger covers  {cov['curated_claim_declarations']} declarations "
            f"({cov['curated_fraction_of_authored_theorem_like']:.1%} of authored theorem-like)"
        )
        for problem, block in summary["per_problem"].items():
            if not block["statement_nodes"]:
                continue
            print(f"  problem {problem}: {block['statement_nodes']} nodes, "
                  f"{block['restatements_of_open_problem']} restatements, "
                  f"{block['with_open_antecedents']} with open antecedents")
            for cls, n in sorted(block["by_logical_class"].items(), key=lambda kv: -kv[1]):
                print(f"      {cls:34s} {n}")

    if FAILURES:
        print(f"\ncheck_semantic_corpus: {len(FAILURES)} failure(s)")
        for failure in FAILURES[:40]:
            print(f"  FAIL {failure}")
        if len(FAILURES) > 40:
            print(f"  ... and {len(FAILURES) - 40} more")
        return 1

    print(
        "\ncheck_semantic_corpus: exhaustive routing and selective "
        "statement-graph contract satisfied"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
