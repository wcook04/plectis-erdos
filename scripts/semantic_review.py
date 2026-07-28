#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Digest and validate authored semantic-review receipts.

Authored meaning, confidence, and a relation basis are not themselves evidence
that someone checked the wording against the cited Lean declarations. This
module owns the stronger receipt. Each receipt identifies one exact subject,
is bound to the pinned formal-source revision and declaration-atlas
fingerprint, and states what the review did and did not establish.

The authored registry is ``docs/semantic/reviews.json``. The semantic corpus
builder attaches only valid receipts; stale receipts make the build fail.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parent.parent
REGISTRY = ROOT / "docs" / "semantic" / "reviews.json"
CORPUS = ROOT / "docs" / "semantic_corpus.json"
CLAIMS = ROOT / "docs" / "claims.json"

REGISTRY_SCHEMA = "erdos249257-semantic-reviews/1"
REQUIRED_RECEIPT_FIELDS = frozenset(
    {
        "reviewer",
        "reviewer_type",
        "reviewed_revision",
        "reviewed_at",
        "evidence_digest",
        "review_scope",
        "claim_ceiling",
    }
)


def canonical_digest(payload: dict) -> str:
    encoded = json.dumps(
        payload,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


def relation_subject_id(edge: dict) -> str:
    """Return the stable identity of one mathematical relation."""
    return f"{edge.get('from')}|{edge.get('relation')}|{edge.get('to')}"


def node_review_material(
    node: dict,
    *,
    evidence_fingerprint: str,
    reviewed_revision: str,
) -> dict:
    return {
        "schema": "erdos249257-semantic-review-material/1",
        "subject_kind": "statement_node",
        "subject_id": node.get("id"),
        "reviewed_revision": reviewed_revision,
        "evidence_fingerprint": evidence_fingerprint,
        "canonical_statement": node.get("canonical_statement"),
        "logical_class": node.get("logical_class"),
        "problem": node.get("problem"),
        "evidence": sorted(
            (
                {
                    "id": evidence.get("id"),
                    "kind": evidence.get("kind"),
                    "resolved": evidence.get("resolved"),
                }
                for evidence in node.get("evidence", [])
            ),
            key=lambda row: (str(row.get("id")), str(row.get("kind"))),
        ),
        "open_antecedents": node.get("open_antecedents", []),
        "scope_caveat": node.get("scope_caveat", ""),
        "prior_art_state": node.get("prior_art_state"),
    }


def relation_review_material(
    edge: dict,
    *,
    evidence_fingerprint: str,
    reviewed_revision: str,
) -> dict:
    return {
        "schema": "erdos249257-semantic-review-material/1",
        "subject_kind": "relation",
        "subject_id": relation_subject_id(edge),
        "reviewed_revision": reviewed_revision,
        "evidence_fingerprint": evidence_fingerprint,
        "from": edge.get("from"),
        "relation": edge.get("relation"),
        "to": edge.get("to"),
        "basis": edge.get("basis"),
        "scope": edge.get("scope"),
        "zone": edge.get("zone"),
        "lens": edge.get("lens"),
        "both_sides_open": edge.get("both_sides_open", False),
    }


def subject_digest(
    subject_kind: str,
    subject: dict,
    *,
    evidence_fingerprint: str,
    reviewed_revision: str,
) -> str:
    if subject_kind == "statement_node":
        material = node_review_material(
            subject,
            evidence_fingerprint=evidence_fingerprint,
            reviewed_revision=reviewed_revision,
        )
    elif subject_kind == "relation":
        material = relation_review_material(
            subject,
            evidence_fingerprint=evidence_fingerprint,
            reviewed_revision=reviewed_revision,
        )
    else:
        raise ValueError(f"unsupported semantic-review subject kind: {subject_kind!r}")
    return canonical_digest(material)


def receipt_payload(review: dict) -> dict:
    return {
        field: review[field]
        for field in sorted(REQUIRED_RECEIPT_FIELDS | {"notes", "source_refs"})
        if field in review
    }


def apply_review_registry(
    registry: dict,
    nodes: dict[str, dict],
    relations: list[dict],
    *,
    evidence_fingerprint: str,
    reviewed_revision: str,
) -> list[str]:
    """Validate and attach receipts, returning every exact error."""
    errors: list[str] = []
    if registry.get("schema") != REGISTRY_SCHEMA:
        errors.append(
            f"semantic review registry schema is {registry.get('schema')!r}, "
            f"expected {REGISTRY_SCHEMA!r}"
        )

    relation_index: dict[str, dict] = {}
    duplicate_relations: set[str] = set()
    for edge in relations:
        if edge.get("suppressed_in_views"):
            continue
        key = relation_subject_id(edge)
        if key in relation_index:
            duplicate_relations.add(key)
        relation_index[key] = edge
    for key in sorted(duplicate_relations):
        errors.append(f"relation review subject is ambiguous: {key}")

    seen: set[tuple[str, str]] = set()
    for review in registry.get("reviews", []):
        kind = review.get("subject_kind")
        subject_id = review.get("subject_id")
        identity = (str(kind), str(subject_id))
        if identity in seen:
            errors.append(
                f"duplicate semantic review receipt for {kind} {subject_id}"
            )
            continue
        seen.add(identity)

        missing = sorted(REQUIRED_RECEIPT_FIELDS - set(review))
        if missing or any(not review.get(field) for field in REQUIRED_RECEIPT_FIELDS):
            errors.append(
                f"semantic review receipt for {kind} {subject_id} "
                f"lacks nonempty fields: {missing or 'one or more required values'}"
            )
            continue
        if review.get("reviewed_revision") != reviewed_revision:
            errors.append(
                f"semantic review receipt for {kind} {subject_id} targets "
                f"{review.get('reviewed_revision')!r}, expected {reviewed_revision!r}"
            )
            continue
        if kind == "statement_node":
            subject = nodes.get(str(subject_id))
        elif kind == "relation":
            subject = relation_index.get(str(subject_id))
        else:
            errors.append(
                f"semantic review receipt has unsupported subject kind: {kind!r}"
            )
            continue
        if subject is None:
            errors.append(
                f"semantic review receipt subject is absent: {kind} {subject_id}"
            )
            continue

        expected = subject_digest(
            str(kind),
            subject,
            evidence_fingerprint=evidence_fingerprint,
            reviewed_revision=reviewed_revision,
        )
        if review.get("evidence_digest") != expected:
            errors.append(
                f"semantic review receipt digest is stale for {kind} {subject_id}: "
                f"{review.get('evidence_digest')!r}, expected {expected!r}"
            )
            continue
        subject["semantic_review"] = receipt_payload(review)
    return errors


def formal_source_revision(claims: dict) -> str:
    return str(claims.get("release", {}).get("formal_source", {}).get("ref", ""))


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def attached_receipt_errors(
    registry: dict,
    corpus: dict,
    *,
    reviewed_revision: str,
) -> list[str]:
    nodes = {node["id"]: dict(node) for node in corpus.get("statement_nodes", [])}
    relations = [dict(edge) for edge in corpus.get("relations", [])]
    for node in nodes.values():
        node.pop("semantic_review", None)
    for edge in relations:
        edge.pop("semantic_review", None)
    errors = apply_review_registry(
        registry,
        nodes,
        relations,
        evidence_fingerprint=str(corpus.get("evidence_fingerprint", "")),
        reviewed_revision=reviewed_revision,
    )
    if errors:
        return errors

    expected_nodes = {
        node_id: node.get("semantic_review")
        for node_id, node in nodes.items()
        if node.get("semantic_review")
    }
    actual_nodes = {
        node["id"]: node.get("semantic_review")
        for node in corpus.get("statement_nodes", [])
        if node.get("semantic_review")
    }
    if actual_nodes != expected_nodes:
        errors.append("generated statement-node review receipts differ from the registry")

    expected_relations = {
        relation_subject_id(edge): edge.get("semantic_review")
        for edge in relations
        if not edge.get("suppressed_in_views") and edge.get("semantic_review")
    }
    actual_relations = {
        relation_subject_id(edge): edge.get("semantic_review")
        for edge in corpus.get("relations", [])
        if not edge.get("suppressed_in_views") and edge.get("semantic_review")
    }
    if actual_relations != expected_relations:
        errors.append("generated relation review receipts differ from the registry")
    return errors


def _find_subject(
    corpus: dict,
    *,
    node_id: str | None,
    relation_id: str | None,
) -> tuple[str, dict]:
    if node_id:
        for node in corpus.get("statement_nodes", []):
            if node.get("id") == node_id:
                return "statement_node", node
        raise ValueError(f"statement node not found: {node_id}")
    if relation_id:
        matches = [
            edge
            for edge in corpus.get("relations", [])
            if not edge.get("suppressed_in_views")
            and relation_subject_id(edge) == relation_id
        ]
        if len(matches) != 1:
            raise ValueError(
                f"relation id resolved to {len(matches)} rows, expected one: {relation_id}"
            )
        return "relation", matches[0]
    raise ValueError("select --digest-node or --digest-relation")


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--report", action="store_true")
    parser.add_argument("--digest-node")
    parser.add_argument("--digest-relation")
    args = parser.parse_args(argv)

    corpus = load(CORPUS)
    claims = load(CLAIMS)
    registry = load(REGISTRY)
    revision = formal_source_revision(claims)

    if args.digest_node or args.digest_relation:
        try:
            kind, subject = _find_subject(
                corpus,
                node_id=args.digest_node,
                relation_id=args.digest_relation,
            )
        except ValueError as error:
            print(f"semantic review: FAIL: {error}")
            return 1
        print(
            json.dumps(
                {
                    "subject_kind": kind,
                    "subject_id": (
                        subject.get("id")
                        if kind == "statement_node"
                        else relation_subject_id(subject)
                    ),
                    "reviewed_revision": revision,
                    "evidence_digest": subject_digest(
                        kind,
                        subject,
                        evidence_fingerprint=str(
                            corpus.get("evidence_fingerprint", "")
                        ),
                        reviewed_revision=revision,
                    ),
                },
                indent=2,
                ensure_ascii=False,
            )
        )
        return 0

    errors = attached_receipt_errors(
        registry,
        corpus,
        reviewed_revision=revision,
    )
    if errors:
        print("semantic review registry: FAIL")
        for error in errors:
            print(f"  {error}")
        return 1

    node_count = sum(
        1
        for row in registry.get("reviews", [])
        if row.get("subject_kind") == "statement_node"
    )
    relation_count = sum(
        1
        for row in registry.get("reviews", [])
        if row.get("subject_kind") == "relation"
    )
    if args.check or args.report:
        print(
            "semantic review registry: PASS; "
            f"{node_count} statement node(s), {relation_count} relation(s), "
            "all revision- and evidence-bound"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
