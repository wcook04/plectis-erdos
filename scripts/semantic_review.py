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
        for field in sorted(
            REQUIRED_RECEIPT_FIELDS
            | {"notes", "source_refs", "evidence_rebindings"}
        )
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


SUBSTANTIVE_MATERIAL_FIELDS_EXCLUDED = ("evidence_fingerprint",)


def substantive_material(material: dict) -> dict:
    """Return the reviewed mathematics, with the moving pins removed.

    A receipt's digest covers the declaration-atlas source fingerprint, which
    is a fingerprint of the whole Lean tree. Adding an unrelated module moves
    it, so every receipt goes stale even though no reviewed wording, evidence
    coordinate, or boundary changed. This projection is what stays fixed when
    only that pin moves, and it is the thing a rebind is not allowed to alter.
    """
    return {
        key: value
        for key, value in material.items()
        if key not in SUBSTANTIVE_MATERIAL_FIELDS_EXCLUDED
    }


def material_for(
    subject_kind: str,
    subject: dict,
    *,
    evidence_fingerprint: str,
    reviewed_revision: str,
) -> dict:
    if subject_kind == "statement_node":
        return node_review_material(
            subject,
            evidence_fingerprint=evidence_fingerprint,
            reviewed_revision=reviewed_revision,
        )
    if subject_kind == "relation":
        return relation_review_material(
            subject,
            evidence_fingerprint=evidence_fingerprint,
            reviewed_revision=reviewed_revision,
        )
    raise ValueError(f"unsupported semantic-review subject kind: {subject_kind!r}")


def _subject_index(corpus: dict) -> dict[tuple[str, str], dict]:
    index: dict[tuple[str, str], dict] = {}
    for node in corpus.get("statement_nodes", []):
        subject = dict(node)
        subject.pop("semantic_review", None)
        index[("statement_node", str(node.get("id")))] = subject
    for edge in corpus.get("relations", []):
        if edge.get("suppressed_in_views"):
            continue
        subject = dict(edge)
        subject.pop("semantic_review", None)
        index[("relation", relation_subject_id(edge))] = subject
    return index


def _field_changes(before: dict, after: dict) -> list[str]:
    changes = []
    for key in sorted(set(before) | set(after)):
        if before.get(key) != after.get(key):
            changes.append(key)
    return changes


def rebind_receipts(
    registry: dict,
    committed_corpus: dict,
    candidate_corpus: dict,
    *,
    reviewed_revision: str,
) -> tuple[list[dict], list[str]]:
    """Rebind every stale receipt whose reviewed material is provably unchanged.

    Returns the rebinding records, every refusal, and every receipt that
    already binds the rebuilt tree and is only waiting on the corpus. A
    receipt is rebound only
    when all three hold: its stored digest reproduces exactly under the
    fingerprint the committed corpus was built with, so it was genuinely valid
    before; the subject still exists; and its substantive material is
    byte-identical between the committed and candidate corpora. Anything else
    is a real content change and needs a real re-review, so it is refused by
    name and the registry is left alone.
    """
    old_fingerprint = str(committed_corpus.get("evidence_fingerprint", ""))
    new_fingerprint = str(candidate_corpus.get("evidence_fingerprint", ""))
    old_subjects = _subject_index(committed_corpus)
    new_subjects = _subject_index(candidate_corpus)

    rebindings: list[dict] = []
    refusals: list[str] = []
    already_current: list[str] = []

    for review in registry.get("reviews", []):
        kind = str(review.get("subject_kind"))
        subject_id = str(review.get("subject_id"))
        identity = (kind, subject_id)
        label = f"{kind} {subject_id}"

        if review.get("reviewed_revision") != reviewed_revision:
            refusals.append(
                f"{label}: receipt targets formal-source revision "
                f"{review.get('reviewed_revision')!r} but the claims release pins "
                f"{reviewed_revision!r}; the formal source moved, so this needs a "
                "re-review, not a rebind"
            )
            continue

        old_subject = old_subjects.get(identity)
        new_subject = new_subjects.get(identity)
        if old_subject is None:
            refusals.append(
                f"{label}: absent from the committed corpus, so there is no "
                "previous state to prove the receipt against"
            )
            continue
        if new_subject is None:
            refusals.append(
                f"{label}: the subject no longer exists in the rebuilt corpus; "
                "retire the receipt or restore the subject"
            )
            continue

        old_material = material_for(
            kind,
            old_subject,
            evidence_fingerprint=old_fingerprint,
            reviewed_revision=reviewed_revision,
        )
        new_material = material_for(
            kind,
            new_subject,
            evidence_fingerprint=new_fingerprint,
            reviewed_revision=reviewed_revision,
        )
        if review.get("evidence_digest") != canonical_digest(old_material):
            if review.get("evidence_digest") == canonical_digest(new_material):
                # Already rebound against the rebuilt tree; the committed
                # corpus on disk is simply the one that has not caught up.
                already_current.append(label)
                continue
            refusals.append(
                f"{label}: the stored digest does not reproduce against the "
                "committed corpus, so this receipt was already stale for a "
                "reason other than a moved atlas fingerprint"
            )
            continue
        changed = _field_changes(
            substantive_material(old_material), substantive_material(new_material)
        )
        if changed:
            refusals.append(
                f"{label}: reviewed material changed in {', '.join(changed)}; "
                "this is a mathematical change and needs a real re-review"
            )
            continue

        expected = canonical_digest(new_material)
        if expected == review.get("evidence_digest"):
            continue

        rebindings.append(
            {
                "review": review,
                "subject_kind": kind,
                "subject_id": subject_id,
                "previous_evidence_digest": review["evidence_digest"],
                "previous_evidence_fingerprint": old_fingerprint,
                "evidence_fingerprint": new_fingerprint,
                "evidence_digest": expected,
            }
        )

    return rebindings, refusals, already_current


def apply_rebindings(rebindings: list[dict]) -> None:
    """Rewrite each receipt in place, keeping the previous binding on record."""
    for record in rebindings:
        review = record["review"]
        history = list(review.get("evidence_rebindings", []))
        history.append(
            {
                "previous_evidence_digest": record["previous_evidence_digest"],
                "previous_evidence_fingerprint": record[
                    "previous_evidence_fingerprint"
                ],
                "evidence_fingerprint": record["evidence_fingerprint"],
                "reason": (
                    "declaration-atlas source fingerprint moved; reviewed "
                    "wording, evidence coordinates, boundary, and formal-source "
                    "revision were verified unchanged"
                ),
            }
        )
        review["evidence_digest"] = record["evidence_digest"]
        review["evidence_rebindings"] = history


MOVED_REVISION_REASON = (
    "re-review at a moved formal-source revision; every cited declaration's "
    "statement verified byte-identical across the move"
)


def _atlas_signatures_at(revision: str) -> dict[tuple[str, str], tuple[str, str]]:
    """Return ``(module, name) -> (kind, signature)`` from the atlas at ``revision``."""
    import subprocess

    raw = subprocess.run(
        ["git", "show", f"{revision}:docs/declaration_atlas.json"],
        cwd=ROOT,
        capture_output=True,
        check=True,
    ).stdout
    atlas = json.loads(raw)
    return {
        (str(row.get("module")), str(row.get("name"))): (
            str(row.get("kind")),
            str(row.get("signature")),
        )
        for row in atlas.get("declarations", [])
    }


def _cited_declarations(kind: str, subject: dict, nodes_by_id: dict) -> list[tuple[str, str]]:
    if kind == "statement_node":
        sources = [subject]
    else:
        sources = [
            nodes_by_id[str(subject.get(end))]
            for end in ("from", "to")
            if str(subject.get(end)) in nodes_by_id
        ]
    cited = {
        (str(evidence.get("module")), str(evidence.get("declaration")))
        for node in sources
        for evidence in node.get("evidence", [])
        if evidence.get("declaration")
    }
    return sorted(cited)


def rereview_moved_revision(
    registry: dict,
    committed_corpus: dict,
    candidate_corpus: dict,
    *,
    new_revision: str,
    today: str,
    old_signatures: dict[tuple[str, str], tuple[str, str]] | None = None,
    new_signatures: dict[tuple[str, str], tuple[str, str]] | None = None,
) -> tuple[list[dict], list[str]]:
    """Re-issue every receipt at a moved formal-source revision.

    A rebind may move only the atlas fingerprint. When the claims release pins
    a new formal-source commit, every receipt names the previous one and the
    rebind refuses. The previous checkpoint moves were done by hand with one
    proof: every declaration cited by a receipted subject was located in both
    revisions and its full statement compared byte for byte. This is that
    proof as a command. A receipt is re-issued only when (1) its digest still
    reproduces against the committed corpus at the old revision, (2) its
    substantive material is unchanged in the rebuilt corpus, and (3) every
    cited declaration has the same kind and signature in the declaration
    atlas at the old revision and in the rebuilt atlas. Any other difference
    is a mathematical change and is refused for a real re-review.
    """
    old_fingerprint = str(committed_corpus.get("evidence_fingerprint"))
    new_fingerprint = str(candidate_corpus.get("evidence_fingerprint"))
    old_subjects = _subject_index(committed_corpus)
    new_subjects = _subject_index(candidate_corpus)
    new_nodes = {
        subject.get("id"): subject
        for (kind, _), subject in new_subjects.items()
        if kind == "statement_node"
    }
    reviews = registry.get("reviews", [])
    old_revisions = {str(review.get("reviewed_revision")) for review in reviews}
    refusals: list[str] = []
    if len(old_revisions) != 1:
        return [], [f"receipts name {len(old_revisions)} distinct revisions; expected one"]
    old_revision = next(iter(old_revisions))
    if old_revision == new_revision:
        return [], ["the claims release still pins the receipts' revision; nothing moved"]
    if new_signatures is None:
        current_atlas = json.loads(
            (ROOT / "docs" / "declaration_atlas.json").read_text(encoding="utf-8")
        )
        new_signatures = {
            (str(row.get("module")), str(row.get("name"))): (
                str(row.get("kind")),
                str(row.get("signature")),
            )
            for row in current_atlas.get("declarations", [])
        }
    if old_signatures is None:
        old_signatures = _atlas_signatures_at(old_revision)

    reissues: list[dict] = []
    for review in reviews:
        kind = str(review.get("subject_kind"))
        subject_id = str(review.get("subject_id"))
        identity = (kind, subject_id)
        label = f"{kind} {subject_id}"
        old_subject = old_subjects.get(identity)
        new_subject = new_subjects.get(identity)
        if old_subject is None or new_subject is None:
            refusals.append(f"{label}: subject absent from the committed or rebuilt corpus")
            continue
        old_material = material_for(
            kind, old_subject, evidence_fingerprint=old_fingerprint, reviewed_revision=old_revision
        )
        if review.get("evidence_digest") != canonical_digest(old_material):
            refusals.append(
                f"{label}: the stored digest does not reproduce against the committed "
                "corpus at the old revision, so this receipt was already stale"
            )
            continue
        new_material_old_rev = material_for(
            kind, new_subject, evidence_fingerprint=new_fingerprint, reviewed_revision=old_revision
        )
        changed = _field_changes(
            substantive_material(old_material), substantive_material(new_material_old_rev)
        )
        if changed:
            refusals.append(
                f"{label}: reviewed material changed in {', '.join(changed)}; "
                "this is a mathematical change and needs a real re-review"
            )
            continue
        cited = _cited_declarations(kind, new_subject, new_nodes)
        if not cited:
            refusals.append(f"{label}: no cited declaration to compare across revisions")
            continue
        moved = [
            f"{module}:{name}"
            for module, name in cited
            if old_signatures.get((module, name)) != new_signatures.get((module, name))
            or (module, name) not in old_signatures
        ]
        if moved:
            refusals.append(
                f"{label}: cited declaration statement differs between {old_revision[:12]} "
                f"and {new_revision[:12]}: {', '.join(moved)}"
            )
            continue
        new_material = material_for(
            kind, new_subject, evidence_fingerprint=new_fingerprint, reviewed_revision=new_revision
        )
        reissues.append(
            {
                "review": review,
                "label": label,
                "cited": cited,
                "previous_evidence_digest": review["evidence_digest"],
                "previous_evidence_fingerprint": old_fingerprint,
                "evidence_fingerprint": new_fingerprint,
                "evidence_digest": canonical_digest(new_material),
                "old_revision": old_revision,
            }
        )
    return reissues, refusals


def apply_rereviews(reissues: list[dict], *, new_revision: str, today: str) -> None:
    for record in reissues:
        review = record["review"]
        old_revision = record["old_revision"]
        history = list(review.get("evidence_rebindings", []))
        history.append(
            {
                "previous_evidence_digest": record["previous_evidence_digest"],
                "previous_evidence_fingerprint": record["previous_evidence_fingerprint"],
                "evidence_fingerprint": record["evidence_fingerprint"],
                "reason": MOVED_REVISION_REASON,
            }
        )
        review["evidence_digest"] = record["evidence_digest"]
        review["evidence_rebindings"] = history
        review["reviewed_revision"] = new_revision
        review["reviewed_at"] = today
        review["review_scope"] = (
            str(review.get("review_scope", "")).rstrip()
            + f" Re-reviewed on {today} for the formal-source move from {old_revision} "
            f"to {new_revision}. Every declaration cited by this subject was located in "
            "both revisions and its full statement compared byte for byte: all are "
            "identical, and only their line coordinates moved. The canonical wording, "
            "typed relation basis, scope, and claim boundary are unchanged, so the "
            "reviewed source-to-wording consistency carries over verbatim to the new "
            "checkpoint. This is a model consistency review, not human mathematical "
            "review and not Lean proof authority."
        )


def _rereview_command(*, apply_changes: bool) -> int:
    import build_semantic_corpus
    from datetime import date

    registry = load(REGISTRY)
    committed_corpus = load(CORPUS)
    claims = load(CLAIMS)
    new_revision = formal_source_revision(claims)
    try:
        candidate_corpus = build_semantic_corpus.collect(defer_review_receipts=True)
    except Exception as error:  # noqa: BLE001 - report the builder's own message
        print("semantic review re-review: FAIL: could not rebuild the candidate corpus")
        print(f"  {error}")
        return 1
    today = date.today().isoformat()
    reissues, refusals = rereview_moved_revision(
        registry, committed_corpus, candidate_corpus, new_revision=new_revision, today=today
    )
    if refusals:
        print("semantic review re-review: REFUSED")
        for refusal in refusals:
            print(f"  {refusal}")
        print("\nNo receipt was rewritten; a differing statement needs a real re-review.")
        return 1
    declarations = sorted({row for record in reissues for row in record["cited"]})
    if not apply_changes:
        print(
            f"semantic review re-review: {len(reissues)} receipt(s) would be re-issued at "
            f"{new_revision}; {len(declarations)} cited declaration statement(s) verified "
            "byte-identical across the move (dry run; add --apply)"
        )
        return 0
    apply_rereviews(reissues, new_revision=new_revision, today=today)
    REGISTRY.write_text(
        json.dumps(registry, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(
        f"semantic review re-review: re-issued {len(reissues)} receipt(s) at {new_revision}; "
        f"{len(declarations)} cited declaration statement(s) verified byte-identical"
    )
    print("next: python3 scripts/build_semantic_corpus.py")
    return 0


def _rebind_command(*, apply_changes: bool) -> int:
    # Imported here, not at module scope: build_semantic_corpus imports this
    # module, so a top-level import would be circular.
    import build_semantic_corpus

    registry = load(REGISTRY)
    committed_corpus = load(CORPUS)
    claims = load(CLAIMS)
    revision = formal_source_revision(claims)

    try:
        candidate_corpus = build_semantic_corpus.collect(defer_review_receipts=True)
    except Exception as error:  # noqa: BLE001 - report the builder's own message
        print("semantic review rebind: FAIL: could not rebuild the candidate corpus")
        print(f"  {error}")
        return 1

    rebindings, refusals, already_current = rebind_receipts(
        registry,
        committed_corpus,
        candidate_corpus,
        reviewed_revision=revision,
    )

    if already_current and not rebindings and not refusals:
        print(
            f"semantic review rebind: {len(already_current)} receipt(s) already "
            "bind the rebuilt declaration atlas; docs/semantic_corpus.json is "
            "the surface that has not caught up"
        )
        print("next: python3 scripts/build_semantic_corpus.py")
        return 0

    if refusals:
        print("semantic review rebind: REFUSED")
        for refusal in refusals:
            print(f"  {refusal}")
        print(
            "\nNo receipt was rewritten. A rebind may only move the atlas "
            "fingerprint pin; it may never re-bless changed mathematics."
        )
        return 1

    if not rebindings:
        print(
            "semantic review rebind: every receipt already binds the current "
            "declaration-atlas fingerprint; nothing to do"
        )
        return 0

    print(
        f"semantic review rebind: {len(rebindings)} receipt(s) went stale only "
        "because the declaration-atlas source fingerprint moved"
    )
    print(f"  from {committed_corpus.get('evidence_fingerprint')}")
    print(f"    to {candidate_corpus.get('evidence_fingerprint')}")
    print(
        "  reviewed wording, evidence coordinates, boundaries, and the pinned "
        f"formal-source revision {revision} are unchanged for every one"
    )
    for record in rebindings:
        print(f"    {record['subject_kind']} {record['subject_id']}")

    if not apply_changes:
        print(
            "\nThis was a dry run. Re-run with --rebind --apply to write the "
            "rebound receipts, then rebuild the semantic corpus."
        )
        return 0

    apply_rebindings(rebindings)
    REGISTRY.write_text(
        json.dumps(registry, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(
        f"\nrewrote {REGISTRY.relative_to(ROOT)}; each rebound receipt keeps its "
        "previous digest and fingerprint under evidence_rebindings"
    )
    print("next: python3 scripts/build_semantic_corpus.py")
    return 0


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--report", action="store_true")
    parser.add_argument("--digest-node")
    parser.add_argument("--digest-relation")
    parser.add_argument(
        "--rebind",
        action="store_true",
        help=(
            "report which receipts went stale purely because the declaration "
            "atlas fingerprint moved, and refuse any whose reviewed material "
            "actually changed"
        ),
    )
    parser.add_argument(
        "--rereview-moved-revision",
        action="store_true",
        help=(
            "re-issue every receipt at the formal-source revision the claims "
            "release now pins, after proving each cited declaration's "
            "statement byte-identical across the move; refuse otherwise"
        ),
    )
    parser.add_argument(
        "--apply",
        action="store_true",
        help="with --rebind or --rereview-moved-revision, write the registry",
    )
    args = parser.parse_args(argv)

    if args.apply and not (args.rebind or args.rereview_moved_revision):
        parser.error("--apply is only meaningful with --rebind or --rereview-moved-revision")
    if args.rebind and args.rereview_moved_revision:
        parser.error("--rebind and --rereview-moved-revision are mutually exclusive")

    if args.rebind:
        return _rebind_command(apply_changes=args.apply)
    if args.rereview_moved_revision:
        return _rereview_command(apply_changes=args.apply)

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
