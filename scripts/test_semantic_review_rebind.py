#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Contract: a receipt rebind may move the atlas pin and nothing else.

A semantic review receipt is bound to the declaration-atlas source fingerprint,
which fingerprints the entire Lean tree. Adding one unrelated module moves it,
so every receipt goes stale without a single reviewed word having changed.
Without a route back, a contributor's only options were to hand-edit thirty
three digests or never touch the Lean sources.

``semantic_review.py --rebind`` is that route, which makes it the most
dangerous code in the review layer: a rebind that is not careful is exactly how
a changed statement quietly inherits somebody else's review. So the rebind
carries a proof obligation, and this is where that obligation is tested. Each
case below is a way the reviewed mathematics could move underneath a receipt,
and each one must be refused by name.
"""

from __future__ import annotations

import semantic_review as sr

REVISION = "9e231ce4371fcda607f81c4520d29b16dcb4482e"
OLD_FINGERPRINT = "sha256:" + "a" * 64
NEW_FINGERPRINT = "sha256:" + "b" * 64


def require(condition: bool, message: str) -> None:
    """Keep rebind-guard failures active when run with ``python -O``."""
    if not condition:
        raise AssertionError(message)


def sample_corpus(fingerprint: str) -> dict:
    return {
        "evidence_fingerprint": fingerprint,
        "statement_nodes": [
            {
                "id": "Z01::example",
                "canonical_statement": "The series is irrational.",
                "logical_class": "unconditional",
                "problem": "257",
                "evidence": [
                    {"id": "Erdos257.example", "kind": "declaration", "resolved": True}
                ],
                "open_antecedents": [],
                "scope_caveat": "Restricted to finite supports.",
                "prior_art_state": "novelty_unassessed",
            }
        ],
        "relations": [
            {
                "from": "Z01::example",
                "relation": "specialises",
                "to": "Z12::other",
                "basis": "The second statement is the first at a fixed base.",
                "scope": "public",
                "zone": "Z01",
                "lens": "irrationality",
                "both_sides_open": False,
            }
        ],
    }


def sample_registry(committed: dict) -> dict:
    """Stamp valid receipts against ``committed`` the way a real review does."""
    reviews = []
    fingerprint = committed["evidence_fingerprint"]
    for node in committed["statement_nodes"]:
        reviews.append(
            {
                "subject_kind": "statement_node",
                "subject_id": node["id"],
                "reviewer": "Fixture Reviewer",
                "reviewer_type": "ai_semantic_consistency_review",
                "reviewed_revision": REVISION,
                "reviewed_at": "2026-08-12",
                "evidence_digest": sr.subject_digest(
                    "statement_node",
                    node,
                    evidence_fingerprint=fingerprint,
                    reviewed_revision=REVISION,
                ),
                "review_scope": "Fixture scope.",
                "claim_ceiling": "Fixture ceiling.",
            }
        )
    for edge in committed["relations"]:
        reviews.append(
            {
                "subject_kind": "relation",
                "subject_id": sr.relation_subject_id(edge),
                "reviewer": "Fixture Reviewer",
                "reviewer_type": "ai_semantic_consistency_review",
                "reviewed_revision": REVISION,
                "reviewed_at": "2026-08-12",
                "evidence_digest": sr.subject_digest(
                    "relation",
                    edge,
                    evidence_fingerprint=fingerprint,
                    reviewed_revision=REVISION,
                ),
                "review_scope": "Fixture scope.",
                "claim_ceiling": "Fixture ceiling.",
            }
        )
    return {"schema": sr.REGISTRY_SCHEMA, "reviews": reviews}


def rebind(registry: dict, committed: dict, candidate: dict):
    return sr.rebind_receipts(
        registry, committed, candidate, reviewed_revision=REVISION
    )


def check_fingerprint_only_move_is_allowed() -> None:
    committed = sample_corpus(OLD_FINGERPRINT)
    candidate = sample_corpus(NEW_FINGERPRINT)
    registry = sample_registry(committed)

    rebindings, refusals, already = rebind(registry, committed, candidate)
    require(not refusals, f"a pure fingerprint move was refused: {refusals}")
    require(not already, f"a stale receipt was reported as current: {already}")
    require(
        len(rebindings) == 2,
        f"expected both receipts to rebind, got {len(rebindings)}",
    )

    sr.apply_rebindings(rebindings)
    for review in registry["reviews"]:
        history = review["evidence_rebindings"]
        require(len(history) == 1, "the rebind did not leave exactly one record")
        require(
            history[0]["previous_evidence_fingerprint"] == OLD_FINGERPRINT
            and history[0]["evidence_fingerprint"] == NEW_FINGERPRINT,
            "the rebind record does not name both fingerprints",
        )
        require(
            history[0]["previous_evidence_digest"] != review["evidence_digest"],
            "the rebind kept the superseded digest as the live one",
        )

    # The rewritten registry must validate against the candidate, and the
    # rebind must be idempotent rather than stacking records on every run.
    rebindings, refusals, already = rebind(registry, candidate, candidate)
    require(
        not rebindings and not refusals,
        f"a rebound registry did not settle: {rebindings or refusals}",
    )


def check_changed_mathematics_is_refused() -> None:
    """Every field a reviewer actually read must block an automatic rebind."""
    mutations = {
        "canonical_statement": lambda node: node.update(
            {"canonical_statement": "The series is rational."}
        ),
        "logical_class": lambda node: node.update({"logical_class": "conditional"}),
        "problem": lambda node: node.update({"problem": "249"}),
        "evidence": lambda node: node.update(
            {
                "evidence": [
                    {
                        "id": "Erdos257.different",
                        "kind": "declaration",
                        "resolved": True,
                    }
                ]
            }
        ),
        "open_antecedents": lambda node: node.update(
            {"open_antecedents": ["Z12::unproved"]}
        ),
        "scope_caveat": lambda node: node.update({"scope_caveat": ""}),
        "prior_art_state": lambda node: node.update({"prior_art_state": "known_prior"}),
    }

    for field, mutate in mutations.items():
        committed = sample_corpus(OLD_FINGERPRINT)
        registry = sample_registry(committed)
        candidate = sample_corpus(NEW_FINGERPRINT)
        mutate(candidate["statement_nodes"][0])

        rebindings, refusals, _ = rebind(registry, committed, candidate)
        require(
            not any(record["subject_id"] == "Z01::example" for record in rebindings),
            f"changing {field} still let the receipt rebind; a review of the old "
            "statement would now vouch for a different one",
        )
        require(
            any(field in refusal for refusal in refusals),
            f"changing {field} was refused without naming the field: {refusals}",
        )


def check_changed_relation_basis_is_refused() -> None:
    committed = sample_corpus(OLD_FINGERPRINT)
    registry = sample_registry(committed)
    candidate = sample_corpus(NEW_FINGERPRINT)
    candidate["relations"][0]["basis"] = "An entirely different justification."

    rebindings, refusals, _ = rebind(registry, committed, candidate)
    require(
        not any(record["subject_kind"] == "relation" for record in rebindings),
        "a relation rebound after its stated basis changed",
    )
    require(
        any("basis" in refusal for refusal in refusals),
        f"a changed relation basis was refused without naming it: {refusals}",
    )


def check_vanished_subject_is_refused() -> None:
    committed = sample_corpus(OLD_FINGERPRINT)
    registry = sample_registry(committed)
    candidate = sample_corpus(NEW_FINGERPRINT)
    candidate["statement_nodes"] = []

    rebindings, refusals, _ = rebind(registry, committed, candidate)
    require(
        not any(record["subject_id"] == "Z01::example" for record in rebindings),
        "a receipt rebound onto a subject that no longer exists",
    )
    require(
        any("no longer exists" in refusal for refusal in refusals),
        f"a vanished subject was not reported as such: {refusals}",
    )


def check_moved_formal_revision_is_refused() -> None:
    """A rebind moves the atlas pin; moving the formal source needs a re-review."""
    committed = sample_corpus(OLD_FINGERPRINT)
    registry = sample_registry(committed)
    for review in registry["reviews"]:
        review["reviewed_revision"] = "0" * 40
    candidate = sample_corpus(NEW_FINGERPRINT)

    rebindings, refusals, _ = rebind(registry, committed, candidate)
    require(not rebindings, "a receipt rebound across a moved formal-source revision")
    require(
        all("re-review" in refusal for refusal in refusals),
        f"a moved formal revision was not routed to re-review: {refusals}",
    )


def check_already_broken_receipt_is_refused() -> None:
    """A digest that never matched cannot be repaired by a rebind."""
    committed = sample_corpus(OLD_FINGERPRINT)
    registry = sample_registry(committed)
    registry["reviews"][0]["evidence_digest"] = "sha256:" + "c" * 64
    candidate = sample_corpus(NEW_FINGERPRINT)

    rebindings, refusals, _ = rebind(registry, committed, candidate)
    require(
        not any(record["subject_id"] == "Z01::example" for record in rebindings),
        "a receipt whose digest never reproduced was silently rebound",
    )
    require(
        any("other than a moved atlas fingerprint" in refusal for refusal in refusals),
        f"a pre-broken receipt was not reported honestly: {refusals}",
    )


def check_corpus_lagging_a_rebind_is_not_alarming() -> None:
    """Rebound receipts plus a not-yet-rebuilt corpus is a build step, not a fault."""
    committed = sample_corpus(OLD_FINGERPRINT)
    registry = sample_registry(committed)
    candidate = sample_corpus(NEW_FINGERPRINT)
    rebindings, _, _ = rebind(registry, committed, candidate)
    sr.apply_rebindings(rebindings)

    rebindings, refusals, already = rebind(registry, committed, candidate)
    require(
        not rebindings and not refusals,
        f"a rebound registry against a lagging corpus was misreported: {refusals}",
    )
    require(
        len(already) == 2,
        "receipts that already bind the rebuilt atlas were not recognised",
    )


def check_substantive_projection_excludes_only_the_pin() -> None:
    """Guard the guard: the exclusion list must never grow silently."""
    require(
        sr.SUBSTANTIVE_MATERIAL_FIELDS_EXCLUDED == ("evidence_fingerprint",),
        "a rebind may only ignore the atlas fingerprint; excluding any further "
        "field would let that field change without review: "
        f"{sr.SUBSTANTIVE_MATERIAL_FIELDS_EXCLUDED}",
    )
    material = sr.node_review_material(
        sample_corpus(OLD_FINGERPRINT)["statement_nodes"][0],
        evidence_fingerprint=OLD_FINGERPRINT,
        reviewed_revision=REVISION,
    )
    projected = sr.substantive_material(material)
    require(
        "reviewed_revision" in projected and "canonical_statement" in projected,
        "the substantive projection dropped a field a reviewer actually read",
    )


def main() -> int:
    check_fingerprint_only_move_is_allowed()
    check_changed_mathematics_is_refused()
    check_changed_relation_basis_is_refused()
    check_vanished_subject_is_refused()
    check_moved_formal_revision_is_refused()
    check_already_broken_receipt_is_refused()
    check_corpus_lagging_a_rebind_is_not_alarming()
    check_substantive_projection_excludes_only_the_pin()
    print(
        "semantic review rebind guard: PASS; a rebind moves the declaration-atlas "
        "fingerprint and refuses every change to reviewed mathematics"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
