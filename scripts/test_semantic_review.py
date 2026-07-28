#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial unit checks for digest-bound semantic review receipts."""

from __future__ import annotations

import json
import subprocess
import sys
from copy import deepcopy
from pathlib import Path

from semantic_review import apply_review_registry, relation_subject_id, subject_digest


ROOT = Path(__file__).resolve().parent.parent
REVISION = "a" * 40
FINGERPRINT = "sha256:" + "b" * 64
CEILING = (
    "Checked canonical wording against cited public Lean signatures and status "
    "boundaries; not Lean proof authority, novelty review, or human review."
)


def fixtures() -> tuple[dict, dict, dict]:
    node = {
        "id": "Z00::sample",
        "canonical_statement": "Every sample has the checked property.",
        "logical_class": "unconditional_object_theorem",
        "problem": "shared_substrate",
        "evidence": [
            {
                "id": "Sample.lean:10:sample",
                "kind": "theorem",
                "resolved": True,
            }
        ],
        "open_antecedents": [],
        "scope_caveat": "",
        "prior_art_state": "not_assessed",
    }
    relation = {
        "from": "Z00::sample",
        "to": "Z00::sample",
        "relation": "alias_of",
        "basis": "The two presentations cite the same theorem.",
        "scope": "intra_zone",
        "zone": "Z00",
    }
    registry = {
        "schema": "erdos249257-semantic-reviews/1",
        "reviews": [],
    }
    for kind, subject, subject_id in (
        ("statement_node", node, node["id"]),
        ("relation", relation, relation_subject_id(relation)),
    ):
        registry["reviews"].append(
            {
                "subject_kind": kind,
                "subject_id": subject_id,
                "reviewer": "Codex Type A",
                "reviewer_type": "ai_semantic_consistency_review",
                "reviewed_revision": REVISION,
                "reviewed_at": "2026-07-28",
                "evidence_digest": subject_digest(
                    kind,
                    subject,
                    evidence_fingerprint=FINGERPRINT,
                    reviewed_revision=REVISION,
                ),
                "review_scope": "canonical wording, cited signatures, and status ceiling",
                "claim_ceiling": CEILING,
            }
        )
    return node, relation, registry


def main() -> int:
    node, relation, registry = fixtures()
    nodes = {node["id"]: deepcopy(node)}
    relations = [deepcopy(relation)]
    errors = apply_review_registry(
        deepcopy(registry),
        nodes,
        relations,
        evidence_fingerprint=FINGERPRINT,
        reviewed_revision=REVISION,
    )
    assert not errors, errors
    assert nodes[node["id"]]["semantic_review"]["reviewer"] == "Codex Type A"
    assert relations[0]["semantic_review"]["reviewer"] == "Codex Type A"

    mutations = {
        "statement wording": lambda n, r, g: n[node["id"]].__setitem__(
            "canonical_statement", "A different claim."
        ),
        "relation basis": lambda n, r, g: r[0].__setitem__(
            "basis", "A different basis."
        ),
        "formal revision": lambda n, r, g: g["reviews"][0].__setitem__(
            "reviewed_revision", "c" * 40
        ),
        "missing ceiling": lambda n, r, g: g["reviews"][0].pop(
            "claim_ceiling"
        ),
    }
    for mutation, apply_mutation in mutations.items():
        mutated_nodes = {node["id"]: deepcopy(node)}
        mutated_relations = [deepcopy(relation)]
        mutated_registry = deepcopy(registry)
        apply_mutation(mutated_nodes, mutated_relations, mutated_registry)
        errors = apply_review_registry(
            mutated_registry,
            mutated_nodes,
            mutated_relations,
            evidence_fingerprint=FINGERPRINT,
            reviewed_revision=REVISION,
        )
        assert errors, f"{mutation} escaped semantic review validation"

    query = subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts" / "query_semantic.py"),
            "semantic-reviews",
            "Z12::mersenne_achievement_set_measure_one",
            "--limit",
            "2",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert query.returncode == 0, query.stderr
    packet = json.loads(query.stdout)
    assert packet["coverage"]["reviewed_statement_nodes"] > 0
    assert packet["coverage"]["reviewed_relations"] > 0
    assert {row["subject_kind"] for row in packet["results"]} == {
        "statement_node",
        "relation",
    }

    print(
        "semantic review test: baseline attached and queryable; all "
        f"{len(mutations)} stale or malformed receipt mutations rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
