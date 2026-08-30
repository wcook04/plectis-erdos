#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial unit checks for digest-bound semantic review receipts."""

from __future__ import annotations

import json
import os
import subprocess
import sys
from copy import deepcopy
from pathlib import Path
from unittest.mock import patch

from semantic_review import apply_review_registry, relation_subject_id, subject_digest
import validation_singleflight as singleflight


ROOT = Path(__file__).resolve().parent.parent
REVISION = "a" * 40
FINGERPRINT = "sha256:" + "b" * 64
CEILING = (
    "Checked canonical wording against cited public Lean signatures and status "
    "boundaries; not Lean proof authority, novelty review, or human review."
)
ENVIRONMENT_CONTRACT = "clean_committed_snapshot_subprocess_environment_v1"


def require(condition: bool, message: str) -> None:
    """Keep the environment contract active when Python is run with -O."""
    if not condition:
        raise AssertionError(message)


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


def run_query(*args: str) -> subprocess.CompletedProcess[str]:
    """Run the semantic query without ambient checkout state or hangs."""
    return subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts" / "query_semantic.py"),
            *args,
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
        env=singleflight.command_environment(),
        timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
    )


def check_query_environment() -> None:
    """Prove semantic review queries ignore hostile inherited selectors."""
    hostile_environment = {
        "GIT_DIR": "/private/wrong-git-dir",
        "GIT_NAMESPACE": "refs/namespaces/wrong-review",
        "GIT_REPLACE_REF_BASE": "refs/replace/",
        "PYTHONPATH": "/private/wrong-python-path",
        "LC_ALL": "C",
        "LANG": "C",
        "PATH": "/private/wrong-bin",
    }
    completed = subprocess.CompletedProcess(
        [sys.executable, "scripts/query_semantic.py"],
        0,
        stdout='{"coverage": {"reviewed_statement_nodes": 0, "reviewed_relations": 0}, "results": []}',
        stderr="",
    )
    with patch.dict(os.environ, hostile_environment, clear=False):
        with patch.object(subprocess, "run", return_value=completed) as run:
            observed = run_query("semantic-reviews", "Z00::sample")

    require(observed is completed, "semantic query result was not returned")
    require(len(run.call_args_list) == 1, "semantic query was not exercised")
    kwargs = run.call_args.kwargs
    sanitized = kwargs["env"]
    for key in (
        "GIT_DIR",
        "GIT_NAMESPACE",
        "GIT_REPLACE_REF_BASE",
        "PYTHONPATH",
    ):
        require(key not in sanitized, f"ambient {key} leaked into semantic query")
    require(sanitized["LC_ALL"] == "C.UTF-8", "canonical locale missing")
    require(sanitized["LANG"] == "C.UTF-8", "canonical LANG missing")
    require(sanitized["PATH"] == os.defpath, "ambient PATH leaked into semantic query")
    require(
        kwargs["timeout"] == singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
        "semantic query timeout drifted",
    )
    require(
        ENVIRONMENT_CONTRACT
        == "clean_committed_snapshot_subprocess_environment_v1",
        "semantic review environment contract drifted",
    )


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

    check_query_environment()
    query = run_query(
        "semantic-reviews",
        "Z12::mersenne_achievement_set_measure_one",
        "--limit",
        "2",
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
