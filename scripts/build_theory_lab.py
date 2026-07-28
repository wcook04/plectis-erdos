#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build the theory-laboratory projection over the semantic corpus.

The semantic corpus answers what has been proved and how the statements relate.
This layer answers three further questions: what are the few mechanisms
underneath those proofs, what survives when the mathematics is deliberately
perturbed, and does the explanation actually transfer to mathematics the system
was not shown.

    Lean source
      -> declaration atlas                 (structural, exhaustive)
      -> semantic corpus                   (one node per distinct statement)
      -> theory lab                        (mechanisms, interventions, receipts)
      -> curated claims and papers

Authority. This file is generated. The authored sources are
``docs/semantic/lab/*.json``; the proof authority remains Lean and the statement
authority remains the semantic corpus. Nothing here decides novelty or
significance -- those stay reviewed judgements with a recorded prior-art state.

Prediction integrity. An intervention records its predicted surviving and broken
mechanisms, and the builder stamps a fingerprint over exactly those fields. An
outcome cites that fingerprint. If the prediction is later edited the fingerprint
changes and the checker rejects the pairing, so "we predicted this" stays
auditable rather than becoming a story told after the result was known.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
ATLAS = ROOT / "docs" / "declaration_atlas.json"
CORPUS = ROOT / "docs" / "semantic_corpus.json"
LAB_DIR = ROOT / "docs" / "semantic" / "lab"
OUTPUT = ROOT / "docs" / "theory_lab.json"

SOURCES = {
    "mechanisms": "mechanisms.json",
    "capsules": "capsules.json",
    "interventions": "interventions.json",
    "receipts": "receipts.json",
    "benchmark_items": "benchmark_items.json",
    "benchmark_results": "benchmark_results.json",
}

INTERVENTION_OPERATORS = (
    "change_base",
    "restrict_support",
    "extend_support",
    "shift_coefficient",
    "renormalise_weight",
    "replace_weight_by_analogue",
    "strengthen_divisibility",
    "weaken_divisibility",
    "change_modulus",
    "digitwise_to_carry",
    "carry_to_low_carry",
    "drop_structural_precondition",
    "fixed_to_uniform_quantifier",
    "finite_to_asymptotic",
    "change_window_parameter",
    "transport_between_problems",
    "remove_hypothesis",
    "add_weakest_sufficient_hypothesis",
    "dualise_to_barrier_search",
)

MECHANISM_RELATIONS = (
    "requires",
    "realises",
    "preserves_under",
    "breaks_under",
    "repair_restores",
    "strictly_strengthens",
    "strictly_weakens",
    "explains",
    "predicts",
    "counterexample_to",
    "transfers_to",
    "fails_because",
    "has_known_limit",
)

OUTCOME_STATES = (
    "predicted_only",
    "confirmed",
    "refuted",
    "partially_confirmed",
    "unresolved",
)

BENCHMARK_ARMS = (
    "signatures",
    "graph",
    "mechanism",
    "negative",
    "mechanism_shuffled",
    "mechanism_offproblem",
)

CONTROL_ARMS = ("mechanism_shuffled", "mechanism_offproblem")

PREDICTION_FIELDS = (
    "intervention_id",
    "operator",
    "target_statement_nodes",
    "mathematical_interpretation",
    "predicted_preserved",
    "predicted_broken",
)


def load(name: str) -> list[dict]:
    path = LAB_DIR / SOURCES[name]
    if not path.exists():
        return []
    data = json.loads(path.read_text(encoding="utf-8"))
    if isinstance(data, dict):
        for key in (name, "records", "items", "results"):
            if key in data and isinstance(data[key], list):
                return data[key]
        return []
    return data if isinstance(data, list) else []


def prediction_fingerprint(record: dict) -> str:
    """Stamp exactly the predictive fields, in a canonical order.

    Outcome prose, evidence and notes are deliberately excluded: the fingerprint
    must not change when a result is recorded, only when the prediction itself is
    altered.
    """
    payload = {}
    for field in PREDICTION_FIELDS:
        value = record.get(field)
        if isinstance(value, list):
            value = sorted(str(v) for v in value)
        payload[field] = value
    blob = json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    return "sha256:" + hashlib.sha256(blob.encode("utf-8")).hexdigest()


def file_digest(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def source_provenance() -> dict:
    """Bind the projection to its exact inputs without consulting Git.

    A Git-derived revision cannot converge when generated atlas or corpus files
    are committed in the same wave as this projection: the new commit becomes
    the newest input revision only after it already contains the old bytes.
    Content digests identify the exact expansion set and stay invariant across
    checkout shape and the commit that first contains the generated output.
    """
    return {
        "identity_kind": "content_addressed_input_set",
        "declaration_atlas_digest": file_digest(ATLAS),
        "semantic_corpus_digest": file_digest(CORPUS),
        "authored_lab_source_digests": {
            f"docs/semantic/lab/{filename}": file_digest(LAB_DIR / filename)
            for filename in sorted(SOURCES.values())
            if (LAB_DIR / filename).is_file()
        },
        "builder_digest": file_digest(Path(__file__).resolve()),
        "git_commit_not_embedded_reason": (
            "Generated projections cannot contain the commit that first contains "
            "their own bytes; exact input digests are the stable provenance."
        ),
    }


def build() -> dict:
    atlas = json.loads(ATLAS.read_text(encoding="utf-8"))
    corpus = json.loads(CORPUS.read_text(encoding="utf-8"))

    known_declarations = {d["name"] for d in atlas["declarations"]}
    known_nodes = {n["id"] for n in corpus["statement_nodes"]}

    mechanisms = load("mechanisms")
    capsules = load("capsules")
    interventions = load("interventions")
    receipts = load("receipts")
    items = load("benchmark_items")
    results = load("benchmark_results")

    # Deliberately does NOT stamp. A fingerprint written by the build would be
    # refreshed every time the prediction was edited, which is exactly the
    # tampering the fingerprint exists to detect. Stamping is an explicit act
    # (``--stamp``) performed when the prediction is recorded; the build only
    # recomputes alongside it so the checker can compare the two.
    for record in interventions:
        record["prediction_fingerprint_recomputed"] = prediction_fingerprint(record)

    mech_ids = {m["mechanism_id"] for m in mechanisms}
    minimum_basis_ids = {
        m["mechanism_id"]
        for m in mechanisms
        if m.get("mechanism_kind") != "scoped_specialisation"
    }

    # Coverage: which statement nodes does some mechanism claim to explain?
    explained: set[str] = set()
    for mech in mechanisms:
        for node in mech.get("statement_nodes", ()) or ():
            if node in known_nodes:
                explained.add(node)

    authored_theorem_like = corpus["summary"]["authored_theorem_like"]

    unexplained = sorted(known_nodes - explained)
    by_class: dict[str, int] = {}
    for node in corpus["statement_nodes"]:
        if node["id"] in unexplained:
            by_class[node["logical_class"]] = by_class.get(node["logical_class"], 0) + 1

    outcome_tally: dict[str, int] = {}
    for record in interventions:
        state = record.get("outcome_state", "predicted_only")
        outcome_tally[state] = outcome_tally.get(state, 0) + 1

    # A prediction is only interesting if it was capable of being wrong. Count
    # the ones where the recorded outcome differs from what was predicted.
    discrepancies = [
        {
            "intervention_id": r["intervention_id"],
            "discrepancy": r.get("discrepancy", ""),
        }
        for r in interventions
        if r.get("discrepancy")
    ]

    arm_tally: dict[str, dict] = {}
    for result in results:
        arm = result.get("arm", "unknown")
        bucket = arm_tally.setdefault(arm, {"runs": 0, "statement_recovered": 0, "mechanism_recovered": 0})
        bucket["runs"] += 1
        if result.get("statement_recovered"):
            bucket["statement_recovered"] += 1
        if result.get("mechanism_recovered"):
            bucket["mechanism_recovered"] += 1

    fingerprint_material = json.dumps(
        {
            "atlas": atlas.get("source_fingerprint"),
            "corpus": corpus.get("evidence_fingerprint"),
            "mechanisms": len(mechanisms),
            "minimum_basis_mechanisms": len(minimum_basis_ids),
            "interventions": len(interventions),
        },
        sort_keys=True,
    )

    return {
        "schema": "erdos249257-theory-lab/2",
        "artifact_role": "generated_interventional_projection_over_the_semantic_corpus",
        "authority_posture": (
            "generated_projection_over_authored_mechanism_and_intervention_records; "
            "not Lean, not the semantic corpus, and not a novelty judgement"
        ),
        "purpose": (
            "Own the layer above the semantic corpus: the few mechanisms underneath "
            "the proofs, the typed interventions that perturb them, the failures "
            "those interventions produced, and the blinded evaluations that test "
            "whether the mechanisms transfer to mathematics the system was not shown."
        ),
        "layering": {
            "below": "docs/semantic_corpus.json owns one node per distinct statement",
            "authored_sources": sorted(f"docs/semantic/lab/{v}" for v in SOURCES.values()),
            "above": "docs/claims.json stays the curated publication ledger",
            "proof_authority": "Lean kernel; a mechanism is an explanation, never a proof",
        },
        "source_provenance": source_provenance(),
        "evidence_fingerprint": "sha256:"
        + hashlib.sha256(fingerprint_material.encode("utf-8")).hexdigest(),
        "vocabularies": {
            "intervention_operators": list(INTERVENTION_OPERATORS),
            "mechanism_relations": list(MECHANISM_RELATIONS),
            "outcome_states": list(OUTCOME_STATES),
            "benchmark_arms": list(BENCHMARK_ARMS),
        },
        "summary": {
            "mechanisms": len(mechanisms),
            "minimum_basis_mechanisms": len(minimum_basis_ids),
            "capsules": len(capsules),
            "interventions": len(interventions),
            "failure_receipts": len(receipts),
            "benchmark_items": len(items),
            "benchmark_results": len(results),
            "statement_nodes_total": len(known_nodes),
            "statement_nodes_explained": len(explained),
            "explained_fraction": round(len(explained) / max(1, len(known_nodes)), 4),
            "authored_theorem_like": authored_theorem_like,
            "unexplained_by_logical_class": by_class,
            "outcome_states": outcome_tally,
            "prediction_discrepancies": len(discrepancies),
            "arm_tally": arm_tally,
        },
        "mechanisms": mechanisms,
        "capsules": capsules,
        "interventions": interventions,
        "failure_receipts": receipts,
        "benchmark": {"items": items, "results": results},
        "views": {
            "minimum_basis": sorted(minimum_basis_ids),
            "unexplained_residual": {
                "rule": (
                    "Statement nodes no mechanism claims to explain. A large residual "
                    "is a real finding about the basis, not a bookkeeping gap."
                ),
                "count": len(unexplained),
                "nodes": unexplained,
            },
            "prediction_discrepancies": {
                "rule": (
                    "Interventions whose observed outcome differed from the recorded "
                    "prediction. These are the entries that carry information."
                ),
                "entries": discrepancies,
            },
        },
        "integrity": {
            "declarations_known": len(known_declarations),
            "statement_nodes_known": len(known_nodes),
            "mechanism_ids": sorted(mech_ids),
            "unknown_declaration_citations": sorted(
                {
                    name
                    for mech in mechanisms
                    for name in (mech.get("realising_declarations") or ())
                    if name not in known_declarations
                }
            ),
            "unknown_node_citations": sorted(
                {
                    node
                    for mech in mechanisms
                    for node in (mech.get("statement_nodes") or ())
                    if node not in known_nodes
                }
            ),
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if the output is stale")
    parser.add_argument(
        "--stamp",
        action="store_true",
        help=(
            "write prediction fingerprints into the authored interventions source. "
            "Run this when a prediction is recorded, before its outcome is known -- "
            "running it afterwards destroys the evidence that the prediction was "
            "made in advance."
        ),
    )
    args = parser.parse_args()

    if args.stamp:
        path = LAB_DIR / SOURCES["interventions"]
        if not path.exists():
            print("build_theory_lab: no interventions source to stamp", file=sys.stderr)
            return 1
        records = load("interventions")
        stamped = 0
        for record in records:
            fingerprint = prediction_fingerprint(record)
            if record.get("prediction_fingerprint") != fingerprint:
                if record.get("outcome_state", "predicted_only") != "predicted_only":
                    print(
                        f"build_theory_lab: refusing to stamp {record.get('intervention_id')}: "
                        "its outcome is already recorded, so a new stamp would assert a "
                        "prediction that was not made in advance",
                        file=sys.stderr,
                    )
                    return 1
                record["prediction_fingerprint"] = fingerprint
                stamped += 1
        path.write_text(
            json.dumps(records, ensure_ascii=False, indent=1) + "\n", encoding="utf-8"
        )
        print(f"build_theory_lab: stamped {stamped} prediction(s)")
        return 0

    data = build()
    rendered = json.dumps(data, ensure_ascii=False, indent=1) + "\n"

    if args.check:
        if not OUTPUT.exists():
            print("build_theory_lab: docs/theory_lab.json is missing", file=sys.stderr)
            return 1
        if OUTPUT.read_text(encoding="utf-8") != rendered:
            print(
                "build_theory_lab: docs/theory_lab.json is stale; rerun without --check",
                file=sys.stderr,
            )
            return 1
        print("build_theory_lab: projection is current")
        return 0

    OUTPUT.write_text(rendered, encoding="utf-8")
    summary = data["summary"]
    print(
        "build_theory_lab: "
        f"{summary['mechanisms']} mechanisms, {summary['capsules']} capsules, "
        f"{summary['interventions']} interventions, "
        f"{summary['failure_receipts']} receipts, "
        f"{summary['benchmark_items']} benchmark items -> "
        f"{summary['statement_nodes_explained']}/{summary['statement_nodes_total']} "
        f"nodes explained ({summary['explained_fraction']:.1%})"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
