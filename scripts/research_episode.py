#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Register prospective insight experiments in the EXISTING research journal.

No second event store or mechanism taxonomy is created. A contract points to an
existing theory-lab mechanism, records a prospective prediction and its frozen
baseline/protocol, and declares an output with all scientific reviews pending.
Only explicit `apply` changes the journal, using compare-and-swap and atomic
batch append in research_record. No command grants publication or novelty.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any

import research_decision as decision
import research_record as record

SCHEMA = "plectis-insight-experiment/1"
REQUIRED_REVIEWS = ("faithfulness_review", "corpus_relation_review", "prior_art_review",
                    "transfer_validation", "publication_review")
CONSUMERS = ("theory_lab", "graph", "claims", "short_paper", "long_record", "comparator")


def validate_contract(contract: Any) -> None:
    if not isinstance(contract, dict):
        raise decision.DecisionError("contract must be an object")
    fields = {"schema", "episode_id", "mechanism_id", "decision_sha256", "question", "scope",
              "baseline", "prediction", "protocol", "budget", "experiment_kind"}
    if set(contract) != fields or contract.get("schema") != SCHEMA:
        raise decision.DecisionError("contract schema/fields mismatch; outcomes do not belong in a prediction")
    for key in ("episode_id", "mechanism_id"):
        if record.c_ident(contract[key]):
            raise decision.DecisionError(f"invalid {key}")
    if not re.fullmatch(r"[0-9a-f]{64}", str(contract["decision_sha256"])):
        raise decision.DecisionError("decision digest required")
    if contract["experiment_kind"] not in {"calibration", "prospective_transfer"}:
        raise decision.DecisionError("invalid experiment kind")
    for key in ("question", "scope"):
        if not isinstance(contract[key], str) or not contract[key].strip():
            raise decision.DecisionError(f"nonempty {key} required")
    shapes = {
        "baseline": {"artifact", "sha256", "comparison_rule"},
        "prediction": {"target", "expected_effect", "disconfirmation", "holdout_manifest_sha256"},
        "protocol": {"path", "sha256"},
        "budget": {"model_tokens", "lean_seconds", "human_review_minutes"},
    }
    for key, keys in shapes.items():
        if not isinstance(contract[key], dict) or set(contract[key]) != keys:
            raise decision.DecisionError(f"{key} must contain exactly {sorted(keys)}")
        for name, value in contract[key].items():
            if key == "budget":
                if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                    raise decision.DecisionError("budget entries must be nonnegative integers")
            elif not isinstance(value, str) or not value.strip():
                raise decision.DecisionError(f"nonempty {key}.{name} required")
            elif name.endswith("sha256") and not re.fullmatch(r"[0-9a-f]{64}", value):
                raise decision.DecisionError(f"invalid digest {key}.{name}")
    if not any(contract["budget"].values()):
        raise decision.DecisionError("an all-zero research budget is not an experiment")


def make_plan(root: Path, capsule: dict[str, Any], contract_path: str, producer: str) -> dict[str, Any]:
    root = Path(root).resolve()
    decision.check_decision(root, capsule)
    path = decision.safe_path(root, contract_path)
    contract_bytes = path.read_bytes()
    contract = json.loads(contract_bytes)
    validate_contract(contract)
    if contract["decision_sha256"] != capsule["decision_sha256"]:
        raise decision.DecisionError("contract is about a different decision")
    lab = json.loads(decision.safe_path(root, "docs/theory_lab.json").read_text())
    mechanisms = {m["mechanism_id"] for m in lab["mechanisms"]}
    if contract["mechanism_id"] not in mechanisms:
        raise decision.DecisionError("unknown mechanism: use the native theory-lab authoring path first")
    if not any(m["mechanism_id"] == contract["mechanism_id"] for m in lab["capsules"]):
        raise decision.DecisionError("mechanism lacks a native explanatory capsule")
    paths = set(capsule["snapshot"]["files"]) | {contract_path, "docs/theory_lab.json",
        "scripts/research_episode.py", contract["baseline"]["artifact"], contract["protocol"]["path"]}
    stamp = decision.snapshot(root, paths)
    if stamp["files"][contract_path] != hashlib.sha256(contract_bytes).hexdigest():
        raise decision.DecisionError("contract changed while preparing plan")
    for section, key in (("baseline", "artifact"), ("protocol", "path")):
        if stamp["files"][contract[section][key]] != contract[section]["sha256"]:
            raise decision.DecisionError(f"{section} bytes do not match contract")
    journal = record.verify(root)
    if not journal["ok"] or journal["head"] != capsule["record_head"]:
        raise decision.DecisionError("journal changed since the decision; compile a fresh capsule")
    _, state = record.replay(root)
    if producer not in state.rounds and producer not in state.returns:
        raise decision.DecisionError("producer must be an existing native round or return")
    if producer in state.returns and not state.returns[producer]["reviews"]:
        raise decision.DecisionError("return producer must be reviewed before experiment registration")
    output_id = "insight/" + contract["episode_id"]
    changes = [{"kind": "output_declared", "subject": output_id, "detail": {
        "output_id": output_id, "kind": "record_row", "locator": {"path": contract_path},
        "problem": capsule["problem"], "produced_by": [producer], "required": list(REQUIRED_REVIEWS)}}]
    for consumer in CONSUMERS:
        changes.append({"kind": "consumer_disposed", "subject": output_id, "detail": {
            "subject_id": output_id, "consumer": consumer, "status": "deferred",
            "reason": "Prospective experiment only; no result or transfer has been accepted.",
            "evidence": ["sha256:" + decision.digest(contract)],
            "reentry": {"owner": "Type A", "trigger": "Review the experiment outcome; update or mark not applicable with evidence."}}})
    result = {"schema": "plectis-insight-registration-plan/1", "contract_path": contract_path,
        "producer": producer, "decision": capsule,
        "contract_sha256": decision.digest(contract), "prediction_sha256": decision.digest(contract["prediction"]),
        "decision_sha256": capsule["decision_sha256"], "expected_head": capsule["record_head"],
        "read_set": stamp, "changes": changes, "novelty": "not_established",
        "transfer": "not_tested", "publication_admitted": False,
        "boundary": "atomic journal registration, not an atomic source/Lean/paper publication"}
    decision.verify_snapshot(root, stamp)
    decision.check_decision(root, capsule)
    result["plan_sha256"] = decision.digest(result)
    return result


def apply(root: Path, plan: dict[str, Any]) -> list[dict[str, Any]]:
    root = Path(root).resolve()
    body = {k: v for k, v in plan.items() if k != "plan_sha256"}
    if plan.get("schema") != "plectis-insight-registration-plan/1" or decision.digest(body) != plan.get("plan_sha256"):
        raise decision.DecisionError("plan digest/schema mismatch")
    # Rebuild, not just re-hash: a caller cannot smuggle a completed review into
    # an otherwise valid registration plan by recomputing its digest.
    expected = make_plan(root, plan["decision"], plan["contract_path"], plan["producer"])
    if expected["plan_sha256"] != plan["plan_sha256"]:
        raise decision.DecisionError("plan differs from native prospective registration")
    # A digest detects accidental modification; it does not authorize a caller.
    # Type A must review the plan and use this only in its controlled writer lane.
    def validate_read_set() -> None:
        decision.verify_snapshot(root, plan["read_set"])
        # The decision's Lean/script/workflow inventory is dynamic. A newly
        # added source has no old hash to compare, so check membership under
        # the journal lock on both validator calls as well as file contents.
        if set(plan["decision"]["snapshot"]["files"]) != decision._integrity_inputs(root):
            raise decision.DecisionError("source inventory changed before journal append")

    return record.append_batch(root, plan["changes"], expected_head=plan["expected_head"],
                               validate_read_set=validate_read_set)


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    sub = p.add_subparsers(dest="command", required=True)
    prep = sub.add_parser("plan")
    prep.add_argument("--decision", type=Path, required=True)
    prep.add_argument("--contract", required=True, help="repository-relative contract file")
    prep.add_argument("--producer", required=True)
    apply_p = sub.add_parser("apply"); apply_p.add_argument("--plan", type=Path, required=True)
    args = p.parse_args()
    try:
        result = make_plan(args.root, json.loads(args.decision.read_text()), args.contract, args.producer) \
            if args.command == "plan" else apply(args.root, json.loads(args.plan.read_text()))
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 0
    except (ValueError, OSError, KeyError) as exc:
        print(f"research_episode: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
