# SPDX-License-Identifier: Apache-2.0
"""Small fixtures for the research-decision/episode suites, never production inputs."""
from pathlib import Path
import json
import hashlib

COMMIT = "a" * 40
TIME = "2026-09-28T22:00:00Z"


def write(root: Path, path: str, value) -> None:
    target = root / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(value), encoding="utf-8")


def fixture(root: Path) -> None:
    write(root, "docs/claims.json", {
        "claims": [{"id": "erdos_249", "status": "open", "statement": "Target is open.",
                     "remaining_open_proposition_ids": ["open.gap"]},
                    {"id": "good_index_endpoint", "status": "conditional reduction",
                     "statement": "Gap implies target; gap remains open.",
                     "remaining_open_proposition_ids": ["open.gap"]},
                    {"id": "unlinked_general_tool", "status": "proved here", "statement": "Tool."}],
        "remaining_open_propositions": [{"id": "open.gap", "open_target_claim": "erdos_249",
                                         "statement": "Establish the gap."}]})
    write(root, "docs/research-commons/record/relations.json",
          {"schema": "plectis-relation-registry/1", "boundary": "test fixture", "rows": []})
    write(root, "docs/research-commons/record/contrasts.json", {"schema": "plectis-contrast-ledger/1", "rows": []})
    write(root, "docs/theory_lab.json", {"mechanisms": [{"mechanism_id": "test_mechanism"}],
                                       "capsules": [{"mechanism_id": "test_mechanism"}]})
    (root / "baseline.txt").write_text("calibration baseline, not a mathematical result\n")
    (root / "protocol.txt").write_text("frozen calibration protocol; no efficacy claim\n")


def open_round(record, root: Path, identifier: str = "round-test"):
    return record.append(root, "round_opened", identifier, {
        "round_id": identifier, "packet_id": "packet-test", "packet_manifest_sha256": "b" * 64,
        "source_commit": COMMIT, "ask": "Calibration only", "consumers": ["theory_lab"],
        "expected_returns": 0}, recorded_at=TIME)


def contract(root: Path, capsule) -> dict:
    sha = lambda path: hashlib.sha256((root / path).read_bytes()).hexdigest()
    return {"schema": "plectis-insight-experiment/1", "episode_id": "calibration-1",
        "mechanism_id": "test_mechanism", "decision_sha256": capsule["decision_sha256"],
        "question": "Does the registration survive replay without asserting an outcome?",
        "scope": "Synthetic infrastructure calibration only; not mathematical transfer.",
        "experiment_kind": "calibration",
        "baseline": {"artifact": "baseline.txt", "sha256": sha("baseline.txt"),
                     "comparison_rule": "Compare the unchanged native record before and after."},
        "prediction": {"target": "Synthetic replay fixture", "expected_effect": "Reviews remain pending.",
                       "disconfirmation": "Any unearned review completion.", "holdout_manifest_sha256": "c" * 64},
        "protocol": {"path": "protocol.txt", "sha256": sha("protocol.txt")},
        "budget": {"model_tokens": 100, "lean_seconds": 0, "human_review_minutes": 1}}
