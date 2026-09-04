#!/usr/bin/env python3
"""Replay the four-return intake and the packet gates it exposed."""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[5]
PROBLEM = ROOT / "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041"
INTAKE = ROOT / "state/formal_math/type_b_return_batches/erdos1041_20260827_return_stream_04/intake.json"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> int:
    intake = json.loads(INTAKE.read_text(encoding="utf-8"))
    require(intake["arrival_state"] == "closed", "return stream must be closed")
    require(intake["arrival_count"] == 4, "expected exactly four arrivals")
    lifecycle = intake["source_packet_lifecycle"]
    require(lifecycle["state"] == "completed_returns_received", "predecessor lifecycle must be explicit")
    require(lifecycle["successor_batch_created"] is False, "this receipt must not relabel the predecessor as successor")
    for row in intake["sources"]:
        path = Path(row["path"])
        require(path.is_file(), f"missing preserved attachment: {path}")
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        require(digest == row["sha256"], f"attachment digest mismatch: {path}")

    authorities = {
        "critical metric": PROBLEM / "CriticalTwoRootProximity.lean",
        "inverse fibre": PROBLEM / "TiedNewtonFaceFibreProduct.md",
        "full-fibre action": PROBLEM / "SixReturnJointAssimilation20260826.md",
        "near-Fekete": PROBLEM / "NearFeketeTransverseClosure.md",
        "generic closure": PROBLEM / "GenericSufficiencyClosure.md",
        "combined charge": PROBLEM / "CriticalTreeLengthCharge.md",
    }
    for label, path in authorities.items():
        require(path.is_file(), f"missing {label} authority: {path}")

    builder = (ROOT / "tools/meta/bridge/type_b_handoff_bundle.py").read_text(encoding="utf-8")
    required_builder_markers = [
        "required_strongest_result_ids",
        "launches moves dominated by source-current result",
        "construction_target_gap_id",
        "proof_absence_does_not_count",
        "broad_search_does_not_count",
        "minimum_distinct_endpoint_attacks_if_no_parent_proof",
        "published_checkpoint_verified",
    ]
    for marker in required_builder_markers:
        require(marker in builder, f"missing packet hardening marker: {marker}")

    note = (PROBLEM / "FourReturnPacketFailureAssimilation20260827.md").read_text(encoding="utf-8")
    for marker in [
        "Common-envelope cluster certificate",
        "max_(z in C_S) |r_S(z)|",
        "Packet regression contract for the next eight",
        "receiver_attention_contract_v1",
        "Erdős 1041 remains open",
    ]:
        require(marker in note, f"assimilation note missing marker: {marker}")

    test = subprocess.run(
        [
            str(ROOT / "repo-pytest"),
            "tools/meta/bridge/tests/test_type_b_handoff_bundle.py",
            "-q",
            "-k",
            "proof_campaign_v8_requires_construction_first_novel_bridge_execution",
            "--host-pressure-policy=warn",
        ],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    if test.returncode or "passed" not in test.stdout or "queued validation" in test.stdout:
        sys.stdout.write(test.stdout)
        sys.stderr.write(test.stderr)
        return test.returncode or 1

    print("PASS: four-return digests, corpus dominance map, common-envelope strengthening, and v8 packet regressions")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
