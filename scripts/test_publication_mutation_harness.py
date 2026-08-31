#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exercise the mutation harness's baseline-validity boundary."""

from __future__ import annotations

import sys
import tempfile
from pathlib import Path

from run_publication_mutations import (
    clone_at_checkpoint,
    parse_check_count,
    resolve_commit,
    run_mutations,
)


def synthetic_manifest(gate_returncode: int, checkpoint: str) -> dict:
    token = "PUBLICATION_MUTATION_HARNESS_SYNTHETIC_TOKEN"
    return {
        "suite_id": "publication-mutation-harness-self-test",
        "experiment_kind": "deterministic_reconstruction_not_exact_historical_replay",
        "checkpoint": checkpoint,
        "historical_evidence": "synthetic_self_test",
        "default_gate_command": [
            sys.executable,
            "-c",
            f"raise SystemExit({gate_returncode})",
        ],
        "operators": [
            {
                "id": "T1",
                "expected_historical_outcome": "escaped",
                "exact_original_target_registered": False,
                "operation": {
                    "kind": "append_text",
                    "path": "README.md",
                    "must_be_absent": token,
                    "text": f"\n{token}\n",
                },
            }
        ],
    }


def main() -> int:
    checkpoint = resolve_commit("HEAD")
    assert parse_check_count("check_release: all 5,207 checks passed") == 5207
    assert parse_check_count("failure across 4,920 checks") == 4920

    with tempfile.TemporaryDirectory() as directory:
        shared = clone_at_checkpoint(checkpoint, Path(directory))
        alternates = shared / ".git" / "objects" / "info" / "alternates"
        assert alternates.is_file()
        assert alternates.read_text().strip()

    invalid = run_mutations(
        synthetic_manifest(1, checkpoint),
        ["T1"],
        30,
        "HEAD",
        checkpoint,
    )
    assert invalid["status"] == "invalid_baseline"
    assert invalid["baseline"]["status"] == "failed"
    assert invalid["summary"]["baseline_valid"] is False
    assert invalid["summary"]["run_count"] == 0
    assert invalid["results"] == []

    valid = run_mutations(
        synthetic_manifest(0, checkpoint),
        ["T1"],
        30,
        "HEAD",
        checkpoint,
    )
    assert valid["status"] == "completed"
    assert valid["baseline"]["status"] == "passed"
    assert valid["summary"]["baseline_valid"] is True
    assert valid["summary"]["run_count"] == 1
    assert valid["results"][0]["outcome"] == "escaped"

    print(
        "publication_mutation_harness: red baseline aborts without outcomes; "
        "green baseline permits one isolated mutation"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
