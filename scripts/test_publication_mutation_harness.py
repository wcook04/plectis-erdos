#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exercise the mutation harness's baseline-validity boundary."""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

from run_publication_mutations import (
    parse_check_count,
    run_mutations,
)
import run_publication_mutations as experiment
import validation_singleflight as singleflight


def require(condition: bool, message: str) -> None:
    """Keep mutation-harness trust checks active when Python runs with -O."""
    if not condition:
        raise AssertionError(message)


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
    hostile = {
        "GIT_DIR": "/private/wrong-git-dir",
        "GIT_NAMESPACE": "refs/namespaces/wrong-mutations",
        "GIT_REPLACE_REF_BASE": "refs/replace/",
        "PYTHONPATH": "/private/wrong-python-path",
        "PYTHONOPTIMIZE": "2",
        "LC_ALL": "C",
        "LANG": "C",
        "LANGUAGE": "C",
        "PATH": "/private/wrong-bin",
    }
    completed = subprocess.CompletedProcess(
        ["fixture"], returncode=0, stdout="ok\n", stderr=""
    )
    with patch.dict(os.environ, hostile, clear=False):
        expected = singleflight.command_environment()
        with patch.object(
            experiment.subprocess, "run", return_value=completed
        ) as runner:
            require(
                experiment.run_checked(["fixture"], Path("/mutation-fixture")).stdout
                == "ok\n",
                "mutation Git helper did not return stdout",
            )
            bounded = experiment.run_gate_command(
                ["fixture"], Path("/mutation-fixture"), 17
            )
            require(bounded["status"] == "passed", "mutation gate fixture failed")

    require(len(runner.call_args_list) == 2, "mutation subprocess helpers were not exercised")
    require(
        runner.call_args_list[0].kwargs["env"] == expected,
        "mutation Git helper environment drifted from canonical isolation",
    )
    require(
        runner.call_args_list[0].kwargs["timeout"]
        == experiment.SUBPROCESS_TIMEOUT_SECONDS,
        "mutation Git helper timeout drifted",
    )
    require(
        runner.call_args_list[1].kwargs["env"] == expected,
        "mutation gate environment drifted from canonical isolation",
    )
    require(
        runner.call_args_list[1].kwargs["timeout"] == 17,
        "mutation gate did not preserve its caller timeout",
    )
    require(
        experiment.ENVIRONMENT_CONTRACT
        == "clean_committed_snapshot_subprocess_environment_v1",
        "mutation environment contract drifted",
    )

    with tempfile.TemporaryDirectory(prefix="publication-mutation-fixture-") as raw:
        source = Path(raw) / "source"
        source.mkdir()
        (source / "README.md").write_text("fixture\n", encoding="utf-8")
        experiment.run_checked(["git", "init", "-q"], source)
        experiment.run_checked(["git", "add", "README.md"], source)
        experiment.run_checked(
            [
                "git",
                "-c",
                "user.email=mutation-test@example.invalid",
                "-c",
                "user.name=Publication mutation test",
                "commit",
                "-qm",
                "fixture checkpoint",
            ],
            source,
        )
        checkpoint = experiment.run_checked(
            ["git", "rev-parse", "HEAD"], source
        ).stdout.strip()
        original_root = experiment.ROOT
        experiment.ROOT = source
        try:
            invalid = run_mutations(
                synthetic_manifest(1, checkpoint),
                ["T1"],
                30,
                "HEAD",
                checkpoint,
            )
            valid = run_mutations(
                synthetic_manifest(0, checkpoint),
                ["T1"],
                30,
                "HEAD",
                checkpoint,
            )
        finally:
            experiment.ROOT = original_root

    require(
        parse_check_count("check_release: all 5,207 checks passed") == 5207,
        "release check count parser lost comma handling",
    )
    require(
        parse_check_count("failure across 4,920 checks") == 4920,
        "release failure count parser lost comma handling",
    )

    require(invalid["status"] == "invalid_baseline", "red baseline did not abort")
    require(invalid["baseline"]["status"] == "failed", "red baseline status drifted")
    require(
        invalid["summary"]["baseline_valid"] is False,
        "red baseline was reported as valid",
    )
    require(invalid["summary"]["run_count"] == 0, "red baseline ran mutations")
    require(invalid["results"] == [], "red baseline emitted mutation outcomes")

    require(valid["status"] == "completed", "green baseline did not complete")
    require(valid["baseline"]["status"] == "passed", "green baseline status drifted")
    require(
        valid["summary"]["baseline_valid"] is True,
        "green baseline was reported as invalid",
    )
    require(valid["summary"]["run_count"] == 1, "green baseline ran wrong mutation count")
    require(
        valid["results"][0]["outcome"] == "escaped",
        "green baseline mutation outcome drifted",
    )

    print(
        "publication_mutation_harness: red baseline aborts without outcomes; "
        "green baseline permits one isolated mutation"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
