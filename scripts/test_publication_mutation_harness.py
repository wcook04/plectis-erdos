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
    clone_at_checkpoint,
    parse_check_count,
    resolve_commit,
    run_mutations,
)
import run_publication_mutations as experiment
import validation_singleflight as singleflight




def require(condition: bool, message: str) -> None:
    """Keep mutation-harness trust checks active when Python runs with -O."""
    if not condition:
        raise AssertionError(message)


def check_subprocess_isolation() -> None:
    """The harness must sanitise a hostile environment before it shells out."""

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


def fixture_repository(parent: Path) -> Path:
    """Create the smallest real Git source that exercises clone/reset/mutation."""

    root = parent / "source"
    root.mkdir()
    (root / "README.md").write_text("publication mutation fixture\n", encoding="utf-8")
    environment = singleflight.command_environment()
    for command in (
        ["git", "init", "--quiet"],
        ["git", "add", "--", "README.md"],
        [
            "git",
            "-c",
            "user.name=Plectis fixture",
            "-c",
            "user.email=fixture@example.invalid",
            "commit",
            "--quiet",
            "-m",
            "fixture",
        ],
    ):
        completed = subprocess.run(
            command,
            cwd=root,
            env=environment,
            capture_output=True,
            text=True,
            check=False,
            timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
        )
        require(
            completed.returncode == 0,
            completed.stderr.strip() or completed.stdout.strip(),
        )
    return root


def main() -> int:
    check_subprocess_isolation()
    assert parse_check_count("check_release: all 5,207 checks passed") == 5207
    assert parse_check_count("failure across 4,920 checks") == 4920

    with tempfile.TemporaryDirectory() as directory:
        root = fixture_repository(Path(directory))
        with patch.object(experiment, "ROOT", root):
            checkpoint = resolve_commit("HEAD")
            shared_parent = Path(directory) / "shared"
            shared_parent.mkdir()
            shared = clone_at_checkpoint(checkpoint, shared_parent)
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
