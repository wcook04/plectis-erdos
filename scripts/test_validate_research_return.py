#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial executable checks for the public return validator."""

from __future__ import annotations

import copy
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest import mock

import validate_research_return as validator
import validation_singleflight as singleflight


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "validate_research_return.py"
FIXTURE = ROOT / ".github" / "fixtures" / "unaccepted-research-return.json"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def run_cli(input_path: Path, *arguments: str) -> subprocess.CompletedProcess[str]:
    """Run the public validator CLI without ambient checkout state."""
    return subprocess.run(
        [sys.executable, str(SCRIPT), str(input_path), *arguments],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
        env=singleflight.command_environment(),
        timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
    )


def main() -> int:
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    identity = validator.repository_identity_contract.load_identity()
    require(
        validator.GIT_COMMAND_TIMEOUT_SECONDS
        == singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
        "return validator Git timeout drifted from the canonical boundary",
    )

    errors = validator.validate_document(
        fixture,
        require_submitted=True,
        repository_identity=identity,
    )
    require(not errors, f"committed submitted fixture should validate: {errors}")
    require(
        validator.validate_document(
            fixture,
            require_accepted=True,
            repository_identity=identity,
        ),
        "an unaccepted fixture crossed the accepted gate",
    )

    negative_fixture = json.loads(
        (ROOT / "docs/research-commons/returns/negative-example.json").read_text(
            encoding="utf-8"
        )
    )
    require(
        not validator.validate_document(negative_fixture, repository_identity=identity),
        "the committed negative fixture should validate before mutation",
    )
    for invalid_exit_code in (False, True, 0.0):
        mutated_exit_code = copy.deepcopy(negative_fixture)
        mutated_exit_code["evidence"][0]["exit_code"] = invalid_exit_code
        require(
            any(
                "evidence[0].exit_code: passed evidence must have exit code 0" in error
                for error in validator.validate_document(
                    mutated_exit_code, repository_identity=identity
                )
            ),
            f"passed evidence accepted non-integer exit code {invalid_exit_code!r}",
        )

    mutated_kind = copy.deepcopy(fixture)
    mutated_kind["record_kind"] = "accepted_receipt"
    require(
        any(
            "accepted commit" in error or "proposed commit" in error
            for error in validator.validate_document(
                mutated_kind,
                require_accepted=True,
                repository_identity=identity,
            )
        ),
        "accepted mutation without accepted/proposed commits was not rejected",
    )
    mutated_paths = copy.deepcopy(fixture)
    mutated_paths["repository"]["changed_paths"] = ["../outside.json"]
    require(
        any("repository.changed_paths" in error for error in validator.validate_document(mutated_paths)),
        "repository escape path was not rejected",
    )

    with tempfile.TemporaryDirectory() as directory:
        directory_path = Path(directory)
        input_path = directory_path / "return.json"
        input_path.write_bytes(FIXTURE.read_bytes())
        malformed_path = directory_path / "malformed-utf8.json"
        malformed_path.write_bytes(b"{\xff\n")
        malformed_cli = run_cli(malformed_path, "--require-submitted")
        require(malformed_cli.returncode == 2, "malformed UTF-8 input was not classified as CLI input failure")
        malformed_receipt = json.loads(malformed_cli.stdout)
        require(
            malformed_receipt["valid"] is False
            and any("utf-8" in error.lower() for error in malformed_receipt["errors"]),
            "malformed UTF-8 input did not produce a machine-readable decode diagnostic",
        )
        require("Traceback" not in malformed_cli.stderr, "malformed UTF-8 input emitted a traceback")
        hostile_environment = {
            "GIT_DIR": "/private/wrong-git-dir",
            "GIT_NAMESPACE": "refs/namespaces/wrong-release",
            "GIT_REPLACE_REF_BASE": "refs/replace/",
            "PYTHONPATH": "/private/wrong-python-path",
            "LC_ALL": "C",
            "LANG": "C",
        }
        with mock.patch.dict(os.environ, hostile_environment, clear=False):
            valid_cli = run_cli(
                input_path, "--require-submitted", "--format", "json"
            )
        require(valid_cli.returncode == 0, valid_cli.stderr)
        receipt = json.loads(valid_cli.stdout)
        require(receipt["valid"] is True and receipt["submitted"] is True, "CLI receipt lost submitted state")

        symlink = directory_path / "symlink-return.json"
        symlink.symlink_to(input_path)
        with mock.patch.dict(os.environ, hostile_environment, clear=False):
            unsafe_cli = run_cli(symlink, "--require-submitted")
        require(unsafe_cli.returncode == 2, "symlinked return input crossed the path boundary")
        unsafe_receipt = json.loads(unsafe_cli.stdout)
        require(
            any("symbolic links" in error for error in unsafe_receipt["errors"]),
            "symlink rejection omitted its path-policy reason",
        )

    print("validate_research_return: submitted gate, accepted exclusion, path and CLI safety PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
