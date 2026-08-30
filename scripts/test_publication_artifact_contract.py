#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial fixtures for the publication-artifact contract."""

from __future__ import annotations

import argparse
import copy
import os
import tempfile
from pathlib import Path
from unittest.mock import patch

from publication_contract import (
    CONTRACT_PATH,
    ENVIRONMENT_CONTRACT,
    RepositoryReader,
    load_json,
    mutation_fixture_failures,
    validate_publication_contract,
)


ROOT = Path(__file__).resolve().parent.parent


def require(condition: bool, message: str) -> None:
    """Keep publication-contract checks active when run with ``python -O``."""
    if not condition:
        raise AssertionError(message)


def assert_committed_snapshot_environment() -> None:
    """Prove Git snapshot reads ignore hostile inherited selectors."""
    hostile = {
        "GIT_DIR": str(ROOT / "not-a-git-directory"),
        "GIT_NAMESPACE": "hostile-namespace",
        "GIT_REPLACE_REF_BASE": "refs/replace/hostile/",
    }
    with patch.dict(os.environ, hostile, clear=False):
        committed = RepositoryReader(ROOT, "HEAD").read_bytes(CONTRACT_PATH)
    require(
        committed.startswith(b"{"),
        "committed publication contract was not read as JSON",
    )
    require(
        ENVIRONMENT_CONTRACT == "clean_committed_snapshot_subprocess_environment_v1",
        "publication contract lost its clean-snapshot environment contract",
    )


def assert_worktree_symlink_boundary() -> None:
    """Prove worktree-mode contract reads cannot follow a substituted directory."""
    with tempfile.TemporaryDirectory(prefix="publication-contract-symlink-") as temporary:
        root = Path(temporary) / "checkout"
        outside = Path(temporary) / "outside"
        root.mkdir()
        outside.mkdir()
        (outside / "publication_contract.json").write_text("{}\n", encoding="utf-8")
        (root / "docs").symlink_to(outside, target_is_directory=True)
        try:
            RepositoryReader(root).read_bytes("docs/publication_contract.json")
        except ValueError as exc:
            require("symbolic links" in str(exc), str(exc))
        else:
            raise AssertionError("worktree publication reader followed a symlink")


def assert_worktree_special_file_boundary() -> None:
    """Prove worktree reads reject a FIFO before attempting to consume it."""
    if not hasattr(os, "mkfifo"):
        return
    with tempfile.TemporaryDirectory(
        prefix="publication-contract-fifo-", dir=ROOT
    ) as temporary:
        root = Path(temporary) / "checkout"
        root.mkdir()
        fifo = root / "publication_contract.json"
        os.mkfifo(fifo)
        try:
            RepositoryReader(root).read_bytes("publication_contract.json")
        except ValueError as exc:
            require("regular file" in str(exc), str(exc))
        else:
            raise AssertionError("worktree publication reader opened a special file")


def assert_problem_note_route_template(reader: RepositoryReader) -> None:
    """Ensure the shared problem-note route joins the selected artifact row."""
    contract = load_json(reader, CONTRACT_PATH)
    route = next(
        row
        for row in contract["entrypoints"]
        if row.get("id") == "read_one_problem_note"
    )
    steps = route["query_steps"]
    require(
        "--publication-artifact <publication_artifact_id>" in steps[0],
        "problem-note route does not bind its publication artifact id",
    )
    require(
        "--artifact <rendered_path>" in steps[1],
        "problem-note route does not bind its rendered path",
    )
    bindings = {
        row["name"]: row
        for row in route["parameter_bindings"]
    }
    require(
        bindings["publication_artifact_id"]["source"] == "artifacts[].id",
        "problem-note artifact-id binding lost its registry source",
    )
    require(
        bindings["rendered_path"]["source"] == "artifacts[].rendered_path",
        "problem-note rendered-path binding lost its registry source",
    )

    mutated = copy.deepcopy(contract)
    mutated_route = next(
        row
        for row in mutated["entrypoints"]
        if row.get("id") == "read_one_problem_note"
    )
    mutated_route["query_steps"][0] = (
        "python3 scripts/query_corpus.py --publication-artifact erdos_269_note"
    )
    errors = validate_publication_contract(reader, contract_override=mutated)
    require(
        any("hard-codes a problem-note artifact id" in error for error in errors),
        "hard-coded problem-note route mutation was not rejected",
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--git-ref",
        help="test a committed Git ref, or ':' for the staged index",
    )
    args = parser.parse_args()
    assert_committed_snapshot_environment()
    assert_worktree_symlink_boundary()
    assert_worktree_special_file_boundary()
    reader = RepositoryReader(ROOT, args.git_ref)
    assert_problem_note_route_template(reader)
    baseline_errors = validate_publication_contract(reader)
    fixture_failures = mutation_fixture_failures(reader) if not baseline_errors else []
    if baseline_errors or fixture_failures:
        print(
            "test_publication_artifact_contract: "
            f"{len(baseline_errors)} baseline failure(s), "
            f"{len(fixture_failures)} fixture failure(s)"
        )
        for error in baseline_errors:
            print(f"  FAIL baseline: {error}")
        for fixture in fixture_failures:
            print(f"  FAIL fixture did not reject: {fixture}")
        return 1
    print(
        "test_publication_artifact_contract: baseline and known-bad "
        "publication mutations verified"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
