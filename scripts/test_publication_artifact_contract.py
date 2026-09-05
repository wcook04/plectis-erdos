#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial fixtures for the publication-artifact contract."""

from __future__ import annotations

import argparse
import copy
import json
import os
import tempfile
from pathlib import Path
from unittest.mock import patch

from publication_contract import (
    CONTRACT_PATH,
    DYNAMIC_PAPER_TARGETS_COMMAND,
    ENVIRONMENT_CONTRACT,
    PAPER_REGISTRY_PATH,
    PAPER_REGISTRY_SCHEMA,
    EVIDENCE_PATH,
    RepositoryReader,
    evaluation_checkpoint_census,
    load_json,
    makefile_papers,
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


def _registry_bytes(rows: list[object], *, schema: str = PAPER_REGISTRY_SCHEMA) -> bytes:
    return (
        json.dumps(
            {
                "schema": schema,
                "this_repository": "plectis-erdos",
                "support_sources": [],
                "papers": rows,
            }
        )
        + "\n"
    ).encode("utf-8")


def _native_row(stem: str, *, paper_id: str | None = None) -> dict[str, str]:
    return {
        "paper_id": paper_id or stem,
        "source": f"paper/{stem}.tex",
        "pdf": f"{stem}.pdf",
        "relation_to_this_repository": "native",
    }


def assert_dynamic_makefile_manifest_is_data_only() -> None:
    dynamic_makefile = f"PAPERS := {DYNAMIC_PAPER_TARGETS_COMMAND}\n"
    rows = [
        _native_row("alpha-paper"),
        {
            "paper_id": "external-mirror",
            "source": "vendor/external.tex",
            "pdf": "external.pdf",
            "relation_to_this_repository": "mirror",
        },
        _native_row("beta-paper"),
    ]
    reader = RepositoryReader(
        ROOT,
        "HEAD",
        {PAPER_REGISTRY_PATH: _registry_bytes(rows)},
    )
    with patch("publication_contract.subprocess.run", side_effect=AssertionError):
        require(
            makefile_papers(dynamic_makefile, reader)
            == {"alpha-paper", "beta-paper"},
            "dynamic Make manifest did not derive native targets from the reader ref",
        )
    require(
        makefile_papers("PAPERS = historical-a historical-b\n")
        == {"historical-a", "historical-b"},
        "historical static PAPERS parsing regressed",
    )
    for unsupported in (
        "PAPERS := $(shell touch should-not-run)\n",
        "PAPERS = ${UNTRUSTED}\n",
    ):
        try:
            makefile_papers(unsupported, reader)
        except ValueError as exc:
            require("unsupported dynamic Make expression" in str(exc), str(exc))
        else:
            raise AssertionError("unsupported Make expression was accepted")


def assert_dynamic_manifest_registry_failures() -> None:
    dynamic_makefile = f"PAPERS := {DYNAMIC_PAPER_TARGETS_COMMAND}\n"
    bad_registries = (
        _registry_bytes([_native_row("alpha")], schema="wrong-schema"),
        _registry_bytes([_native_row("alpha"), _native_row("beta", paper_id="alpha")]),
        _registry_bytes([_native_row("Unsafe_Name")]),
        _registry_bytes(
            [
                {
                    **_native_row("alpha"),
                    "source": "paper/not-alpha.tex",
                }
            ]
        ),
        _registry_bytes([_native_row("alpha"), _native_row("alpha", paper_id="other")]),
        b"{not json}\n",
    )
    for registry in bad_registries:
        reader = RepositoryReader(ROOT, byte_overrides={PAPER_REGISTRY_PATH: registry})
        try:
            makefile_papers(dynamic_makefile, reader)
        except ValueError:
            pass
        else:
            raise AssertionError("malformed dynamic paper registry was accepted")

    with tempfile.TemporaryDirectory(prefix="publication-registry-missing-") as temp:
        try:
            makefile_papers(dynamic_makefile, RepositoryReader(Path(temp)))
        except ValueError as exc:
            require(PAPER_REGISTRY_PATH in str(exc), str(exc))
        else:
            raise AssertionError("missing dynamic paper registry was accepted")
def assert_snapshot_reuse_and_live_readers() -> None:
    """Keep batch framing, moving refs, overrides, and live index reads distinct."""
    with tempfile.TemporaryDirectory(prefix="publication-snapshot-", dir=ROOT) as temp:
        root = Path(temp)
        live = RepositoryReader(root)

        def git(*args: str) -> None:
            result = live._git_run(*args)
            require(result.returncode == 0, result.stderr.decode(errors="replace"))

        git("init", "--quiet")
        original = b"binary\x00line\n123 blob 4\nend\r\n"
        (root / "a").write_bytes(original)
        (root / "b").write_bytes(b"old b")
        git("add", "a", "b")
        git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
            "commit", "--quiet", "-m", "first")
        snapshot = RepositoryReader(root, "HEAD")
        with patch.object(snapshot, "_git_run", wraps=snapshot._git_run) as calls:
            snapshot.prefetch(["0-missing", "a", "a", "missing"])
            require(snapshot.read_bytes("a") == original, "batch changed binary bytes")
            require(snapshot.read_bytes("a") == original, "repeated snapshot read drifted")
            require(sum(call.args[:2] == ("cat-file", "--batch")
                        for call in calls.call_args_list) == 1, "batch was duplicated")
            require(not any(call.args[0] == "show" for call in calls.call_args_list),
                    "prefetched bytes were read again through Git")
        staged = RepositoryReader(root, ":")
        overlay = snapshot.with_overrides({"a": b"overlay"})
        require(overlay.read_bytes("a") == b"overlay", "overlay lost its replacement")
        require(snapshot.read_bytes("a") == original, "overlay modified its parent")
        require(staged.read_bytes("a") == original, "initial staged bytes drifted")
        (root / "a").write_bytes(b"new a")
        (root / "b").write_bytes(b"new b")
        require(live.read_bytes("a") == b"new a", "worktree reader cached stale bytes")
        git("add", "a", "b")
        require(staged.read_bytes("a") == b"new a", "index reader cached stale bytes")
        git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
            "commit", "--quiet", "-m", "second")
        require(snapshot.read_bytes("b") == b"old b", "snapshot mixed moved HEAD bytes")
        require(overlay.read_bytes("b") == b"old b", "overlay mixed moved HEAD bytes")
        require(RepositoryReader(root, "HEAD").read_bytes("b") == b"new b",
                "new snapshot did not observe moved HEAD")
        snapshot.byte_overrides["a"] = b"mutation"
        require(snapshot.read_bytes("a") == b"mutation", "cache hid fixture override")
        require(not snapshot.exists("missing"), "batch invented a missing file")
        with patch.object(live, "_git_run", wraps=live._git_run) as calls:
            for _ in range(2):
                require(live.git_object_exists(snapshot._snapshot_ref), "commit disappeared")
                require(live.git_object_exists("HEAD"), "HEAD disappeared")
                require(not live.git_object_exists("0" * 40), "missing commit invented")
            require(calls.call_count == 5,
                    "only positive immutable commit identities may be reused")


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
    assert_dynamic_makefile_manifest_is_data_only()
    assert_dynamic_manifest_registry_failures()
    assert_snapshot_reuse_and_live_readers()
    reader = RepositoryReader(ROOT, args.git_ref)
    assert_problem_note_route_template(reader)
    baseline_errors = validate_publication_contract(reader)
    if not baseline_errors:
        checkpoint = load_json(reader, EVIDENCE_PATH)["evaluation"]["checkpoint"]
        census = evaluation_checkpoint_census(reader, checkpoint)
        original_count = census["module_count"]
        census["module_count"] = -1
        require(evaluation_checkpoint_census(reader, checkpoint)["module_count"] == original_count,
                "a consumer mutated the shared historical census")
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
