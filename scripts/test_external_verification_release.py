#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Focused adversarial tests for independent replay and release identity."""

from __future__ import annotations

import copy
import hashlib
import inspect
import json
import os
import subprocess
import tempfile
from pathlib import Path
from unittest.mock import patch

import external_verification_release as release
import replay_external_verification as replay
import run_external_verification as receipt


def git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def digest(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    """Keep release-identity assertions active when run with ``python -O``."""
    if not condition:
        raise AssertionError(message)


def expect_error(action, fragment: str) -> None:
    try:
        action()
    except release.ReleaseIdentityError as exc:
        require(
            fragment in str(exc),
            f"expected error fragment {fragment!r}; got {str(exc)!r}",
        )
    else:
        raise AssertionError(f"expected ReleaseIdentityError containing {fragment!r}")


def test_receipt_subprocess_environment() -> None:
    """Receipt production must not inherit ambient Git or runtime controls."""
    source = inspect.getsource(receipt.main)
    require(
        "projection_check = run(" in source,
        "receipt projection check bypassed the bounded subprocess wrapper",
    )
    hostile_environment = {
        "GIT_DIR": "/private/wrong-git-dir",
        "GIT_NAMESPACE": "refs/namespaces/wrong-release",
        "GIT_REPLACE_REF_BASE": "refs/replace/",
        "PYTHONHOME": "/private/wrong-python-home",
        "PYTHONPATH": "/private/wrong-python-path",
        "PYTHONOPTIMIZE": "2",
        "LC_ALL": "C",
        "LANG": "C",
        "LANGUAGE": "C",
        "PATH": "/private/wrong-bin",
    }
    completed = subprocess.CompletedProcess(
        ["fixture"], returncode=0, stdout="fixture\n", stderr=""
    )
    with patch.dict(os.environ, hostile_environment, clear=False):
        with patch.object(receipt.subprocess, "run", return_value=completed) as runner:
            require(receipt.git("rev-parse", "HEAD") == "fixture", "receipt Git read failed")
            receipt.run(["fixture"], cwd=receipt.ROOT)

    require(len(runner.call_args_list) == 2, "receipt subprocess calls were not exercised")
    for call in runner.call_args_list:
        kwargs = call.kwargs
        environment = kwargs["env"]
        for key in (
            "GIT_DIR",
            "GIT_NAMESPACE",
            "GIT_REPLACE_REF_BASE",
            "PYTHONHOME",
            "PYTHONPATH",
            "PYTHONOPTIMIZE",
        ):
            require(key not in environment, f"ambient {key} leaked into receipt child")
        require(environment["PATH"] == os.defpath, "receipt child PATH was not pinned")
        require(environment["LC_ALL"] == "C.UTF-8", "receipt child LC_ALL was not pinned")
        require(environment["LANG"] == "C.UTF-8", "receipt child LANG was not pinned")
        require(environment["LANGUAGE"] == "C.UTF-8", "receipt child LANGUAGE was not pinned")
        require(environment["GIT_ASKPASS"] == "/bin/false", "receipt Git prompting was not disabled")
        require(
            kwargs["timeout"] == receipt.SUBPROCESS_TIMEOUT_SECONDS,
            "receipt child timeout drifted",
        )
    require(
        receipt.ENVIRONMENT_CONTRACT
        == "clean_committed_snapshot_subprocess_environment_v1",
        "receipt environment contract drifted",
    )


def synthetic_repository(parent: Path) -> tuple[Path, dict, str, str, str, Path]:
    root = parent / "repo"
    root.mkdir()
    git(root, "init", "-q")
    git(root, "config", "user.email", "release-test@example.invalid")
    git(root, "config", "user.name", "External verification release test")
    contract = json.loads(
        (release.ROOT / release.CONTRACT_PATH).read_text(encoding="utf-8")
    )
    write_json(root / release.CONTRACT_PATH, contract)
    for relative in contract["tracked_artifacts"]:
        path = root / relative
        if path == root / release.CONTRACT_PATH:
            continue
        path.parent.mkdir(parents=True, exist_ok=True)
        if relative == "verification/comparator.json":
            source = release.ROOT / relative
            path.write_bytes(source.read_bytes())
        else:
            path.write_bytes(f"synthetic artifact: {relative}\n".encode())
    git(root, "add", ".")
    git(root, "commit", "-qm", "immutable release candidate")
    commit = git(root, "rev-parse", "HEAD")
    tree = git(root, "rev-parse", "HEAD^{tree}")
    tag = "v-test-external-verification"
    git(root, "tag", "-a", tag, "-m", "test release")

    config = json.loads(
        (root / "verification/comparator.json").read_text(encoding="utf-8")
    )
    diagnostic = contract["replay"]["expected_negative_diagnostic"]
    receipt = {
        "schema": release.RUNTIME_SCHEMA,
        "result": "pass",
        "phase": "final",
        "repository_commit": commit,
        "repository_tree": tree,
        "expected_repository_commit": commit,
        "repository_commit_matches_expected": True,
        "comparator_toolchain": {
            "expected_revisions": contract["toolchain"],
            "observed_revisions": contract["toolchain"],
            "revisions_match": True,
            "binary_digests": {
                name: "sha256:" + index * 64
                for name, index in zip(contract["toolchain"], "123")
            },
        },
        "statement_contract": {
            "theorem_names": config["theorem_names"],
            "permitted_axioms": config["permitted_axioms"],
            "config_digest": digest(root / "verification/comparator.json"),
        },
        "checks": {
            "positive_comparator_exit": 0,
            "negative_fixture_rejected": True,
            "negative_expected_diagnostic": diagnostic,
        },
        "whole_programme_disclosure": {"all_statuses_open": True},
    }
    receipt_path = parent / "runtime-receipt.json"
    write_json(receipt_path, receipt)
    return root, contract, commit, tree, tag, receipt_path


def test_replay_plan() -> None:
    commit = "a" * 40
    tree = "b" * 40
    plan = replay.replay_plan(commit, tree)
    require(plan["source"]["commit"] == commit, "replay plan lost source commit")
    require(plan["source"]["tree"] == tree, "replay plan lost source tree")
    require(
        plan["security"] == {
            "requires_linux_systemd_transient_unit": True,
            "network_disabled_inside_comparator": True,
            "floating_ref_accepted": False,
            "github_pull_request_merge_sha_accepted": False,
        },
        "replay plan security boundary changed",
    )
    require(
        plan["statement_contract"]["theorem"] in json.loads(
            (replay.ROOT / plan["statement_contract"]["positive_config"]).read_text()
        )["theorem_names"],
        "replay plan theorem is absent from its positive configuration",
    )
    live_contract = release.contract(release.ROOT)
    require(
        all(
            (release.ROOT / relative).is_file()
            for relative in live_contract["tracked_artifacts"]
        ),
        "release contract names a missing tracked artifact",
    )
    positive = json.loads(
        (release.ROOT / live_contract["replay"]["positive_config"]).read_text()
    )
    negative = json.loads(
        (release.ROOT / live_contract["replay"]["negative_config"]).read_text()
    )
    require(
        positive["theorem_names"] == [live_contract["replay"]["theorem"]],
        "positive replay theorem differs from the release contract",
    )
    require(
        negative["theorem_names"] == [live_contract["replay"]["theorem"]],
        "negative replay theorem differs from the release contract",
    )
    require(
        positive["permitted_axioms"] == live_contract["replay"]["permitted_axioms"],
        "positive replay axioms differ from the release contract",
    )
    require(
        negative["permitted_axioms"] == live_contract["replay"]["permitted_axioms"],
        "negative replay axioms differ from the release contract",
    )
    try:
        replay.replay_plan("main", tree)
    except replay.ReplayError as exc:
        require(
            "full lowercase Git id" in str(exc),
            "floating replay error did not identify the immutable-id rule",
        )
    else:
        raise AssertionError("floating branch name was accepted as a replay commit")


def test_release_manifest() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        parent = Path(temporary)
        root, contract, commit, tree, tag, receipt_path = synthetic_repository(parent)
        manifest = release.build_manifest(
            root=root,
            source_commit=commit,
            source_tree=tree,
            release_tag=tag,
            runtime_receipt_path=receipt_path,
        )
        release.validate_manifest(manifest, root=root, runtime_receipt_path=receipt_path)
        require(
            manifest["source"]["commit_url"].endswith("/commit/" + commit),
            "release manifest source URL is not commit-bound",
        )
        require(
            all(
                f"/blob/{commit}/" in row["immutable_url"]
                for row in manifest["tracked_artifacts"]
            ),
            "release manifest artifact URL is not commit-bound",
        )
        expected_theorem_count = len(
            json.loads(
                (root / "verification/comparator.json").read_text(encoding="utf-8")
            )["theorem_names"]
        )
        require(
            manifest["runtime_receipt"]["theorem_count"] == expected_theorem_count,
            "release manifest theorem count differs from the comparator contract",
        )
        require(
            manifest["release_assets"]["required"] == [
                f"external-verification-receipt-{commit}.json",
                f"external-verification-release-manifest-{commit}.json",
            ],
            "release manifest asset names are not commit-bound",
        )
        encoded = json.dumps(manifest)
        require("/blob/main/" not in encoded, "release manifest contains a floating main URL")
        require("/blob/HEAD/" not in encoded, "release manifest contains a floating HEAD URL")

        wrong_tree = copy.deepcopy(manifest)
        wrong_tree["source"]["tree"] = "f" * 40
        expect_error(
            lambda: release.validate_manifest(
                wrong_tree, root=root, runtime_receipt_path=receipt_path
            ),
            "checkout tree",
        )
        floating = copy.deepcopy(manifest)
        floating["tracked_artifacts"][0]["immutable_url"] = (
            contract["repository"] + "/blob/main/formalization.yaml"
        )
        expect_error(
            lambda: release.validate_manifest(
                floating, root=root, runtime_receipt_path=receipt_path
            ),
            "tracked-artifact identities are stale",
        )
        failed_receipt = json.loads(receipt_path.read_text())
        failed_receipt["result"] = "fail"
        failed_path = parent / "failed-receipt.json"
        write_json(failed_path, failed_receipt)
        expect_error(
            lambda: release.build_manifest(
                root=root,
                source_commit=commit,
                source_tree=tree,
                release_tag=tag,
                runtime_receipt_path=failed_path,
            ),
            "not a final pass",
        )
        expect_error(
            lambda: release.build_manifest(
                root=root,
                source_commit=commit,
                source_tree=tree,
                release_tag="main",
                runtime_receipt_path=receipt_path,
            ),
            "non-floating tag",
        )


def main() -> int:
    test_receipt_subprocess_environment()
    test_replay_plan()
    test_release_manifest()
    print(
        "external-verification release contract: replay plan, immutable manifest, "
        "runtime receipt, floating-ref and mismatch adversaries passed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
