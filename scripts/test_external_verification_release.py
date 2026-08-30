#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Focused adversarial tests for independent replay and release identity."""

from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import tempfile
from pathlib import Path

import external_verification_release as release
import replay_external_verification as replay


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


def expect_error(action, fragment: str) -> None:
    try:
        action()
    except release.ReleaseIdentityError as exc:
        assert fragment in str(exc), (fragment, str(exc))
    else:
        raise AssertionError(f"expected ReleaseIdentityError containing {fragment!r}")


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
    assert plan["source"]["commit"] == commit
    assert plan["source"]["tree"] == tree
    assert plan["security"] == {
        "requires_linux_systemd_transient_unit": True,
        "network_disabled_inside_comparator": True,
        "floating_ref_accepted": False,
        "github_pull_request_merge_sha_accepted": False,
    }
    assert plan["statement_contract"]["theorem"] in json.loads(
        (replay.ROOT / plan["statement_contract"]["positive_config"]).read_text()
    )["theorem_names"]
    live_contract = release.contract(release.ROOT)
    assert all(
        (release.ROOT / relative).is_file()
        for relative in live_contract["tracked_artifacts"]
    )
    positive = json.loads(
        (release.ROOT / live_contract["replay"]["positive_config"]).read_text()
    )
    negative = json.loads(
        (release.ROOT / live_contract["replay"]["negative_config"]).read_text()
    )
    assert positive["theorem_names"] == [live_contract["replay"]["theorem"]]
    assert negative["theorem_names"] == [live_contract["replay"]["theorem"]]
    assert positive["permitted_axioms"] == live_contract["replay"]["permitted_axioms"]
    assert negative["permitted_axioms"] == live_contract["replay"]["permitted_axioms"]
    try:
        replay.replay_plan("main", tree)
    except replay.ReplayError as exc:
        assert "full lowercase Git id" in str(exc)
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
        assert manifest["source"]["commit_url"].endswith("/commit/" + commit)
        assert all(
            f"/blob/{commit}/" in row["immutable_url"]
            for row in manifest["tracked_artifacts"]
        )
        expected_theorem_count = len(
            json.loads(
                (root / "verification/comparator.json").read_text(encoding="utf-8")
            )["theorem_names"]
        )
        assert manifest["runtime_receipt"]["theorem_count"] == expected_theorem_count
        assert manifest["release_assets"]["required"] == [
            f"external-verification-receipt-{commit}.json",
            f"external-verification-release-manifest-{commit}.json",
        ]
        encoded = json.dumps(manifest)
        assert "/blob/main/" not in encoded
        assert "/blob/HEAD/" not in encoded

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
    test_replay_plan()
    test_release_manifest()
    print(
        "external-verification release contract: replay plan, immutable manifest, "
        "runtime receipt, floating-ref and mismatch adversaries passed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
