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
import validation_singleflight as singleflight


def git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
        env=singleflight.command_environment(),
        timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
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


def test_release_file_boundary() -> None:
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        private = root / "private"
        private.mkdir()
        (private / "secret.json").write_text("{}\n", encoding="utf-8")
        repository = root / "verification"
        repository.mkdir()
        (repository / "linked").symlink_to(private, target_is_directory=True)
        expect_error(
            lambda: release.load_json(
                repository / "linked" / "secret.json", root=root
            ),
            "symlinked release input",
        )
        external = root / "external-receipt.json"
        external.write_text("{}\n", encoding="utf-8")
        link = root / "receipt-link.json"
        link.symlink_to(external)
        expect_error(
            lambda: release.load_json(link),
            "symlinked release input",
        )
        fifo = root / "release.fifo"
        os.mkfifo(fifo)
        with patch.object(release, "safe_release_file", return_value=fifo):
            expect_error(
                lambda: release.sha256_file(fifo),
                "regular file",
            )
        sentinel = root / "manifest-sentinel.json"
        sentinel.write_text("sentinel\n", encoding="utf-8")
        output_link = root / "manifest-link.json"
        output_link.symlink_to(sentinel)
        expect_error(
            lambda: release.write_json(output_link, {"ok": True}, overwrite=True),
            "output path contains a symlink",
        )
        require(
            sentinel.read_text(encoding="utf-8") == "sentinel\n",
            "symlinked output path modified its target",
        )

    private_tmp = Path("/private/tmp")
    temporary_root = str(private_tmp) if private_tmp.is_dir() else None
    with tempfile.TemporaryDirectory(
        prefix="external-release-parent-race-", dir=temporary_root
    ) as raw:
        root = Path(raw)
        raced_parent = root / "manifest-parent"
        raced_parent.mkdir()
        original_parent = root / "manifest-parent-original"
        outside = root / "outside"
        outside.mkdir()
        sentinel = outside / "sentinel.txt"
        sentinel.write_text("keep me\n", encoding="utf-8")
        raced_output = raced_parent / "manifest.json"
        original_open = release.os.open

        def swap_parent(
            path: Path,
            flags: int,
            mode: int = 0o777,
            *,
            dir_fd: int | None = None,
        ) -> int:
            if dir_fd is not None and Path(path).name == raced_output.name:
                raced_parent.rename(original_parent)
                raced_parent.symlink_to(outside, target_is_directory=True)
            return original_open(path, flags, mode, dir_fd=dir_fd) if dir_fd is not None else original_open(path, flags, mode)

        with patch.object(release.os, "open", side_effect=swap_parent):
            release.write_json(raced_output, {"status": "blocked"}, overwrite=True)
        require(
            not (outside / raced_output.name).exists(),
            "manifest writer followed a swapped parent directory",
        )
        require(
            sentinel.read_text(encoding="utf-8") == "keep me\n",
            "manifest parent-swap race modified the outside sentinel",
        )
        require(
            (original_parent / raced_output.name).is_file(),
            "manifest writer did not create through the held parent descriptor",
        )


def test_replay_file_boundary() -> None:
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        private = root / "private"
        private.mkdir()
        (private / "config.json").write_text("{}\n", encoding="utf-8")
        repository = root / "verification"
        repository.mkdir()
        (repository / "linked").symlink_to(private, target_is_directory=True)
        try:
            replay.load_json(
                repository / "linked" / "config.json", root=root
            )
        except replay.ReplayError as exc:
            require("symlinked replay input" in str(exc), str(exc))
        else:
            raise AssertionError("replay followed a symlinked parent")
        link = root / "tool-link"
        link.symlink_to(private / "config.json")
        try:
            replay.sha256_file(link)
        except replay.ReplayError as exc:
            require("symlinked replay input" in str(exc), str(exc))
        else:
            raise AssertionError("replay hashed a symlinked tool")
        fifo = root / "replay.fifo"
        os.mkfifo(fifo)
        with patch.object(replay, "safe_replay_file", return_value=fifo):
            try:
                replay.sha256_file(fifo)
            except replay.ReplayError as exc:
                require("regular file" in str(exc), str(exc))
            else:
                raise AssertionError("replay hashed a special file")
        sentinel = root / "replay-sentinel.json"
        sentinel.write_text("sentinel\n", encoding="utf-8")
        output_link = root / "replay-link.json"
        output_link.symlink_to(sentinel)
        try:
            replay._write_replay_receipt(output_link, {"ok": True})
        except replay.ReplayError as exc:
            require("output path contains a symlink" in str(exc), str(exc))
        else:
            raise AssertionError("replay followed a symlinked output")
        require(
            sentinel.read_text(encoding="utf-8") == "sentinel\n",
            "symlinked replay output modified its target",
        )


def test_replay_output_boundary() -> None:
    private_tmp = Path("/private/tmp")
    temporary_root = str(private_tmp) if private_tmp.is_dir() else None
    with tempfile.TemporaryDirectory(
        prefix="replay-receipt-parent-race-", dir=temporary_root
    ) as raw:
        root = Path(raw)
        raced_parent = root / "receipt-parent"
        raced_parent.mkdir()
        original_parent = root / "receipt-parent-original"
        outside = root / "outside"
        outside.mkdir()
        sentinel = outside / "sentinel.txt"
        sentinel.write_text("keep me\n", encoding="utf-8")
        raced_output = raced_parent / "replay.json"
        original_open = replay.os.open

        def swap_parent(
            path: Path,
            flags: int,
            mode: int = 0o777,
            *,
            dir_fd: int | None = None,
        ) -> int:
            if dir_fd is not None and Path(path).name == raced_output.name:
                raced_parent.rename(original_parent)
                raced_parent.symlink_to(outside, target_is_directory=True)
            return original_open(path, flags, mode, dir_fd=dir_fd) if dir_fd is not None else original_open(path, flags, mode)

        with patch.object(replay.os, "open", side_effect=swap_parent):
            replay._write_replay_receipt(raced_output, {"status": "blocked"})
        require(
            not (outside / raced_output.name).exists(),
            "replay receipt writer followed a swapped parent directory",
        )
        require(
            sentinel.read_text(encoding="utf-8") == "keep me\n",
            "replay parent-swap race modified the outside sentinel",
        )
        require(
            (original_parent / raced_output.name).is_file(),
            "replay receipt writer did not create through the held parent descriptor",
        )


def test_runtime_input_boundary() -> None:
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        private = root / "private"
        private.mkdir()
        (private / "secret.bin").write_bytes(b"outside\n")
        repository = root / "verification"
        repository.mkdir()
        (repository / "linked").symlink_to(private, target_is_directory=True)
        try:
            receipt.safe_runtime_file(
                repository / "linked" / "secret.bin", root=root
            )
        except receipt.VerificationInputError:
            pass
        else:
            raise AssertionError("runtime receipt followed a symlinked parent")
        link = root / "binary-link"
        link.symlink_to(private / "secret.bin")
        require(receipt.digest(link) is None, "runtime receipt hashed a symlinked tool")


def test_runtime_output_boundary() -> None:
    private_tmp = Path("/private/tmp")
    temporary_root = str(private_tmp) if private_tmp.is_dir() else None
    with tempfile.TemporaryDirectory(
        prefix="runtime-receipt-parent-race-", dir=temporary_root
    ) as raw:
        root = Path(raw)
        raced_parent = root / "receipt-parent"
        raced_parent.mkdir()
        original_parent = root / "receipt-parent-original"
        outside = root / "outside"
        outside.mkdir()
        sentinel = outside / "sentinel.txt"
        sentinel.write_text("keep me\n", encoding="utf-8")
        raced_output = raced_parent / "runtime.json"
        original_open = receipt.os.open

        def swap_parent(
            path: Path,
            flags: int,
            mode: int = 0o777,
            *,
            dir_fd: int | None = None,
        ) -> int:
            if dir_fd is not None and Path(path).name == raced_output.name:
                raced_parent.rename(original_parent)
                raced_parent.symlink_to(outside, target_is_directory=True)
            return original_open(path, flags, mode, dir_fd=dir_fd) if dir_fd is not None else original_open(path, flags, mode)

        with patch.object(receipt.os, "open", side_effect=swap_parent):
            written = receipt.write_runtime_receipt(
                raced_output, {"status": "blocked"}
            )
        require(
            written == raced_output,
            "runtime receipt writer changed its reported output path",
        )
        require(
            not (outside / raced_output.name).exists(),
            "runtime receipt writer followed a swapped parent directory",
        )
        require(
            sentinel.read_text(encoding="utf-8") == "keep me\n",
            "runtime receipt parent-swap race modified the outside sentinel",
        )
        require(
            (original_parent / raced_output.name).is_file(),
            "runtime receipt writer did not create through the held parent descriptor",
        )


def test_fixture_git_environment() -> None:
    """Synthetic release repositories must ignore ambient Git/runtime state."""
    hostile_environment = {
        "GIT_DIR": "/private/wrong-git-dir",
        "GIT_NAMESPACE": "refs/namespaces/wrong-release",
        "GIT_REPLACE_REF_BASE": "refs/replace/",
        "PYTHONPATH": "/private/wrong-python-path",
        "LC_ALL": "C",
        "LANG": "C",
        "PATH": "/private/wrong-bin",
    }
    completed = subprocess.CompletedProcess(
        ["git"], returncode=0, stdout="fixture\n", stderr=""
    )
    with patch.dict(os.environ, hostile_environment, clear=False):
        with patch.object(subprocess, "run", return_value=completed) as runner:
            require(
                release.git(Path("/fixture"), "rev-parse", "HEAD") == "fixture",
                "fixture Git read failed",
            )

    kwargs = runner.call_args.kwargs
    environment = kwargs["env"]
    for key in (
        "GIT_DIR",
        "GIT_NAMESPACE",
        "GIT_REPLACE_REF_BASE",
        "PYTHONPATH",
    ):
        require(key not in environment, f"ambient {key} leaked into fixture Git")
    require(environment["GIT_CONFIG_NOSYSTEM"] == "1", "fixture Git system config was not disabled")
    require(environment["GIT_ASKPASS"] == "/bin/false", "fixture Git prompting was not disabled")
    require(environment["PATH"] == os.defpath, "fixture Git PATH was not pinned")
    require(environment["LC_ALL"] == "C.UTF-8", "fixture Git locale was not pinned")
    require(
        kwargs["timeout"] == singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
        "fixture Git timeout drifted",
    )


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


def test_replay_subprocess_environment() -> None:
    """Independent replay probes must use clean state and bounded commands."""
    hostile_environment = {
        "GIT_DIR": "/private/wrong-git-dir",
        "GIT_NAMESPACE": "refs/namespaces/wrong-replay",
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
        with patch.object(replay.subprocess, "run", return_value=completed) as runner:
            require(replay.git(Path("/fixture"), "rev-parse", "HEAD") == "fixture", "replay Git read failed")
            require(
                replay.sandbox_mode(Path("/fixture")) == "user-manager",
                "replay systemd probe failed",
            )
            replay.run(["fixture"], cwd=Path("/fixture"))
            _command, comparator_environment = replay.comparator_command(
                source=Path("/fixture"),
                tools={
                    "comparator": Path("/tmp/comparator"),
                    "landrun": Path("/tmp/landrun"),
                    "lean4export": Path("/tmp/lean4export"),
                },
                mode="user-manager",
                config="verification/comparator.json",
            )

    require(len(runner.call_args_list) == 3, "replay probes were not exercised")
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
            require(key not in environment, f"ambient {key} leaked into replay")
        require(environment["PATH"] == os.defpath, "replay PATH was not pinned")
        require(environment["LC_ALL"] == "C.UTF-8", "replay LC_ALL was not pinned")
        require(environment["LANG"] == "C.UTF-8", "replay LANG was not pinned")
        require(environment["LANGUAGE"] == "C.UTF-8", "replay LANGUAGE was not pinned")
        require(environment["GIT_ASKPASS"] == "/bin/false", "replay Git prompting was not disabled")
        require(
            kwargs["timeout"] == replay.SUBPROCESS_TIMEOUT_SECONDS,
            "replay default timeout drifted",
        )
    require(
        comparator_environment["PATH"] == os.defpath,
        "comparator command retained ambient PATH",
    )
    require(
        comparator_environment["COMPARATOR_LANDRUN"] == "/tmp/landrun",
        "comparator command lost its pinned landrun path",
    )
    require(
        replay.ENVIRONMENT_CONTRACT
        == "clean_committed_snapshot_subprocess_environment_v1",
        "replay environment contract drifted",
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
    test_replay_file_boundary()
    test_replay_output_boundary()
    test_runtime_input_boundary()
    test_release_file_boundary()
    test_fixture_git_environment()
    test_receipt_subprocess_environment()
    test_replay_subprocess_environment()
    test_replay_plan()
    test_release_manifest()
    print(
        "external-verification release contract: replay plan, immutable manifest, "
        "runtime receipt, floating-ref and mismatch adversaries passed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
