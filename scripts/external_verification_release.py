#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build or validate the immutable external-verification release manifest.

The manifest is intentionally a release asset rather than a tracked file: a
tracked file cannot contain the commit id and digest of the commit that first
contains that file.  The builder therefore runs only from an exact committed
checkout whose release tag already resolves to that commit.  It binds the
review packet, eight papers, Comparator inputs, and a successful runtime
receipt to one commit and tree without using a floating branch name.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import subprocess
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
CONTRACT_PATH = Path("verification/external-verification-release-contract.json")
SCHEMA = "erdos-external-verification-release-manifest/1"
RUNTIME_SCHEMA = "erdos-external-verification-runtime-receipt/1"
FULL_SHA_RE = re.compile(r"[0-9a-f]{40}")
TAG_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]*")
SYNTHETIC_MERGE_MESSAGE_RE = re.compile(
    r"Merge [0-9a-f]{40} into [0-9a-f]{40}(?:\n|$)"
)


class ReleaseIdentityError(RuntimeError):
    """Raised when a candidate is not an immutable, reproducible release."""


def _is_allowed_platform_alias(path: Path) -> bool:
    """Permit the host's canonical temporary-directory aliases only."""
    try:
        aliases = {
            Path("/var"): Path("/private/var"),
            Path("/tmp"): Path("/private/tmp"),
        }
        return path in aliases and path.resolve(strict=True) == aliases[path]
    except OSError:
        return False


def safe_release_file(path: Path, *, root: Path | None = None) -> Path:
    """Return a regular file without following a symlinked path component.

    Repository inputs must remain inside ``root``.  The separately produced
    runtime receipt has no such root, but still cannot be supplied through a
    symlink.  macOS's ``/var`` and ``/tmp`` aliases are the only permitted
    platform indirections for that external asset.
    """
    root_path = Path(os.path.abspath(root)) if root is not None else None
    candidate = Path(os.path.abspath(path))
    current = candidate
    while True:
        if current.is_symlink():
            if not _is_allowed_platform_alias(current):
                raise ReleaseIdentityError(f"symlinked release input: {path}")
            current = current.resolve(strict=True)
        if root_path is not None and current == root_path:
            break
        if current.parent == current:
            if root_path is None:
                break
            raise ReleaseIdentityError(f"release input escaped checkout: {path}")
        current = current.parent
    if not candidate.is_file():
        raise ReleaseIdentityError(f"required release input is not a regular file: {path}")
    return candidate


def sha256_bytes(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def _read_safe_bytes(path: Path, *, root: Path | None = None) -> bytes:
    """Read a release input through a no-follow, regular-file descriptor."""
    candidate = safe_release_file(path, root=root)
    flags = os.O_RDONLY
    flags |= getattr(os, "O_CLOEXEC", 0)
    flags |= getattr(os, "O_NONBLOCK", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(candidate, flags)
    except OSError as exc:
        raise ReleaseIdentityError(f"could not open release input safely: {candidate}") from exc
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise ReleaseIdentityError(f"release input is not a regular file: {candidate}")
        with os.fdopen(descriptor, "rb") as stream:
            descriptor = -1
            return stream.read()
    finally:
        if descriptor >= 0:
            os.close(descriptor)


def sha256_file(path: Path, *, root: Path | None = None) -> str:
    return sha256_bytes(_read_safe_bytes(path, root=root))


def load_json(path: Path, *, root: Path | None = None) -> dict[str, Any]:
    candidate = safe_release_file(path, root=root)
    try:
        value = json.loads(_read_safe_bytes(candidate, root=root).decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ReleaseIdentityError(f"could not read JSON {candidate}: {exc}") from exc
    if not isinstance(value, dict):
        raise ReleaseIdentityError(f"JSON root must be an object: {candidate}")
    return value


def git(root: Path, *args: str) -> str:
    completed = subprocess.run(
        ["git", *args],
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        raise ReleaseIdentityError(
            completed.stderr.strip() or f"git {' '.join(args)} failed"
        )
    return completed.stdout.strip()


def full_sha(value: Any, field: str) -> str:
    if not isinstance(value, str) or FULL_SHA_RE.fullmatch(value) is None:
        raise ReleaseIdentityError(f"{field} must be a full lowercase Git id")
    return value


def contract(root: Path) -> dict[str, Any]:
    value = load_json(root / CONTRACT_PATH, root=root)
    if value.get("schema") != "erdos-external-verification-release-contract/1":
        raise ReleaseIdentityError("unsupported external-verification release contract")
    pins = value.get("toolchain")
    if not isinstance(pins, dict) or set(pins) != {
        "comparator",
        "lean4export",
        "landrun",
    }:
        raise ReleaseIdentityError("release contract has a malformed toolchain pin set")
    for name, revision in pins.items():
        full_sha(revision, f"toolchain.{name}")
    paths = value.get("tracked_artifacts")
    if not isinstance(paths, list) or not paths or len(paths) != len(set(paths)):
        raise ReleaseIdentityError("tracked_artifacts must be a nonempty unique list")
    for path in paths:
        if (
            not isinstance(path, str)
            or not path
            or Path(path).is_absolute()
            or ".." in Path(path).parts
        ):
            raise ReleaseIdentityError(f"unsafe tracked artifact path: {path!r}")
    return value


def exact_source_identity(
    root: Path, source_commit: str, source_tree: str, release_tag: str
) -> None:
    source_commit = full_sha(source_commit, "source_commit")
    source_tree = full_sha(source_tree, "source_tree")
    if TAG_RE.fullmatch(release_tag) is None or release_tag in {"HEAD", "main", "master"}:
        raise ReleaseIdentityError("release_tag must be a concrete non-floating tag")
    head = git(root, "rev-parse", "HEAD^{commit}")
    tree = git(root, "rev-parse", "HEAD^{tree}")
    if head != source_commit:
        raise ReleaseIdentityError(f"checkout HEAD {head} != source_commit {source_commit}")
    if tree != source_tree:
        raise ReleaseIdentityError(f"checkout tree {tree} != source_tree {source_tree}")
    message = git(root, "show", "-s", "--format=%B", source_commit)
    if SYNTHETIC_MERGE_MESSAGE_RE.match(message):
        raise ReleaseIdentityError("GitHub pull-request synthetic merge commit is forbidden")
    resolved_tag = git(root, "rev-parse", f"refs/tags/{release_tag}^{{commit}}")
    if resolved_tag != source_commit:
        raise ReleaseIdentityError(
            f"release tag {release_tag} resolves to {resolved_tag}, not {source_commit}"
        )


def expected_config(root: Path, relative_path: str) -> dict[str, Any]:
    value = load_json(root / relative_path, root=root)
    names = value.get("theorem_names")
    if not isinstance(names, list) or not names or not all(
        isinstance(name, str) and name for name in names
    ):
        raise ReleaseIdentityError(f"malformed theorem set in {relative_path}")
    return value


def validate_runtime_receipt(
    receipt: dict[str, Any],
    *,
    root: Path,
    source_commit: str,
    source_tree: str,
    release_contract: dict[str, Any],
) -> None:
    if receipt.get("schema") != RUNTIME_SCHEMA:
        raise ReleaseIdentityError("unsupported runtime receipt schema")
    if receipt.get("result") != "pass" or receipt.get("phase") != "final":
        raise ReleaseIdentityError("runtime receipt is not a final pass")
    if receipt.get("repository_commit") != source_commit:
        raise ReleaseIdentityError("runtime receipt commit does not match release commit")
    if receipt.get("repository_tree") != source_tree:
        raise ReleaseIdentityError("runtime receipt tree does not match release tree")
    if receipt.get("expected_repository_commit") != source_commit:
        raise ReleaseIdentityError("runtime receipt lacks the explicit release commit expectation")
    if receipt.get("repository_commit_matches_expected") is not True:
        raise ReleaseIdentityError("runtime receipt did not match its expected commit")

    comparator = receipt.get("comparator_toolchain")
    pins = release_contract["toolchain"]
    if not isinstance(comparator, dict):
        raise ReleaseIdentityError("runtime receipt lacks Comparator toolchain evidence")
    if comparator.get("expected_revisions") != pins:
        raise ReleaseIdentityError("runtime receipt expected revisions differ from contract")
    if comparator.get("observed_revisions") != pins or comparator.get("revisions_match") is not True:
        raise ReleaseIdentityError("runtime receipt did not observe every pinned revision")
    digests = comparator.get("binary_digests")
    if not isinstance(digests, dict) or set(digests) != set(pins):
        raise ReleaseIdentityError("runtime receipt binary digest set is incomplete")
    if not all(
        isinstance(value, str) and re.fullmatch(r"sha256:[0-9a-f]{64}", value)
        for value in digests.values()
    ):
        raise ReleaseIdentityError("runtime receipt contains a malformed binary digest")

    statement = receipt.get("statement_contract")
    config = expected_config(root, "verification/comparator.json")
    if not isinstance(statement, dict):
        raise ReleaseIdentityError("runtime receipt lacks statement-contract evidence")
    if statement.get("theorem_names") != config["theorem_names"]:
        raise ReleaseIdentityError("runtime receipt theorem set differs from comparator.json")
    if statement.get("permitted_axioms") != config.get("permitted_axioms"):
        raise ReleaseIdentityError("runtime receipt axiom budget differs from comparator.json")
    if statement.get("config_digest") != sha256_file(
        root / "verification/comparator.json", root=root
    ):
        raise ReleaseIdentityError("runtime receipt config digest is stale")

    checks = receipt.get("checks")
    expected_diagnostic = release_contract["replay"]["expected_negative_diagnostic"]
    if not isinstance(checks, dict):
        raise ReleaseIdentityError("runtime receipt lacks check results")
    if checks.get("positive_comparator_exit") != 0:
        raise ReleaseIdentityError("runtime positive Comparator check did not pass")
    if checks.get("negative_fixture_rejected") is not True:
        raise ReleaseIdentityError("runtime negative fixture was not rejected")
    if checks.get("negative_expected_diagnostic") != expected_diagnostic:
        raise ReleaseIdentityError("runtime negative diagnostic differs from contract")
    if receipt.get("whole_programme_disclosure", {}).get("all_statuses_open") is not True:
        raise ReleaseIdentityError("runtime receipt lost the all-eight-open disclosure")


def artifact_rows(
    root: Path, release_contract: dict[str, Any], source_commit: str
) -> list[dict[str, str]]:
    repository = release_contract["repository"]
    rows = []
    for relative in release_contract["tracked_artifacts"]:
        path = root / relative
        rows.append(
            {
                "path": relative,
                "sha256": sha256_file(path, root=root),
                "immutable_url": f"{repository}/blob/{source_commit}/{relative}",
            }
        )
    return rows


def build_manifest(
    *,
    root: Path,
    source_commit: str,
    source_tree: str,
    release_tag: str,
    runtime_receipt_path: Path,
) -> dict[str, Any]:
    release_contract = contract(root)
    exact_source_identity(root, source_commit, source_tree, release_tag)
    receipt = load_json(runtime_receipt_path)
    validate_runtime_receipt(
        receipt,
        root=root,
        source_commit=source_commit,
        source_tree=source_tree,
        release_contract=release_contract,
    )
    assets = release_contract["release_assets"]
    runtime_name = assets["runtime_receipt_pattern"].format(
        source_commit=source_commit
    )
    manifest_name = assets["manifest_pattern"].format(source_commit=source_commit)
    repository = release_contract["repository"]
    return {
        "schema": SCHEMA,
        "source": {
            "repository": repository,
            "commit": source_commit,
            "tree": source_tree,
            "commit_url": f"{repository}/commit/{source_commit}",
            "release_tag": release_tag,
            "release_url": f"{repository}/releases/tag/{release_tag}",
        },
        "contract": {
            "path": str(CONTRACT_PATH),
            "sha256": sha256_file(root / CONTRACT_PATH, root=root),
            "immutable_url": f"{repository}/blob/{source_commit}/{CONTRACT_PATH}",
        },
        "toolchain": release_contract["toolchain"],
        "tracked_artifacts": artifact_rows(root, release_contract, source_commit),
        "runtime_receipt": {
            "asset_name": runtime_name,
            "sha256": sha256_file(runtime_receipt_path),
            "result": "pass",
            "theorem_count": len(receipt["statement_contract"]["theorem_names"]),
        },
        "release_assets": {
            "required": [runtime_name, manifest_name],
            "retention": assets["retention"],
        },
        "independent_replay": {
            "config": release_contract["replay"]["positive_config"],
            "theorem": release_contract["replay"]["theorem"],
            "command": (
                "python3 scripts/replay_external_verification.py run "
                f"--source-commit {source_commit} --source-tree {source_tree} "
                "--output external-verification-replay-receipt.json"
            ),
            "posture": "reviewer_executed_outside_github_actions",
        },
    }


def validate_manifest(
    manifest: dict[str, Any],
    *,
    root: Path,
    runtime_receipt_path: Path,
) -> None:
    if manifest.get("schema") != SCHEMA:
        raise ReleaseIdentityError("unsupported release manifest schema")
    source = manifest.get("source")
    if not isinstance(source, dict):
        raise ReleaseIdentityError("release manifest lacks source identity")
    source_commit = full_sha(source.get("commit"), "manifest source commit")
    source_tree = full_sha(source.get("tree"), "manifest source tree")
    release_tag = source.get("release_tag")
    if not isinstance(release_tag, str):
        raise ReleaseIdentityError("release manifest lacks a release tag")
    release_contract = contract(root)
    exact_source_identity(root, source_commit, source_tree, release_tag)
    if source.get("repository") != release_contract["repository"]:
        raise ReleaseIdentityError("manifest repository differs from contract")
    if source.get("commit_url") != f"{source['repository']}/commit/{source_commit}":
        raise ReleaseIdentityError("manifest commit URL is not commit-pinned")
    if f"/blob/{source_commit}/" not in manifest.get("contract", {}).get(
        "immutable_url", ""
    ):
        raise ReleaseIdentityError("manifest contract URL is not commit-pinned")
    if manifest.get("contract", {}).get("sha256") != sha256_file(
        root / CONTRACT_PATH, root=root
    ):
        raise ReleaseIdentityError("release contract digest differs from checkout")
    if manifest.get("toolchain") != release_contract["toolchain"]:
        raise ReleaseIdentityError("manifest toolchain differs from release contract")

    expected_rows = artifact_rows(root, release_contract, source_commit)
    if manifest.get("tracked_artifacts") != expected_rows:
        raise ReleaseIdentityError("manifest tracked-artifact identities are stale")
    receipt = load_json(runtime_receipt_path)
    validate_runtime_receipt(
        receipt,
        root=root,
        source_commit=source_commit,
        source_tree=source_tree,
        release_contract=release_contract,
    )
    if manifest.get("runtime_receipt", {}).get("sha256") != sha256_file(runtime_receipt_path):
        raise ReleaseIdentityError("manifest runtime-receipt digest is stale")
    expected_names = [
        release_contract["release_assets"]["runtime_receipt_pattern"].format(
            source_commit=source_commit
        ),
        release_contract["release_assets"]["manifest_pattern"].format(
            source_commit=source_commit
        ),
    ]
    if manifest.get("release_assets", {}).get("required") != expected_names:
        raise ReleaseIdentityError("manifest release-asset names are not canonical")
    encoded = json.dumps(manifest, sort_keys=True)
    for floating in release_contract["identity"]["forbidden_floating_refs"]:
        if f"/blob/{floating}/" in encoded:
            raise ReleaseIdentityError(f"manifest contains floating source URL: {floating}")


def write_json(path: Path, value: dict[str, Any], *, overwrite: bool) -> None:
    candidate = Path(os.path.abspath(path))
    current = candidate
    while True:
        if current.is_symlink():
            if _is_allowed_platform_alias(current):
                current = current.resolve(strict=True)
                continue
            raise ReleaseIdentityError(
                f"output path contains a symlink: {candidate}"
            )
        if current.parent == current:
            break
        current = current.parent
    try:
        existing_mode = os.lstat(candidate).st_mode
    except FileNotFoundError:
        existing_mode = None
    if existing_mode is not None and not stat.S_ISREG(existing_mode):
        raise ReleaseIdentityError(
            f"output path is not a regular file: {candidate}"
        )
    if existing_mode is not None and not overwrite:
        raise ReleaseIdentityError(f"output exists; pass --overwrite: {path}")
    candidate.parent.mkdir(parents=True, exist_ok=True)
    flags = os.O_WRONLY | os.O_CREAT
    flags |= getattr(os, "O_CLOEXEC", 0)
    flags |= getattr(os, "O_NONBLOCK", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0)
    flags |= os.O_TRUNC if overwrite else os.O_EXCL
    descriptor = os.open(candidate, flags, 0o644)
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise ReleaseIdentityError(
                f"output path is not a regular file: {candidate}"
            )
        with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
            descriptor = -1
            stream.write(json.dumps(value, indent=2) + "\n")
    finally:
        if descriptor >= 0:
            os.close(descriptor)


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser()
    subparsers = result.add_subparsers(dest="command", required=True)
    for name in ("build", "validate"):
        sub = subparsers.add_parser(name)
        sub.add_argument("--root", type=Path, default=ROOT)
        sub.add_argument("--receipt", type=Path, required=True)
        if name == "build":
            sub.add_argument("--source-commit", required=True)
            sub.add_argument("--source-tree", required=True)
            sub.add_argument("--release-tag", required=True)
            sub.add_argument("--output", type=Path, required=True)
            sub.add_argument("--overwrite", action="store_true")
        else:
            sub.add_argument("--manifest", type=Path, required=True)
    return result


def main() -> int:
    args = parser().parse_args()
    try:
        root = args.root.resolve()
        if args.command == "build":
            manifest = build_manifest(
                root=root,
                source_commit=args.source_commit,
                source_tree=args.source_tree,
                release_tag=args.release_tag,
                runtime_receipt_path=args.receipt.resolve(),
            )
            write_json(args.output, manifest, overwrite=args.overwrite)
            print(args.output)
        else:
            manifest = load_json(args.manifest)
            validate_manifest(
                manifest,
                root=root,
                runtime_receipt_path=args.receipt.resolve(),
            )
            print(
                "external-verification release manifest valid: "
                f"{manifest['source']['commit']}"
            )
    except ReleaseIdentityError as exc:
        print(f"external-verification release error: {exc}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
