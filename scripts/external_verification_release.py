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

import validation_singleflight as singleflight


ROOT = Path(__file__).resolve().parent.parent
CONTRACT_PATH = Path("verification/external-verification-release-contract.json")
SCHEMA = "erdos-external-verification-release-manifest/2"
RUNTIME_SCHEMA = "erdos-external-verification-runtime-receipt/2"
RUNTIME_LOG_BINDINGS = {
    "artifacts-positive.log": ("checks", "positive_log_digest"),
    "artifacts-negative.log": ("checks", "negative_log_digest"),
    "artifacts-portfolio-positive.log": (
        "comparator_replay_portfolio",
        "positive_log_digest",
    ),
    "artifacts-1049-positive.log": (
        "programme_local_checks",
        "erdos_1049_numerical_height",
        "positive_log_digest",
    ),
    "artifacts-1049-negative.log": (
        "programme_local_checks",
        "erdos_1049_numerical_height",
        "negative_log_digest",
    ),
}
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


def _canonical_input_path(path: Path) -> Path:
    """Resolve only the explicitly permitted macOS temporary aliases."""
    candidate = Path(os.path.abspath(path))
    if len(candidate.parts) >= 2:
        alias = Path(os.sep, candidate.parts[1])
        if _is_allowed_platform_alias(alias):
            return alias.resolve(strict=True).joinpath(*candidate.parts[2:])
    return candidate


def _open_input_descriptor(path: Path) -> int:
    """Open a release input relative to no-follow directory descriptors."""
    directory_flags = os.O_RDONLY
    directory_flags |= getattr(os, "O_CLOEXEC", 0)
    directory_flags |= getattr(os, "O_DIRECTORY", 0)
    directory_flags |= getattr(os, "O_NOFOLLOW", 0)
    directory = os.open(os.sep, directory_flags)
    try:
        for component in path.parts[1:-1]:
            child = os.open(component, directory_flags, dir_fd=directory)
            try:
                if not stat.S_ISDIR(os.fstat(child).st_mode):
                    raise OSError(f"release input parent is not a directory: {path.parent}")
            except BaseException:
                os.close(child)
                raise
            os.close(directory)
            directory = child
        flags = os.O_RDONLY
        flags |= getattr(os, "O_CLOEXEC", 0)
        flags |= getattr(os, "O_NONBLOCK", 0)
        flags |= getattr(os, "O_NOFOLLOW", 0)
        return os.open(path.name, flags, dir_fd=directory)
    finally:
        os.close(directory)


def _read_safe_bytes(path: Path, *, root: Path | None = None) -> bytes:
    """Read a release input through a no-follow, regular-file descriptor."""
    candidate = _canonical_input_path(safe_release_file(path, root=root))
    try:
        descriptor = _open_input_descriptor(candidate)
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
        env=singleflight.command_environment(),
        timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
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
    if value.get("schema") != "erdos-external-verification-release-contract/2":
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


def expected_proof_environment(root: Path) -> dict[str, str]:
    """Return the exact Lean and mathlib identities pinned by the checkout."""
    try:
        lean_toolchain = _read_safe_bytes(
            root / "lean-toolchain", root=root
        ).decode("utf-8").strip()
    except UnicodeDecodeError as exc:
        raise ReleaseIdentityError("lean-toolchain is not UTF-8") from exc
    manifest = load_json(root / "lake-manifest.json", root=root)
    packages = manifest.get("packages")
    if not isinstance(packages, list):
        raise ReleaseIdentityError("lake-manifest.json has no package list")
    mathlib_rows = [
        row
        for row in packages
        if isinstance(row, dict) and row.get("name") == "mathlib"
    ]
    if len(mathlib_rows) != 1:
        raise ReleaseIdentityError("lake-manifest.json must pin exactly one mathlib package")
    mathlib_revision = full_sha(
        mathlib_rows[0].get("rev"), "lake-manifest mathlib revision"
    )
    if not lean_toolchain:
        raise ReleaseIdentityError("lean-toolchain is empty")
    return {
        "lean_toolchain": lean_toolchain,
        "mathlib_revision": mathlib_revision,
    }


def is_success_exit(value: Any) -> bool:
    """Accept the integer exit status 0, never JSON booleans such as false."""
    return isinstance(value, int) and not isinstance(value, bool) and value == 0


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

    provenance = release_contract.get("runtime_receipt_provenance")
    ci = receipt.get("ci")
    if not isinstance(provenance, dict) or not isinstance(ci, dict):
        raise ReleaseIdentityError("runtime receipt lacks release provenance")
    if ci.get("repository") != provenance.get("repository"):
        raise ReleaseIdentityError("runtime receipt came from a different repository")
    if ci.get("workflow") != provenance.get("workflow"):
        raise ReleaseIdentityError("runtime receipt came from a different workflow")
    if ci.get("github_actions") is not True:
        raise ReleaseIdentityError("runtime receipt was not produced in GitHub Actions")
    if ci.get("provenance_matches_release_contract") is not True:
        raise ReleaseIdentityError("runtime receipt provenance was not contract-matched")
    if ci.get("attestation_posture") != provenance.get("attestation_posture"):
        raise ReleaseIdentityError("runtime receipt attestation posture is stale")
    if not all(
        isinstance(ci.get(field), str) and ci[field].isdigit()
        for field in ("run_id", "run_attempt")
    ):
        raise ReleaseIdentityError("runtime receipt lacks numeric Actions run identity")
    if ci.get("sandbox_mode") not in release_contract["replay"]["sandbox_modes"]:
        raise ReleaseIdentityError("runtime receipt used a non-release sandbox mode")

    if receipt.get("proof_environment") != expected_proof_environment(root):
        raise ReleaseIdentityError("runtime receipt proof environment differs from checkout")

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

    portfolio = receipt.get("comparator_replay_portfolio")
    portfolio_contract = release_contract.get("aggregate_replay_portfolio")
    if not isinstance(portfolio_contract, dict):
        raise ReleaseIdentityError("release contract lacks aggregate replay portfolio")
    portfolio_path = portfolio_contract.get("config")
    if not isinstance(portfolio_path, str):
        raise ReleaseIdentityError("release contract has no aggregate replay config")
    portfolio_config = expected_config(root, portfolio_path)
    if not isinstance(portfolio, dict):
        raise ReleaseIdentityError("runtime receipt lacks aggregate Comparator replay evidence")
    if portfolio.get("status") != "commit_bound_comparator_replay_pass":
        raise ReleaseIdentityError("aggregate Comparator replay is not a commit-bound pass")
    if portfolio.get("config") != portfolio_path:
        raise ReleaseIdentityError("aggregate Comparator replay config path is noncanonical")
    if portfolio.get("config_digest") != sha256_file(
        root / portfolio_path, root=root
    ):
        raise ReleaseIdentityError("aggregate Comparator replay config digest is stale")
    if portfolio.get("theorem_names") != portfolio_config["theorem_names"]:
        raise ReleaseIdentityError("aggregate Comparator replay theorem set is stale")
    if portfolio.get("challenge_module") != portfolio_contract.get("challenge_module"):
        raise ReleaseIdentityError("aggregate Comparator Challenge module is stale")
    if portfolio.get("solution_module") != portfolio_contract.get("solution_module"):
        raise ReleaseIdentityError("aggregate Comparator Solution module is stale")
    if portfolio.get("challenge_module") != portfolio_config.get("challenge_module"):
        raise ReleaseIdentityError("aggregate Comparator Challenge differs from config")
    if portfolio.get("solution_module") != portfolio_config.get("solution_module"):
        raise ReleaseIdentityError("aggregate Comparator Solution differs from config")
    if portfolio.get("theorem_count") != len(portfolio_config["theorem_names"]):
        raise ReleaseIdentityError("aggregate Comparator replay theorem count is stale")
    if portfolio.get("permitted_axioms") != portfolio_config.get("permitted_axioms"):
        raise ReleaseIdentityError("aggregate Comparator replay axiom budget is stale")
    if portfolio_config.get("enable_nanoda") is not False:
        raise ReleaseIdentityError("aggregate Comparator config enabled NanoDa")
    if portfolio.get("enable_nanoda") is not portfolio_config.get("enable_nanoda"):
        raise ReleaseIdentityError("aggregate Comparator replay enabled NanoDa")
    if not is_success_exit(portfolio.get("projection_check_exit")):
        raise ReleaseIdentityError("aggregate Comparator replay projection was stale")
    if not is_success_exit(portfolio.get("positive_comparator_exit")):
        raise ReleaseIdentityError("aggregate Comparator replay did not pass")
    if not isinstance(portfolio.get("positive_log_digest"), str) or re.fullmatch(
        r"sha256:[0-9a-f]{64}", portfolio["positive_log_digest"]
    ) is None:
        raise ReleaseIdentityError("aggregate Comparator replay lacks a log digest")

    checks = receipt.get("checks")
    expected_diagnostic = release_contract["replay"]["expected_negative_diagnostic"]
    if not isinstance(checks, dict):
        raise ReleaseIdentityError("runtime receipt lacks check results")
    if not is_success_exit(checks.get("projection_and_isolation_check_exit")):
        raise ReleaseIdentityError("runtime projection and isolation check did not pass")
    if not is_success_exit(checks.get("positive_comparator_exit")):
        raise ReleaseIdentityError("runtime positive Comparator check did not pass")
    negative_exit = checks.get("negative_mismatch_comparator_exit")
    if isinstance(negative_exit, bool) or not isinstance(negative_exit, int) or negative_exit == 0:
        raise ReleaseIdentityError("runtime negative Comparator fixture was not rejected by exit status")
    for key in ("positive_log_digest", "negative_log_digest"):
        if not isinstance(checks.get(key), str) or re.fullmatch(
            r"sha256:[0-9a-f]{64}", checks[key]
        ) is None:
            raise ReleaseIdentityError(f"runtime Comparator check lacks {key}")
    if checks.get("negative_fixture_rejected") is not True:
        raise ReleaseIdentityError("runtime negative fixture was not rejected")
    if checks.get("negative_expected_diagnostic") != expected_diagnostic:
        raise ReleaseIdentityError("runtime negative diagnostic differs from contract")

    local = receipt.get("programme_local_checks", {}).get(
        "erdos_1049_numerical_height"
    )
    if not isinstance(local, dict):
        raise ReleaseIdentityError("runtime receipt lacks the #1049 local Comparator check")
    local_contract = release_contract.get("programme_local_checks", {}).get(
        "erdos_1049_numerical_height"
    )
    if not isinstance(local_contract, dict):
        raise ReleaseIdentityError("release contract lacks the #1049 local Comparator check")
    local_config_path = local_contract.get("config")
    if not isinstance(local_config_path, str):
        raise ReleaseIdentityError("release contract has no #1049 Comparator config")
    if local.get("config") != local_config_path:
        raise ReleaseIdentityError("#1049 local Comparator config path is noncanonical")
    if local.get("config_digest") != sha256_file(root / local_config_path, root=root):
        raise ReleaseIdentityError("#1049 local Comparator config digest is stale")
    local_config = expected_config(root, local_config_path)
    for field in (
        "challenge_module",
        "solution_module",
        "theorem_names",
        "permitted_axioms",
        "enable_nanoda",
    ):
        if local_config.get(field) != local_contract.get(field):
            raise ReleaseIdentityError(f"#1049 local Comparator {field} differs from contract")
    if local_config.get("enable_nanoda") is not False:
        raise ReleaseIdentityError("#1049 local Comparator config enabled NanoDa")
    if not is_success_exit(local.get("positive_comparator_exit")):
        raise ReleaseIdentityError("#1049 local positive Comparator check did not pass")
    local_negative_exit = local.get("negative_mismatch_comparator_exit")
    if (
        isinstance(local_negative_exit, bool)
        or not isinstance(local_negative_exit, int)
        or local_negative_exit == 0
    ):
        raise ReleaseIdentityError("#1049 local negative Comparator fixture was not rejected by exit status")
    if local.get("negative_fixture_rejected") is not True:
        raise ReleaseIdentityError("#1049 local negative fixture was not rejected")
    if local.get("negative_expected_diagnostic") != local_contract.get(
        "expected_negative_diagnostic"
    ):
        raise ReleaseIdentityError("#1049 local negative diagnostic differs from contract")
    for key in ("positive_log_digest", "negative_log_digest"):
        if not isinstance(local.get(key), str) or re.fullmatch(
            r"sha256:[0-9a-f]{64}", local[key]
        ) is None:
            raise ReleaseIdentityError(f"#1049 local Comparator check lacks {key}")
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


def runtime_log_rows(
    receipt: dict[str, Any],
    runtime_log_dir: Path,
    release_contract: dict[str, Any],
) -> list[dict[str, str]]:
    """Hash the five uploaded replay logs and match them to the receipt."""
    expected_files = list(RUNTIME_LOG_BINDINGS)
    if release_contract.get("release_assets", {}).get("runtime_log_files") != expected_files:
        raise ReleaseIdentityError("release contract runtime-log roster is stale")
    rows: list[dict[str, str]] = []
    for filename, receipt_path in RUNTIME_LOG_BINDINGS.items():
        value: Any = receipt
        for key in receipt_path:
            if not isinstance(value, dict):
                value = None
                break
            value = value.get(key)
        actual = sha256_file(runtime_log_dir / filename)
        if value != actual:
            raise ReleaseIdentityError(f"runtime log digest differs from receipt: {filename}")
        rows.append({"path": filename, "sha256": actual})
    return rows


def build_manifest(
    *,
    root: Path,
    source_commit: str,
    source_tree: str,
    release_tag: str,
    runtime_receipt_path: Path,
    runtime_log_dir: Path,
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
    log_rows = runtime_log_rows(receipt, runtime_log_dir, release_contract)
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
        "runtime_logs": log_rows,
        "release_assets": {
            "required": [runtime_name, manifest_name, *assets["runtime_log_files"]],
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
    runtime_log_dir: Path,
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
    expected_log_rows = runtime_log_rows(receipt, runtime_log_dir, release_contract)
    if manifest.get("runtime_logs") != expected_log_rows:
        raise ReleaseIdentityError("manifest runtime-log identities are stale")
    if manifest.get("runtime_receipt", {}).get("sha256") != sha256_file(runtime_receipt_path):
        raise ReleaseIdentityError("manifest runtime-receipt digest is stale")
    expected_names = [
        release_contract["release_assets"]["runtime_receipt_pattern"].format(
            source_commit=source_commit
        ),
        release_contract["release_assets"]["manifest_pattern"].format(
            source_commit=source_commit
        ),
        *release_contract["release_assets"]["runtime_log_files"],
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
    candidate = _canonical_output_path(candidate)
    flags = os.O_WRONLY | os.O_CREAT
    flags |= getattr(os, "O_CLOEXEC", 0)
    flags |= getattr(os, "O_NONBLOCK", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0)
    flags |= os.O_TRUNC if overwrite else os.O_EXCL
    try:
        descriptor = _open_output_descriptor(candidate, flags)
    except OSError as exc:
        raise ReleaseIdentityError(
            f"output path could not be opened safely: {path}"
        ) from exc
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


def _canonical_output_path(path: Path) -> Path:
    """Resolve only the explicitly permitted macOS temporary aliases."""
    parts = path.parts
    if len(parts) >= 2:
        alias = Path(os.sep, parts[1])
        if _is_allowed_platform_alias(alias):
            target = alias.resolve(strict=True)
            return target.joinpath(*parts[2:])
    return path


def _open_output_descriptor(path: Path, flags: int) -> int:
    """Open an output relative to no-follow directory descriptors."""
    directory_flags = os.O_RDONLY
    directory_flags |= getattr(os, "O_CLOEXEC", 0)
    directory_flags |= getattr(os, "O_DIRECTORY", 0)
    directory_flags |= getattr(os, "O_NOFOLLOW", 0)
    directory = os.open(os.sep, directory_flags)
    try:
        for component in path.parts[1:-1]:
            child = os.open(component, directory_flags, dir_fd=directory)
            try:
                if not stat.S_ISDIR(os.fstat(child).st_mode):
                    raise OSError(f"output parent is not a directory: {path.parent}")
            except BaseException:
                os.close(child)
                raise
            os.close(directory)
            directory = child
        return os.open(path.name, flags, 0o644, dir_fd=directory)
    finally:
        os.close(directory)


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser()
    subparsers = result.add_subparsers(dest="command", required=True)
    for name in ("build", "validate"):
        sub = subparsers.add_parser(name)
        sub.add_argument("--root", type=Path, default=ROOT)
        sub.add_argument("--receipt", type=Path, required=True)
        sub.add_argument("--runtime-log-dir", type=Path, required=True)
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
                runtime_log_dir=args.runtime_log_dir.resolve(),
            )
            write_json(args.output, manifest, overwrite=args.overwrite)
            print(args.output)
        else:
            manifest = load_json(args.manifest)
            validate_manifest(
                manifest,
                root=root,
                runtime_receipt_path=args.receipt.resolve(),
                runtime_log_dir=args.runtime_log_dir.resolve(),
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
