#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check the public-candidate boundary for acquired third-party source files.

The disposition ledger is the authority for PDFs, scans, and source archives
kept while researching.  Retrieval routes, DOI/arXiv records, and digests are
not redistribution grants.  This checker therefore permits an absent
``working_tree_only`` artifact in a clean clone, but never permits an
unregistered or candidate-included binary, and verifies any copy that is
present locally without printing its contents.
"""

from __future__ import annotations

import hashlib
import json
import os
import stat
import subprocess
import sys
from pathlib import Path, PurePosixPath
from typing import Any

import validation_singleflight as singleflight


ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "docs" / "primary-sources" / "redistribution-dispositions.json"
NOTICE = ROOT / "docs" / "THIRD_PARTY_NOTICES.md"
SOURCE_ROOT = ROOT / "docs" / "primary-sources"
SCHEMA = "plectis.third_party_source_redistribution_dispositions.v1"
DISPOSITIONS = {
    "public_redistribution_verified",
    "link_and_digest_only",
    "operator_permission_required",
    "unresolved_release_blocker",
}
ARTIFACT_SUFFIXES = (".pdf", ".scan", ".tar", ".tar.gz", ".tgz", ".zip", ".7z")
PRIVATE_PATH_MARKERS = (
    ("Unix home path", b"/Users/"),
    ("Linux home path", b"/home/"),
    ("root home path", b"/root/"),
    ("private temporary path", b"/private/var/"),
    ("file URI", b"file://"),
    ("Codex home path", b"~/.codex/"),
    ("agents home path", b"~/.agents/"),
    ("Windows user profile", b"%USERPROFILE%\\"),
    ("Windows user path", b"C:\\Users\\"),
    ("UNC user path", b"\\\\Users\\"),
)


def require(condition: bool, message: str, errors: list[str]) -> None:
    if not condition:
        errors.append(message)


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


def _canonical_input_path(path: Path) -> Path:
    """Resolve only the explicitly permitted macOS temporary aliases."""
    candidate = Path(os.path.abspath(path))
    if len(candidate.parts) >= 2:
        alias = Path(os.sep, candidate.parts[1])
        if _is_allowed_platform_alias(alias):
            return alias.resolve(strict=True).joinpath(*candidate.parts[2:])
    return candidate


def artifact_path(value: Any, errors: list[str]) -> Path | None:
    if not isinstance(value, str) or not value.startswith("docs/primary-sources/"):
        errors.append(f"artifact path must stay under docs/primary-sources: {value!r}")
        return None
    pure = PurePosixPath(value)
    if pure.is_absolute() or pure.as_posix() != value or ".." in pure.parts:
        errors.append(f"artifact path must be a normalized relative path: {value!r}")
        return None
    if not value.lower().endswith(ARTIFACT_SUFFIXES):
        errors.append(f"artifact path has an unsupported source-file suffix: {value!r}")
        return None
    return ROOT.joinpath(*pure.parts)


def read_regular_bytes(path: Path, *, root: Path | None = ROOT) -> bytes:
    """Read a disposition input through a no-follow regular-file descriptor."""
    candidate = Path(os.path.abspath(path))
    root_path = Path(os.path.abspath(root)) if root is not None else None
    current = candidate
    while True:
        if current.is_symlink():
            raise OSError(f"symlinked disposition input: {candidate}")
        if root_path is not None and current == root_path:
            break
        if current.parent == current:
            if root_path is not None:
                raise OSError(f"disposition input escaped checkout: {candidate}")
            break
        current = current.parent
    if not candidate.is_file():
        raise OSError(f"disposition input is not a regular file: {candidate}")
    candidate = _canonical_input_path(candidate)
    directory_flags = os.O_RDONLY
    directory_flags |= getattr(os, "O_CLOEXEC", 0)
    directory_flags |= getattr(os, "O_DIRECTORY", 0)
    directory_flags |= getattr(os, "O_NOFOLLOW", 0)
    directory = os.open(os.sep, directory_flags)
    descriptor = -1
    try:
        for component in candidate.parts[1:-1]:
            child = os.open(component, directory_flags, dir_fd=directory)
            try:
                if not stat.S_ISDIR(os.fstat(child).st_mode):
                    raise OSError(
                        f"disposition input parent is not a directory: {candidate.parent}"
                    )
            except BaseException:
                os.close(child)
                raise
            os.close(directory)
            directory = child
        flags = os.O_RDONLY
        flags |= getattr(os, "O_CLOEXEC", 0)
        flags |= getattr(os, "O_NONBLOCK", 0)
        flags |= getattr(os, "O_NOFOLLOW", 0)
        descriptor = os.open(candidate.name, flags, dir_fd=directory)
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise OSError(f"disposition input is not a regular file: {candidate}")
        with os.fdopen(descriptor, "rb") as stream:
            descriptor = -1
            return stream.read()
    finally:
        os.close(directory)
        if descriptor >= 0:
            os.close(descriptor)


def safe_reference_file(reference: str, *, root: Path = ROOT) -> bool:
    """Accept only normalized regular files beneath the asserted checkout."""
    path = PurePosixPath(reference)
    if (
        path.is_absolute()
        or path.as_posix() != reference
        or not reference.startswith("docs/")
        or ".." in path.parts
    ):
        return False
    root = Path(os.path.abspath(root))
    candidate = Path(os.path.abspath(root.joinpath(*path.parts)))
    if candidate != root and root not in candidate.parents:
        return False
    current = candidate
    while True:
        if current.is_symlink():
            return False
        if current == root:
            break
        if current.parent == current:
            return False
        current = current.parent
    return candidate.is_file()


def tracked_paths() -> set[str]:
    result = subprocess.run(
        ["git", "ls-files", "--", "docs/primary-sources"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
        env=singleflight.command_environment(),
        timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
    )
    return {line for line in result.stdout.splitlines() if line}


def present_artifact_paths() -> set[str]:
    if not SOURCE_ROOT.is_dir():
        return set()
    return {
        path.relative_to(ROOT).as_posix()
        for path in SOURCE_ROOT.rglob("*")
        if path.is_file() and path.name != LEDGER.name and path.name.lower().endswith(ARTIFACT_SUFFIXES)
    }


def metadata_private_path_errors(metadata: dict[str, bytes]) -> list[str]:
    errors: list[str] = []
    for name, payload in metadata.items():
        for label, marker in PRIVATE_PATH_MARKERS:
            if marker in payload:
                errors.append(f"primary-source metadata contains a {label} marker: {name}")
    return errors


def primary_source_metadata_errors() -> list[str]:
    errors: list[str] = []
    metadata_paths = {LEDGER}
    if SOURCE_ROOT.is_dir():
        metadata_paths.update(SOURCE_ROOT.rglob("*.md"))
        metadata_paths.update(SOURCE_ROOT.rglob("*.json"))
    metadata: dict[str, bytes] = {}
    for path in sorted(metadata_paths):
        name = path.relative_to(ROOT).as_posix()
        if path.is_symlink():
            errors.append(f"primary-source metadata must not be a symlink: {name}")
        elif not path.is_file():
            errors.append(f"primary-source metadata is missing: {name}")
        else:
            try:
                metadata[name] = read_regular_bytes(path)
            except OSError as exc:
                errors.append(f"primary-source metadata could not be read safely: {name}: {exc}")
    errors.extend(metadata_private_path_errors(metadata))
    return errors


def notice_errors(
    data: dict[str, Any],
    notice_text: str,
    requirements_text: str,
    lake_manifest_text: str,
) -> list[str]:
    """Keep the human-readable notice synchronized with release authorities."""
    errors: list[str] = []
    require(
        "Third-party source-artifact notices" in notice_text,
        "third-party notice is missing its release heading",
        errors,
    )
    require(
        "not a release allowlist" in notice_text,
        "third-party notice must distinguish notices from the release allowlist",
        errors,
    )
    require(
        "primary-sources/redistribution-dispositions.json" in notice_text,
        "third-party notice must name the canonical disposition ledger",
        errors,
    )
    require(
        "retrieval, citation, attribution" in notice_text.lower()
        and "permission" in notice_text.lower(),
        "third-party notice must distinguish retrieval evidence from permission",
        errors,
    )

    artifacts = data.get("artifacts")
    unverified_summary = (
        "Every current record is `working_tree_only`, `link_and_digest_only`, and\n"
        "`permission_evidence_status: not_verified`."
    )
    require(
        unverified_summary in notice_text,
        "third-party notice is missing its current unverified disposition summary",
        errors,
    )
    if isinstance(artifacts, list):
        require(
            all(
                isinstance(record, dict)
                and record.get("inventory_state") == "working_tree_only"
                and record.get("disposition") == "link_and_digest_only"
                and record.get("permission_evidence_status") == "not_verified"
                and record.get("public_candidate_inclusion") is False
                for record in artifacts
            ),
            "third-party notice's all-unverified summary no longer matches the disposition ledger",
            errors,
        )
        for record in artifacts:
            if not isinstance(record, dict):
                continue
            path = record.get("path")
            if not isinstance(path, str):
                continue
            require(
                path in notice_text,
                f"third-party notice is missing artifact path: {path}",
                errors,
            )
            digest = record.get("sha256")
            if isinstance(digest, str):
                require(
                    digest in notice_text,
                    f"third-party notice is missing digest for {path}",
                    errors,
                )
            routes = record.get("official_retrieval_routes", [])
            if isinstance(routes, list):
                for route in routes:
                    if isinstance(route, str):
                        require(
                            route in notice_text,
                            f"third-party notice is missing official route for {path}",
                            errors,
                        )
            for boundary in ("source_record", "support_boundary_ref"):
                reference = record.get(boundary)
                if isinstance(reference, str):
                    require(
                        reference in notice_text,
                        f"third-party notice is missing {boundary} for {path}",
                        errors,
                    )

    requirement_lines = [
        line.strip()
        for line in requirements_text.splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]
    require(
        "requirements-release.txt" in notice_text
        and f"{len(requirement_lines)} exact `name==version` records" in notice_text,
        "third-party notice must reconcile the release-validator manifest count",
        errors,
    )
    require(
        "pip --require-hashes" in notice_text
        and "do not grant permission" in notice_text,
        "third-party notice must bind hash-pinned retrieval to the permission boundary",
        errors,
    )
    try:
        lake_manifest = json.loads(lake_manifest_text)
    except json.JSONDecodeError:
        lake_manifest = {}
    packages = lake_manifest.get("packages") if isinstance(lake_manifest, dict) else None
    package_count = len(packages) if isinstance(packages, list) else 0
    require(
        "lake-manifest.json" in notice_text
        and f"{package_count} HTTPS Git dependency records" in notice_text,
        "third-party notice must reconcile the Lake manifest package count",
        errors,
    )
    return errors


def disposition_errors(
    data: dict[str, Any],
    *,
    tracked: set[str] | None = None,
    present: set[str] | None = None,
) -> list[str]:
    """Return every ledger, digest, and candidate-boundary failure."""
    errors: list[str] = []
    require(data.get("schema") == SCHEMA, f"ledger must use schema {SCHEMA}", errors)
    policy = data.get("policy")
    require(isinstance(policy, dict), "ledger policy must be an object", errors)
    if isinstance(policy, dict):
        require(
            set(policy.get("allowed_dispositions", [])) == DISPOSITIONS,
            "ledger allowed_dispositions must match the canonical disposition set",
            errors,
        )
        require(
            policy.get("public_candidate_rule") == "Only public_redistribution_verified artifacts may be tracked in the public candidate.",
            "ledger must state the verified-permission candidate rule",
            errors,
        )
        require(
            "not redistribution permission" in str(policy.get("permission_boundary", "")),
            "ledger must distinguish retrieval/citation from redistribution permission",
            errors,
        )
        require(
            "exclude the binary from the public candidate" in str(policy.get("link_and_digest_rule", "")),
            "ledger link-and-digest rule must exclude unverified binaries",
            errors,
        )
        require(
            "unresolved_release_blocker" in str(policy.get("unresolved_rule", "")),
            "ledger unresolved rule must retain a release blocker",
            errors,
        )
        require(
            "permission_evidence_scope equal to its exact artifact path" in str(policy.get("verified_permission_rule", "")),
            "ledger verified-permission rule must require artifact-exact evidence",
            errors,
        )
    inventory = data.get("inventory")
    artifacts = data.get("artifacts")
    require(isinstance(inventory, dict), "ledger inventory must be an object", errors)
    require(isinstance(artifacts, list), "ledger artifacts must be a list", errors)
    if not isinstance(inventory, dict) or not isinstance(artifacts, list):
        return errors
    require(
        inventory.get("root") == "docs/primary-sources/",
        "ledger inventory root must remain docs/primary-sources/",
        errors,
    )

    expected_counts = {
        "artifact_count": len(artifacts),
        "tracked_release_snapshot_count": 0,
        "working_tree_only_count": 0,
        "public_candidate_verified_count": 0,
        "link_and_digest_only_count": 0,
        "operator_permission_required_count": 0,
        "unresolved_release_blocker_count": 0,
    }
    seen: set[str] = set()
    listed_artifacts: set[str] = set()
    for index, record in enumerate(artifacts):
        if not isinstance(record, dict):
            errors.append(f"artifact record {index} must be an object")
            continue
        raw_path = record.get("path")
        local = artifact_path(raw_path, errors)
        if not isinstance(raw_path, str):
            continue
        listed_artifacts.add(raw_path)
        if raw_path in seen:
            errors.append(f"artifact path is duplicated: {raw_path}")
        seen.add(raw_path)
        digest = record.get("sha256")
        require(
            isinstance(digest, str) and len(digest) == 64 and all(c in "0123456789abcdef" for c in digest),
            f"{raw_path} must carry a lowercase SHA-256 digest",
            errors,
        )
        disposition = record.get("disposition")
        require(disposition in DISPOSITIONS, f"{raw_path} has an unknown disposition", errors)
        inventory_state = record.get("inventory_state")
        require(
            inventory_state in {"tracked_release_snapshot", "working_tree_only"},
            f"{raw_path} has an unknown inventory state",
            errors,
        )
        candidate = record.get("public_candidate_inclusion")
        require(isinstance(candidate, bool), f"{raw_path} candidate inclusion must be boolean", errors)
        permission_status = record.get("permission_evidence_status")
        routes = record.get("official_retrieval_routes")
        require(
            isinstance(routes, list) and routes and all(
                isinstance(route, str) and route.startswith("https://") for route in routes
            ),
            f"{raw_path} must retain at least one HTTPS official retrieval route",
            errors,
        )
        for field in ("source_record", "support_boundary_ref"):
            ref = record.get(field)
            require(isinstance(ref, str) and ref.startswith("docs/"), f"{raw_path} lacks {field}", errors)
            if isinstance(ref, str):
                require(
                    safe_reference_file(ref),
                    f"{raw_path} has unusable {field}",
                    errors,
                )
        consumers = record.get("consumer_refs")
        require(isinstance(consumers, list) and consumers, f"{raw_path} lacks consumer_refs", errors)
        if isinstance(consumers, list):
            for consumer in consumers:
                require(isinstance(consumer, str), f"{raw_path} has a non-string consumer ref", errors)
                if isinstance(consumer, str):
                    require(
                        safe_reference_file(consumer),
                        f"{raw_path} has unusable consumer ref",
                        errors,
                    )

        if inventory_state == "tracked_release_snapshot":
            expected_counts["tracked_release_snapshot_count"] += 1
        elif inventory_state == "working_tree_only":
            expected_counts["working_tree_only_count"] += 1
        if disposition == "public_redistribution_verified":
            expected_counts["public_candidate_verified_count"] += 1
        elif disposition == "link_and_digest_only":
            expected_counts["link_and_digest_only_count"] += 1
        elif disposition == "operator_permission_required":
            expected_counts["operator_permission_required_count"] += 1
        elif disposition == "unresolved_release_blocker":
            expected_counts["unresolved_release_blocker_count"] += 1

        require(
            candidate is True and disposition == "public_redistribution_verified"
            or candidate is False,
            f"{raw_path} is included without verified redistribution permission",
            errors,
        )
        if disposition == "public_redistribution_verified":
            require(permission_status == "verified", f"{raw_path} lacks verified permission status", errors)
            require(record.get("permission_evidence_scope") == raw_path, f"{raw_path} permission scope is not artifact-exact", errors)
            require(bool(record.get("permission_evidence_locator")), f"{raw_path} lacks permission evidence locator", errors)
        elif permission_status == "verified":
            errors.append(f"{raw_path} claims verified permission under a non-verified disposition")

        if local is not None:
            if local.is_symlink():
                errors.append(f"{raw_path} must not be a symlink")
            elif local.is_file():
                try:
                    observed = hashlib.sha256(read_regular_bytes(local)).hexdigest()
                except OSError as exc:
                    errors.append(f"{raw_path} could not be read safely: {exc}")
                else:
                    if isinstance(digest, str) and observed != digest:
                        errors.append(f"{raw_path} digest does not match the disposition ledger")
            elif inventory_state == "tracked_release_snapshot":
                errors.append(f"tracked artifact is missing: {raw_path}")

    if tracked is not None:
        tracked_artifacts = {path for path in tracked if path.lower().endswith(ARTIFACT_SUFFIXES)}
        for path in listed_artifacts:
            state = next((row.get("inventory_state") for row in artifacts if isinstance(row, dict) and row.get("path") == path), None)
            if path in tracked_artifacts and state != "tracked_release_snapshot":
                errors.append(f"working-tree-only artifact is tracked: {path}")
            if state == "tracked_release_snapshot" and path not in tracked_artifacts:
                errors.append(f"tracked-release artifact is not tracked: {path}")
        unlisted_tracked = sorted(tracked_artifacts - listed_artifacts)
        errors.extend(f"tracked source artifact is absent from the disposition ledger: {path}" for path in unlisted_tracked)
    if present is not None:
        errors.extend(f"present source artifact is absent from the disposition ledger: {path}" for path in sorted(present - listed_artifacts))

    errors.extend(primary_source_metadata_errors())

    for key, expected in expected_counts.items():
        if inventory.get(key) != expected:
            errors.append(f"inventory {key} is inconsistent with artifact records")
    verified = expected_counts["public_candidate_verified_count"]
    status = str(inventory.get("permission_evidence_status", ""))
    if verified == 0:
        require("none" in status or "not" in status, "inventory must say no bound record asserts permission", errors)
    return errors


def main() -> int:
    try:
        data = json.loads(read_regular_bytes(LEDGER).decode("utf-8"))
        errors = disposition_errors(data, tracked=tracked_paths(), present=present_artifact_paths())
        notice_text = read_regular_bytes(NOTICE).decode("utf-8")
        requirements_text = read_regular_bytes(ROOT / "requirements-release.txt").decode("utf-8")
        lake_manifest_text = read_regular_bytes(ROOT / "lake-manifest.json").decode("utf-8")
        errors.extend(
            notice_errors(data, notice_text, requirements_text, lake_manifest_text)
        )
    except (OSError, UnicodeDecodeError, json.JSONDecodeError, subprocess.CalledProcessError) as exc:
        print(f"check_primary_source_dispositions: FAIL: {exc}", file=sys.stderr)
        return 1
    if errors:
        print(f"check_primary_source_dispositions: {len(errors)} failure(s)", file=sys.stderr)
        for error in errors:
            print(f"  FAIL {error}", file=sys.stderr)
        return 1
    count = len(data["artifacts"])
    print(
        "check_primary_source_dispositions: "
        f"{count} artifacts dispositioned; verified-permission candidate count 0; "
        "working-tree-only binaries excluded"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
