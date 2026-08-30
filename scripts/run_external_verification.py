#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Write and enforce the commit-bound external-verification runtime receipt."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

import validation_singleflight as singleflight

ROOT = Path(__file__).resolve().parent.parent
EXPECTED_MISMATCH = (
    "Challenge and solution theorem statement do not match: "
    "'Erdos249257.ExternalVerification.finrank_totientKernelThroughLevelFamily_eq'"
)
EXPECTED_1049_MISMATCH = (
    "Challenge and solution theorem statement do not match: "
    "'Erdos249257.ExternalVerification1049.comparator_sevenHalves_numericalHeight'"
)
ENVIRONMENT_CONTRACT = "clean_committed_snapshot_subprocess_environment_v1"
SUBPROCESS_TIMEOUT_SECONDS = singleflight.DEFAULT_WORKER_TIMEOUT_SECONDS


class VerificationInputError(RuntimeError):
    """Raised when a receipt input crosses the intended file boundary."""


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


def safe_runtime_file(path: Path, *, root: Path | None = None) -> Path:
    """Return a regular receipt input without following path symlinks.

    Canonical repository inputs must stay below ``root``.  External tool,
    log, and receipt paths remain supported, but their path components still
    cannot be substituted through symlinks.
    """
    root_path = Path(os.path.abspath(root)) if root is not None else None
    candidate = Path(os.path.abspath(path))
    current = candidate
    while True:
        if current.is_symlink():
            if not _is_allowed_platform_alias(current):
                raise VerificationInputError(f"symlinked verification input: {path}")
            current = current.resolve(strict=True)
        if root_path is not None and current == root_path:
            break
        if current.parent == current:
            if root_path is None:
                break
            raise VerificationInputError(f"verification input escaped checkout: {path}")
        current = current.parent
    if not candidate.is_file():
        raise VerificationInputError(f"verification input is not a regular file: {path}")
    return candidate


def optional_runtime_text(path: Path | None) -> str:
    """Read an optional external log only when it is a safe regular file."""
    if path is None:
        return ""
    try:
        return safe_runtime_file(path).read_text(encoding="utf-8", errors="replace")
    except (OSError, VerificationInputError):
        return ""


def digest(path: Path | None) -> str | None:
    if path is None:
        return None
    try:
        path = safe_runtime_file(path)
    except (OSError, VerificationInputError):
        return None
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args: str) -> str:
    return run(["git", *args], cwd=ROOT, check=True).stdout.strip()


def run(
    args: list[str], *, cwd: Path, check: bool = False
) -> subprocess.CompletedProcess[str]:
    """Run receipt-producing children with bounded, canonical state."""
    return subprocess.run(
        args,
        cwd=cwd,
        capture_output=True,
        text=True,
        check=check,
        env=singleflight.command_environment(),
        timeout=SUBPROCESS_TIMEOUT_SECONDS,
    )


def _canonical_output_path(path: Path) -> Path:
    """Resolve only the explicitly permitted macOS temporary aliases."""
    candidate = Path(os.path.abspath(path))
    current = candidate
    while True:
        if current.is_symlink():
            if not _is_allowed_platform_alias(current):
                raise VerificationInputError(f"output path contains a symlink: {path}")
            current = current.resolve(strict=True)
        if current.parent == current:
            break
        current = current.parent
    try:
        existing_mode = os.lstat(candidate).st_mode
    except FileNotFoundError:
        existing_mode = None
    if existing_mode is not None and not stat.S_ISREG(existing_mode):
        raise VerificationInputError(f"output path is not a regular file: {path}")
    if len(candidate.parts) >= 2:
        alias = Path(os.sep, candidate.parts[1])
        if _is_allowed_platform_alias(alias):
            return alias.resolve(strict=True).joinpath(*candidate.parts[2:])
    return candidate


def _open_output_descriptor(path: Path) -> int:
    """Open a runtime receipt relative to no-follow directory descriptors."""
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
        flags = os.O_WRONLY | os.O_CREAT | os.O_TRUNC
        flags |= getattr(os, "O_CLOEXEC", 0)
        flags |= getattr(os, "O_NONBLOCK", 0)
        flags |= getattr(os, "O_NOFOLLOW", 0)
        return os.open(path.name, flags, 0o644, dir_fd=directory)
    finally:
        os.close(directory)


def write_runtime_receipt(path: Path, receipt: dict[str, Any]) -> Path:
    """Write a receipt without allowing an output parent to be substituted."""
    candidate = _canonical_output_path(path)
    candidate.parent.mkdir(parents=True, exist_ok=True)
    try:
        descriptor = _open_output_descriptor(candidate)
    except OSError as exc:
        raise VerificationInputError(
            f"output path could not be opened safely: {path}"
        ) from exc
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise VerificationInputError(f"output path is not a regular file: {path}")
        with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
            descriptor = -1
            stream.write(json.dumps(receipt, indent=2) + "\n")
    finally:
        if descriptor >= 0:
            os.close(descriptor)
    return candidate


def is_expected_negative_rejection(
    exit_code: int, log_text: str, expected: str = EXPECTED_MISMATCH
) -> bool:
    return exit_code != 0 and expected in log_text


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--phase", default="final")
    parser.add_argument("--expected-commit")
    parser.add_argument("--positive-exit", type=int, default=-999)
    parser.add_argument("--negative-exit", type=int, default=-999)
    parser.add_argument("--positive-log", type=Path)
    parser.add_argument("--negative-log", type=Path)
    parser.add_argument("--local-1049-positive-exit", type=int, default=-999)
    parser.add_argument("--local-1049-negative-exit", type=int, default=-999)
    parser.add_argument("--local-1049-positive-log", type=Path)
    parser.add_argument("--local-1049-negative-log", type=Path)
    parser.add_argument("--comparator-rev")
    parser.add_argument("--lean4export-rev")
    parser.add_argument("--landrun-rev")
    parser.add_argument("--comparator-bin", type=Path)
    parser.add_argument("--lean4export-bin", type=Path)
    parser.add_argument("--landrun-bin", type=Path)
    parser.add_argument("--comparator-lean-toolchain")
    parser.add_argument("--sandbox-mode")
    parser.add_argument(
        "--output", type=Path, default=ROOT / "artifacts/external-verification-receipt.json"
    )
    args = parser.parse_args()

    projection_check = run(
        ["python3", "scripts/build_external_verification.py", "--check"],
        cwd=ROOT,
    ).returncode
    claims = json.loads(
        safe_runtime_file(ROOT / "docs/claims.json", root=ROOT).read_text(
            encoding="utf-8"
        )
    )
    owner = claims["external_verification_packet"]
    packet = json.loads(
        safe_runtime_file(
            ROOT / "docs/external_verification_packet.json", root=ROOT
        ).read_text(encoding="utf-8")
    )
    manifest = json.loads(
        safe_runtime_file(ROOT / "lake-manifest.json", root=ROOT).read_text(
            encoding="utf-8"
        )
    )
    mathlib = next(package for package in manifest["packages"] if package["name"] == "mathlib")
    observed_revisions = {
        "comparator": args.comparator_rev,
        "lean4export": args.lean4export_rev,
        "landrun": args.landrun_rev,
    }
    binary_digests = {
        "comparator": digest(args.comparator_bin),
        "lean4export": digest(args.lean4export_bin),
        "landrun": digest(args.landrun_bin),
    }
    repository_commit = git("rev-parse", "HEAD")
    repository_tree = git("rev-parse", "HEAD^{tree}")
    expected_commit_matches = (
        args.expected_commit is None or repository_commit == args.expected_commit
    )
    pins_match = observed_revisions == owner["comparator"]["pins"]
    negative_text = optional_runtime_text(args.negative_log)
    negative_semantic_rejection = is_expected_negative_rejection(
        args.negative_exit, negative_text
    )
    local_1049_negative_text = optional_runtime_text(args.local_1049_negative_log)
    local_1049_negative_semantic_rejection = is_expected_negative_rejection(
        args.local_1049_negative_exit,
        local_1049_negative_text,
        EXPECTED_1049_MISMATCH,
    )
    all_statuses_open = all(
        row["status"] == "open" for row in packet["problem_index"]["problems"]
    )
    passed = (
        projection_check == 0
        and args.positive_exit == 0
        and negative_semantic_rejection
        and args.local_1049_positive_exit == 0
        and local_1049_negative_semantic_rejection
        and pins_match
        and all(binary_digests.values())
        and expected_commit_matches
        and args.sandbox_mode in {"user-manager", "system-manager-nonprivileged-unit", "local-fake-landrun-smoke"}
        and all_statuses_open
    )
    receipt = {
        "schema": "erdos-external-verification-runtime-receipt/1",
        "result": "pass" if passed else "fail",
        "phase": args.phase,
        "repository_commit": repository_commit,
        "repository_tree": repository_tree,
        "expected_repository_commit": args.expected_commit,
        "repository_commit_matches_expected": expected_commit_matches,
        "generated_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "ci": {
            "repository": os.environ.get("GITHUB_REPOSITORY"),
            "run_id": os.environ.get("GITHUB_RUN_ID"),
            "run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT"),
            "workflow": os.environ.get("GITHUB_WORKFLOW"),
            "sandbox_mode": args.sandbox_mode,
        },
        "proof_environment": {
            "lean_toolchain": safe_runtime_file(
                ROOT / "lean-toolchain", root=ROOT
            ).read_text().strip(),
            "mathlib_revision": mathlib["rev"],
        },
        "comparator_toolchain": {
            "expected_revisions": owner["comparator"]["pins"],
            "observed_revisions": observed_revisions,
            "revisions_match": pins_match,
            "comparator_lean_toolchain": args.comparator_lean_toolchain,
            "binary_digests": binary_digests,
        },
        "whole_programme_disclosure": {
            "scope": owner["scope"],
            "problem_index": packet["problem_index"]["projection"],
            "problem_index_digest": packet["problem_index"]["projection_digest"],
            "problem_count": packet["problem_index"]["problem_count"],
            "problem_ids": owner["problem_ids"],
            "all_statuses_open": all_statuses_open,
        },
        "statement_contract": {
            "config": owner["comparator"]["config"],
            "config_digest": packet["config_digest"],
            "challenge_import_closure": packet["challenge_import_closure"],
            "trusted_build_inputs": packet["trusted_build_inputs"],
            "theorem_names": [row["wrapper_declaration"] for row in owner["main_results"]],
            "permitted_axioms": owner["comparator"]["permitted_axioms"],
        },
        "checks": {
            "projection_and_isolation_check_exit": projection_check,
            "positive_comparator_exit": args.positive_exit,
            "positive_log_digest": digest(args.positive_log),
            "negative_mismatch_comparator_exit": args.negative_exit,
            "negative_log_digest": digest(args.negative_log),
            "negative_fixture_rejected": negative_semantic_rejection,
            "negative_expected_diagnostic": EXPECTED_MISMATCH,
        },
        "programme_local_checks": {
            "erdos_1049_numerical_height": {
                "headline_interface_count_changed": False,
                "config": "verification/comparator-1049-numerical-height.json",
                "config_digest": digest(
                    ROOT / "verification/comparator-1049-numerical-height.json"
                ),
                "positive_comparator_exit": args.local_1049_positive_exit,
                "positive_log_digest": digest(args.local_1049_positive_log),
                "negative_mismatch_comparator_exit": args.local_1049_negative_exit,
                "negative_log_digest": digest(args.local_1049_negative_log),
                "negative_fixture_rejected": local_1049_negative_semantic_rejection,
                "negative_expected_diagnostic": EXPECTED_1049_MISMATCH,
            }
        },
    }
    output = args.output if args.output.is_absolute() else ROOT / args.output
    written_output = write_runtime_receipt(output, receipt)
    print(written_output)
    return 0 if passed else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except VerificationInputError as exc:
        print(f"run_external_verification: unsafe input: {exc}", file=sys.stderr)
        raise SystemExit(1)
