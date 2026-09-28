#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Prepare a clean release before transport; admit only its exact outgoing commit."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import stat
import shlex
from datetime import datetime, timezone
import re
import subprocess
import sys
import tempfile
from pathlib import Path

import check_release_ref as snapshot

# Complete release parity runs before network transport, never inside a hook.
RELEASE_TIMEOUT_SECONDS = 2400


def outgoing_commits(lines: list[str]) -> list[str]:
    commits = []
    for line in lines:
        fields = line.split()
        if len(fields) != 4 or not re.fullmatch(r"(?:[0-9a-f]{40}|[0-9a-f]{64})", fields[1]):
            raise ValueError("invalid Git pre-push input")
        oid = fields[1]
        if set(oid) != {"0"} and oid not in commits:
            commits.append(oid)
    return commits


def prepare_commit(oid: str, release_receipt: Path | None = None) -> int:
    commit = snapshot.resolve_commit(oid)
    if release_receipt is not None:
        receipt = json.loads(release_receipt.read_text())
        coverage = receipt.get("gate_coverage", {})
        if not (receipt.get("schema") == snapshot.SCHEMA
                and receipt.get("resolved_commit") == commit
                and receipt.get("status") == "passed"
                and receipt.get("gate_exit_code") == 0
                and receipt.get("failed_gate_count") == 0
                and receipt.get("snapshot_posture") == "clean_committed_clone_excludes_caller_worktree_changes"
                and receipt.get("release_commands") == [list(c) for c in snapshot.RELEASE_COMMANDS]
                and coverage.get("all_configured_gates_completed") is True
                and coverage.get("completed_gate_count") == len(snapshot.RELEASE_COMMANDS)):
            raise ValueError("release receipt is failed, incomplete or for another immutable commit")
        save_admission(commit, "complete_clean_release_receipt")
        return 0
    receipt, code = snapshot.validate_ref(commit, timeout_seconds=RELEASE_TIMEOUT_SECONDS,
                                          probe_only=False)
    print(snapshot.render_text(receipt), flush=True)
    if code == 0:
        save_admission(commit, "complete_clean_release_validation")
    return code


def admission_identity(commit: str) -> dict:
    tree = snapshot.run(["git", "rev-parse", f"{commit}^{{tree}}"], cwd=snapshot.ROOT)
    if tree.returncode:
        raise ValueError("cannot resolve outgoing commit tree")
    driver = hashlib.sha256(Path(__file__).read_bytes() + Path(snapshot.__file__).read_bytes()).hexdigest()
    return {"schema": "prepared_publication_admission_v1", "commit": commit,
            "tree": tree.stdout.strip(), "driver": driver}


def admission_path(commit: str) -> Path:
    result = snapshot.run(["git", "rev-parse", "--path-format=absolute", "--git-common-dir"], cwd=snapshot.ROOT)
    if result.returncode:
        raise ValueError("cannot find the repository-local admission store")
    directory = Path(result.stdout.strip()) / "plectis-publication-admission-v1"
    directory.mkdir(mode=0o700, exist_ok=True)
    if directory.is_symlink() or not directory.is_dir() or directory.stat().st_uid != os.getuid():
        raise ValueError("publication admission store is not an owned directory")
    return directory / (commit + ".json")


def save_admission(commit: str, evidence: str) -> None:
    destination = admission_path(commit)
    payload = {**admission_identity(commit), "result": 0, "evidence": evidence,
               "completed_at": datetime.now(timezone.utc).isoformat(),
               "validation_python": sys.version, "validation_platform": sys.platform}
    with tempfile.NamedTemporaryFile("w", dir=destination.parent, delete=False) as handle:
        json.dump(payload, handle); handle.write("\n"); temporary = Path(handle.name)
    temporary.replace(destination)
    print(f"Prepared exact commit {commit}; the push hook will only verify this receipt and the live base.", flush=True)


def check_commit(oid: str) -> int:
    commit = snapshot.resolve_commit(oid)
    path = admission_path(commit)
    if path.is_file() and not path.is_symlink():
        info = path.stat()
        if info.st_uid == os.getuid() and not (stat.S_IMODE(info.st_mode) & 0o077):
            try:
                receipt = json.loads(path.read_text())
                if receipt.get("result") == 0 and all(receipt.get(k) == v for k, v in admission_identity(commit).items()):
                    print(f"pre-push {commit[:12]}: prepared immutable-commit admission verified", flush=True)
                    return 0
            except (OSError, ValueError):
                pass
    print(f"Push stopped: no current admission for {commit}. Before pushing, run {shlex.quote(sys.executable)} {shlex.quote(str(Path(__file__).resolve()))} --repository {shlex.quote(str(snapshot.ROOT))} --prepare {commit}. "
          "Validation runs before the network transport opens; it is never skipped.", file=sys.stderr)
    return 1


def require_current_base(remote: str, lines: list[str]) -> None:
    """Reject branch updates based on an older configured PR base.

    Observe the actual remote, not a possibly stale tracking ref. Fetch only
    the observed immutable object when necessary; never change local branches,
    the index, the working tree or FETCH_HEAD. CI still guards a later base move.
    """
    groups: dict[str, list[str]] = {}
    for row in lines:
        fields = row.split()
        if len(fields) != 4 or not fields[2].startswith("refs/heads/"):
            continue
        commits = outgoing_commits([row])
        if not commits:
            continue
        destination = fields[2].removeprefix("refs/heads/")
        configured = snapshot.run(["git", "config", "--get", f"branch.{destination}.plectisAdmissionBase"], cwd=snapshot.ROOT)
        if configured.returncode not in (0, 1):
            raise ValueError("cannot read publication base configuration")
        base_ref = configured.stdout.strip() or "refs/heads/main"
        if not base_ref.startswith("refs/heads/"):
            raise ValueError("publication base must be an explicit remote branch ref")
        groups.setdefault(base_ref, []).extend(commits)
    for base_ref, commits in groups.items():
        require_base(remote, commits, base_ref)


def require_base(remote: str, commits: list[str], base_ref: str) -> None:
    result = snapshot.run(["git", "ls-remote", "--exit-code", remote, base_ref],
                          cwd=snapshot.ROOT, timeout=60)
    if result.returncode == 2 and not result.stdout.strip():
        # A new repository has no main yet; projection admission still applies.
        return
    if result.returncode:
        raise ValueError("cannot observe destination base; retry when the remote is reachable")
    rows = [line.split() for line in result.stdout.splitlines()]
    if len(rows) != 1 or len(rows[0]) != 2 or rows[0][1] != base_ref or not re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", rows[0][0]):
        raise ValueError("destination base did not resolve to one immutable commit")
    base = rows[0][0]
    known = snapshot.run(["git", "cat-file", "-e", f"{base}^{{commit}}"], cwd=snapshot.ROOT)
    if known.returncode:
        fetched = snapshot.run(["git", "fetch", "--no-tags", "--no-write-fetch-head", remote, base],
                               cwd=snapshot.ROOT, timeout=60)
        if fetched.returncode:
            raise ValueError("cannot fetch the observed destination base")
    for commit in commits:
        ancestor = snapshot.run(["git", "merge-base", "--is-ancestor", base, commit], cwd=snapshot.ROOT)
        if ancestor.returncode == 1:
            raise ValueError(f"destination {base_ref.removeprefix('refs/heads/')} advanced to {base[:12]}; merge or rebase it, regenerate affected projections, commit them and retry")
        if ancestor.returncode:
            raise ValueError("cannot establish outgoing commit ancestry")


def install_shared() -> int:
    """Install one versioned guard for the repository's existing worktrees."""
    common = admission_path(snapshot.resolve_commit("HEAD")).parent.parent
    directory = common / "plectis-publication-hooks"
    current = subprocess.run(["git", "config", "--local", "--get", "core.hooksPath"],
                             cwd=snapshot.ROOT, text=True, capture_output=True)
    if current.returncode not in (0, 1) or current.stdout.strip() not in ("", str(directory)):
        raise ValueError("preserve the existing shared custom hook; integrate the publication guard explicitly")
    digest = admission_identity(snapshot.resolve_commit("HEAD"))["driver"]
    bundle = directory / digest
    bundle.mkdir(parents=True, exist_ok=True)
    for source in (Path(__file__), Path(snapshot.__file__)):
        (bundle / source.name).write_bytes(source.read_bytes())
    hook = directory / "pre-push"
    hook.write_text("#!/bin/sh\n# Plectis managed immutable publication admission\nexec python3 " +
                    shlex.quote(str(bundle / "check_push.py")) +
                    ' --repository "$(git rev-parse --show-toplevel)" "$@"\n')
    hook.chmod(0o755)
    subprocess.run(["git", "config", "--local", "core.hooksPath", str(directory)], cwd=snapshot.ROOT, check=True)
    print(f"Installed shared publication admission for this repository: {directory}")
    return 0


def install() -> int:
    # Worktree-local configuration avoids changing another branch's hooks.
    existing = subprocess.run(["git", "config", "--get", "core.hooksPath"],
                              cwd=snapshot.ROOT, capture_output=True, text=True)
    expected = str(snapshot.ROOT / ".githooks")
    if existing.returncode not in (0, 1):
        raise ValueError("cannot inspect Git hook configuration")
    if existing.stdout.strip() not in ("", expected):
        raise ValueError("core.hooksPath is already configured; preserve and integrate the existing hook")
    for args in (["git", "config", "extensions.worktreeConfig", "true"],
                 ["git", "config", "--worktree", "core.hooksPath", expected]):
        subprocess.run(args, cwd=snapshot.ROOT, check=True)
    print("Installed the committed-snapshot pre-push check for this worktree.")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--install", action="store_true")
    parser.add_argument("--install-shared", action="store_true")
    parser.add_argument("--repository", type=Path, help="explicit worktree for a shared repository guard")
    parser.add_argument("--base-ref", help="actual PR base, e.g. refs/heads/main or a stacked parent")
    parser.add_argument("--destination-branch", help="remote branch whose PR base is being configured")
    parser.add_argument("--prepare", metavar="COMMIT", help="validate and record a committed snapshot before git push")
    parser.add_argument("--release-receipt", type=Path, help="reuse a complete check_release_ref receipt for --prepare")
    parser.add_argument("remote", nargs="?")
    parser.add_argument("url", nargs="?")
    args = parser.parse_args()
    try:
        if args.repository is not None:
            root = args.repository.resolve()
            observed = snapshot.run(["git", "rev-parse", "--show-toplevel"], cwd=root)
            if observed.returncode or Path(observed.stdout.strip()).resolve() != root:
                raise ValueError("--repository must name the worktree root")
            snapshot.ROOT = root
        if args.install_shared:
            return install_shared()
        if args.install:
            return install()
        if args.base_ref or args.destination_branch:
            if not (args.prepare and args.base_ref and args.destination_branch):
                raise ValueError("base configuration requires --prepare, --base-ref and --destination-branch")
            for ref in (args.base_ref, "refs/heads/" + args.destination_branch):
                valid = snapshot.run(["git", "check-ref-format", ref], cwd=snapshot.ROOT)
                if valid.returncode or not ref.startswith("refs/heads/"):
                    raise ValueError("publication base/destination must be branch refs")
            subprocess.run(["git", "config", "--local", f"branch.{args.destination_branch}.plectisAdmissionBase", args.base_ref],
                           cwd=snapshot.ROOT, check=True)
        if args.prepare:
            return prepare_commit(args.prepare, args.release_receipt)
        if args.release_receipt:
            raise ValueError("--release-receipt requires --prepare")
        lines = sys.stdin.readlines()
        commits = outgoing_commits(lines)
        if args.remote:
            require_current_base(args.remote, lines)
        for oid in commits:
            code = check_commit(oid)
            if code:
                return code
        return 0
    except (ValueError, OSError, subprocess.SubprocessError, snapshot.SnapshotError) as error:
        print(f"pre-push: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
