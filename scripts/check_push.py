#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check the exact outgoing commits with the shared cold projection preflight."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path

import check_release_ref as snapshot


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


def check_commit(oid: str) -> int:
    commit = snapshot.resolve_commit(oid)
    with tempfile.TemporaryDirectory(prefix="plectis-push-preflight-") as temp:
        clone = snapshot.prepare_clone(commit, Path(temp))
        if not snapshot.is_safe_snapshot_file(clone, clone / "scripts/refresh_projections.py"):
            raise ValueError("outgoing commit lacks a regular projection preflight script")
        result = snapshot.run(
            [sys.executable, "scripts/refresh_projections.py", "--preflight"],
            cwd=clone, timeout=300,
        )
        print(f"pre-push {commit[:12]}: {result.stdout.strip()}", flush=True)
        if result.stderr:
            print(result.stderr, file=sys.stderr, end="")
        if result.returncode:
            print("Push stopped. Repair and commit the named evidence, then retry.", file=sys.stderr)
        return result.returncode


def require_current_base(remote: str, lines: list[str]) -> None:
    """Reject branch updates based on an older destination main.

    Observe the actual remote, not a possibly stale tracking ref. Fetch only
    the observed immutable object when necessary; never change local branches,
    the index, the working tree or FETCH_HEAD. CI still guards a later base move.
    """
    branches = [row for row in lines if row.split()[2].startswith("refs/heads/")]
    commits = outgoing_commits(branches)
    if not commits:
        return
    result = snapshot.run(["git", "ls-remote", "--exit-code", remote, "refs/heads/main"],
                          cwd=snapshot.ROOT, timeout=60)
    if result.returncode == 2 and not result.stdout.strip():
        # A new repository has no main yet; projection admission still applies.
        return
    if result.returncode:
        raise ValueError("cannot observe destination main; retry when the remote is reachable")
    rows = [line.split() for line in result.stdout.splitlines()]
    if len(rows) != 1 or len(rows[0]) != 2 or rows[0][1] != "refs/heads/main" or not re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", rows[0][0]):
        raise ValueError("destination main did not resolve to one immutable commit")
    base = rows[0][0]
    known = snapshot.run(["git", "cat-file", "-e", f"{base}^{{commit}}"], cwd=snapshot.ROOT)
    if known.returncode:
        fetched = snapshot.run(["git", "fetch", "--no-tags", "--no-write-fetch-head", remote, base],
                               cwd=snapshot.ROOT, timeout=60)
        if fetched.returncode:
            raise ValueError("cannot fetch the observed destination main")
    for commit in commits:
        ancestor = snapshot.run(["git", "merge-base", "--is-ancestor", base, commit], cwd=snapshot.ROOT)
        if ancestor.returncode == 1:
            raise ValueError(f"destination main advanced to {base[:12]}; merge or rebase it, regenerate affected projections, commit them and retry")
        if ancestor.returncode:
            raise ValueError("cannot establish outgoing commit ancestry")


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
    parser.add_argument("remote", nargs="?")
    parser.add_argument("url", nargs="?")
    args = parser.parse_args()
    try:
        if args.install:
            return install()
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
