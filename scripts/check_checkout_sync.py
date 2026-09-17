#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Report local/public divergence; optionally fast-forward an existing main checkout."""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path


def git(root: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(root), *args], text=True, stderr=subprocess.PIPE
    ).strip()


def snapshot(root: Path) -> dict:
    ahead, behind = map(int, git(root, "rev-list", "--left-right", "--count", "HEAD...origin/main").split())
    return {
        "branch": git(root, "branch", "--show-current") or "DETACHED",
        "head": git(root, "rev-parse", "HEAD"),
        "origin_main": git(root, "rev-parse", "origin/main"),
        "local_only_commits": ahead,
        "main_only_commits": behind,
        "tracked_changes": bool(git(root, "diff", "HEAD", "--name-only")),
        "untracked_paths": git(root, "ls-files", "--others", "--exclude-standard").splitlines(),
        "synchronized": ahead == 0 and behind == 0,
        "remote_boundary": "origin/main is the last fetched remote state; use --fetch for a current observation",
    }


def synchronize_main(root: Path) -> dict:
    before = snapshot(root)
    if before["branch"] != "main":
        raise ValueError("Refusing to switch branches: preserve unfinished work in its own worktree first")
    if before["local_only_commits"] or before["tracked_changes"]:
        raise ValueError("Refusing to overwrite local commits or tracked changes; reconcile them explicitly")
    # Git refuses an untracked-file collision. No reset, clean, stash, or force.
    git(root, "merge", "--ff-only", "origin/main")
    return snapshot(root)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--fetch", action="store_true", help="Fetch origin before comparing")
    parser.add_argument("--sync-main", action="store_true", help="Fast-forward main only; implies --fetch")
    args = parser.parse_args()
    try:
        if args.fetch or args.sync_main:
            git(args.root, "fetch", "origin")
        result = synchronize_main(args.root) if args.sync_main else snapshot(args.root)
    except (subprocess.CalledProcessError, ValueError) as exc:
        detail = exc.stderr if isinstance(exc, subprocess.CalledProcessError) else str(exc)
        print(json.dumps({"status": "blocked", "detail": detail}, indent=2))
        return 2
    print(json.dumps(result, indent=2))
    return 0 if result["synchronized"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
