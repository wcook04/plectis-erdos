#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Report divergence or merge conflicts; optionally fast-forward a main checkout."""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path

import validation_singleflight as singleflight


def git(root: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(root), *args], text=True, stderr=subprocess.PIPE,
        env=singleflight.command_environment(),
        timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
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


def mergeability(root: Path, base: str = "origin/main") -> dict:
    """Check the committed candidate without changing refs, index or worktree."""
    result = {
        "head": git(root, "rev-parse", "HEAD"),
        "base": base,
        "base_commit": git(root, "rev-parse", "--verify", f"{base}^{{commit}}"),
    }
    if (git(root, "diff", "HEAD", "--name-only")
            or git(root, "ls-files", "--others", "--exclude-standard")):
        return result | {
            "status": "uncommitted_inputs",
            "detail": "Commit the intended candidate first; a HEAD-only check cannot certify working edits.",
        }
    checked = subprocess.run(
        ["git", "-C", str(root), "merge-tree", "--write-tree", "--name-only",
         "--no-messages", "-z", result["head"], result["base_commit"]],
        capture_output=True, text=True,
        env=singleflight.command_environment(),
        timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
    )
    if checked.returncode not in (0, 1):
        raise subprocess.CalledProcessError(
            checked.returncode, checked.args, checked.stdout, checked.stderr,
        )
    # NUL separation preserves filenames containing whitespace or newlines.
    fields = checked.stdout.split("\0")
    return result | {
        "status": "mergeable" if checked.returncode == 0 else "conflicting",
        "conflicting_paths": sorted(set(filter(None, fields[1:]))),
        "boundary": "Committed trees only; this does not validate regenerated artifacts or merged proofs.",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--fetch", action="store_true", help="Fetch origin before comparing")
    parser.add_argument("--sync-main", action="store_true", help="Fast-forward main only; implies --fetch")
    parser.add_argument("--check-merge", action="store_true", help="Check committed HEAD can merge with the base, without switching or merging the checkout")
    parser.add_argument("--base", default="origin/main", help="Base ref for --check-merge (default: origin/main)")
    args = parser.parse_args()
    if args.check_merge and args.sync_main:
        parser.error("--check-merge and --sync-main are mutually exclusive")
    try:
        if args.fetch or args.sync_main:
            git(args.root, "fetch", "origin")
        result = (mergeability(args.root, args.base) if args.check_merge else
                  synchronize_main(args.root) if args.sync_main else snapshot(args.root))
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired, OSError, ValueError) as exc:
        detail = (exc.stderr or str(exc)) if isinstance(exc, subprocess.CalledProcessError) else str(exc)
        print(json.dumps({"status": "blocked", "detail": detail}, indent=2))
        return 2
    print(json.dumps(result, indent=2))
    if args.check_merge:
        return {"mergeable": 0, "conflicting": 1, "uncommitted_inputs": 2}[result["status"]]
    return 0 if result["synchronized"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
