#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check publication-artifact coverage, identity, routing, and evidence limits."""

from __future__ import annotations

import argparse
from pathlib import Path

from publication_contract import (
    RepositoryReader,
    apply_artifact_digest_restamps,
    artifact_digest_restamp_plan,
    validate_publication_contract,
)


ROOT = Path(__file__).resolve().parent.parent


def restamp_command(*, apply_changes: bool) -> int:
    """Rebind drifted artifact digests to the manuscripts on disk."""
    reader = RepositoryReader(ROOT)
    restamps, refusals = artifact_digest_restamp_plan(reader)
    if not restamps and not refusals:
        print(
            "check_publication_contract: every artifact digest already matches "
            "its manuscript"
        )
        return 0
    if restamps:
        print(
            f"check_publication_contract: {len(restamps)} digest(s) to restamp"
        )
        for record in restamps:
            print(
                f"  {record['artifact_id']} {record['field']} ({record['path']})\n"
                f"    {record['expected']}\n"
                f" -> {record['actual']}"
            )
        print(
            "\nA restamp records new bytes; it does not review new mathematics. "
            "Read `git diff` on each source above and confirm the revision is one "
            "you meant to publish."
        )
    if refusals:
        separator = "\n" if restamps else ""
        print(
            f"{separator}check_publication_contract: "
            f"{len(refusals)} artifact(s) REFUSED"
        )
        for refusal in refusals:
            print(f"  REFUSED {refusal}")
    if restamps and not apply_changes:
        print(
            "\nThis was a dry run. Re-run with --restamp --apply to write the "
            "digests above; no other field of docs/publication_contract.json is "
            "touched."
        )
        return 1
    if restamps:
        apply_artifact_digest_restamps(ROOT, restamps)
        print(f"\nRestamped {len(restamps)} digest(s) in docs/publication_contract.json")
    return 1 if refusals else 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--git-ref",
        help="validate a committed Git ref, or ':' for the staged index",
    )
    parser.add_argument(
        "--restamp",
        action="store_true",
        help=(
            "recompute drifted artifact digests from the manuscripts on disk; "
            "dry run unless --apply is given"
        ),
    )
    parser.add_argument(
        "--apply",
        action="store_true",
        help="with --restamp, write the recomputed digests to the registry",
    )
    args = parser.parse_args()
    if args.apply and not args.restamp:
        parser.error("--apply is only meaningful with --restamp")
    if args.restamp and args.git_ref:
        parser.error("--restamp rewrites the worktree registry, so it takes no --git-ref")
    if args.restamp:
        return restamp_command(apply_changes=args.apply)
    errors = validate_publication_contract(RepositoryReader(ROOT, args.git_ref))
    if errors:
        print(f"check_publication_contract: {len(errors)} failure(s)")
        for error in errors:
            print(f"  FAIL {error}")
        return 1
    target = args.git_ref or "worktree"
    print(f"check_publication_contract: publication contract verified at {target}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
