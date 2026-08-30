#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep the human scope boundary aligned with the formal-source contract."""

from __future__ import annotations

import json
import os
import re
import stat
import tempfile
from pathlib import Path
from unittest.mock import patch


ROOT = Path(__file__).resolve().parent.parent
OPEN_ID_RE = re.compile(r"`(remaining_open\.[A-Za-z0-9_]+)`")
NON_CLAIM_ID_RE = re.compile(r"`(not_[A-Za-z0-9_]+)`")


def require(condition: bool, message: str) -> None:
    """Keep scope identity failures active when run with ``python -O``."""
    if not condition:
        raise AssertionError(message)


class UnsafeScopeInput(ValueError):
    """A release-identity input is outside the regular-file boundary."""


def safe_scope_text(path: Path, root: Path = ROOT) -> str:
    """Read an identity input through a no-follow regular-file descriptor."""
    candidate = Path(os.path.abspath(path))
    root = Path(os.path.abspath(root))
    if candidate != root and root not in candidate.parents:
        raise UnsafeScopeInput(f"scope input escaped checkout: {candidate}")
    current = candidate
    while True:
        if current.is_symlink():
            raise UnsafeScopeInput(f"symlinked scope input: {candidate}")
        if current == root:
            break
        if current.parent == current:
            raise UnsafeScopeInput(f"scope input escaped checkout: {candidate}")
        current = current.parent
    if not candidate.is_file():
        raise UnsafeScopeInput(f"scope input is not a regular file: {candidate}")
    flags = os.O_RDONLY | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_NOFOLLOW", 0)
    if hasattr(os, "O_CLOEXEC"):
        flags |= os.O_CLOEXEC
    try:
        descriptor = os.open(candidate, flags)
    except OSError as exc:
        raise UnsafeScopeInput(
            f"scope input could not be opened safely: {candidate}"
        ) from exc
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise UnsafeScopeInput(
                f"scope input is not a regular file: {candidate}"
            )
        chunks: list[bytes] = []
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
    except OSError as exc:
        raise UnsafeScopeInput(
            f"scope input could not be read safely: {candidate}"
        ) from exc
    finally:
        os.close(descriptor)
    try:
        return b"".join(chunks).decode("utf-8")
    except UnicodeDecodeError as exc:
        raise UnsafeScopeInput(f"scope input is not UTF-8: {candidate}") from exc


def check_input_boundary() -> int:
    """Reject substituted and special files before identity validation."""
    private_tmp = Path("/private/tmp")
    temporary_root = str(private_tmp) if private_tmp.is_dir() else None
    with tempfile.TemporaryDirectory(
        prefix="scope-identity-boundary-", dir=temporary_root
    ) as raw:
        workspace = Path(raw)
        regular = workspace / "regular.txt"
        regular.write_text("identity input\n", encoding="utf-8")
        require(
            safe_scope_text(regular, workspace) == "identity input\n",
            "regular scope input was not read safely",
        )

        linked = workspace / "linked.txt"
        linked.symlink_to(regular)
        try:
            safe_scope_text(linked, workspace)
        except UnsafeScopeInput:
            pass
        else:
            raise AssertionError("scope identity reader followed a symlink")

        fifo = workspace / "input.fifo"
        if hasattr(os, "mkfifo"):
            os.mkfifo(fifo)
            try:
                safe_scope_text(fifo, workspace)
            except UnsafeScopeInput:
                pass
            else:
                raise AssertionError("scope identity reader accepted a FIFO")

        raced = workspace / "raced.txt"
        raced.write_text("placeholder\n", encoding="utf-8")
        original_open = os.open

        def replace_with_fifo(path: Path, flags: int, mode: int = 0o777) -> int:
            if Path(path) == raced:
                raced.unlink()
                os.mkfifo(raced)
            return original_open(path, flags, mode)

        with patch.object(os, "open", side_effect=replace_with_fifo):
            try:
                safe_scope_text(raced, workspace)
            except UnsafeScopeInput as error:
                require("regular file" in str(error), str(error))
            else:
                raise AssertionError(
                    "scope identity reader opened a path replaced by a FIFO"
                )
    return 4


def scope_machine_handle_errors(
    scope: str, open_ids: set[str], non_claim_ids: set[str]
) -> list[str]:
    """Require exact registered handles and bounded open queries in SCOPE.md."""
    errors: list[str] = []
    observed_open_ids = set(OPEN_ID_RE.findall(scope))
    for open_id in sorted(open_ids - observed_open_ids):
        errors.append(f"SCOPE.md lost exact open identifier {open_id}")
    for open_id in sorted(observed_open_ids - open_ids):
        errors.append(f"SCOPE.md carries unknown open identifier {open_id}")
    for open_id in sorted(open_ids):
        command = f"python3 scripts/query_corpus.py --open {open_id}"
        if command not in scope:
            errors.append(f"SCOPE.md lost bounded open query {command}")

    observed_non_claim_ids = set(NON_CLAIM_ID_RE.findall(scope))
    for non_claim_id in sorted(non_claim_ids - observed_non_claim_ids):
        errors.append(f"SCOPE.md lost exact non-claim identifier {non_claim_id}")
    for non_claim_id in sorted(observed_non_claim_ids - non_claim_ids):
        errors.append(f"SCOPE.md carries unknown non-claim identifier {non_claim_id}")

    for phrase in (
        "Finite instances, conditional reductions, cited neighbours, and named",
        "do not discharge these propositions",
        "required by `docs/methodology.json`",
    ):
        if phrase not in scope:
            errors.append(f"SCOPE.md lost open-transition boundary: {phrase}")
    return errors


def main() -> int:
    boundary_count = check_input_boundary()
    claims = json.loads(safe_scope_text(ROOT / "docs" / "claims.json"))
    formal_source = claims["release"]["formal_source"]
    open_ids = {row["id"] for row in claims["remaining_open_propositions"]}
    non_claim_ids = {row["id"] for row in claims["non_claims"]}
    scope = safe_scope_text(ROOT / "SCOPE.md")

    require(
        re.fullmatch(r"[0-9a-f]{40}", formal_source["ref"]) is not None,
        "formal-source reference is not a full lowercase Git id",
    )
    require(formal_source["ref_kind"] == "commit", "formal-source ref is not a commit")
    require(
        re.fullmatch(
            r"formal-source-\d{4}-\d{2}-\d{2}(?:-r[1-9]\d*)?",
            formal_source["public_tag"],
        )
        is not None,
        "formal-source public tag is not immutable and date-qualified",
    )
    require(
        formal_source["publication_state"] == "published_committed_checkpoint",
        "formal-source checkpoint is not published and committed",
    )
    require(
        formal_source["relationship_to_last_tag"]
        in {"at_last_tag", "post_tag_checkpoint"},
        "formal-source relationship to the citation tag is invalid",
    )
    require(
        re.search(r"immutable\s+formal-source checkpoint", scope) is not None,
        "scope omits the immutable formal-source checkpoint",
    )
    require("citation identity" in scope, "scope omits citation identity")
    require(
        "not a substitute for an exact proof-source identity" in scope,
        "scope permits citation identity to substitute for proof-source identity",
    )
    require(
        "until it is included in a new tagged\nrelease" not in scope,
        "scope implies an untagged change can enter the release",
    )
    require(
        not scope_machine_handle_errors(scope, open_ids, non_claim_ids),
        "scope machine handles are not synchronized with the claim registry",
    )

    missing_open = scope.replace(
        "python3 scripts/query_corpus.py --open "
        "remaining_open.universal_257_all_infinite_supports",
        "",
        1,
    )
    require(
        any(
            "lost bounded open query" in error
            for error in scope_machine_handle_errors(
                missing_open, open_ids, non_claim_ids
            )
        ),
        "missing bounded open query was accepted",
    )
    weakened_transition = scope.replace(
        "do not discharge these propositions",
        "are enough to discharge these propositions",
        1,
    )
    require(
        any(
            "lost open-transition boundary" in error
            for error in scope_machine_handle_errors(
                weakened_transition, open_ids, non_claim_ids
            )
        ),
        "weakened open-transition boundary was accepted",
    )
    stale_open = scope.replace(
        "Machine-resolvable open propositions:",
        "Machine-resolvable open propositions:\n\n"
        "- `remaining_open.retired_placeholder`:\n"
        "  `python3 scripts/query_corpus.py --open remaining_open.retired_placeholder`",
        1,
    )
    require(
        any(
            "unknown open identifier" in error
            for error in scope_machine_handle_errors(stale_open, open_ids, non_claim_ids)
        ),
        "stale open identifier was accepted",
    )
    stale_non_claim = scope + (
        "\n| `not_retired_placeholder` | A stale scope claim that is no longer registered |\n"
    )
    require(
        any(
            "unknown non-claim identifier" in error
            for error in scope_machine_handle_errors(
                stale_non_claim, open_ids, non_claim_ids
            )
        ),
        "stale non-claim identifier was accepted",
    )

    print(
        "test_scope_source_identity: scope separates release identity, proof "
        f"checkpoint, {len(open_ids)} exact open propositions, and "
        f"{len(non_claim_ids)} exact non-claims; "
        f"4 negative fixtures and {boundary_count} file-boundary checks rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
