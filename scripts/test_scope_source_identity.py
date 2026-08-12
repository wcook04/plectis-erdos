#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep the human scope boundary aligned with the formal-source contract."""

from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
OPEN_ID_RE = re.compile(r"`(remaining_open\.[A-Za-z0-9_]+)`")
NON_CLAIM_ID_RE = re.compile(r"`(not_[A-Za-z0-9_]+)`")


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
    claims = json.loads((ROOT / "docs" / "claims.json").read_text(encoding="utf-8"))
    formal_source = claims["release"]["formal_source"]
    open_ids = {row["id"] for row in claims["remaining_open_propositions"]}
    non_claim_ids = {row["id"] for row in claims["non_claims"]}
    scope = (ROOT / "SCOPE.md").read_text(encoding="utf-8")

    assert re.fullmatch(r"[0-9a-f]{40}", formal_source["ref"])
    assert formal_source["ref_kind"] == "commit"
    assert re.fullmatch(
        r"formal-source-\d{4}-\d{2}-\d{2}(?:-r[1-9]\d*)?",
        formal_source["public_tag"],
    )
    assert formal_source["publication_state"] == "published_committed_checkpoint"
    assert formal_source["relationship_to_last_tag"] in {"at_last_tag", "post_tag_checkpoint"}
    assert re.search(r"immutable\s+formal-source checkpoint", scope)
    assert "citation identity" in scope
    assert "not a substitute for an exact proof-source identity" in scope
    assert "until it is included in a new tagged\nrelease" not in scope
    assert not scope_machine_handle_errors(scope, open_ids, non_claim_ids)

    missing_open = scope.replace(
        "python3 scripts/query_corpus.py --open "
        "remaining_open.universal_257_all_infinite_supports",
        "",
        1,
    )
    assert any(
        "lost bounded open query" in error
        for error in scope_machine_handle_errors(
            missing_open, open_ids, non_claim_ids
        )
    )
    weakened_transition = scope.replace(
        "do not discharge these propositions",
        "are enough to discharge these propositions",
        1,
    )
    assert any(
        "lost open-transition boundary" in error
        for error in scope_machine_handle_errors(
            weakened_transition, open_ids, non_claim_ids
        )
    )
    stale_open = scope.replace(
        "Machine-resolvable open propositions:",
        "Machine-resolvable open propositions:\n\n"
        "- `remaining_open.retired_placeholder`:\n"
        "  `python3 scripts/query_corpus.py --open remaining_open.retired_placeholder`",
        1,
    )
    assert any(
        "unknown open identifier" in error
        for error in scope_machine_handle_errors(stale_open, open_ids, non_claim_ids)
    )
    stale_non_claim = scope + (
        "\n| `not_retired_placeholder` | A stale scope claim that is no longer registered |\n"
    )
    assert any(
        "unknown non-claim identifier" in error
        for error in scope_machine_handle_errors(
            stale_non_claim, open_ids, non_claim_ids
        )
    )

    print(
        "test_scope_source_identity: scope separates release identity, proof "
        f"checkpoint, {len(open_ids)} exact open propositions, and "
        f"{len(non_claim_ids)} exact non-claims; "
        "4 negative fixtures rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
