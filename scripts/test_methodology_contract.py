#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial fixtures for methodology claim-transition checks."""

from __future__ import annotations

import json
from copy import deepcopy
import sys
from pathlib import Path

from methodology_contract import mutation_fixture_errors, render_markdown, validate_contract


ROOT = Path(__file__).resolve().parent.parent


def main() -> int:
    claims = json.loads((ROOT / "docs" / "claims.json").read_text(encoding="utf-8"))
    methodology = json.loads((ROOT / "docs" / "methodology.json").read_text(encoding="utf-8"))

    baseline_errors = validate_contract(claims, methodology)
    if baseline_errors:
        print("test_methodology_contract: baseline contract is invalid")
        for error in baseline_errors:
            print(f"  FAIL {error}")
        return 1

    # Release boundaries follow the claim owner, including newly registered
    # handles, rather than preserving a second hand-maintained scope guide.
    rendered = render_markdown(methodology, claims)
    from test_scope_source_identity import scope_machine_handle_errors
    open_ids = {row["id"] for row in claims["remaining_open_propositions"]}
    non_claim_ids = {row["id"] for row in claims["non_claims"]}
    assert not scope_machine_handle_errors(rendered, open_ids, non_claim_ids)
    assert "## Release scope" in rendered
    assert claims["external_verification_packet"]["boundary"] in rendered
    changed = deepcopy(claims)
    changed["external_verification_packet"]["boundary"] = "Changed release boundary fixture."
    changed["remaining_open_propositions"].append({"id": "remaining_open.new_fixture"})
    changed["non_claims"].append({"id": "not_new_fixture", "meaning": "New non-claim fixture"})
    changed_rendered = render_markdown(methodology, changed)
    assert "Changed release boundary fixture." in changed_rendered
    assert "python3 scripts/query_corpus.py --open remaining_open.new_fixture" in changed_rendered
    assert "`not_new_fixture`: New non-claim fixture." in changed_rendered
    assert "35-result/open envelope" not in rendered

    fixture_errors = mutation_fixture_errors(claims, methodology)
    failures = [fixture_id for fixture_id, errors in fixture_errors.items() if not errors]
    if failures:
        print("test_methodology_contract: mutations escaped validation: " + ", ".join(failures))
        return 1

    print(f"test_methodology_contract: baseline passed; all {len(fixture_errors)} invalid mutations were rejected")
    return 0


if __name__ == "__main__":
    sys.exit(main())
