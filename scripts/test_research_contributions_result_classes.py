#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Ensure negative and inconclusive returns remain valid but non-accepted."""

from __future__ import annotations

import copy
import json
import tempfile
from pathlib import Path

import validate_research_return as validator
import build_research_contributions as contributions


ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / ".github" / "fixtures" / "unaccepted-research-return.json"
INCONCLUSIVE = ROOT / "scripts" / "fixtures" / "research_returns" / "valid_inconclusive.json"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> int:
    identity = validator.repository_identity_contract.load_identity()
    negative = json.loads(FIXTURE.read_text(encoding="utf-8"))
    inconclusive = json.loads(INCONCLUSIVE.read_text(encoding="utf-8"))
    for label, value in (("negative", negative), ("inconclusive", inconclusive)):
        errors = validator.validate_document(value, repository_identity=identity)
        require(not errors, f"{label} fixture is invalid: {errors}")
        require(value["record_kind"] != "accepted_receipt", f"{label} fixture is already accepted")
        require(
            validator.validate_document(value, require_accepted=True, repository_identity=identity),
            f"{label} fixture crossed accepted gate",
        )

    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        (root / "negative.json").write_text(json.dumps(negative), encoding="utf-8")
        (root / "inconclusive.json").write_text(json.dumps(inconclusive), encoding="utf-8")
        require(contributions.load_receipts(root) == [], "negative/inconclusive returns entered accepted source loading")

    changed = copy.deepcopy(negative)
    changed["result"]["class"] = "positive"
    changed["result"]["claim_ceiling"] = "unbounded_theorem"
    require(
        validator.validate_document(changed, repository_identity=identity),
        "a class mutation made an unaccepted fixture accepted",
    )
    print("research contribution result classes: negative/inconclusive validation and accepted exclusion PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
