#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Prove the claim-following verb reports drift instead of absorbing it.

A checker that cannot be shown failing is decoration. The register is currently
sound, so running `verify_claims.py` against this repository proves only that it
says yes. These fixtures give it registers that are wrong in each of the ways a
register goes wrong -- a shifted line, a renamed declaration, a status outside
the taxonomy, an open proposition pointing at a claim that no longer exists --
and require a report for every one.

Two of the fixtures also pin the Lean spellings that a naive matcher gets wrong,
because both mistakes were made while writing the checker: a declaration whose
name wraps onto the line below its `theorem` keyword, and a declaration written
inside a namespace but registered under its qualified name.
"""

from __future__ import annotations

import json
import tempfile
from pathlib import Path

import verify_claims

# Deliberately awkward, and all of it real Lean shape from this corpus:
# a wrapped `theorem`, a namespaced declaration, and a modifier before `def`.
SAMPLE_MODULE = """\
import Mathlib

namespace Sample

/-- **Wrapped declaration.**  The name sits below the keyword. -/
theorem
    alpha (n : Nat) : n = n := rfl

/-- **Modifier before the keyword.** -/
noncomputable def beta : Nat := 0

end Sample
"""

# Line numbers into SAMPLE_MODULE above (1-indexed). `alpha` is recorded at the
# `theorem` keyword on line 6 with its name on line 7, which is how the real
# register records wrapped declarations.
ALPHA_KEYWORD_LINE = 6
BETA_LINE = 10

TAXONOMY = {"proved here": "Lean theorem in the committed formal-source checkpoint"}


def build_register(claims: list[dict], open_props: list[dict] | None = None) -> dict:
    return {
        "schema": "erdos249257-claims/3",
        "release": {"version": "test", "formal_source": {}},
        "status_taxonomy": TAXONOMY,
        "non_claims": [],
        "remaining_open_propositions": open_props or [],
        "claims": claims,
    }


def claim(decl_name: str, line: int, status: str = "proved here") -> dict:
    return {
        "id": "sample_claim",
        "label": "Sample",
        "status": status,
        "statement": "A sample statement.",
        "paper_label": None,
        "declarations": [
            {"name": decl_name, "module": "Sample.lean", "line": line}
        ],
    }


def run_case(root: Path, register: dict) -> dict:
    (root / "docs").mkdir(parents=True, exist_ok=True)
    (root / "docs" / "claims.json").write_text(json.dumps(register), encoding="utf-8")
    verify_claims.REPO_ROOT = root
    verify_claims.CLAIMS_PATH = root / "docs" / "claims.json"
    return verify_claims.verify_all_claims(register)


def statuses(report: dict) -> set[str]:
    return {problem.get("status") for problem in report["problems"]}


def main() -> int:
    failures: list[str] = []
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        (root / "Sample.lean").write_text(SAMPLE_MODULE, encoding="utf-8")

        # A wrapped declaration recorded at its keyword line must resolve, and a
        # namespaced declaration registered under its qualified name must too.
        for name, line, label in (
            ("Sample.alpha", ALPHA_KEYWORD_LINE, "wrapped namespaced theorem"),
            ("Sample.beta", BETA_LINE, "noncomputable def"),
        ):
            report = run_case(root, build_register([claim(name, line)]))
            if not report["verified"]:
                failures.append(f"{label}: sound register reported as broken {report['problems']}")

        # A shifted line is drift, and drift must be named.
        report = run_case(root, build_register([claim("Sample.alpha", 2)]))
        if "drifted" not in statuses(report):
            failures.append(f"shifted line not reported as drift: {report['problems']}")

        # A renamed declaration is a citation pointing at nothing.
        report = run_case(root, build_register([claim("Sample.gone", ALPHA_KEYWORD_LINE)]))
        if "declaration_missing" not in statuses(report):
            failures.append(f"renamed declaration not reported: {report['problems']}")

        # A status outside the declared taxonomy means the ceiling is undefined.
        report = run_case(
            root, build_register([claim("Sample.alpha", ALPHA_KEYWORD_LINE, "definitely true")])
        )
        if "status_outside_taxonomy" not in statuses(report):
            failures.append(f"undeclared status not reported: {report['problems']}")

        # An open proposition must not outlive the claim it targets.
        report = run_case(
            root,
            build_register(
                [claim("Sample.alpha", ALPHA_KEYWORD_LINE)],
                [{"id": "remaining_open.orphan", "open_target_claim": "deleted_claim"}],
            ),
        )
        if "open_proposition_targets_unknown_claim" not in statuses(report):
            failures.append(f"orphaned open proposition not reported: {report['problems']}")

    if failures:
        for failure in failures:
            print(f"  FAIL {failure}")
        return 1
    print(
        "test_verify_claims: drift, renames, undeclared statuses, and orphaned "
        "open propositions are each reported"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
