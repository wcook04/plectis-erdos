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
import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

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


def build_register(
    claims: list[dict],
    open_props: list[dict] | None = None,
    main_results: list[dict] | None = None,
) -> dict:
    register = {
        "schema": "erdos249257-claims/3",
        "release": {"version": "test", "formal_source": {}},
        "status_taxonomy": TAXONOMY,
        "non_claims": [],
        "remaining_open_propositions": open_props or [],
        "claims": claims,
    }
    if main_results is not None:
        register["external_verification_packet"] = {
            "boundary": "Comparator checks statements, not significance.",
            "comparator": {"permitted_axioms": ["propext"], "config": "verification/comparator.json"},
            "claim_status_contract": {"unregistered_interface": "Not a canonical reviewed claim."},
            "main_results": main_results,
        }
    return register


def claim(
    decl_name: str,
    line: int,
    status: str = "proved here",
    paper_label: str | None = None,
) -> dict:
    return {
        "id": "sample_claim",
        "label": "Sample",
        "status": status,
        "statement": "A sample statement.",
        "paper_label": paper_label,
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

        # A published checkout must not let caller Git selectors redirect the
        # child process to a private repository, namespace, or replacement map.
        hostile_environment = {
            "GIT_DIR": "/private/wrong-git-dir",
            "GIT_WORK_TREE": "/private/wrong-work-tree",
            "GIT_INDEX_FILE": "/private/wrong-index",
            "GIT_NAMESPACE": "wrong-namespace",
            "GIT_REPLACE_REF_BASE": "refs/replacements/wrong",
            "GIT_OBJECT_DIRECTORY": "/private/wrong-objects",
            "GIT_ALTERNATE_OBJECT_DIRECTORIES": "/private/wrong-alternates",
            "GIT_COMMON_DIR": "/private/wrong-common",
        }
        with patch.dict(os.environ, hostile_environment, clear=False):
            sanitized = verify_claims.clean_environment()
            assert all(key not in sanitized for key in hostile_environment)
            assert verify_claims.describe_environment({})[
                "subprocess_environment"
            ] == {
                "contract": verify_claims.ENVIRONMENT_CONTRACT,
                "sanitized_git_selectors": list(
                    verify_claims.SANITIZED_GIT_ENVIRONMENT_KEYS
                ),
            }
            child = verify_claims.run(
                [
                    sys.executable,
                    "-c",
                    "import json, os; print(json.dumps({k: os.environ[k] for k in "
                    "('GIT_DIR', 'GIT_NAMESPACE', 'GIT_REPLACE_REF_BASE') "
                    "if k in os.environ}))",
                ],
                cwd=root,
            )
            assert child.returncode == 0
            assert json.loads(child.stdout) == {}

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

        # The same edge on the Comparator side: a selected interface may name a
        # claim id, and that binding must not outlive the claim either.
        report = run_case(
            root,
            build_register(
                [claim("Sample.alpha", ALPHA_KEYWORD_LINE)],
                main_results=[{"id": "iface", "claim_id": "deleted_claim"}],
            ),
        )
        if "comparator_interface_targets_unknown_claim" not in statuses(report):
            failures.append(f"orphaned Comparator binding not reported: {report['problems']}")

        # A claim whose paper label no paper carries sends a reader after prose
        # that is not there.
        (root / "paper").mkdir(exist_ok=True)
        (root / "paper" / "sample.tex").write_text(
            "\\label{res:present}\n", encoding="utf-8"
        )
        report = run_case(
            root,
            build_register([claim("Sample.alpha", ALPHA_KEYWORD_LINE, paper_label="res:absent")]),
        )
        if "paper_label_resolves_to_no_paper" not in statuses(report):
            failures.append(f"unresolvable paper label not reported: {report['problems']}")

        # ...and a label a paper does carry is not reported.
        report = run_case(
            root,
            build_register([claim("Sample.alpha", ALPHA_KEYWORD_LINE, paper_label="res:present")]),
        )
        if not report["verified"]:
            failures.append(f"resolvable paper label reported as broken: {report['problems']}")

        # Absent paper sources are an environment fact, not a claim fault. A
        # checkout without the write-ups must still verify, or the exposition
        # check would convert a truncated clone into a broken register -- the
        # exact conflation this module separates everywhere else.
        (root / "paper" / "sample.tex").unlink()
        (root / "paper").rmdir()
        report = run_case(
            root,
            build_register([claim("Sample.alpha", ALPHA_KEYWORD_LINE, paper_label="res:absent")]),
        )
        if not report["verified"]:
            failures.append(f"absent paper sources reported as a claim fault: {report['problems']}")

    if failures:
        for failure in failures:
            print(f"  FAIL {failure}")
        return 1
    print(
        "test_verify_claims: drift, renames, undeclared statuses, orphaned open "
        "propositions, orphaned Comparator bindings, and unresolvable paper "
        "labels are each reported; absent paper sources are not"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
