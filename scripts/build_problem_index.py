#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build the bounded, problem-owned navigation index.

A cold agent that clones this repository can already reach the reviewed corpus
through ``docs/orientation.json`` and ``docs/claims.json``.  Neither surface
routes the expansion library ``ErdosProblems``, whose declarations are exact
Lean propositions rather than reviewed public claims.  This program builds the
route that does: one row per Erdős problem, naming its modules, its note, what
is checked, what is not, and the obligation that survives.

Authored judgement -- the questions, the checked and unchecked lists, the open
obligations -- lives in ``docs/problem_index_source.json``.  Everything a
machine can derive is derived here: module paths, declaration and theorem
counts, note artifact routes, and content digests.  The index is therefore
stale whenever the source, the Lean modules, or the notes move.

Run from the repository root:

    python3 scripts/build_problem_index.py           # write docs/problems.json
    python3 scripts/build_problem_index.py --check   # fail if it is stale
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / "docs" / "problem_index_source.json"
OUTPUT = ROOT / "docs" / "problems.json"
CONTRACT = ROOT / "docs" / "publication_contract.json"
SCHEMA = "erdos249257-problem-index/1"
SOURCE_SCHEMA = "erdos249257-problem-index-source/1"
LIBRARY = "ErdosProblems"

THEOREM_RE = re.compile(r"^\s*(?:private |protected |nonrec )?(theorem|lemma)\s+([A-Za-z_])")
DECL_RE = re.compile(
    r"^\s*(?:private |protected |noncomputable |nonrec )*"
    r"(theorem|lemma|def|abbrev|structure|instance)\s+([A-Za-z_])"
)


def sha256(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def module_path(module: str) -> str:
    """Turn a dotted Lean module name into its repository-relative path."""
    return "/".join(module.split(".")) + ".lean"


def module_facts(module: str) -> dict[str, object]:
    relative = module_path(module)
    path = ROOT / relative
    if not path.is_file():
        return {"module": module, "path": relative, "present": False}
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    return {
        "module": module,
        "path": relative,
        "present": True,
        "line_count": len(lines),
        "declaration_count": sum(1 for line in lines if DECL_RE.match(line)),
        "theorem_count": sum(1 for line in lines if THEOREM_RE.match(line)),
        "content_digest": sha256(text.encode("utf-8")),
    }


def note_facts(artifact_id: str, artifacts: dict[str, dict]) -> dict[str, object] | None:
    row = artifacts.get(artifact_id)
    if row is None:
        return None
    return {
        "artifact_id": artifact_id,
        "title": row["title"],
        "source_path": row["source_path"],
        "rendered_path": row["rendered_path"],
        "authority_posture": row["authority_posture"],
    }


def build(source: dict, artifacts: dict[str, dict]) -> dict:
    problems = []
    for row in source["problems"]:
        modules = [module_facts(row["principal_module"])]
        modules.extend(module_facts(name) for name in row.get("companion_modules", []))
        problems.append(
            {
                "problem_id": row["problem_id"],
                "erdos_number": row["erdos_number"],
                "short_title": row["short_title"],
                "status": row["status"],
                "question": row["question"],
                "library_root": "ErdosProblems.lean",
                "claim_registry_status": (
                    "not_registered; the claim registry does not carry these "
                    "declarations and kernel checking them does not promote "
                    "them into reviewed public claims"
                ),
                "directory": row["directory"],
                "modules": modules,
                "note": note_facts(row["note_artifact_id"], artifacts),
                "what_is_checked": row["what_is_checked"],
                "what_is_not_checked": row["what_is_not_checked"],
                "open_obligations": row["open_obligations"],
                "finite_search": row.get("finite_search"),
            }
        )
    return {
        "schema": SCHEMA,
        "artifact_role": "generated_problem_owned_navigation_index",
        "authority_posture": (
            "navigation_projection_not_Lean_proof_authority_and_not_a_"
            "reviewed_claim_registry"
        ),
        "purpose": source["purpose"],
        "generated_by": "scripts/build_problem_index.py",
        "authored_source": "docs/problem_index_source.json",
        "reading_rule": source["reading_rule"],
        "status_vocabulary": source["status_vocabulary"],
        "library_roots": source["library_roots"],
        "problem_count": len(problems),
        "problems": problems,
        "reviewed_problems": source["reviewed_problems"],
        "validation_commands": source["validation_commands"],
    }


def canonical(data: dict) -> bytes:
    return (json.dumps(data, indent=2, ensure_ascii=False) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if the index is stale")
    args = parser.parse_args()

    source = json.loads(SOURCE.read_text(encoding="utf-8"))
    if source.get("schema") != SOURCE_SCHEMA:
        print(f"docs/problem_index_source.json must use schema {SOURCE_SCHEMA}")
        return 1
    contract = json.loads(CONTRACT.read_text(encoding="utf-8"))
    artifacts = {row["id"]: row for row in contract.get("artifacts", [])}

    errors: list[str] = []
    for row in source["problems"]:
        if row["note_artifact_id"] not in artifacts:
            errors.append(
                f"{row['problem_id']}: note artifact {row['note_artifact_id']!r} "
                "is not registered in the publication contract"
            )
        for module in [row["principal_module"], *row.get("companion_modules", [])]:
            if not module.startswith(f"{LIBRARY}."):
                errors.append(f"{row['problem_id']}: {module} is outside {LIBRARY}")
            elif not (ROOT / module_path(module)).is_file():
                errors.append(f"{row['problem_id']}: {module_path(module)} is missing")
    if errors:
        print(f"build_problem_index: {len(errors)} failure(s)")
        for error in errors:
            print(f"  FAIL {error}")
        return 1

    payload = canonical(build(source, artifacts))
    budget = source["index_max_bytes"]
    if len(payload) > budget:
        print(f"docs/problems.json exceeds its {budget}-byte budget: {len(payload)}")
        return 1

    if args.check:
        actual = OUTPUT.read_bytes() if OUTPUT.is_file() else b""
        if actual != payload:
            print("docs/problems.json is stale; run python3 scripts/build_problem_index.py")
            return 1
        print(
            f"problem index current: {len(source['problems'])} problem(s), "
            f"{len(payload)} of {budget} bytes"
        )
        return 0

    OUTPUT.write_bytes(payload)
    print(
        f"wrote docs/problems.json: {len(source['problems'])} problem(s), "
        f"{len(payload)} of {budget} bytes"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
