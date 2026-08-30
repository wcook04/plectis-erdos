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
counts, note artifact routes, content digests, the standalone paper that writes
the problem up, and the Comparator disposition of each contribution family.
The index is therefore stale whenever the source, the Lean modules, the notes,
the review matrix, or the paper corpus move.

The last two are joins rather than new judgement.  ``docs/claims.json`` already
carries a review matrix with one row per Erdős number, and each row already
names the problem's paper and an authored disposition for every contribution
family.  ``docs/papers/corpus.json`` already names every manuscript.  Nothing
here decides whether a family is externally checked or which paper covers a
problem; it routes an agent standing at a problem card to answers that were
written down elsewhere.

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
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / "docs" / "problem_index_source.json"
OUTPUT = ROOT / "docs" / "problems.json"
CONTRACT = ROOT / "docs" / "publication_contract.json"
CLAIMS = ROOT / "docs" / "claims.json"
CORPUS = ROOT / "docs" / "papers" / "corpus.json"
SCHEMA = "erdos249257-problem-index/1"
SOURCE_SCHEMA = "erdos249257-problem-index-source/1"
LIBRARY = "ErdosProblems"

# The review matrix records one authored disposition per contribution family.
# The vocabulary is open -- a new family arrives with its own suffix -- but each
# value states one of four things, and the class is what a reader needs before
# the detail.  Order matters only in that the longest distinguishing prefix
# comes first; the four are disjoint today.
DISPOSITION_CLASSES = {
    "targeted": (
        "Comparator checked a separately declared statement of this family"
    ),
    "represented_by_": (
        "another selected interface carries this family's content"
    ),
    "not_selected_": (
        "a Lean proposition here, not selected for external execution"
    ),
    "not_applicable_": (
        "not a Lean theorem, so there is nothing for Comparator to check"
    ),
}

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


def disposition_class(value: str) -> str:
    """Name the class a review-matrix disposition belongs to.

    ``unclassified`` is a real answer, not a fallback to hide behind: a
    disposition outside the four known shapes is a vocabulary the projection
    has not been taught, and ``main`` refuses to build until someone says
    which class it belongs to.
    """
    for prefix in DISPOSITION_CLASSES:
        if value.startswith(prefix):
            return prefix.rstrip("_")
    return "unclassified"


def review_matrix_by_number(claims: dict | None) -> dict[int, dict]:
    if claims is None:
        return {}
    packet = claims.get("external_verification_packet", {})
    return {row["problem"]: row for row in packet.get("review_matrix", [])}


def corpus_by_source(corpus: dict | None) -> dict[str, dict]:
    if corpus is None:
        return {}
    return {
        paper["local_source"]: paper
        for paper in corpus.get("papers", [])
        if paper.get("local_source")
    }


def external_check_facts(erdos_number: int, matrix: dict[int, dict]) -> dict[str, object]:
    """State how much of this problem Comparator was asked to check."""
    row = matrix.get(erdos_number)
    if row is None:
        return {"state": "no_review_matrix_row"}
    families = row.get("families", [])
    by_class: dict[str, int] = {}
    dispositions: dict[str, str] = {}
    for family in families:
        value = family.get("comparator_disposition", "")
        dispositions[family["id"]] = value
        name = disposition_class(value)
        by_class[name] = by_class.get(name, 0) + 1
    return {
        "state": "reviewed",
        "family_count": len(families),
        "by_class": dict(sorted(by_class.items())),
        "dispositions": dispositions,
    }


def paper_facts(
    erdos_number: int,
    matrix: dict[int, dict],
    papers: dict[str, dict],
    corpus_present: bool,
) -> dict[str, object]:
    """Route from a problem to the manuscript that writes it up.

    A cold agent standing at a problem card could reach the Lean modules and
    the open obligations but not the paper, even though the review matrix has
    named it all along.
    """
    row = matrix.get(erdos_number)
    if row is None:
        return {"resolution": "no_review_matrix_row"}
    local_source = row.get("paper")
    if not local_source:
        return {"resolution": "no_paper_in_review_matrix"}
    if not corpus_present:
        return {"source": local_source, "resolution": "paper_corpus_absent"}
    paper = papers.get(local_source)
    if paper is None:
        return {"source": local_source, "resolution": "source_not_in_paper_corpus"}
    return {
        "paper_id": paper["paper_id"],
        "title": paper["title"],
        "source": local_source,
        "pdf": paper.get("local_pdf"),
        "full_text": paper.get("local_full_text"),
        "resolution": "resolved",
    }


RESEARCH_CORPUS_FILES = ("frontier", "strongest_results", "manifest", "checkpoint")


def research_corpus_facts(config: dict | None) -> dict[str, object] | None:
    """Expose a problem's public research frontier without promoting it.

    The corpus is a reader route and evidence bundle, not part of the reviewed
    claim registry. Keep the route source-fingerprinted so a problem card
    cannot silently point at a changed frontier or activation map.
    """
    if config is None:
        return None
    if not isinstance(config, dict):
        raise ValueError("research_corpus must be an object")
    directory = config.get("directory")
    if not isinstance(directory, str) or not directory:
        raise ValueError("research_corpus.directory must be a nonempty path")
    authority_posture = config.get("authority_posture")
    reading_rule = config.get("reading_rule")
    if not isinstance(authority_posture, str) or not isinstance(reading_rule, str):
        raise ValueError("research_corpus authority posture and reading rule are required")

    files: dict[str, dict[str, str]] = {}
    for key in RESEARCH_CORPUS_FILES:
        raw = config.get(key)
        if not isinstance(raw, str) or not raw:
            raise ValueError(f"research_corpus.{key} must be a nonempty path")
        pure = PurePosixPath(raw)
        if pure.is_absolute() or ".." in pure.parts:
            raise ValueError(f"unsafe research corpus path: {raw}")
        path = ROOT.joinpath(*pure.parts)
        if not path.is_file() or path.is_symlink():
            raise ValueError(f"missing or symlinked research corpus file: {raw}")
        files[key] = {"path": raw, "content_digest": sha256(path.read_bytes())}

    strongest = json.loads(
        (ROOT / files["strongest_results"]["path"]).read_text(encoding="utf-8")
    )
    checkpoint = json.loads(
        (ROOT / files["checkpoint"]["path"]).read_text(encoding="utf-8")
    )
    results = strongest.get("results")
    if not isinstance(results, list) or not results:
        raise ValueError("research corpus strongest-result map is empty")
    source_checkpoint = strongest.get("source_checkpoint")
    if source_checkpoint != checkpoint.get("source_commit"):
        raise ValueError("research corpus strongest-result and checkpoint commits differ")
    return {
        "directory": directory,
        "authority_posture": authority_posture,
        "reading_rule": reading_rule,
        "files": files,
        "strongest_result_summary": {
            "source_checkpoint": source_checkpoint,
            "status": strongest.get("status"),
            "result_count": len(results),
        },
        "checkpoint_summary": {
            "source_subtree_tree": checkpoint.get("source_subtree_tree"),
            "exported_source_file_count": checkpoint.get("exported_source_file_count"),
            "status": checkpoint.get("status"),
        },
    }


def build(
    source: dict,
    artifacts: dict[str, dict],
    claims: dict | None,
    corpus: dict | None,
) -> dict:
    matrix = review_matrix_by_number(claims)
    papers = corpus_by_source(corpus)
    problems = []
    for row in source["problems"]:
        modules = [module_facts(row["principal_module"])]
        modules.extend(module_facts(name) for name in row.get("companion_modules", []))
        problem = {
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
            "paper": paper_facts(
                row["erdos_number"], matrix, papers, corpus is not None
            ),
            "external_check": external_check_facts(row["erdos_number"], matrix),
        }
        research_route = research_corpus_facts(row.get("research_corpus"))
        if research_route is not None:
            problem["research_corpus"] = research_route
        problems.append(problem)
    packet = (claims or {}).get("external_verification_packet", {})
    receipt = packet.get("receipt_contract", {})
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
        "route_template": source["route_template"],
        "status_vocabulary": source["status_vocabulary"],
        "library_roots": source["library_roots"],
        # Both routes below are joins into surfaces that already hold the
        # answer.  The wording and the boundary are quoted from the packet
        # rather than restated, so this projection cannot drift into a
        # stronger description of Comparator than its owner allows.
        "external_check": {
            "source": "docs/claims.json::external_verification_packet.review_matrix",
            "public_wording": receipt.get("public_wording"),
            "forbidden_wording": receipt.get("forbidden_wording"),
            "boundary": packet.get("boundary"),
            "review_status": packet.get("review_status"),
            "disposition_classes": dict(DISPOSITION_CLASSES),
            "reading_rule": (
                "A per-family disposition says whether Comparator was asked to "
                "check that family, not whether the family is true and not "
                "whether the problem is solved."
            ),
        },
        "paper_corpus": {
            "source": "docs/papers/corpus.json",
            "reading_rule": (
                "Each problem's paper block names the manuscript that writes "
                "the problem up. The paper is authored exposition; it is not "
                "proof authority and it does not register claims."
            ),
        },
        "problem_count": len(problems),
        "problems": problems,
        "reviewed_problems": source["reviewed_problems"],
        "validation_commands": source["validation_commands"],
    }


def canonical(data: dict) -> bytes:
    # This is a machine-readable route projection with a strict cold-reader
    # byte budget.  Compact JSON preserves the complete object and its key
    # order while keeping newly joined problem/family routes inside that
    # externally advertised envelope.
    return (
        json.dumps(data, ensure_ascii=False, separators=(",", ":")) + "\n"
    ).encode("utf-8")


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
    claims = json.loads(CLAIMS.read_text(encoding="utf-8")) if CLAIMS.is_file() else None
    # The paper corpus is exported from the private system repository. A
    # checkout without it is an environment missing a file, not a problem
    # index missing an answer, so the paper route reports its own absence
    # rather than failing the build.
    corpus = json.loads(CORPUS.read_text(encoding="utf-8")) if CORPUS.is_file() else None
    matrix = review_matrix_by_number(claims)
    papers = corpus_by_source(corpus)

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
        # A problem the review matrix does not cover would publish a card with
        # no external-check answer at all, which reads as "not checked" rather
        # than "nobody said".
        if claims is not None and row["erdos_number"] not in matrix:
            errors.append(
                f"{row['problem_id']}: the review matrix in docs/claims.json has "
                f"no row for Erdős {row['erdos_number']}"
            )
        for family in matrix.get(row["erdos_number"], {}).get("families", []):
            value = family.get("comparator_disposition", "")
            if disposition_class(value) == "unclassified":
                errors.append(
                    f"{row['problem_id']}: family {family['id']!r} has disposition "
                    f"{value!r}, which matches none of the four known classes; "
                    "teach DISPOSITION_CLASSES the new prefix rather than "
                    "publishing a card that cannot say what it means"
                )
        # The review matrix names a paper for every problem. If that path no
        # longer names a manuscript, the card would route a reader to nothing.
        local_source = matrix.get(row["erdos_number"], {}).get("paper")
        if corpus is not None and local_source and local_source not in papers:
            errors.append(
                f"{row['problem_id']}: the review matrix names {local_source!r}, "
                "which is not a manuscript in docs/papers/corpus.json"
            )
    if errors:
        print(f"build_problem_index: {len(errors)} failure(s)")
        for error in errors:
            print(f"  FAIL {error}")
        return 1

    payload = canonical(build(source, artifacts, claims, corpus))
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
