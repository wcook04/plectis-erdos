#!/usr/bin/env python3
"""Check that this repository's paper corpus still matches its local sources.

``scripts/export_paper_corpus.py`` is the public owner and can regenerate the
corpus from the local authored paper registry and its manuscripts. This
lightweight companion does not require pandoc: it verifies the authored
registry is represented exactly and every recorded manuscript and shipped PDF
still has the hash the corpus was built from.

That catches both failures that matter at this boundary: someone edits a paper
and the generated text silently keeps describing the old one; or a generated
catalogue drops an active paper while every retained file still hashes. It uses
nothing but the standard library, so it can run in any CI job.

Exit status is 0 when the corpus is current, 1 when a manuscript has moved on,
and 2 when the corpus is missing or unreadable.

    python3 docs/papers/check_paper_corpus.py
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

CORPUS_REL = "docs/papers/corpus.json"
REGISTRY_REL = "docs/papers/paper_registry.json"
EXPORTER_REL = "scripts/export_paper_corpus.py"
THIS_REPOSITORY = "plectis-erdos"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--singleflight-worker",
        action="store_true",
        help=argparse.SUPPRESS,
    )
    parser.parse_args(argv)
    repo_root = Path(__file__).resolve().parents[2]
    corpus_path = repo_root / CORPUS_REL
    registry_path = repo_root / REGISTRY_REL
    try:
        corpus = json.loads(corpus_path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        print(f"cannot read {CORPUS_REL}: {exc}", file=sys.stderr)
        return 2
    try:
        registry = json.loads(registry_path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        print(f"cannot read {REGISTRY_REL}: {exc}", file=sys.stderr)
        return 2

    stale: list[str] = []
    missing: list[str] = []
    incomplete: list[str] = []
    checked = 0

    registry_rows = registry.get("papers")
    if not isinstance(registry_rows, list):
        print(f"cannot read {REGISTRY_REL}: papers is not a list", file=sys.stderr)
        return 2
    registry_ids = [
        row.get("paper_id")
        for row in registry_rows
        if isinstance(row, dict) and isinstance(row.get("paper_id"), str)
    ]
    if len(registry_ids) != len(registry_rows):
        incomplete.append("paper registry contains a row without a paper_id")
    if len(registry_ids) != len(set(registry_ids)):
        incomplete.append("duplicate paper ids in paper registry")
    registry_by_id = {
        row["paper_id"]: row
        for row in registry_rows
        if isinstance(row, dict) and isinstance(row.get("paper_id"), str)
    }
    support_sources = registry.get("support_sources")
    if not isinstance(support_sources, list) or not all(
        isinstance(value, str) for value in support_sources
    ):
        incomplete.append("paper registry lacks support_sources")
        support_sources = []
    discovered_tex = {
        str(path.relative_to(repo_root)) for path in (repo_root / "paper").glob("*.tex")
    }
    registered_tex = {
        row.get("source")
        for row in registry_rows
        if isinstance(row, dict)
        and row.get("relation_to_this_repository") == "native"
        and isinstance(row.get("source"), str)
    }
    covered_tex = registered_tex | set(support_sources)
    if discovered_tex != covered_tex:
        incomplete.append(
            "paper registry does not cover paper/*.tex exactly: "
            f"missing={sorted(discovered_tex - covered_tex)}, "
            f"stale={sorted(covered_tex - discovered_tex)}"
        )

    expected_ids = corpus.get("expected_paper_ids")
    papers = corpus.get("papers", [])
    if not isinstance(expected_ids, list) or not all(
        isinstance(paper_id, str) for paper_id in expected_ids
    ):
        incomplete.append("missing expected_paper_ids export manifest")
        expected_ids = []
    if expected_ids != registry_ids:
        incomplete.append(
            "expected_paper_ids does not match the authored paper registry"
        )
    if corpus.get("generated_by") != EXPORTER_REL:
        incomplete.append(f"generated_by must name {EXPORTER_REL}")
    if corpus.get("this_repository") != THIS_REPOSITORY:
        incomplete.append(f"this_repository must be {THIS_REPOSITORY}")
    if not isinstance(papers, list):
        print(f"cannot read {CORPUS_REL}: papers is not a list", file=sys.stderr)
        return 2

    actual_ids = [
        paper.get("paper_id")
        for paper in papers
        if isinstance(paper, dict) and isinstance(paper.get("paper_id"), str)
    ]
    if len(expected_ids) != len(set(expected_ids)):
        incomplete.append("duplicate paper ids in expected_paper_ids export manifest")
    if len(actual_ids) != len(set(actual_ids)):
        incomplete.append("duplicate paper ids in papers")
    expected_set = set(expected_ids)
    actual_set = set(actual_ids)
    missing_records = sorted(expected_set - actual_set)
    unexpected_records = sorted(actual_set - expected_set)
    if missing_records:
        incomplete.append(
            "missing expected paper records: " + ", ".join(missing_records)
        )
    if unexpected_records:
        incomplete.append(
            "unexpected paper records: " + ", ".join(unexpected_records)
        )

    for paper in papers:
        if not isinstance(paper, dict):
            incomplete.append("non-object paper record")
            continue
        source_rel = paper.get("local_source")
        expected = paper.get("source_sha256")
        paper_id = paper.get("paper_id")
        registry_row = registry_by_id.get(paper_id)
        if registry_row is not None:
            if source_rel != registry_row.get("source"):
                incomplete.append(f"{paper_id}: local_source disagrees with registry")
            if paper.get("local_pdf") != registry_row.get("pdf"):
                incomplete.append(f"{paper_id}: local_pdf disagrees with registry")
        full_text_rel = paper.get("local_full_text")
        if not isinstance(full_text_rel, str) or not (repo_root / full_text_rel).is_file():
            incomplete.append(f"{paper_id}: generated full text is missing")
        if not source_rel or not expected:
            continue
        source_path = repo_root / source_rel
        try:
            actual = "sha256:" + hashlib.sha256(source_path.read_bytes()).hexdigest()
        except OSError:
            missing.append(source_rel)
            continue
        checked += 1
        if actual != expected:
            stale.append(
                f"{paper.get('paper_id')}: {source_rel}\n"
                f"    corpus was built from {expected}\n"
                f"    the file now hashes to {actual}"
            )

        pdf_rel = paper.get("local_pdf")
        expected_pdf = paper.get("pdf_sha256")
        if pdf_rel and expected_pdf:
            pdf_path = repo_root / pdf_rel
            try:
                actual_pdf = "sha256:" + hashlib.sha256(pdf_path.read_bytes()).hexdigest()
            except OSError:
                missing.append(pdf_rel)
                continue
            checked += 1
            if actual_pdf != expected_pdf:
                stale.append(
                    f"{paper.get('paper_id')}: {pdf_rel}\n"
                    f"    corpus was built from {expected_pdf}\n"
                    f"    the file now hashes to {actual_pdf}"
                )

    if missing:
        for rel in missing:
            print(f"missing manuscript: {rel}", file=sys.stderr)
        return 2

    if stale:
        print("The paper corpus is out of date.\n", file=sys.stderr)
        for row in stale:
            print(f"  {row}", file=sys.stderr)
        print(
            "\nThe generated text under docs/papers/ no longer describes these "
            "manuscripts.\nRe-export it from this public repository:\n"
            f"    python3 {EXPORTER_REL} --write",
            file=sys.stderr,
        )
        return 1

    if incomplete:
        print("The paper corpus is incomplete.\n", file=sys.stderr)
        for row in incomplete:
            print(f"  {row}", file=sys.stderr)
        print(
            "\nRe-export it from this public repository:\n"
            f"    python3 {EXPORTER_REL} --write",
            file=sys.stderr,
        )
        return 1

    print(
        f"paper corpus current: {checked} recorded artefacts "
        "(manuscripts and shipped PDFs) match their hashes"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
