#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Bind the systems paper's historical claims to their evidence owner."""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from publication_contract import normalize_latex_evidence


ROOT = Path(__file__).resolve().parent.parent
PAPER_PATH = ROOT / "paper" / "claim-faithful-publication-systems-paper.tex"
EVIDENCE_PATH = ROOT / "docs" / "publication_evidence.json"

NUMBER_WORDS = {
    0: "zero",
    1: "one",
    2: "two",
    3: "three",
    4: "four",
    5: "five",
    6: "six",
    7: "seven",
    8: "eight",
    9: "nine",
    10: "ten",
}


def number_word(value: int) -> str:
    if value not in NUMBER_WORDS:
        raise ValueError(f"unsupported systems-paper evidence count: {value}")
    return NUMBER_WORDS[value]


def validate_systems_paper_evidence(
    paper_text: str | None = None,
    evidence: dict[str, Any] | None = None,
) -> list[str]:
    """Check the paper's outcome and ceilings against the typed receipt."""
    if paper_text is None:
        paper_text = PAPER_PATH.read_text(encoding="utf-8")
    if evidence is None:
        evidence = json.loads(EVIDENCE_PATH.read_text(encoding="utf-8"))

    errors: list[str] = []
    normalized = normalize_latex_evidence(paper_text)
    evaluation = evidence.get("evaluation", {})
    summary = evaluation.get("summary", {})
    mutations = evaluation.get("mutations", [])
    post_repair = evidence.get("post_repair", {})
    provenance = evidence.get("provenance", {})

    total = summary.get("authored_mutation_count")
    rejected = summary.get("rejected_mutation_count")
    escaped_ids = summary.get("escaped_mutation_ids")
    if not isinstance(total, int) or not isinstance(rejected, int):
        errors.append("publication evidence lacks integer mutation totals")
    elif not isinstance(escaped_ids, list):
        errors.append("publication evidence lacks escaped mutation ids")
    else:
        if len(mutations) != total:
            errors.append("publication evidence mutation total disagrees with its matrix")
        if rejected + len(escaped_ids) != total:
            errors.append("publication evidence outcomes do not partition the mutation total")
        if len(escaped_ids) != 1:
            errors.append("systems paper prose currently supports exactly one escaped mutation")
        else:
            expected = (
                f"{number_word(rejected)} of the {number_word(total)} edits were "
                "rejected. one escaped"
            )
            if expected not in normalized:
                errors.append(
                    "systems paper historical outcome disagrees with publication evidence"
                )

    if provenance.get("raw_run_logs_registered") is False:
        if "the original run logs were not retained" not in normalized:
            errors.append("systems paper lost the original-run-log absence ceiling")

    if post_repair.get("other_original_mutations_rerun") is False:
        rerun_ids = post_repair.get("rerun_mutation_ids", [])
        if isinstance(total, int) and isinstance(rerun_ids, list):
            other_count = total - len(rerun_ids)
            expected = (
                f"the other {number_word(other_count)} edits were not rerun "
                "against the extended checklist"
            )
            if expected not in normalized:
                errors.append("systems paper lost the post-repair rerun ceiling")

    author_relationship = evaluation.get("protocol", {}).get(
        "mutation_author_relationship"
    )
    if author_relationship == "mutations_authored_by_checker_author":
        if "the edits were authored by the checker's author" not in normalized:
            errors.append("systems paper lost the mutation-author dependence ceiling")

    return errors


def reflow_tolerant_replace(
    source: str, phrase: str, replacement: str, count: int = 1
) -> str:
    """Replace ``phrase`` treating each gap between words as any whitespace.

    LaTeX paragraphs get rewrapped freely, so a fixture anchored on a literal
    line break stops mutating the moment the text reflows: the "mutated" copy
    becomes byte-identical to the source and the check can no longer fail.
    That is the silent-decay failure the paper itself warns about, and it has
    happened here once.  Matching whitespace flexibly keeps every fixture armed
    across rewrapping, and can only widen what the anchor finds, never narrow
    it.  A phrase that is genuinely gone still leaves the source unchanged, so
    the ``_anchor_missing`` detection below is preserved.
    """
    pattern = r"\s+".join(re.escape(word) for word in phrase.split())
    return re.sub(pattern, lambda _match: replacement, source, count=count)


def mutation_fixture_failures() -> list[str]:
    """Ensure known paper/evidence disagreements remain rejectable."""
    source = PAPER_PATH.read_text(encoding="utf-8")
    logs_retained = reflow_tolerant_replace(
        source,
        "original run logs were not retained",
        "original run logs were retained",
        count=0,
    )
    fixtures = {
        "historical_outcome_inverted": reflow_tolerant_replace(
            source,
            "nine of the ten edits were rejected",
            "all ten edits were rejected",
        ),
        "original_logs_claimed_retained": reflow_tolerant_replace(
            logs_retained,
            "Original run logs were not retained",
            "Original run logs were retained",
            count=0,
        ),
        "post_repair_rerun_ceiling_removed": reflow_tolerant_replace(
            source,
            "The other nine edits",
            "The other edits",
        ),
        "mutation_author_dependence_removed": reflow_tolerant_replace(
            source,
            "The edits were authored by the checker's author",
            "The edits were independently authored",
        ),
    }
    failures: list[str] = []
    for fixture_id, mutated in fixtures.items():
        if mutated == source:
            failures.append(f"{fixture_id}_anchor_missing")
            continue
        if not validate_systems_paper_evidence(paper_text=mutated):
            failures.append(fixture_id)
    return failures


def main() -> int:
    errors = validate_systems_paper_evidence()
    fixture_failures = mutation_fixture_failures() if not errors else []
    if errors or fixture_failures:
        print(
            "systems_paper_evidence: "
            f"{len(errors)} baseline failure(s), "
            f"{len(fixture_failures)} fixture failure(s)"
        )
        for error in errors:
            print(f"  FAIL {error}")
        for fixture in fixture_failures:
            print(f"  FAIL fixture did not reject: {fixture}")
        return 1
    print(
        "systems_paper_evidence: historical outcome and evidence ceilings "
        "match; four opposing fixtures reject"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
