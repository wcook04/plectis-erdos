#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial tests for negative-knowledge labelling, plus a surface report.

The fixtures fail hard: a route called closed, dead, or impossible without a
vocabulary label and evidence is rejected, and a label outside the vocabulary
raises.  The pass over `docs/RESULTS.md` and `docs/semantic/frontier.json` is
a report only.  Pre-existing prose is not failed here, because rewriting eight
notes is a publication-content change the operator signs, and a gate that
fails on text nobody is allowed to edit tonight is a gate that gets disabled.

The report is written outside the repository by default so the release
footprint does not change.  Pass `--report <path>` to put it elsewhere.

Stdlib only, no Lean, no network, no git mutation.
"""

from __future__ import annotations

import argparse
import json
import sys
import tempfile
from dataclasses import asdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import negative_knowledge_labels as labels  # noqa: E402
from negative_knowledge_labels import LabelledRoute, UnknownLabel  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
SURFACES = {
    "docs/RESULTS.md": ROOT / "docs" / "RESULTS.md",
    "docs/semantic/frontier.json": ROOT / "docs" / "semantic" / "frontier.json",
}
DEFAULT_REPORT = (
    Path(tempfile.gettempdir()) / "plectis_negative_knowledge_report.json"
)


def require(condition: bool, message: str) -> None:
    """Keep assertions active when Python is run with -O."""
    if not condition:
        raise AssertionError(message)


UNLABELLED = LabelledRoute(
    route_id="erdos249.cyclotomic_lattice",
    statement="The cyclotomic lattice route is dead.",
)
UNEVIDENCED = LabelledRoute(
    route_id="erdos257.window_controls",
    statement="The window-control approach is closed.",
    label="proved_class_obstruction",
    evidence="   ",
)
OUT_OF_VOCABULARY = LabelledRoute(
    route_id="erdos243.coprimality_cap",
    statement="The coprimality route is impossible.",
    label="ruled_out",
    evidence="a desk said so",
)
WELL_FORMED = (
    LabelledRoute(
        route_id="erdos249.finite_dyadic_exclusions",
        statement="The finite dyadic exclusion route is dead as a source of "
        "progress.",
        label="empirical_deprioritisation",
        evidence="finite exclusions are free and never advance the endpoint; "
        "see the #249 eight-return batch",
    ),
    LabelledRoute(
        route_id="erdos251.fencing_identity",
        statement="The fencing-identity approach is closed because it is "
        "circular.",
        label="target_equivalent_reformulation",
        evidence="q = 1 fencing identity is equivalent to the target",
    ),
    LabelledRoute(
        route_id="erdos1041.min_two_arm",
        statement="The minimum two-arm statement is dead as an attack.",
        label="counterexample_to_proposal",
        evidence="explicit wall specimen refutes the statement",
    ),
    LabelledRoute(
        route_id="erdos257.strong_repair",
        statement="The uniform repair route is not closed; it survives under "
        "one remaining inequality.",
        label="conditional_reduction",
        evidence="one remaining inequality, stated in the note",
    ),
    LabelledRoute(
        route_id="erdos68.arity_route",
        statement="Every fixed-arity attack in this class is impossible.",
        label="proved_class_obstruction",
        evidence="Lean module proving the class obstruction",
    ),
)
NOT_A_ROUTE_CLAIM = (
    LabelledRoute(
        route_id="erdos257.cylinder_mass",
        statement="cylinderMass_split decomposes the closed cylinder mass.",
    ),
    LabelledRoute(
        route_id="erdos249.closed_form",
        statement="The Casoratian has a closed form.",
    ),
    LabelledRoute(
        route_id="erdos251.propositions",
        statement="The file contains 101 named closed propositions.",
    ),
)


def check_fixtures() -> int:
    """The fixtures are the part of this script that fails."""
    checks = 0

    errors = labels.audit_routes([UNLABELLED])
    require(
        any("no negative-knowledge label" in error for error in errors),
        "an unlabelled route write-off escaped the vocabulary check",
    )
    checks += 1

    errors = labels.audit_routes([UNEVIDENCED])
    require(
        any("carries no evidence" in error for error in errors),
        "a label with no evidence escaped the vocabulary check",
    )
    checks += 1

    errors = labels.audit_routes([OUT_OF_VOCABULARY])
    require(
        any("not in the vocabulary" in error for error in errors),
        "an out-of-vocabulary label escaped the vocabulary check",
    )
    checks += 1

    try:
        labels.check_label("route_is_over")
    except UnknownLabel:
        checks += 1
    else:
        raise AssertionError("check_label accepted an unknown label")

    errors = labels.audit_routes(WELL_FORMED)
    require(
        not errors,
        f"well-formed labelled routes must pass: {errors}",
    )
    checks += 1

    require(
        len({route.label for route in WELL_FORMED}) == len(
            labels.NEGATIVE_KNOWLEDGE_LABELS
        ),
        "the fixtures must exercise every label in the vocabulary",
    )
    checks += 1

    errors = labels.audit_routes(NOT_A_ROUTE_CLAIM)
    require(
        not errors,
        "ordinary mathematical uses of the closure words must not be flagged: "
        f"{errors}",
    )
    checks += 1

    require(
        labels.uses_closure_language("The greedy route is dead.") == "dead",
        "closure language applied to a route must be detected",
    )
    require(
        labels.uses_closure_language("The set is closed.") is None,
        "closure language with no route must not be detected",
    )
    checks += 1

    require(
        "empirical_deprioritisation" in labels.NON_PROOF_LABELS,
        "the decision label must be marked as a non-proof label",
    )
    checks += 1
    return checks


def write_report(path: Path, uses: list[labels.ClosureUse]) -> None:
    """Emit the surface report the operator reads before rewriting prose."""
    payload = {
        "schema": "plectis.negative-knowledge-surface-report/1",
        "vocabulary": sorted(labels.NEGATIVE_KNOWLEDGE_LABELS),
        "non_proof_labels": sorted(labels.NON_PROOF_LABELS),
        "closure_words": list(labels.CLOSURE_WORDS),
        "surfaces_scanned": sorted(SURFACES),
        "unlabelled_route_closure_uses": [asdict(use) for use in uses],
        "gate_disposition": "report_only_pre_existing_text",
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, default=DEFAULT_REPORT)
    args = parser.parse_args(argv)

    checks = check_fixtures()
    uses = labels.scan_surfaces(SURFACES)
    write_report(args.report, uses)

    print(
        "test_negative_knowledge_labels: "
        f"{checks} labelling fixtures held; "
        f"{len(uses)} unlabelled route-closure use(s) found across "
        f"{len(SURFACES)} reader surfaces; report at {args.report}"
    )
    for use in uses:
        print(f"  REPORT {use.surface}:{use.line} [{use.word}] {use.text}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
