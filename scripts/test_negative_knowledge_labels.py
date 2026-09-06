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


# --- contextual classification -----------------------------------------------

NEGATED_CLOSURE = (
    "A strategy requiring the transformed observations to match anchors is "
    "NOT closed.",
    "The repair route is not closed; it survives under one inequality.",
    "This attack is never dead while the certificate supply is open.",
)
QUOTED_INFORMAL_CLOSURE = (
    "No declaration instantiates the concrete shifted channels, so 'the raw "
    "shifted-channel determinant route is closed' is an informal application, "
    "not formalised content.",
    "The note reports `the greedy route is dead`, which is not proved here.",
)
IDENTIFIER_ONLY = (
    "depth29_cutoff26_promotion_impossible blocks one promotion of one window "
    "and the run continues at cutoff 25 to depth 51.",
    "The lemma route_closed_of_rank_one is stated for an arbitrary family.",
)
STILL_A_CLOSURE_CLAIM = (
    "The cyclotomic lattice route is dead.",
    "No declaration proves the hypothesis, and the window-control approach is "
    "closed.",
    "The determinant route is closed, and nothing else is.",
)


def check_contextual_classification() -> int:
    """Three ordinary sentences must stop reading as closure claims."""
    checks = 0
    for sentence in NEGATED_CLOSURE:
        require(
            labels.sentence_closure_word(sentence) is None,
            f"a route said NOT to be closed was counted as closed: {sentence}",
        )
    checks += 1

    for sentence in QUOTED_INFORMAL_CLOSURE:
        require(
            labels.sentence_closure_word(sentence) is None,
            f"a quoted informal closure was counted as a closure claim: {sentence}",
        )
    checks += 1

    for sentence in IDENTIFIER_ONLY:
        require(
            labels.sentence_closure_word(sentence) is None,
            f"a declaration name was counted as closure prose: {sentence}",
        )
    checks += 1

    # The contextual rules must not swallow the real cases.
    for sentence in STILL_A_CLOSURE_CLAIM:
        require(
            labels.sentence_closure_word(sentence) is not None,
            f"a real closure claim stopped being detected: {sentence}",
        )
    checks += 1
    return checks


def check_disposition_binding() -> int:
    """A route the ledger already disposes must not read as unlabelled."""
    checks = 0
    frontier = {
        "bare_equivalences": [{"node": "certificate_supply_is_equivalent_to_249"}],
        "excluded_from_nonrecurring_with_reason": [
            {"node": "totient_denominator_exclusion_ladder", "reason": "no improvement"}
        ],
        "open_antecedents": [{"id": "OA249-block-certificate-supply"}],
    }
    claims = {"claims": [{"id": "certificate_reduction", "status": "conditional reduction"}]}
    dispositions = labels.route_dispositions(frontier, claims)
    require(
        dispositions["certificate_supply_is_equivalent_to_249"]
        == "target_equivalent_reformulation",
        "a bare equivalence must dispose as a target-equivalent reformulation",
    )
    require(
        dispositions["totient_denominator_exclusion_ladder"]
        == "empirical_deprioritisation",
        "an exclusion with a reason must dispose as a deprioritisation",
    )
    require(
        dispositions["OA249-block-certificate-supply"] == "conditional_reduction",
        "an open antecedent must dispose as a conditional reduction",
    )
    require(
        dispositions["certificate_reduction"] == "conditional_reduction",
        "a conditional-reduction claim row must dispose as one",
    )
    checks += 1

    uses = [
        labels.ClosureUse(
            surface="docs/semantic/frontier.json",
            line=1,
            word="closed",
            text="the certificate_supply_is_equivalent_to_249 route is closed",
        ),
        labels.ClosureUse(
            surface="docs/RESULTS.md",
            line=2,
            word="dead",
            text="the sparse anchor route is dead",
        ),
    ]
    disposed, residual = labels.split_by_disposition(uses, dispositions)
    require(
        [row["route_id"] for row in disposed]
        == ["certificate_supply_is_equivalent_to_249"],
        "a disposed route must be folded out of the residual set",
    )
    require(
        [use.line for use in residual] == [2],
        "an undisposed route must stay in the residual set",
    )
    checks += 1

    require(
        not labels.route_dispositions({}, {}),
        "an empty ledger must dispose nothing rather than defaulting to a label",
    )
    checks += 1
    return checks


def write_report(
    path: Path,
    residual: list[labels.ClosureUse],
    disposed: list[dict],
    dispositions: dict[str, str],
) -> None:
    """Emit the surface report the operator reads before rewriting prose."""
    payload = {
        "schema": "plectis.negative-knowledge-surface-report/2",
        "vocabulary": sorted(labels.NEGATIVE_KNOWLEDGE_LABELS),
        "non_proof_labels": sorted(labels.NON_PROOF_LABELS),
        "closure_words": list(labels.CLOSURE_WORDS),
        "surfaces_scanned": sorted(SURFACES),
        "contextual_exclusions": [
            "negated closure, where a route is said not to be closed",
            "a quoted informal closure in a sentence that states its limit",
            "a declaration name carrying a closure word",
        ],
        "reviewed_route_disposition_count": len(dispositions),
        "closure_uses_already_disposed": disposed,
        "unlabelled_route_closure_uses": [asdict(use) for use in residual],
        "gate_disposition": "report_only_pre_existing_text",
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n")


def load_dispositions() -> dict[str, str]:
    """Read the dispositions the repository already records."""
    frontier_path = ROOT / "docs" / "semantic" / "frontier.json"
    claims_path = ROOT / "docs" / "claims.json"
    frontier = json.loads(frontier_path.read_text()) if frontier_path.is_file() else {}
    claims = json.loads(claims_path.read_text()) if claims_path.is_file() else {}
    return labels.route_dispositions(frontier, claims)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, default=DEFAULT_REPORT)
    args = parser.parse_args(argv)

    checks = (
        check_fixtures()
        + check_contextual_classification()
        + check_disposition_binding()
    )
    dispositions = load_dispositions()
    uses = labels.scan_surfaces(SURFACES)
    disposed, residual = labels.split_by_disposition(uses, dispositions)
    write_report(args.report, residual, disposed, dispositions)

    print(
        "test_negative_knowledge_labels: "
        f"{checks} labelling fixtures held; "
        f"{len(uses)} route-closure use(s) across {len(SURFACES)} reader "
        f"surfaces, {len(disposed)} already disposed by one of "
        f"{len(dispositions)} reviewed route dispositions, "
        f"{len(residual)} unlabelled residual; report at {args.report}"
    )
    for row in disposed:
        print(
            f"  DISPOSED {row['surface']}:{row['line']} [{row['word']}] "
            f"{row['route_id']} -> {row['label']}"
        )
    for use in residual:
        print(f"  REPORT {use.surface}:{use.line} [{use.word}] {use.text}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
