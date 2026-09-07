#!/usr/bin/env python3
"""Mine strict-record divisor ancestry from a bound exact replay receipt.

For a strict defect record ``n``, every earlier record successor ``r + 1``
that divides ``n + 1`` contributes all of its selected divisors to ``n + 1``.
This script tests whether the best such inherited load nearly pays the record
repair bill.  It consumes the immutable two-million-rank exact replay rather
than reconstructing the greedy word again.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import platform
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
SOURCE_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "twenty_one_computational_structure_receipt_2000002.json"
)
DEFAULT_SOURCE = REPO_ROOT / SOURCE_REF
RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "twenty_one_record_ancestor_inheritance_receipt.json"
)
DEFAULT_RECEIPT = REPO_ROOT / RECEIPT_REF
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/"
    "TwentyOneRecordAncestorInheritance.md"
)
MOTIVATING_ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/"
    "TwentyOneComputationalStructureLab.md"
)
COMPANION_ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/"
    "TwentyOneRecordDivisorSupplyNoGo.md"
)
EXPECTED_SOURCE_SCHEMA = "twenty_one_computational_structure_lab_v0"
EXPECTED_SOURCE_RANKS = 2_000_002
EXPECTED_SOURCE_RECORD_COUNT = 39
EXPECTED_SOURCE_PAYLOAD_SHA256 = (
    "c3b2d899da07d668fcd712e342b83648d63c3b8cae15235ba007dc55ae6ea7b7"
)
SOURCE_BINDING_COMMIT = "3900ab8eef1edbb8243cac19ddae45b00e0ca3ac"
TESTED_ADDITIVE_CONSTANT = 8


def canonical_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def canonical_payload_sha256(payload: dict[str, Any]) -> str:
    encoded = json.dumps(
        payload, separators=(",", ":"), sort_keys=True
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def resolve_path(value: str | None, default: Path) -> Path:
    if value is None:
        return default
    path = Path(value)
    return path if path.is_absolute() else REPO_ROOT / path


def load_source(path: Path) -> dict[str, Any]:
    source = json.loads(path.read_text())
    claimed_digest = source.get("receipt_payload_sha256")
    digest_payload = dict(source)
    digest_payload.pop("receipt_payload_sha256", None)
    computed_digest = canonical_payload_sha256(digest_payload)
    if claimed_digest != computed_digest:
        raise AssertionError(
            "source receipt payload digest mismatch: "
            f"claimed={claimed_digest} computed={computed_digest}"
        )
    if source.get("schema") != EXPECTED_SOURCE_SCHEMA:
        raise AssertionError(f"unexpected source schema: {source.get('schema')}")
    if source.get("parameters", {}).get("ranks") != EXPECTED_SOURCE_RANKS:
        raise AssertionError("unexpected source horizon")
    if source.get("strict_record_count") != EXPECTED_SOURCE_RECORD_COUNT:
        raise AssertionError("unexpected source strict-record count")
    if claimed_digest != EXPECTED_SOURCE_PAYLOAD_SHA256:
        raise AssertionError("source receipt is not the bound historical artifact")
    return source


def build_receipt(source: dict[str, Any], source_path: Path) -> dict[str, Any]:
    records = source["strict_record_rows"]
    if len(records) != source["strict_record_count"]:
        raise AssertionError("strict-record row count mismatch")

    record_ranks = {int(row["rank"]) for row in records}
    rows: list[dict[str, Any]] = []
    genealogy_depth_by_rank: dict[int, int] = {}
    for index, row in enumerate(records):
        rank = int(row["rank"])
        successor = rank + 1
        repair_bill = int(row["defect"]) + int(row["successor_target_bit"])
        ancestors = []
        for prior in records[:index]:
            ancestor_successor = int(prior["successor"])
            if successor % ancestor_successor != 0:
                continue
            ancestors.append(
                {
                    "record_rank": int(prior["rank"]),
                    "record_defect": int(prior["defect"]),
                    "successor": ancestor_successor,
                    "selected_divisor_load": int(
                        prior["successor_selected_divisor_load"]
                    ),
                    "successor_quotient": successor // ancestor_successor,
                }
            )
        best = max(
            ancestors,
            key=lambda item: (
                item["selected_divisor_load"], -item["successor"]
            ),
            default=None,
        )
        canonical_parent = max(
            ancestors,
            key=lambda item: item["successor"],
            default=None,
        )
        ancestry_is_divisibility_chain = all(
            left["successor"] % right["successor"] == 0
            or right["successor"] % left["successor"] == 0
            for left_index, left in enumerate(ancestors)
            for right in ancestors[left_index + 1 :]
        )
        inherited_load = (
            int(best["selected_divisor_load"]) if best is not None else 0
        )
        canonical_parent_load = (
            int(canonical_parent["selected_divisor_load"])
            if canonical_parent is not None
            else 0
        )
        direct_parent = (rank - 1) // 2
        dyadic_parent = direct_parent if direct_parent in record_ranks else None
        canonical_parent_rank = (
            int(canonical_parent["record_rank"])
            if canonical_parent is not None
            else None
        )
        canonical_parent_defect = (
            int(canonical_parent["record_defect"])
            if canonical_parent is not None
            else None
        )
        genealogy_depth = (
            genealogy_depth_by_rank[canonical_parent_rank] + 1
            if canonical_parent_rank is not None
            else 0
        )
        genealogy_depth_by_rank[rank] = genealogy_depth
        rows.append(
            {
                "record_rank": rank,
                "record_defect": int(row["defect"]),
                "successor": successor,
                "successor_target_bit": int(row["successor_target_bit"]),
                "repair_bill": repair_bill,
                "actual_successor_selected_divisor_load": int(
                    row["successor_selected_divisor_load"]
                ),
                "actual_repair_margin": int(row["record_repair_margin"]),
                "dyadic_parent_record_rank": dyadic_parent,
                "record_class": (
                    "dyadic_child" if dyadic_parent is not None else "dyadic_root"
                ),
                "eligible_ancestor_count": len(ancestors),
                "eligible_ancestors": ancestors,
                "eligible_ancestors_form_divisibility_chain": (
                    ancestry_is_divisibility_chain
                ),
                "best_ancestor": best,
                "best_inherited_selected_divisor_load": inherited_load,
                "inherited_repair_margin": inherited_load - repair_bill,
                "required_additive_constant": max(0, repair_bill - inherited_load),
                "canonical_largest_successor_parent": canonical_parent,
                "canonical_parent_genealogy_depth": genealogy_depth,
                "canonical_parent_is_best_load_ancestor": (
                    canonical_parent_load == inherited_load
                ),
                "canonical_parent_inherited_repair_margin": (
                    canonical_parent_load - repair_bill
                ),
                "canonical_parent_required_additive_constant": max(
                    0, repair_bill - canonical_parent_load
                ),
                "canonical_parent_gp4_margin": (
                    4 * canonical_parent_defect - int(row["defect"])
                    if canonical_parent_defect is not None
                    else None
                ),
                "canonical_parent_gp7_over_2_margin": (
                    7 * canonical_parent_defect - 2 * int(row["defect"])
                    if canonical_parent_defect is not None
                    else None
                ),
            }
        )

    sharp_constant = max(
        int(row["required_additive_constant"]) for row in rows
    )
    sharp_rows = [
        row for row in rows
        if row["required_additive_constant"] == sharp_constant
    ]
    violations = [
        row for row in rows
        if row["inherited_repair_margin"] + TESTED_ADDITIVE_CONSTANT < 0
    ]
    if sharp_constant != TESTED_ADDITIVE_CONSTANT:
        raise AssertionError(
            f"expected sharp finite constant {TESTED_ADDITIVE_CONSTANT}, "
            f"found {sharp_constant}"
        )
    if violations:
        raise AssertionError("additive ancestor-inheritance candidate failed")
    if [int(row["record_rank"]) for row in sharp_rows] != [13_859]:
        raise AssertionError("unexpected sharp finite witness")

    canonical_parent_dominance_failures = [
        row
        for row in rows
        if not row["canonical_parent_is_best_load_ancestor"]
    ]
    if canonical_parent_dominance_failures:
        raise AssertionError(
            "largest eligible record successor did not maximize inherited load"
        )
    canonical_parent_violations = [
        row
        for row in rows
        if row["canonical_parent_inherited_repair_margin"]
        + TESTED_ADDITIVE_CONSTANT
        < 0
    ]
    if canonical_parent_violations:
        raise AssertionError("canonical-parent additive candidate failed")
    branching_ancestry_rows = [
        row
        for row in rows
        if not row["eligible_ancestors_form_divisibility_chain"]
    ]
    if not branching_ancestry_rows:
        raise AssertionError("expected a branching ancestry counterexample")
    if int(branching_ancestry_rows[0]["record_rank"]) != 139:
        raise AssertionError("unexpected first branching ancestry witness")

    parented_rows = [
        row
        for row in rows
        if row["canonical_largest_successor_parent"] is not None
    ]
    gp4_violations = [
        row for row in parented_rows if int(row["canonical_parent_gp4_margin"]) < 0
    ]
    gp7_over_2_violations = [
        row
        for row in parented_rows
        if int(row["canonical_parent_gp7_over_2_margin"]) < 0
    ]
    if gp4_violations or gp7_over_2_violations:
        raise AssertionError("genealogical multiplicative defect bound failed")
    sharp_genealogical_ratio = max(
        (
            Fraction(
                int(row["record_defect"]),
                int(row["canonical_largest_successor_parent"]["record_defect"]),
            ),
            int(row["record_rank"]),
        )
        for row in parented_rows
    )
    if sharp_genealogical_ratio != (Fraction(7, 2), 779):
        raise AssertionError(
            f"unexpected sharp genealogical ratio: {sharp_genealogical_ratio}"
        )
    maximum_genealogy_depth = max(
        int(row["canonical_parent_genealogy_depth"]) for row in rows
    )
    maximum_depth_record_ranks = [
        int(row["record_rank"])
        for row in rows
        if int(row["canonical_parent_genealogy_depth"])
        == maximum_genealogy_depth
    ]

    dyadic_rows = [row for row in rows if row["record_class"] == "dyadic_child"]
    root_rows = [row for row in rows if row["record_class"] == "dyadic_root"]
    nonnegative_rows = [
        row for row in rows if row["inherited_repair_margin"] >= 0
    ]
    source_display = (
        str(source_path.relative_to(REPO_ROOT))
        if source_path.is_relative_to(REPO_ROOT)
        else str(source_path)
    )
    payload: dict[str, Any] = {
        "schema": "twenty_one_record_ancestor_inheritance_v1",
        "parameters": {
            "source_ranks": int(source["parameters"]["ranks"]),
            "tested_additive_constant": TESTED_ADDITIVE_CONSTANT,
            "ancestor_definition": (
                "earlier strict record r whose successor r+1 divides the "
                "current record successor n+1"
            ),
        },
        "authority": {
            "script_ref": str(Path(__file__).resolve().relative_to(REPO_ROOT)),
            "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "analysis_ref": ANALYSIS_REF,
            "motivating_analysis_ref": MOTIVATING_ANALYSIS_REF,
            "companion_analysis_ref": COMPANION_ANALYSIS_REF,
            "source_receipt_ref": source_display,
            "source_receipt_payload_sha256": source["receipt_payload_sha256"],
            "source_receipt_binding_commit": SOURCE_BINDING_COMMIT,
            "source_itinerary_sha256": source["itinerary_sha256"],
            "source_script_ref": source["authority"]["script_ref"],
            "source_script_sha256": source["authority"]["script_sha256"],
            "python_version": platform.python_version(),
            "method": (
                "exact divisibility mining over strict-record rows from the "
                "digest-validated historical exact replay receipt"
            ),
            "floating_point_used": False,
        },
        "record_count": len(rows),
        "dyadic_child_count": len(dyadic_rows),
        "dyadic_root_count": len(root_rows),
        "nonnegative_inherited_margin_count": len(nonnegative_rows),
        "record_rows": rows,
        "ancestor_inheritance_candidate": {
            "id": "AI8",
            "statement": (
                "For every strict record n, A(n)+8 >= Q_n+t_(n+1), "
                "where A(n)=max f(r+1) over earlier strict records r with "
                "r+1 dividing n+1, and A(n)=0 if the set is empty."
            ),
            "finite_status": "verified_on_every_bound_two_million_rank_record",
            "tested_record_count": len(rows),
            "minimum_unshifted_inherited_margin": min(
                int(row["inherited_repair_margin"]) for row in rows
            ),
            "maximum_required_additive_constant": sharp_constant,
            "sharp_finite_witness_record_ranks": [
                int(row["record_rank"]) for row in sharp_rows
            ],
            "constant_seven_violation_count": sum(
                int(row["required_additive_constant"]) > 7 for row in rows
            ),
            "constant_eight_violation_count": len(violations),
            "constant_eight_violations": violations,
            "falsifier": (
                "a strict record with required_additive_constant greater "
                "than eight"
            ),
            "all_depth_consequence_if_proved": (
                "Divisor inclusion gives f(n+1)>=A(n), so Q_n<=f(n+1)+8 "
                "at every strict record.  For the last strict record n<=N, "
                "Q_N<=Q_n<=tau(n+1)+8<=2*sqrt(N+1)+8.  The Lean-checked "
                "subexponential-defect theorem then yields denominator-21 "
                "membership and infinite support."
            ),
        },
        "canonical_parent_candidate": {
            "id": "P8",
            "parent_definition": (
                "p(n)+1 is the numerically largest earlier strict-record "
                "successor dividing n+1; its inherited load is zero when "
                "no such successor exists"
            ),
            "statement": (
                "For every strict record n, f(p(n)+1)+8 >= "
                "Q_n+t_(n+1), with the absent-parent load defined as zero."
            ),
            "finite_status": "verified_on_every_bound_two_million_rank_record",
            "tested_record_count": len(rows),
            "records_with_parent_count": sum(
                row["canonical_largest_successor_parent"] is not None
                for row in rows
            ),
            "records_without_parent_ranks": [
                int(row["record_rank"])
                for row in rows
                if row["canonical_largest_successor_parent"] is None
            ],
            "maximum_parent_quotient": max(
                int(row["canonical_largest_successor_parent"]["successor_quotient"])
                for row in rows
                if row["canonical_largest_successor_parent"] is not None
            ),
            "maximum_required_additive_constant": max(
                int(row["canonical_parent_required_additive_constant"])
                for row in rows
            ),
            "constant_eight_violation_count": len(canonical_parent_violations),
            "constant_eight_violations": canonical_parent_violations,
            "falsifier": (
                "a strict record whose canonical largest-successor parent "
                "misses its repair bill by more than eight"
            ),
            "all_depth_consequence_if_proved": (
                "P8 directly gives Q_n<=f(n+1)+8 at every strict record by "
                "divisor inclusion, hence Q_N<=2*sqrt(N+1)+8 and the "
                "Lean-checked denominator-21 membership conclusion."
            ),
        },
        "largest_parent_load_dominance_candidate": {
            "id": "LPD",
            "statement": (
                "Among earlier strict-record successors dividing a current "
                "record successor, the numerically largest has maximum "
                "selected-divisor load."
            ),
            "finite_status": "verified_on_every_bound_two_million_rank_record",
            "tested_record_count": len(rows),
            "violation_count": len(canonical_parent_dominance_failures),
            "violations": canonical_parent_dominance_failures,
            "divisibility_chain_explanation": {
                "status": "falsified_on_actual_denominator_21_orbit",
                "branching_record_count": len(branching_ancestry_rows),
                "first_witness_record_rank": int(
                    branching_ancestry_rows[0]["record_rank"]
                ),
                "first_witness_eligible_successors": [
                    int(ancestor["successor"])
                    for ancestor in branching_ancestry_rows[0][
                        "eligible_ancestors"
                    ]
                ],
                "reason": (
                    "the eligible successors include incomparable divisors, "
                    "so load dominance is not automatic divisor inclusion"
                ),
            },
        },
        "genealogical_polynomial_candidate": {
            "id": "GP4",
            "statement": (
                "Every strict record n>19 has canonical divisor parent p(n), "
                "and Q_n <= 4*Q_p(n)."
            ),
            "stronger_finite_statement": (
                "Every tested parent edge satisfies 2*Q_n <= 7*Q_p(n)."
            ),
            "finite_status": "verified_on_every_bound_two_million_rank_edge",
            "tested_parent_edge_count": len(parented_rows),
            "parent_existence_after_seed_violation_count": sum(
                int(row["record_rank"]) > 19
                and row["canonical_largest_successor_parent"] is None
                for row in rows
            ),
            "gp4_violation_count": len(gp4_violations),
            "gp4_violations": gp4_violations,
            "gp7_over_2_violation_count": len(gp7_over_2_violations),
            "gp7_over_2_violations": gp7_over_2_violations,
            "sharp_finite_ratio": {
                "numerator": sharp_genealogical_ratio[0].numerator,
                "denominator": sharp_genealogical_ratio[0].denominator,
                "record_rank": sharp_genealogical_ratio[1],
            },
            "maximum_checked_genealogy_depth": maximum_genealogy_depth,
            "maximum_depth_record_ranks": maximum_depth_record_ranks,
            "falsifiers": [
                "a strict record above the finite seed with no earlier "
                "strict-record successor dividing its successor",
                "a canonical parent edge with Q_child > 4*Q_parent",
            ],
            "all_depth_consequence_if_proved": (
                "Each proper divisor-parent edge at least doubles the "
                "successor, so an n-record has genealogy depth at most "
                "log_2(n+1).  GP4 then gives Q_n=O((n+1)^2) at records, "
                "hence at every rank.  This polynomial bound feeds the "
                "Lean-checked subexponential-defect theorem and yields "
                "denominator-21 membership with infinite support."
            ),
            "proof_advantage": (
                "GP4 discards all selected-divisor load estimates and is "
                "strictly weaker than P8/RR as a target producer."
            ),
        },
        "class_summary": {
            "dyadic_child_minimum_inherited_margin": min(
                int(row["inherited_repair_margin"]) for row in dyadic_rows
            ),
            "dyadic_root_minimum_inherited_margin": min(
                int(row["inherited_repair_margin"]) for row in root_rows
            ),
            "negative_margin_record_ranks": [
                int(row["record_rank"])
                for row in rows
                if row["inherited_repair_margin"] < 0
            ],
        },
        "analytic_lineage": {
            "motivating_question": (
                "Can the positive dyadic inheritance mechanism be widened "
                "to root records using arbitrary divisor ancestry?"
            ),
            "machine_evidence_field": "record_rows",
            "consequence_field": (
                "canonical_parent_candidate."
                "all_depth_consequence_if_proved"
            ),
            "lean_consumers": source["authority"]["lean_consumers"],
        },
        "nonclaims": [
            "AI8 remains an all-depth conjecture, not a proof.",
            "P8 and LPD remain all-depth conjectures, not proofs.",
            "GP4 remains an all-depth conjecture, not a proof.",
            "The finite sharpness of eight need not persist at later records.",
            "This receipt does not by itself decide Erdos Problem 257.",
        ],
    }
    payload["canonical_payload_sha256"] = canonical_payload_sha256(payload)
    return payload


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", default=str(DEFAULT_SOURCE))
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--write", nargs="?", const=None, metavar="PATH")
    action.add_argument("--check", nargs="?", const=None, metavar="PATH")
    args = parser.parse_args()

    source_path = resolve_path(args.source, DEFAULT_SOURCE)
    payload = build_receipt(load_source(source_path), source_path)
    rendered = canonical_json(payload)
    argv = __import__("sys").argv
    if args.write is not None or "--write" in argv:
        path = resolve_path(args.write, DEFAULT_RECEIPT)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(rendered)
        print(
            canonical_json(
                {
                    "status": "written",
                    "path": str(path.relative_to(REPO_ROOT)),
                    "canonical_payload_sha256": payload[
                        "canonical_payload_sha256"
                    ],
                }
            ),
            end="",
        )
        return 0
    if args.check is not None or "--check" in argv:
        path = resolve_path(args.check, DEFAULT_RECEIPT)
        if path.read_text() != rendered:
            raise AssertionError(f"receipt drift: {path}")
        print(
            canonical_json(
                {
                    "status": "matched",
                    "path": str(path.relative_to(REPO_ROOT)),
                    "canonical_payload_sha256": payload[
                        "canonical_payload_sha256"
                    ],
                }
            ),
            end="",
        )
        return 0
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
