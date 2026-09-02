#!/usr/bin/env python3
"""Certify two non-collinear q-Apéry selectors at each displayed tail.

One modular selector can accidentally lie in the analytic remainder nullspace.
Two selectors whose exact integer coefficient-pair sums have nonzero determinant
cannot both do so for the same real value.  This checker extracts exact LLL
witnesses at the first four starts and independently replays a stored BKZ-16
binary witness at the first LLL blind spot.  The finite starts do not prove an
all-start selector theorem.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[5]
SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_determinantal import (  # noqa: E402
    ModularSignedRelation,
    collinear_scalar_coordinates,
    find_short_collinear_relations,
    first_noncollinear_relation_pair,
    minor,
)
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
)


BASE_CHECKER_PATH = SCRIPT_DIR / "check_qapery_selector_remainder_escape.py"
spec = importlib.util.spec_from_file_location("qapery_selector_base", BASE_CHECKER_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load q-Apéry selector base checker")
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)


SOURCE_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
BASE_CHECKER_REF = str(BASE_CHECKER_PATH.relative_to(REPO_ROOT))
DETERMINANTAL_REF = "system/lib/formal_math_determinantal.py"
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "PrimitivePluckerComputationalLab.md"
)
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "TwoSelectorRemainderEscape.lean"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "research_packet.json"
)
PRIOR_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_qapery_selector_remainder_escape_receipt.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_qapery_two_selector_escape_receipt.json"
)
START_CONFIGS = ((0, 1), (1, 1), (2, 1), (3, 1), (4, 1))
BKZ_BINARY_PAIR_START_FOUR = (
    (
        0, 0, 1, 0, -1, 0, 1, 0, 0, 0, -1, -1, 0, -1, 0, 0, 0, -1,
        0, 1, 0, -1, 1, -1, -1, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1, 0,
        -1, -1, 0, 1, -1, 0, 0, 0, -1, 0, 0, 0, 1, -1, -1, 0, 0, 0,
        0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ),
    (
        0, 0, 0, 0, 1, -1, -1, 0, 0, 0, 0, -1, 0, -1, -1, 0, 0, 1,
        0, 0, 0, 0, 1, 1, -1, 0, 1, 0, 1, 1, -1, 0, 0, 1, -1, -1,
        0, 0, 0, 1, 0, -1, -1, 1, 0, 0, 0, 1, 0, -1, 1, -1, -1, 0,
        1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ),
)


def replay_relation(
    family: list[tuple[int, int]], modulus: int, coefficients: tuple[int, ...]
) -> ModularSignedRelation:
    """Replay a discovered selector in both exact integer channels."""

    if len(coefficients) != len(family):
        raise AssertionError("selector width does not match the q-Apéry family")
    scalars = collinear_scalar_coordinates(family, modulus)
    row_sum = (
        sum(value * row[0] for value, row in zip(coefficients, family)),
        sum(value * row[1] for value, row in zip(coefficients, family)),
    )
    if row_sum[0] % modulus or row_sum[1] % modulus:
        raise AssertionError("stored selector failed exact two-channel replay")
    return ModularSignedRelation(coefficients, scalars, modulus, row_sum)


def relation_record(start: int, relation: Any) -> dict[str, Any]:
    coefficients = relation.coefficients
    return {
        "support_size": sum(value != 0 for value in coefficients),
        "coefficients": list(coefficients),
        "positive_selector_indices": [
            start + i for i, value in enumerate(coefficients) if value == 1
        ],
        "negative_selector_indices": [
            start + i for i, value in enumerate(coefficients) if value == -1
        ],
        "weighted_selector_terms": [
            {"index": start + i, "coefficient": value}
            for i, value in enumerate(coefficients)
            if value != 0
        ],
        "combined_pair": {
            "A": str(relation.row_sum[0]),
            "B": str(relation.row_sum[1]),
        },
        "combined_pair_modulus_remainders": [
            relation.row_sum[0] % relation.modulus,
            relation.row_sum[1] % relation.modulus,
        ],
    }


def build_result() -> dict[str, Any]:
    maximum_index = max(
        start + (3 * start * start + 3 * start + 1) + 2 * (start + 1)
        for start, _ in START_CONFIGS
    )
    rows = base.primitive_rows(maximum_index)
    records = []
    for start, coefficient_bound in START_CONFIGS:
        two_depth = 3 * start * start + 3 * start + 1
        three_depth = start + 1
        width = two_depth + 2 * three_depth
        modulus = 2**two_depth * 3**three_depth
        family = rows[start : start + width]
        relations = find_short_collinear_relations(
            family,
            modulus,
            max_abs_coefficient=coefficient_bound,
            lll_delta=base.LLL_DELTA,
            lll_last_coordinate_weight=base.LLL_LAST_COORDINATE_WEIGHT,
        )
        if start == 4:
            pair = tuple(
                replay_relation(family, modulus, coefficients)
                for coefficients in BKZ_BINARY_PAIR_START_FOUR
            )
            selector_source = "fpylll_bkz16_stored_exact_replay"
        else:
            pair = first_noncollinear_relation_pair(relations)
            selector_source = "sympy_exact_lll_reduced_basis"
        if pair is None:
            raise AssertionError(
                f"bounded reduced basis has no non-collinear pair at start {start}"
            )
        determinant = minor(pair[0].row_sum, pair[1].row_sum)
        if determinant == 0:
            raise AssertionError("selected exact coefficient pairs are collinear")
        records.append(
            {
                "tail_start": start,
                "row_count": width,
                "modulus": modulus,
                "modulus_v2": two_depth,
                "modulus_v3": three_depth,
                "max_abs_coefficient": coefficient_bound,
                "bounded_reduced_basis_relation_count": len(relations),
                "selector_source": selector_source,
                "selectors": [
                    relation_record(start, relation) for relation in pair
                ],
                "exact_pair_determinant": str(determinant),
                "exact_pair_determinant_nonzero": True,
                "analytic_consequence": (
                    "For every real F, at least one of B1*F-A1 and B2*F-A2 "
                    "is nonzero."
                ),
            }
        )

    summary = (
        "At every q-Apéry tail start s=0,1,2,3,4, two coefficient-one selectors "
        "have exact integer coefficient-pair sums with nonzero determinant. The "
        "s=4 pair is an exact replay of a BKZ-16 discovery that the prior exact "
        "LLL reduced basis did not expose. In every record the two analytic "
        "remainders cannot vanish simultaneously for any real value."
    )
    return {
        "schema": "erdos1049-qapery-two-selector-escape/3",
        "problem_id": "erdos_1049",
        "claim_ceiling": (
            "Exact finite binary two-selector analytic-nullspace escape at starts "
            "0,1,2,3,4; no "
            "all-start selector theorem, asymptotic height estimate, or "
            "irrationality theorem."
        ),
        "parameters": {
            "tail_start_coefficient_bounds": [
                {"tail_start": start, "max_abs_coefficient": bound}
                for start, bound in START_CONFIGS
            ],
            "lll_delta": base.LLL_DELTA,
            "lll_last_coordinate_weight": base.LLL_LAST_COORDINATE_WEIGHT,
            "start_four_discovery_backend": {
                "library": "fpylll",
                "library_version": "0.6.4",
                "reduction": "LLL(delta=0.99) followed by BKZ block size 16",
                "modular_coordinate_weight": base.LLL_LAST_COORDINATE_WEIGHT,
                "binary_relations_exposed": 6,
                "authority": "stored coefficients independently replayed by this checker",
            },
        },
        "selector_pair_records": records,
        "all_displayed_starts_have_rank_two_exact_image": True,
        "result_summary": summary,
        "mechanism_effect": (
            "Replace numerical bracketing of one selected remainder by an exact "
            "rank-two image target: prove two bounded modular selectors with "
            "non-collinear coefficient-pair sums at every tail start. The start-4 "
            "binary pair eliminates the only observed coefficient-cap separation "
            "and makes stronger lattice reduction part of the computational route."
        ),
        "consequence_decisions": [
            {
                "decision": "update_now",
                "files": [
                    SOURCE_REF,
                    ANALYSIS_REF,
                    PACKET_REF,
                    str(DEFAULT_OUTPUT.relative_to(REPO_ROOT)),
                    "formal_math/erdos257_period_noncollapse/ErdosProblems/"
                    "assimilation_manifest.json",
                ],
                "reason": (
                    "Bind the exact binary witness, backend recipe, mechanism "
                    "classification, and frontier consequence together."
                ),
            },
            {
                "decision": "verified_no_change",
                "files": [
                    LEAN_REF,
                    "formal_math/erdos257_period_noncollapse/prior_art_routes/"
                    "erdos1049_rational_base_lambert_v0.json",
                ],
                "reason": (
                    "The Lean rank-two consumer is already source-independent, and "
                    "the prior-art route does not encode the finite selector-cap boundary."
                ),
            },
            {
                "decision": "outside_scope",
                "files": [
                    "state/formal_math_research_operations",
                    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243",
                    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249",
                ],
                "reason": "Generic lattice and receipt vocabulary only; no q-Apéry selector dependency.",
            },
            {
                "decision": "defer_with_reason",
                "files": ["tools/meta/factory/build_lean_mathematics_microcosm_projection.py"],
                "reason": "Refresh the generated navigation projection after the source commit has a stable identity.",
            },
        ],
        "experiment_contract": build_experiment_contract(
            problem_id="erdos_1049",
            target_statement="Prove irrationality of the Lambert value at q=3/2.",
            claim_ceiling=(
                "Finite exact binary rank-two selector image at starts 0,1,2,3,4; "
                "no all-start theorem or "
                "irrationality conclusion."
            ),
            hypothesis_id="start_four_binary_rank_two_requires_coefficient_cap_two",
            hypothesis_statement=(
                "At the first exact-LLL blind spot s=4, every coefficient-one "
                "modular selector pair has collinear exact coefficient-pair image, "
                "so rank-two escape requires coefficient cap two."
            ),
            probe_id="bkz_binary_pair_exact_replay",
            probe_question=(
                "Does a stronger lattice backend expose two binary selectors at "
                "s=4 with non-collinear exact coefficient-pair sums?"
            ),
            computation=(
                "Generate exact primitive recurrence rows; reduce the weighted "
                "modular lattice with fpylll LLL(delta=0.99) and BKZ-16; store two "
                "binary coefficient vectors; regenerate and replay both integer "
                "channels and their exact determinant without trusting BKZ output."
            ),
            falsifier=(
                "Two bounded selectors in the same modular kernel whose exact "
                "coefficient-pair determinant is nonzero."
            ),
            stop_condition=(
                "After separating exact-image rank from coefficient-cap effects, "
                "replace finite extension by an all-start quantitative two-selector "
                "existence theorem."
            ),
            survival_consequence=(
                "A genuine cap-two boundary would separate the cardinality-proved "
                "binary collision supply from the rank-two analytic consumer."
            ),
            falsification_consequence=(
                "A replayed binary rank-two pair eliminates the observed cap-two "
                "boundary and identifies the prior zero count as reduced-basis "
                "exposure debt."
            ),
            consumer_ref=LEAN_REF,
            consumer_declarations=[
                "ErdosProblems.Erdos1049.twoSelector_one_remainder_ne_zero"
            ],
            analysis_refs=[ANALYSIS_REF, PACKET_REF],
            source_refs=[SOURCE_REF, BASE_CHECKER_REF, DETERMINANTAL_REF],
            input_receipt_refs=[PRIOR_RECEIPT_REF],
            result_status="exact_one_way_result",
            result_summary=summary,
            progress_class="mechanism_eliminated",
            decision_basis=(
                "Every recorded pair is independently replayed in both integer "
                "channels modulo 2^S*3^R and has nonzero exact determinant; the "
                "start-4 BKZ discovery is stored as coefficients rather than trusted "
                "through floating-point or lattice-reduction output."
            ),
            next_analytic_target=(
                "Prove an all-start supply of two bounded selector collisions with "
                "rank-two exact image and quantitative height control."
            ),
        ),
        "sources": [
            source_record(REPO_ROOT, ref)
            for ref in [SOURCE_REF, BASE_CHECKER_REF, DETERMINANTAL_REF, ANALYSIS_REF, LEAN_REF]
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(build_result(), indent=2, sort_keys=True) + "\n"
    output = args.output.resolve()
    if args.check:
        if not output.exists() or output.read_text(encoding="utf-8") != rendered:
            print(f"stale or missing receipt: {output}", file=sys.stderr)
            return 1
        print(json.dumps({"status": "current", "output": str(output)}))
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(output)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
