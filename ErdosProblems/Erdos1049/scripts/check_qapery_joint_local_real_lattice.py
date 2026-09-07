#!/usr/bin/env python3
"""Certify analytic-aware unimodular recombinations of q-Apéry selectors."""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import sys
from typing import Any


if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


REPO_ROOT = Path(__file__).resolve().parents[5]
SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_determinantal import (  # noqa: E402
    divide_row_sum_exact,
    find_consecutive_small_linear_forms,
    minor,
)
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


SOURCE_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
REMAINDER_REF = str(
    (SCRIPT_DIR / "verify_qapery_remainder_at_three_halves.py").relative_to(
        REPO_ROOT
    )
)
DETERMINANTAL_REF = "system/lib/formal_math_determinantal.py"
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "TwoSelectorRemainderEscape.lean"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "QAperyJointLocalRealLatticeLab.md"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "research_packet.json"
)
INPUT_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_qapery_two_selector_escape_receipt.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_qapery_joint_local_real_lattice_receipt.json"
)
BRACKET_TERMS = 18000
BRACKET_BITS = 22000
MAX_TAIL_START = 3


def f_three_halves_bracket(terms: int, bits: int) -> tuple[Fraction, Fraction]:
    """Replay the canonical fixed-point bracket with incremental exact powers."""

    scale = 1 << bits
    total = 0
    two_power = 1
    three_power = 1
    for _ in range(1, terms + 1):
        two_power *= 2
        three_power *= 3
        total += (scale * two_power) // (three_power - two_power)
    lower = Fraction(total, scale)
    two_power *= 2
    three_power *= 3
    tail_ratio = Fraction(two_power, three_power)
    tail_upper = 3 * tail_ratio / (1 - tail_ratio)
    return lower, lower + Fraction(terms, scale) + tail_upper


def encode_fraction(value: Fraction) -> dict[str, Any]:
    digest = hashlib.sha256(
        f"{value.numerator}/{value.denominator}".encode("ascii")
    ).hexdigest()
    return {
        "sign": "negative" if value < 0 else "positive" if value > 0 else "zero",
        "numerator_bit_length": abs(value.numerator).bit_length(),
        "denominator_bit_length": value.denominator.bit_length(),
        "log_absolute_value": (
            math.log(abs(value.numerator)) - math.log(value.denominator)
            if value
            else -math.inf
        ),
        "sha256": digest,
    }


def compute() -> dict[str, Any]:
    payload = json.loads((REPO_ROOT / INPUT_RECEIPT_REF).read_text(encoding="utf-8"))
    f_lower, f_upper = f_three_halves_bracket(BRACKET_TERMS, BRACKET_BITS)
    records = []
    for record in payload["selector_pair_records"]:
        if int(record["tail_start"]) > MAX_TAIL_START:
            continue
        modulus = int(record["modulus"])
        base_rows = tuple(
            divide_row_sum_exact(
                (
                    int(selector["combined_pair"]["A"]),
                    int(selector["combined_pair"]["B"]),
                ),
                modulus,
            )
            for selector in record["selectors"]
        )
        if len(base_rows) != 2:
            raise AssertionError("expected exactly two stored selectors")
        forms = find_consecutive_small_linear_forms(
            base_rows, f_lower, f_upper, absolute_ceiling=Fraction(1)
        )
        if forms is None:
            raise AssertionError(
                f"no consecutive certified subunit forms at start {record['tail_start']}"
            )
        coefficient_determinant = minor(forms[0].coefficients, forms[1].coefficients)
        base_determinant = minor(base_rows[0], base_rows[1])
        recombined_determinant = minor(forms[0].row_sum, forms[1].row_sum)
        if abs(coefficient_determinant) != 1:
            raise AssertionError("adjacent convergents were not unimodular")
        if recombined_determinant != coefficient_determinant * base_determinant:
            raise AssertionError("recombination determinant identity failed")
        coefficient_height = max(
            abs(value) for form in forms for value in form.coefficients
        )
        base_denominator_l1_height = sum(abs(row[1]) for row in base_rows)
        certified_common_remainder_ceiling = max(
            max(abs(form.lower), abs(form.upper)) for form in forms
        )
        forced_coefficient_height_lower_bound = Fraction(
            abs(base_determinant),
            2 * base_denominator_l1_height,
        ) / certified_common_remainder_ceiling
        if coefficient_height < forced_coefficient_height_lower_bound:
            raise AssertionError("determinant-forced height lower bound failed")
        records.append(
            {
                "tail_start": int(record["tail_start"]),
                "modulus_v2": int(record["modulus_v2"]),
                "modulus_v3": int(record["modulus_v3"]),
                "base_normalized_determinant": str(base_determinant),
                "coefficient_determinant": coefficient_determinant,
                "recombined_normalized_determinant": str(recombined_determinant),
                "determinant_magnitude_preserved": (
                    abs(recombined_determinant) == abs(base_determinant)
                ),
                "height_decay_balance": {
                    "base_denominator_l1_height": str(base_denominator_l1_height),
                    "unimodular_coefficient_height": str(coefficient_height),
                    "certified_common_remainder_ceiling": encode_fraction(
                        certified_common_remainder_ceiling
                    ),
                    "determinant_forced_coefficient_height_lower_bound": (
                        encode_fraction(forced_coefficient_height_lower_bound)
                    ),
                    "observed_height_satisfies_forced_lower_bound": (
                        coefficient_height >= forced_coefficient_height_lower_bound
                    ),
                    "observed_to_forced_height_ratio": encode_fraction(
                        Fraction(coefficient_height, 1)
                        / forced_coefficient_height_lower_bound
                    ),
                },
                "forms": [
                    {
                        "continued_fraction_index": form.continued_fraction_index,
                        "base_selector_coefficients": [
                            str(value) for value in form.coefficients
                        ],
                        "coefficient_bit_lengths": [
                            abs(value).bit_length() for value in form.coefficients
                        ],
                        "combined_normalized_pair": {
                            "A": str(form.row_sum[0]),
                            "B": str(form.row_sum[1]),
                        },
                        "remainder_lower": encode_fraction(form.lower),
                        "remainder_upper": encode_fraction(form.upper),
                        "remainder_bracket_excludes_zero": not form.lower <= 0 <= form.upper,
                        "absolute_remainder_upper_below_one": (
                            max(abs(form.lower), abs(form.upper)) < 1
                        ),
                    }
                    for form in forms
                ],
            }
        )
    return {
        "records": records,
        "all_displayed_starts_have_two_nonzero_subunit_forms": all(
            all(
                form["remainder_bracket_excludes_zero"]
                and form["absolute_remainder_upper_below_one"]
                for form in record["forms"]
            )
            for record in records
        ),
        "all_recombinations_are_unimodular": all(
            abs(record["coefficient_determinant"]) == 1 for record in records
        ),
        "all_records_satisfy_determinant_height_tradeoff": all(
            record["height_decay_balance"][
                "observed_height_satisfies_forced_lower_bound"
            ]
            for record in records
        ),
        "mechanism_verdict": "analytic_aware_unimodular_recombination_opens",
        "asymptotic_verdict": (
            "generic_unimodular_decay_is_not_an_independent_irrationality_engine"
        ),
        "lean_theorems": [
            "twoSelector_det_height_decay_tradeoff",
            "twoSelector_unimodular_height_decay_tradeoff",
            "rational_integerLinearForm_gap",
            "rational_twoSelector_remainder_gap",
            "rational_twoSelector_not_both_tendsto_zero",
        ],
        "remaining_barrier": (
            "Any surviving all-start decay theorem must use source-specific "
            "q-Apery structure beyond generic continued-fraction recombination. "
            "At a rational target the 1/q gap forbids both non-collinear integral "
            "forms from tending to zero, so cofinal decay already entails the "
            "irrationality conclusion."
        ),
    }


def build_payload() -> dict[str, Any]:
    result = compute()
    contract = build_experiment_contract(
        problem_id="erdos_1049",
        target_statement="Prove irrationality of the Lambert value at q=3/2.",
        claim_ceiling=(
            "Exact finite analytic-aware recombinations at starts 0 through 3; no "
            "all-start height theorem, decay theorem, or irrationality conclusion."
        ),
        hypothesis_id="analytic_coordinate_repairs_modular_selector_consumer",
        hypothesis_statement=(
            "Unimodular continued-fraction recombination of each stored noncollinear "
            "selector pair can retain local divisibility and rank while making both "
            "normalized real forms nonzero and smaller than one."
        ),
        probe_id="exact_joint_local_real_unimodular_recombination",
        probe_question=(
            "Does optimizing the actual normalized real coordinate repair the stored "
            "selectors without sacrificing their exact rank-two certificate?"
        ),
        computation=(
            "Divide the two stored selector pairs by their exact local modulus; take "
            "adjacent continued-fraction convergents to the ratio of their midpoint "
            "real forms; certify both recombined forms against a 22000-bit rational "
            "bracket and replay the determinant identity exactly."
        ),
        falsifier=(
            "At every displayed start, two adjacent recombinations have nonzero exact "
            "brackets strictly inside (-1,1), and their coefficient determinant is ±1."
        ),
        stop_condition=(
            "After the finite consumer is repaired at all stored starts, stop tuning "
            "the modular-only LLL objective and target coefficient-height growth."
        ),
        survival_consequence=(
            "Failure would eliminate this two-dimensional analytic recombination route."
        ),
        falsification_consequence=(
            "The normalized-consumer failure is not structural: an analytic-aware "
            "unimodular step repairs it while preserving noncollinearity."
        ),
        consumer_ref=PACKET_REF,
        analysis_refs=[ANALYSIS_REF],
        source_refs=[SOURCE_REF, REMAINDER_REF, DETERMINANTAL_REF, LEAN_REF],
        input_receipt_refs=[INPUT_RECEIPT_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "Every tested tail start 0 through 3 admits two certified nonzero "
            "subunit normalized forms obtained by a determinant-preserving "
            "unimodular recombination of the stored selector pair."
        ),
        progress_class="mechanism_opened",
        decision_basis=(
            "The probe changes the construction objective and exactly tests the "
            "rationality consumer rather than extending the finite tail horizon."
        ),
        next_analytic_target=(
            "Replace generic continued-fraction optimization by a source-specific "
            "q-Apery theorem that meets the determinant-forced height cost with a "
            "source-derived upper bound and proves cofinal decay without assuming "
            "irrationality."
        ),
        resource_bounds={
            "tail_start_maximum": MAX_TAIL_START,
            "configured_tail_start_count": MAX_TAIL_START + 1,
            "remainder_bracket_terms": BRACKET_TERMS,
            "remainder_bracket_bits": BRACKET_BITS,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos1049-qapery-joint-local-real-lattice/1",
        "status": "exact_analytic_aware_mechanism_opened",
        "result": result,
        "experiment_contract": contract,
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [
                SOURCE_REF,
                REMAINDER_REF,
                DETERMINANTAL_REF,
                LEAN_REF,
                ANALYSIS_REF,
                PACKET_REF,
                INPUT_RECEIPT_REF,
            ]
        ],
    }


def emit(payload: dict[str, Any], output: Path, check: bool) -> int:
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if check:
        if not output.exists() or output.read_text(encoding="utf-8") != rendered:
            print(f"stale receipt: {output}", file=sys.stderr)
            return 1
        print(json.dumps({"status": "current", "output": str(output)}))
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(output)}))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    return emit(build_payload(), args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
