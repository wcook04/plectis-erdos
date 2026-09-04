#!/usr/bin/env python3
"""Test stored q-Apéry selectors against the normalized analytic consumer."""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import importlib.util
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
    linear_form_bracket,
)
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


REMAINDER_PATH = SCRIPT_DIR / "verify_qapery_remainder_at_three_halves.py"
spec = importlib.util.spec_from_file_location("qapery_remainder", REMAINDER_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load q-Apéry remainder checker")
remainder_source = importlib.util.module_from_spec(spec)
spec.loader.exec_module(remainder_source)


SOURCE_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
REMAINDER_REF = str(REMAINDER_PATH.relative_to(REPO_ROOT))
DETERMINANTAL_REF = "system/lib/formal_math_determinantal.py"
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "QAperySelectorNormalizedRemainderLab.md"
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
    "erdos1049_qapery_selector_normalized_remainder_receipt.json"
)
BRACKET_TERMS = 24000
BRACKET_BITS = 30000


def encode_fraction(value: Fraction) -> dict[str, str]:
    numerator = value.numerator
    denominator = value.denominator
    digest = hashlib.sha256(f"{numerator}/{denominator}".encode("ascii")).hexdigest()
    return {
        "sign": "negative" if numerator < 0 else "positive" if numerator > 0 else "zero",
        "numerator_bit_length": str(abs(numerator).bit_length()),
        "denominator_bit_length": str(denominator.bit_length()),
        "sha256": digest,
    }


def log_abs(value: Fraction) -> float:
    if value == 0:
        return -math.inf
    return math.log(abs(value.numerator)) - math.log(value.denominator)


def absolute_bounds(
    lower: Fraction, upper: Fraction
) -> tuple[Fraction, Fraction] | None:
    if lower <= 0 <= upper:
        return None
    values = sorted((abs(lower), abs(upper)))
    return values[0], values[1]


def compute() -> dict[str, Any]:
    payload = json.loads((REPO_ROOT / INPUT_RECEIPT_REF).read_text(encoding="utf-8"))
    f_lower, f_upper = remainder_source.f_three_halves_bracket(
        terms=BRACKET_TERMS, bits=BRACKET_BITS
    )
    rows = []
    for record in payload["selector_pair_records"]:
        modulus = int(record["modulus"])
        selectors = []
        for selector in record["selectors"]:
            pair = (
                int(selector["combined_pair"]["A"]),
                int(selector["combined_pair"]["B"]),
            )
            normalized = divide_row_sum_exact(pair, modulus)
            lower, upper = linear_form_bracket(normalized, f_lower, f_upper)
            bounds = absolute_bounds(lower, upper)
            bracket_excludes_zero = bounds is not None
            absolute_lower, absolute_upper = (
                bounds
                if bounds is not None
                else (Fraction(0), max(abs(lower), abs(upper)))
            )
            selectors.append(
                {
                    "support_size": int(selector["support_size"]),
                    "normalized_pair": {
                        "A": str(normalized[0]),
                        "B": str(normalized[1]),
                    },
                    "normalized_pair_bit_lengths": [
                        abs(normalized[0]).bit_length(),
                        abs(normalized[1]).bit_length(),
                    ],
                    "normalized_remainder_lower": encode_fraction(lower),
                    "normalized_remainder_upper": encode_fraction(upper),
                    "absolute_normalized_remainder_lower": encode_fraction(
                        absolute_lower
                    ),
                    "absolute_normalized_remainder_upper": encode_fraction(
                        absolute_upper
                    ),
                    "normalized_remainder_bracket_excludes_zero": (
                        bracket_excludes_zero
                    ),
                    "log_absolute_normalized_remainder_lower": log_abs(
                        absolute_lower
                    ),
                    "absolute_normalized_remainder_lower_exceeds_one": (
                        absolute_lower > 1
                    ),
                }
            )
        rows.append(
            {
                "tail_start": int(record["tail_start"]),
                "modulus_v2": int(record["modulus_v2"]),
                "modulus_v3": int(record["modulus_v3"]),
                "selectors": selectors,
                "both_normalized_remainders_lower_exceed_one": all(
                    selector["absolute_normalized_remainder_lower_exceeds_one"]
                    for selector in selectors
                ),
            }
        )
    return {
        "consumer_identity": (
            "If F=a/q is rational and (A,B)=M(A',B'), then "
            "q(B'F-A')=B'a-qA' is an integer. Two noncollinear normalized "
            "forms both tending to zero would force a contradiction."
        ),
        "selector_rows": rows,
        "all_starts_one_through_four_have_both_remainders_above_one": all(
            row["both_normalized_remainders_lower_exceed_one"]
            for row in rows
            if row["tail_start"] >= 1
        ),
        "mechanism_verdict": (
            "stored_modular_only_selector_pairs_fail_normalized_remainder_consumer"
        ),
        "next_construction": (
            "Include normalized analytic remainder in the lattice objective; "
            "modular collision plus coefficient cap alone is insufficient."
        ),
    }


def build_payload() -> dict[str, Any]:
    result = compute()
    contract = build_experiment_contract(
        problem_id="erdos_1049",
        target_statement="Prove irrationality of the Lambert value at q=3/2.",
        claim_ceiling=(
            "Exact evaluation eliminates only the stored modular-only selector "
            "pairs as analytic consumers. It does not exclude an analytic-aware "
            "congruence lattice, future selector pairs, or irrationality."
        ),
        hypothesis_id="stored_qapery_selectors_supply_small_normalized_forms",
        hypothesis_statement=(
            "After division by their certified local modulus, the two stored "
            "noncollinear selector forms are small enough to feed the rationality "
            "integer lower bound."
        ),
        probe_id="exact_normalized_selector_remainder_bracket",
        probe_question=(
            "Do the stored modular collision witnesses remain small after their "
            "common modulus is removed?"
        ),
        computation=(
            "Divide both exact selector coordinates by the certified modulus, "
            "evaluate B'F-A' against a 30000-bit rational bracket, and retain exact "
            "absolute lower bounds."
        ),
        falsifier=(
            "At starts one through four, both exact absolute normalized-remainder "
            "lower bounds exceed one."
        ),
        stop_condition=(
            "Once every stored post-initial pair fails the necessary subunit "
            "consumer, do not extend the same modular-only selector sequence."
        ),
        survival_consequence=(
            "Subunit normalized forms would justify seeking an all-start decay law."
        ),
        falsification_consequence=(
            "Replace the lattice objective itself with joint local and real control."
        ),
        consumer_ref=PACKET_REF,
        analysis_refs=[ANALYSIS_REF],
        source_refs=[SOURCE_REF, REMAINDER_REF, DETERMINANTAL_REF],
        input_receipt_refs=[INPUT_RECEIPT_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "After exact modulus division, both stored selector remainders exceed "
            "one in absolute value at every tail start 1,2,3,4; their logarithmic "
            "lower bounds grow from about 64 to thousands."
        ),
        progress_class="mechanism_eliminated",
        decision_basis=(
            "The calculation tests the actual rationality consumer rather than "
            "another modular-collision horizon."
        ),
        next_analytic_target=(
            "Construct two noncollinear congruence relations while minimizing the "
            "normalized real remainder as part of the lattice norm."
        ),
        resource_bounds={
            "tail_start_maximum": 4,
            "configured_tail_start_count": 5,
            "remainder_bracket_terms": BRACKET_TERMS,
            "remainder_bracket_bits": BRACKET_BITS,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos1049-qapery-selector-normalized-remainder/1",
        "status": "exact_stored_selector_consumer_no_go",
        "result": result,
        "experiment_contract": contract,
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [
                SOURCE_REF,
                REMAINDER_REF,
                DETERMINANTAL_REF,
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
