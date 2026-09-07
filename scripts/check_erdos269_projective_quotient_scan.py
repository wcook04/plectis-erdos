#!/usr/bin/env python3
"""Exact quotient-normalized projective-window probe for Erdős #269.

The checker scans only source-faithful dyadic windows for which the window
base clears the proved short bound and the canonical carry is both within that
bound and coprime to the reduced denominator.  For each denominator it records
the first pair violating projective coherence.  It also verifies the exact
factorization proved in Lean and tests whether centered quotient defects stay
in the conjectured quarter-modulus band.

The bounded rectangle is mechanism evidence, never a universal denominator or
cofinal-window theorem.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from math import gcd
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT))

from formal_math.erdos257_period_noncollapse.scripts.check_erdos269_dyadic_windows import (  # noqa: E402
    build_dyadic_blocks,
    short_bound,
    window,
)
from formal_math.erdos257_period_noncollapse.scripts.check_erdos269_projective_window_pair import (  # noqa: E402
    three_prime_height_at_dyadic_scale,
)
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos269_projective_quotient_scan.py"
)
WINDOW_ENGINE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos269_dyadic_windows.py"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "DyadicWindowComputationalLab.md"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "HalfHeightDenominatorTransport.lean"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos269_projective_quotient_scan_receipt.json"
)


def centered_residue(value: int, modulus: int) -> int:
    residue = value % modulus
    return residue - modulus if 2 * residue > modulus else residue


def endpoint_row(
    blocks: list[tuple[int, int, int]], denominator: int, start: int, end: int
) -> dict[str, int] | None:
    base, forcing, ending_index = window(blocks, start, end - start)
    bound = short_bound(denominator, ending_index)
    carry = (-denominator * forcing) % base or base
    if base <= bound or carry > bound or gcd(carry, denominator) != 1:
        return None
    quotient, remainder = divmod(carry + denominator * forcing, base)
    if remainder != 0:
        raise AssertionError(("nonintegral quotient", denominator, start, end))
    return {
        "start": start,
        "end": end,
        "window_base": base,
        "window_forcing": forcing,
        "ending_jump_index": ending_index,
        "short_bound": bound,
        "canonical_carry": carry,
        "ceiling_quotient": quotient,
        "start_height": three_prime_height_at_dyadic_scale(start),
        "endpoint_height": three_prime_height_at_dyadic_scale(end),
    }


def pair_witness(
    denominator: int, first: dict[str, int], second: dict[str, int]
) -> dict[str, Any]:
    quotient_defect = (
        first["ceiling_quotient"] * second["start_height"]
        - second["ceiling_quotient"] * first["start_height"]
    )
    projective_defect = (
        first["canonical_carry"] * second["endpoint_height"]
        - second["canonical_carry"] * first["endpoint_height"]
    )
    factored_defect = (
        first["window_base"]
        * second["window_base"]
        * quotient_defect
        + denominator
        * (
            second["window_forcing"]
            * first["start_height"]
            * first["window_base"]
            - first["window_forcing"]
            * second["start_height"]
            * second["window_base"]
        )
    )
    if projective_defect != factored_defect:
        raise AssertionError(("factorization mismatch", denominator, first, second))
    if (projective_defect - first["window_base"] * second["window_base"] * quotient_defect) % denominator:
        raise AssertionError(("modular factorization mismatch", denominator))
    centered = centered_residue(quotient_defect, denominator)
    return {
        "denominator": denominator,
        "first": first,
        "second": second,
        "quotient_defect": quotient_defect,
        "centered_quotient_defect": centered,
        "projective_defect_mod_denominator": projective_defect % denominator,
        "factorization_verified": True,
        "quarter_modulus_band_holds": 4 * abs(centered) <= denominator,
    }


def scan(max_denominator: int, max_end: int, max_span: int) -> dict[str, Any]:
    blocks = build_dyadic_blocks(max_end)
    tested = 0
    failures: list[dict[str, int]] = []
    quotient_histogram: Counter[int] = Counter()
    first_quarter_band_counterexample: dict[str, Any] | None = None
    furthest_centered_witness: dict[str, Any] | None = None
    endpoint_histogram: Counter[int] = Counter()

    for denominator in range(2, max_denominator + 1):
        if gcd(denominator, 30) != 1:
            continue
        tested += 1
        admissible: list[dict[str, int]] = []
        witness: dict[str, Any] | None = None
        for end in range(3, max_end + 1):
            for start in range(max(1, end - max_span), end):
                current = endpoint_row(blocks, denominator, start, end)
                if current is None:
                    continue
                for prior in admissible:
                    candidate = pair_witness(denominator, prior, current)
                    if candidate["projective_defect_mod_denominator"] != 0:
                        witness = candidate
                        break
                if witness is not None:
                    break
                admissible.append(current)
            if witness is not None:
                break

        if witness is None:
            failures.append(
                {"denominator": denominator, "admissible_endpoint_count": len(admissible)}
            )
            continue

        defect = int(witness["quotient_defect"])
        centered = int(witness["centered_quotient_defect"])
        quotient_histogram[defect] += 1
        endpoint_histogram[int(witness["second"]["end"])] += 1
        if not witness["quarter_modulus_band_holds"] and first_quarter_band_counterexample is None:
            first_quarter_band_counterexample = witness
        if (
            furthest_centered_witness is None
            or abs(centered) * int(furthest_centered_witness["denominator"])
            > abs(int(furthest_centered_witness["centered_quotient_defect"]))
            * denominator
        ):
            furthest_centered_witness = witness

    if first_quarter_band_counterexample is None:
        raise AssertionError("quarter-modulus hypothesis survived configured scan")
    if furthest_centered_witness is None:
        raise AssertionError("no projective witness found")

    return {
        "parameters": {
            "min_denominator": 2,
            "max_denominator": max_denominator,
            "coprime_to": 30,
            "max_endpoint_scale": max_end,
            "max_window_span": max_span,
        },
        "tested_denominator_count": tested,
        "denominators_without_projective_pair": failures,
        "all_tested_denominators_have_pair": not failures,
        "distinct_first_quotient_defect_count": len(quotient_histogram),
        "repeated_first_quotient_defect_count": sum(
            count - 1 for count in quotient_histogram.values() if count > 1
        ),
        "first_pair_endpoint_histogram": dict(sorted(endpoint_histogram.items())),
        "first_quarter_modulus_band_counterexample": first_quarter_band_counterexample,
        "furthest_centered_witness": furthest_centered_witness,
        "furthest_centered_ratio": {
            "numerator": abs(int(furthest_centered_witness["centered_quotient_defect"])),
            "denominator": int(furthest_centered_witness["denominator"]),
        },
    }


def build_receipt(max_denominator: int, max_end: int, max_span: int) -> dict[str, Any]:
    result = scan(max_denominator, max_end, max_span)
    contract = build_experiment_contract(
        problem_id="erdos_269",
        target_statement=(
            "Prove irrationality for the running-LCM series generated by the "
            "prime support {2,3,5}."
        ),
        claim_ceiling=(
            "Exact finite mechanism elimination and bounded projective-pair map; "
            "no universal denominator exclusion, cofinal pair supply, or irrationality proof."
        ),
        hypothesis_id="centered_projective_quotient_defects_stay_in_quarter_modulus_band",
        hypothesis_statement=(
            "After removing the window-base factors, the first locally admissible "
            "projective defect always has centered residue of magnitude at most B/4."
        ),
        probe_id="exact_projective_quotient_factorization_and_adversarial_scan",
        probe_question=(
            "Does quotient normalization turn projective incoherence into a uniformly "
            "small discrepancy suitable for a direct inequality proof?"
        ),
        computation=(
            "Enumerate actual {2,3,5} dyadic windows, retain only base-clear canonical "
            "carries within the proved short bound and coprime to B, verify the exact "
            "Lean factorization, and record each denominator's first incoherent pair."
        ),
        falsifier=(
            "One exact locally admissible pair whose centered normalized defect has "
            "magnitude greater than B/4."
        ),
        stop_condition=(
            "Stop once the quarter-band conjecture is falsified and the configured "
            "denominator rectangle is mapped; do not interpret the rectangle as cofinal."
        ),
        survival_consequence=(
            "A surviving quarter-band would justify seeking a uniform small-error "
            "ceiling inequality for the projective producer."
        ),
        falsification_consequence=(
            "The projective mechanism remains strong, but its producer must control "
            "full modular ceiling discrepancy rather than a small centered alphabet."
        ),
        consumer_ref=CONSUMER_REF,
        analysis_refs=[ANALYSIS_REF, CONSUMER_REF],
        source_refs=[SOURCE_REF, WINDOW_ENGINE_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "The exact scan falsifies the quarter-modulus normalized-defect hypothesis "
            "while retaining projective exclusions throughout the configured rectangle."
        ),
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos269-projective-quotient-scan/1",
        "status": "verified_exact_normalized_defect_mechanism_elimination",
        "experiment_contract": contract,
        "result": result,
        "consequence_decisions": [
            {
                "mechanism": "uniform_small_centered_quotient_defect",
                "decision": "eliminated_by_exact_counterexample",
            },
            {
                "mechanism": "full_modular_ceiling_discrepancy",
                "decision": "retained_as_projective_pair_producer_target",
            },
            {
                "mechanism": "universal_denominator_exclusion_or_irrationality",
                "decision": "not_claimed",
            },
        ],
        "source_records": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, WINDOW_ENGINE_REF),
            source_record(REPO_ROOT, ANALYSIS_REF),
            source_record(REPO_ROOT, CONSUMER_REF),
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
    parser.add_argument("--max-denominator", type=int, default=100_000)
    parser.add_argument("--max-end", type=int, default=40)
    parser.add_argument("--max-span", type=int, default=10)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.max_denominator < 2 or args.max_end < 3 or args.max_span < 1:
        parser.error("scan bounds are outside the supported positive range")
    return emit(
        build_receipt(args.max_denominator, args.max_end, args.max_span),
        args.output,
        args.check,
    )


if __name__ == "__main__":
    raise SystemExit(main())
