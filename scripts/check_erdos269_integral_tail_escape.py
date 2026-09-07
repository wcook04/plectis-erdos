#!/usr/bin/env python3
"""Probe the exact denominator-one branch of the Erdős #269 tail dichotomy.

If the genuine normalized source tail ever reaches an integer, every later
state is a positive integer following the actual dyadic affine recurrence.
For a window whose accumulated base exceeds the proved tail cap, the endpoint
state must equal the least positive source residue.  This checker measures the
new denominator-one question: after that first base-clear event, how many
further actual blocks can the canonical integer state remain below the cap?

The finite result selects an all-scale modular-classification target.  It is
not itself a cofinal theorem or an irrationality proof.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT))

from formal_math.erdos257_period_noncollapse.scripts.check_erdos269_dyadic_windows import (  # noqa: E402
    build_dyadic_blocks,
    certificate,
)
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos269_integral_tail_escape.py"
)
WINDOW_ENGINE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos269_dyadic_windows.py"
)
TAIL_LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "DyadicShellSummability.lean"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "ResidueEscape.lean"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "DyadicWindowComputationalLab.md"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "research_packet.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos269_integral_tail_escape_receipt.json"
)


def scan(max_start: int, max_length: int) -> dict[str, Any]:
    blocks = build_dyadic_blocks(max_start + max_length)
    length_histogram: Counter[int] = Counter()
    delay_histogram: Counter[int] = Counter()
    failures: list[int] = []
    maximal_delay_examples: list[dict[str, Any]] = []
    maximal_delay = -1

    for start in range(1, max_start + 1):
        first_clear: int | None = None
        trajectory: list[dict[str, int | bool | None]] = []
        hit: dict[str, int | bool | None] | None = None
        for length in range(1, max_length + 1):
            current = certificate(blocks, 1, start, length)
            block_base, block_digit, _ = blocks[start + length - 2]
            row = {
                "length": length,
                "last_block_base": block_base,
                "last_block_digit": block_digit,
                "window_base": current["window_base"],
                "canonical_state": current["least_positive_residue"],
                "tail_cap": current["short_bound"],
                "base_clears_cap": current["base_clears_bound"],
                "state_escapes_cap": current["residue_escapes"],
            }
            trajectory.append(row)
            if current["base_clears_bound"] and first_clear is None:
                first_clear = length
            if current["consumer_fires"]:
                hit = current
                break

        if hit is None or first_clear is None:
            failures.append(start)
            continue

        minimal_length = length
        delay = minimal_length - first_clear
        length_histogram[minimal_length] += 1
        delay_histogram[delay] += 1
        example = {
            "dyadic_start": start,
            "first_base_clear_length": first_clear,
            "escape_length": minimal_length,
            "post_clear_delay": delay,
            "post_clear_trajectory": trajectory[first_clear - 1 :],
        }
        if delay > maximal_delay:
            maximal_delay = delay
            maximal_delay_examples = [example]
        elif delay == maximal_delay and len(maximal_delay_examples) < 16:
            maximal_delay_examples.append(example)

    return {
        "parameters": {
            "denominator": 1,
            "min_dyadic_start": 1,
            "max_dyadic_start": max_start,
            "max_window_length": max_length,
        },
        "tested_start_count": max_start,
        "starts_without_escape_certificate": failures,
        "all_tested_starts_escape": not failures,
        "minimal_escape_length_histogram": dict(sorted(length_histogram.items())),
        "post_clear_delay_histogram": dict(sorted(delay_histogram.items())),
        "maximal_post_clear_delay": maximal_delay,
        "maximal_delay_examples": maximal_delay_examples,
        "three_transition_hypothesis_survives": not failures and maximal_delay <= 3,
    }


def build_payload(max_start: int, max_length: int) -> dict[str, Any]:
    result = scan(max_start, max_length)
    if not result["all_tested_starts_escape"]:
        status = "exact_finite_counterexample_to_bounded_window_supply"
        summary = "A tested dyadic start has no denominator-one escape certificate."
    elif result["three_transition_hypothesis_survives"]:
        status = "exact_denominator_one_mechanism_opening"
        summary = (
            "Every tested denominator-one orbit escapes within three transitions "
            "after its window base first clears the analytic tail cap."
        )
    else:
        status = "exact_counterexample_to_three_transition_hypothesis"
        summary = (
            "The denominator-one branch escapes in the tested range, but a start "
            "survives more than three transitions after first base-clear."
        )

    contract = build_experiment_contract(
        problem_id="erdos_269",
        target_statement=(
            "Exclude the exact integral-state branch of the genuine normalized "
            "{2,3,5} dyadic source tail."
        ),
        claim_ceiling=(
            "Exact finite denominator-one mechanism map only. The scan neither "
            "proves an all-scale delay bound nor excludes every integral tail state."
        ),
        hypothesis_id="denominator_one_three_transition_post_clear_escape",
        hypothesis_statement=(
            "For the actual source digits with B=1, once a local window base first "
            "exceeds the proved tail cap, its canonical state escapes that cap "
            "within at most three further affine transitions."
        ),
        probe_id="exact_integral_tail_post_clear_automaton",
        probe_question=(
            "Does the sole integral branch exhibit a fixed post-clear transition "
            "bound that is absent from general-denominator affine cylinders?"
        ),
        computation=(
            "For every configured dyadic start, compose exact actual block bases "
            "and digits, locate the first base-clear window, and follow the least "
            "positive denominator-one residue until it exceeds the analytic cap."
        ),
        falsifier=(
            "One exact start with no certificate in the configured window or with "
            "post-clear delay at least four."
        ),
        stop_condition=(
            "Stop at the configured structural map; do not enlarge the horizon as "
            "a substitute for proving or refuting the three-transition law."
        ),
        survival_consequence=(
            "Seek an all-scale finite modular classification of the at-most-four "
            "post-clear states, using the source floor-sum digits and cap recurrence."
        ),
        falsification_consequence=(
            "Extract the first longer survivor as the new recurrent-cone object and "
            "abandon a fixed three-transition proof."
        ),
        consumer_ref=CONSUMER_REF,
        consumer_declarations=[
            "ErdosProblems.Erdos269.dyadicShellTsumTail_integer_or_cofinal_far",
            "ErdosProblems.Erdos269.leastPositiveResidue_windowForcing_eq_carry",
        ],
        analysis_refs=[ANALYSIS_REF, PACKET_REF, TAIL_LEAN_REF, CONSUMER_REF],
        source_refs=[SOURCE_REF, WINDOW_ENGINE_REF],
        resource_bounds={
            "min_dyadic_start": 1,
            "max_dyadic_start": max_start,
            "max_window_length": max_length,
        },
        result_status="exact_one_way_result",
        result_summary=summary,
        progress_class="mechanism_opened" if result["three_transition_hypothesis_survives"] else "mechanism_eliminated",
        decision_basis=(
            "The probe tests a denominator-one transition law, not a larger copy "
            "of the general denominator rectangle."
        ),
        next_analytic_target=(
            "Prove the all-scale three-transition post-clear law from the exact "
            "source digit and tail-cap recurrences."
            if result["three_transition_hypothesis_survives"]
            else "Analyze the first longer survivor as a genuine expanding-error "
            "cone and abandon every proof that assumes a three-transition cap."
        ),
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos269-integral-tail-escape/1",
        "status": status,
        "experiment_contract": contract,
        "result": result,
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [SOURCE_REF, WINDOW_ENGINE_REF, TAIL_LEAN_REF, CONSUMER_REF, ANALYSIS_REF, PACKET_REF]
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
    parser.add_argument("--max-start", type=int, default=3_000)
    parser.add_argument("--max-length", type=int, default=16)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.max_start < 1 or args.max_length < 1:
        parser.error("scan bounds must be positive")
    return emit(build_payload(args.max_start, args.max_length), args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
