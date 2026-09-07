#!/usr/bin/env python3
"""Test a two-step integer-gap Lyapunov law for Erdős #269.

The already-landed denominator-one computation follows the sole branch left by
the bounded-radix dichotomy: an exact integral normalized tail.  Once a window
base first exceeds the analytic cap, its possible positive integer endpoint is
the canonical least-positive residue ``rho``.  While that state remains below
the cap ``C``, define the integer gap ``g = C - rho``.

For consecutive source blocks the exact affine update has the form

    g' = b * g - h,
    h = b * C - C' - d.

This checker tests the structurally different producer that within two source
transitions every still-trapped post-clear state either escapes or reaches a
strictly smaller nonnegative gap.  An all-scale proof of that statement would
exclude an infinite integral tail by descent on ``g``; it does not assume a
uniform escape-time bound.  The finite scan can open or eliminate that proof
geometry, but cannot prove the all-scale statement.
"""

from __future__ import annotations

import argparse
import json
import sys
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
    "check_erdos269_integral_tail_gap_descent.py"
)
WINDOW_ENGINE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos269_dyadic_windows.py"
)
PRIOR_CHECKER_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos269_integral_tail_escape.py"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "IntegralTailStructureLab.md"
)
LEAN_RECURRENCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "DyadicOrderedTailRecurrence.lean"
)
LEAN_CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "DyadicShellSummability.lean"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "research_packet.json"
)
PRIOR_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos269_integral_tail_escape_receipt.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos269_integral_tail_structure_receipt.json"
)
DESCENT_WINDOW = 2


def _trajectory(
    blocks: list[tuple[int, int, int]], start: int, max_length: int
) -> tuple[int | None, list[dict[str, int | bool]]]:
    first_clear: int | None = None
    rows: list[dict[str, int | bool]] = []
    for length in range(1, max_length + 1):
        current = certificate(blocks, 1, start, length)
        cap = int(current["short_bound"])
        state = int(current["least_positive_residue"])
        row: dict[str, int | bool] = {
            "length": length,
            "last_block_base": int(current["last_block_base"]),
            "last_block_digit": int(current["last_block_digit"]),
            "window_base": int(current["window_base"]),
            "canonical_state": state,
            "tail_cap": cap,
            "base_clears_cap": bool(current["base_clears_bound"]),
            "state_escapes_cap": bool(current["residue_escapes"]),
            "gap": cap - state,
        }
        rows.append(row)
        if row["base_clears_cap"] and first_clear is None:
            first_clear = length
        if bool(current["consumer_fires"]):
            break
    return first_clear, rows


def scan(max_start: int, max_length: int) -> dict[str, Any]:
    blocks = build_dyadic_blocks(max_start + max_length)
    starts_without_terminal_escape: list[int] = []
    one_step_violations: list[dict[str, Any]] = []
    two_step_violations: list[dict[str, Any]] = []
    identity_failures: list[dict[str, Any]] = []
    trapped_position_count = 0
    one_step_descent_count = 0
    two_step_resolved_count = 0
    maximum_descent_wait = 0
    maximum_descent_wait_examples: list[dict[str, Any]] = []
    minimum_charge: tuple[int, int, int] | None = None

    for start in range(1, max_start + 1):
        first_clear, rows = _trajectory(blocks, start, max_length)
        if first_clear is None or not bool(rows[-1]["state_escapes_cap"]):
            starts_without_terminal_escape.append(start)
            continue

        post_clear = rows[first_clear - 1 :]
        for left, right in zip(post_clear, post_clear[1:]):
            # The literal zero-lift affine identity is required only while the
            # successor remains trapped.  The terminal escaping residue may
            # wrap modulo the enlarged window base, and escape itself already
            # resolves the Lyapunov alternative.
            if bool(right["state_escapes_cap"]):
                continue
            base = int(right["last_block_base"])
            digit = int(right["last_block_digit"])
            charge = (
                base * int(left["tail_cap"])
                - int(right["tail_cap"])
                - digit
            )
            predicted = base * int(left["gap"]) - charge
            if predicted != int(right["gap"]):
                identity_failures.append(
                    {
                        "dyadic_start": start,
                        "from_length": int(left["length"]),
                        "predicted_gap": predicted,
                        "observed_gap": int(right["gap"]),
                    }
                )
            charge_key = (charge, start, int(left["length"]))
            if minimum_charge is None or charge_key < minimum_charge:
                minimum_charge = charge_key

        # The terminal escaping row has negative gap.  At every prior row the
        # state is trapped and the gap is a nonnegative integer.
        for index, row in enumerate(post_clear[:-1]):
            trapped_position_count += 1
            initial_gap = int(row["gap"])
            wait: int | None = None
            for offset in range(1, min(DESCENT_WINDOW, len(post_clear) - index - 1) + 1):
                later = post_clear[index + offset]
                if bool(later["state_escapes_cap"]) or int(later["gap"]) < initial_gap:
                    wait = offset
                    break
            if wait == 1:
                one_step_descent_count += 1
            else:
                one_step_violations.append(
                    {
                        "dyadic_start": start,
                        "from_length": int(row["length"]),
                        "initial_gap": initial_gap,
                        "next_row": post_clear[index + 1],
                    }
                )
            if wait is None:
                two_step_violations.append(
                    {
                        "dyadic_start": start,
                        "from_length": int(row["length"]),
                        "initial_gap": initial_gap,
                        "lookahead": post_clear[
                            index + 1 : index + DESCENT_WINDOW + 1
                        ],
                    }
                )
            else:
                two_step_resolved_count += 1
                if wait > maximum_descent_wait:
                    maximum_descent_wait = wait
                    maximum_descent_wait_examples = [
                        {
                            "dyadic_start": start,
                            "from_length": int(row["length"]),
                            "initial_gap": initial_gap,
                            "resolution_offset": wait,
                            "resolution_row": post_clear[index + wait],
                        }
                    ]
                elif wait == maximum_descent_wait and len(maximum_descent_wait_examples) < 12:
                    maximum_descent_wait_examples.append(
                        {
                            "dyadic_start": start,
                            "from_length": int(row["length"]),
                            "initial_gap": initial_gap,
                            "resolution_offset": wait,
                            "resolution_row": post_clear[index + wait],
                        }
                    )

    return {
        "parameters": {
            "min_dyadic_start": 1,
            "max_dyadic_start": max_start,
            "max_window_length": max_length,
            "descent_window": DESCENT_WINDOW,
        },
        "tested_start_count": max_start,
        "starts_without_terminal_escape": starts_without_terminal_escape,
        "all_tested_starts_reach_terminal_escape": not starts_without_terminal_escape,
        "gap_recurrence_identity_failure_count": len(identity_failures),
        "gap_recurrence_identity_failures": identity_failures[:12],
        "minimum_source_charge": list(minimum_charge) if minimum_charge else None,
        "trapped_post_clear_position_count": trapped_position_count,
        "one_step_strict_descent_or_escape_count": one_step_descent_count,
        "one_step_violation_count": len(one_step_violations),
        "first_one_step_violations": one_step_violations[:12],
        "two_step_strict_descent_or_escape_count": two_step_resolved_count,
        "two_step_violation_count": len(two_step_violations),
        "first_two_step_violations": two_step_violations[:12],
        "maximum_observed_descent_wait": maximum_descent_wait,
        "maximum_descent_wait_examples": maximum_descent_wait_examples,
        "two_step_gap_descent_candidate_survives": (
            not starts_without_terminal_escape
            and not identity_failures
            and not two_step_violations
        ),
    }


def build_payload(max_start: int, max_length: int) -> dict[str, Any]:
    result = scan(max_start, max_length)
    survives = bool(result["two_step_gap_descent_candidate_survives"])
    if survives:
        status = "exact_finite_two_step_gap_descent_mechanism_opening"
        summary = (
            "Every tested trapped post-clear state either escapes or reaches a "
            "strictly smaller nonnegative integer cap gap within two source "
            "transitions; the one-step law is tested separately."
        )
        progress_class = "mechanism_opened"
        next_target = (
            "Prove the two-step gap descent directly from the ordered source "
            "digit and quadratic cap recurrences. Integer descent would then "
            "exclude the exact-integral normalized tail branch."
        )
    else:
        status = "exact_counterexample_to_two_step_gap_descent"
        summary = (
            "An exact trapped post-clear state survives two source transitions "
            "without reaching a smaller cap gap, eliminating the proposed "
            "two-step Lyapunov mechanism."
        )
        progress_class = "mechanism_eliminated"
        next_target = (
            "Use the first exact violation to test a source-conditioned or "
            "nonlocal descent functional; do not increase the window constant."
        )

    contract = build_experiment_contract(
        problem_id="erdos_269",
        target_statement=(
            "Exclude the exact integral-state branch of the genuine normalized "
            "{2,3,5} dyadic source tail."
        ),
        claim_ceiling=(
            "Exact finite Lyapunov-mechanism decision only. Survival in the "
            "configured scan is not an all-scale descent theorem or an "
            "irrationality proof."
        ),
        hypothesis_id="denominator_one_two_step_integer_gap_descent",
        hypothesis_statement=(
            "After first base-clear, every still-trapped denominator-one state "
            "either escapes or reaches a strictly smaller integer cap gap within "
            "two actual source transitions."
        ),
        probe_id="exact_post_clear_gap_charge_recurrence",
        probe_question=(
            "Can a state-dependent integer Lyapunov descent replace the false "
            "uniform three-transition escape bound?"
        ),
        computation=(
            "Replay every denominator-one canonical post-clear trajectory; verify "
            "g'=b*g-h with h=b*C-C'-d exactly; and test strict gap descent or "
            "escape within the predeclared two-transition window at every trapped "
            "position."
        ),
        falsifier=(
            "One exact trapped position whose next two source states neither "
            "escape nor have cap gap strictly below the starting gap."
        ),
        stop_condition=(
            "Stop after deciding the two-step Lyapunov law. Do not replace a "
            "counterexample by a larger lookahead constant."
        ),
        survival_consequence=(
            "An all-scale proof gives well-founded descent on a nonnegative "
            "integer and excludes every infinite integral-tail orbit, closing "
            "the remaining branch of the Lean-checked dichotomy."
        ),
        falsification_consequence=(
            "The first witness eliminates all proofs based on this two-step cap-gap "
            "Lyapunov function and forces a genuinely nonlocal functional."
        ),
        consumer_ref=LEAN_CONSUMER_REF,
        consumer_declarations=[
            "ErdosProblems.Erdos269.dyadicShellTsumTail_integer_or_cofinal_far",
            "ErdosProblems.Erdos269.dyadicNormalizedShellTsumTailR235_succ",
        ],
        analysis_refs=[ANALYSIS_REF, PACKET_REF, LEAN_RECURRENCE_REF],
        source_refs=[SOURCE_REF, WINDOW_ENGINE_REF, PRIOR_CHECKER_REF],
        input_receipt_refs=[PRIOR_RECEIPT_REF],
        resource_bounds={
            "min_dyadic_start": 1,
            "max_dyadic_start": max_start,
            "max_window_length": max_length,
            "descent_window": DESCENT_WINDOW,
        },
        result_status="exact_one_way_result",
        result_summary=summary,
        progress_class=progress_class,
        decision_basis=(
            "The probe tests a state-dependent well-founded descent criterion, "
            "not a longer fixed escape horizon or a renamed residue target."
        ),
        next_analytic_target=next_target,
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos269-integral-tail-gap-descent/1",
        "status": status,
        "result": result,
        "experiment_contract": contract,
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [
                SOURCE_REF,
                WINDOW_ENGINE_REF,
                PRIOR_CHECKER_REF,
                ANALYSIS_REF,
                LEAN_RECURRENCE_REF,
                LEAN_CONSUMER_REF,
                PACKET_REF,
                PRIOR_RECEIPT_REF,
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
    parser.add_argument("--max-start", type=int, default=3_000)
    parser.add_argument("--max-length", type=int, default=16)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.max_start < 1 or args.max_length < 3:
        parser.error("need positive starts and a window length of at least three")
    return emit(build_payload(args.max_start, args.max_length), args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
