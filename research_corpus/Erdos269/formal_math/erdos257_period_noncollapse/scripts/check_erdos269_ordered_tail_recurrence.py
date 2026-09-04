#!/usr/bin/env python3
"""Replay the exact summable source-to-carry recurrence for Erdős #269.

The checker builds literal reciprocal running-height masses from independently
enumerated {2,3,5}-smooth points.  For a declared terminal dyadic scale it
forms every finite source tail and verifies

    X_(a+1) = b_a X_a - d_a,
    X_a = H(2^a) T_a / 2,

with exact ``Fraction`` arithmetic.  It also checks the quadratic digit and
polynomial-geometric shell majorants used by Lean to construct the genuine
infinite ``tsum`` tail.  Lean proves summability, the exact infinite-tail
recurrence, and its bounded-radix dichotomy; the finite replay is a regression
and source-convention check, not an infinitary claim.
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT))

from formal_math.erdos257_period_noncollapse.scripts.check_erdos269_block_mass_identity import (  # noqa: E402
    height235,
    smooth_values_through,
)
from formal_math.erdos257_period_noncollapse.scripts.check_erdos269_dyadic_windows import (  # noqa: E402
    build_dyadic_blocks,
)
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos269_ordered_tail_recurrence.py"
)
BLOCK_CHECKER_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos269_block_mass_identity.py"
)
RECURRENCE_LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "DyadicOrderedTailRecurrence.lean"
)
SUMMABILITY_LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "DyadicShellSummability.lean"
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
    "erdos269_ordered_tail_recurrence_receipt.json"
)


def frac(value: Fraction) -> dict[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


def build_payload(max_a: int) -> dict[str, object]:
    if max_a < 3:
        raise ValueError("max-a must be at least 3")
    blocks = build_dyadic_blocks(max_a)
    smooth = smooth_values_through(1 << (max_a + 1))
    shell_mass: dict[int, Fraction] = {}
    for a in range(1, max_a + 1):
        lo, hi = 1 << a, 1 << (a + 1)
        shell_mass[a] = sum(
            (Fraction(1, height235(x)) for x in smooth if lo <= x < hi),
            Fraction(),
        )

    tails: dict[int, Fraction] = {max_a + 1: Fraction()}
    for a in range(max_a, 0, -1):
        tails[a] = shell_mass[a] + tails[a + 1]
    states = {
        a: Fraction(height235(1 << a), 2) * tails[a]
        for a in range(1, max_a + 2)
    }

    rows = []
    max_digit_ratio = Fraction()
    max_digit_ratio_scale = 0
    for a in range(1, max_a + 1):
        base, digit, _ = blocks[a - 1]
        cleared_shell = Fraction(height235(1 << (a + 1)), 2) * shell_mass[a]
        predicted = base * states[a] - digit
        digit_ratio = Fraction(digit, (a + 1) ** 2)
        shell_majorant = Fraction(30 * (a + 1) ** 2, 1 << (a + 1))
        assert cleared_shell == digit
        assert states[a + 1] == predicted
        assert digit <= 15 * (a + 1) ** 2
        assert shell_mass[a] <= shell_majorant
        if digit_ratio > max_digit_ratio:
            max_digit_ratio = digit_ratio
            max_digit_ratio_scale = a
        rows.append(
            {
                "a": a,
                "block_base": base,
                "ordered_digit": digit,
                "shell_mass": frac(shell_mass[a]),
                "normalized_tail_state": frac(states[a]),
                "next_normalized_tail_state": frac(states[a + 1]),
                "cleared_shell_equals_digit": True,
                "affine_recurrence_verified": True,
                "quadratic_digit_majorant_verified": True,
                "polynomial_geometric_shell_majorant_verified": True,
            }
        )

    contract = build_experiment_contract(
        problem_id="erdos_269",
        target_statement=(
            "Bind the all-scale ordered {2,3,5} source digit into the actual "
            "normalized tail recurrence."
        ),
        claim_ceiling=(
            "Lean proves summability of the literal shell masses, constructs the "
            "genuine infinite tsum tail, and applies the bounded-radix dichotomy. "
            "The exact-integral-state branch remains open, so irrationality is not proved."
        ),
        hypothesis_id="ordered_source_digit_drives_normalized_tail",
        hypothesis_statement=(
            "For X_a=H(2^a)T_a/2, the literal dyadic shell decomposition gives "
            "X_(a+1)=b_a X_a-d_a with the existing ordered source digit d_a."
        ),
        probe_id="direct_finite_source_tail_replay",
        probe_question=(
            "Do independently enumerated smooth-point tails obey the claimed "
            "normalization and affine recurrence exactly?"
        ),
        computation=(
            "Enumerate literal smooth points, sum reciprocal running heights as "
            "Fractions, form all backward finite tails, and replay every recurrence."
        ),
        falsifier=(
            "Any scale where half the next endpoint height fails to clear the shell "
            "to d_a, or where the normalized states fail the affine update."
        ),
        stop_condition=(
            "Stop finite extension after exact convention and majorant replay; use "
            "the all-scale Lean dichotomy and rotate to integral-tail exclusion."
        ),
        survival_consequence=(
            "The existing bounded-radix dichotomy applies directly to the genuine "
            "infinite literal source tail."
        ),
        falsification_consequence=(
            "Reject the half-height normalization and repair the shell endpoint or digit."
        ),
        consumer_ref=SUMMABILITY_LEAN_REF,
        consumer_declarations=[
            "half_threePrimeHeight_mul_dyadicShellMassQ235",
            "dyadicNormalizedTailStateQ235_succ",
            "half_threePrimeHeight_mul_dyadicShellMassR235",
            "dyadicNormalizedTailStateR235_succ",
            "summable_dyadicShellMassR235",
            "dyadicShellTsumTailR235_eq_shell_add",
            "dyadicNormalizedShellTsumTailR235_succ",
            "dyadicShellTsumTail_integer_or_cofinal_far",
        ],
        analysis_refs=[ANALYSIS_REF, PACKET_REF],
        source_refs=[
            SOURCE_REF,
            BLOCK_CHECKER_REF,
            RECURRENCE_LEAN_REF,
            SUMMABILITY_LEAN_REF,
        ],
        resource_bounds={"min_a": 1, "max_a": max_a},
        result_status="exact_one_way_result",
        result_summary=(
            "The exact source mass, ordered digit, normalized finite tail, and both "
            "summability majorants agree at every tested scale; Lean proves the "
            "genuine infinite tail either reaches an integral state or returns "
            "cofinally far from all integers."
        ),
        progress_class="mechanism_opened",
        decision_basis=(
            "The previously abstract bounded-radix orbit is now driven by the "
            "literal ordered smooth-source digit rather than a free input."
        ),
        next_analytic_target=(
            "Exclude exact integral normalized states of the genuine source tail; "
            "the other branch already supplies cofinal 1/31 escape."
        ),
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos269-ordered-tail-recurrence/1",
        "status": "verified_exact_source_to_carry_mechanism_opening",
        "parameters": {"min_a": 1, "max_a": max_a},
        "checked_recurrence_count": len(rows),
        "checked_majorant_count": len(rows),
        "max_observed_digit_over_scale_square": frac(max_digit_ratio),
        "max_observed_digit_over_scale_square_scale": max_digit_ratio_scale,
        "first_rows": rows[:4],
        "last_rows": rows[-3:],
        "lean_declarations": [
            "half_threePrimeHeight_mul_dyadicShellMassQ235",
            "dyadicNormalizedTailStateQ235_succ",
            "half_threePrimeHeight_mul_dyadicShellMassR235",
            "dyadicNormalizedTailStateR235_succ",
            "summable_dyadicShellMassR235",
            "dyadicShellTsumTailR235_eq_shell_add",
            "dyadicNormalizedShellTsumTailR235_succ",
            "dyadicShellTsumTail_integer_or_cofinal_far",
        ],
        "experiment_contract": contract,
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [
                SOURCE_REF,
                BLOCK_CHECKER_REF,
                RECURRENCE_LEAN_REF,
                SUMMABILITY_LEAN_REF,
                ANALYSIS_REF,
                PACKET_REF,
            ]
        ],
    }


def emit(payload: dict[str, object], output: Path, check: bool) -> int:
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
    parser.add_argument("--max-a", type=int, default=40)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    return emit(build_payload(args.max_a), args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
