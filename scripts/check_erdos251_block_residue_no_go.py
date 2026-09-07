#!/usr/bin/env python3
"""Exact regression for the Erdős #251 fixed-lattice block-residue no-go.

The computation is deliberately not a prime-gap horizon.  It constructs many
bounded rational dyadic orbits from their actual initial states and checks
that fixed-lattice block escape is forced solely by denominator separation and
the recurrence identity.  Lean owns the universal theorem; this script keeps
its computational coordinates, analytic motivation, and consequence linked.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from fractions import Fraction
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_dyadic_tail import (  # noqa: E402
    dyadic_tail_block,
    forced_block_escape_margin,
    nearest_multiple_distance,
    rational_distance_to_integer,
)
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
)


SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos251_block_residue_no_go.py"
)
UTILITY_REF = "system/lib/formal_math_dyadic_tail.py"
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/"
    "AffineCylinderCollapse.lean"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/"
    "BlockResidueComputationalLab.md"
)
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "erdos251_block_residue_no_go_receipt.json"
)
THEOREMS = [
    "ErdosProblems.Erdos251.one_div_den_le_abs_sub_int_of_ne",
    "ErdosProblems.Erdos251.exists_blockResidue_escape_of_not_integral",
    "ErdosProblems.Erdos251.cofinal_blockResidue_escape_iff_not_eventuallyIntegral",
]


def balanced_step(state: Fraction) -> tuple[int, Fraction]:
    """Choose an integer digit keeping the next state in ``[-1/2, 1/2)``."""

    doubled = 2 * state
    digit = (2 * doubled.numerator + doubled.denominator) // (2 * doubled.denominator)
    next_state = doubled - digit
    if not Fraction(-1, 2) <= next_state < Fraction(1, 2):
        raise AssertionError((state, digit, next_state))
    return digit, next_state


def first_power_strictly_above(value: int) -> int:
    if value < 1:
        raise ValueError("value must be positive")
    return value.bit_length()


def orbit_row(numerator: int, denominator: int) -> dict[str, object]:
    initial = Fraction(numerator, denominator)
    depth = first_power_strictly_above(initial.denominator)
    states = [initial]
    digits = [0]
    for _ in range(depth):
        digit, next_state = balanced_step(states[-1])
        digits.append(digit)
        states.append(next_state)

    block = dyadic_tail_block(digits, 0, depth)
    modulus = 1 << depth
    terminal = states[-1]
    distance = nearest_multiple_distance(block, modulus)
    terminal_bound = Fraction(1, 2)
    forced_margin = forced_block_escape_margin(initial, terminal_bound, depth)
    identity_right = modulus * initial - block

    if identity_right != terminal:
        raise AssertionError(("iterate identity", initial, depth, identity_right, terminal))
    if Fraction(distance) < forced_margin:
        raise AssertionError(("reverse triangle", initial, depth, distance, forced_margin))
    if forced_margin <= terminal_bound or distance <= terminal_bound:
        raise AssertionError(("escape failed", initial, depth, distance, forced_margin))

    return {
        "initial_numerator": initial.numerator,
        "initial_denominator": initial.denominator,
        "predicted_depth": depth,
        "dyadic_modulus": modulus,
        "terminal_numerator": terminal.numerator,
        "terminal_denominator": terminal.denominator,
        "block": block,
        "nearest_lattice_distance": distance,
        "basepoint_integer_distance_numerator": rational_distance_to_integer(initial).numerator,
        "basepoint_integer_distance_denominator": rational_distance_to_integer(initial).denominator,
        "forced_margin_numerator": forced_margin.numerator,
        "forced_margin_denominator": forced_margin.denominator,
    }


def build_result(max_odd_denominator: int) -> dict[str, object]:
    if max_odd_denominator < 3:
        raise ValueError("max_odd_denominator must be at least three")
    rows = []
    for denominator in range(3, max_odd_denominator + 1, 2):
        for numerator in range(1, denominator):
            if math.gcd(numerator, denominator) == 1:
                rows.append(orbit_row(numerator, denominator))

    minimum_margin = min(
        Fraction(row["forced_margin_numerator"], row["forced_margin_denominator"])
        for row in rows
    )
    maximum_depth = max(row["predicted_depth"] for row in rows)
    representatives = []
    seen_depths: set[int] = set()
    for row in rows:
        depth = int(row["predicted_depth"])
        if depth not in seen_depths:
            representatives.append(row)
            seen_depths.add(depth)

    result_summary = (
        f"Lean proves the fixed-lattice supply equivalent to non-eventual integrality "
        f"for every dyadically dominated bound. Exact balanced-orbit replay verifies "
        f"the denominator-forced escape coordinates for {len(rows)} reduced rational "
        f"initial states through odd denominator {max_odd_denominator}."
    )
    return {
        "schema": "erdos251-block-residue-no-go/1",
        "claim_ceiling": (
            "Erdos 251 remains open. The result retires fixed-lattice block-residue "
            "escape under dyadically dominated terminal bounds as an independent "
            "producer; it does not prove cofinal nonintegrality."
        ),
        "parameters": {
            "maximum_odd_denominator": max_odd_denominator,
            "terminal_abs_bound_numerator": 1,
            "terminal_abs_bound_denominator": 2,
            "depth_rule": "least r with 2^r > reduced denominator",
        },
        "exact_result": {
            "tested_initial_state_count": len(rows),
            "maximum_predicted_depth": maximum_depth,
            "minimum_forced_margin_numerator": minimum_margin.numerator,
            "minimum_forced_margin_denominator": minimum_margin.denominator,
            "all_recurrence_identities_exact": True,
            "all_reverse_triangle_bounds_exact": True,
            "all_fixed_lattice_escapes": True,
            "representative_first_row_by_depth": representatives,
        },
        "structural_consequence": {
            "identity": "B_(N,r)-2^r*z = 2^r*(T_h(N)-z)-T_h(N+r)",
            "denominator_gap": "nonintegral rational x satisfies dist(x,Z) >= 1/x.den",
            "forced_escape": (
                "If 2^r/x.den > 2*bound(N+r), block escape follows without any "
                "property of the intervening digit word."
            ),
            "mechanism_disposition": (
                "For every DyadicScaleDominates bound, cofinal fixed-lattice "
                "block escape is equivalent to non-eventual integrality and therefore "
                "cannot serve as its independent prime-theoretic producer."
            ),
            "lean_theorems": THEOREMS,
        },
        "experiment_contract": build_experiment_contract(
            problem_id="erdos_251",
            target_statement=(
                "Prove irrationality of the dyadic series built from consecutive prime gaps."
            ),
            claim_ceiling=(
                "The no-go does not prove cofinal nonintegrality or Erdős 251."
            ),
            hypothesis_id="fixed_lattice_block_residue_independent_producer",
            hypothesis_statement=(
                "Cofinal distance of observed blocks from 2^r*Z supplies new prime-word "
                "information beyond non-eventual integrality of the tail shift."
            ),
            probe_id="denominator_forced_balanced_dyadic_orbits",
            probe_question=(
                "Does fixed-lattice escape arise automatically from rational denominator "
                "separation and the terminal bound, independently of digit structure?"
            ),
            computation=(
                "Generate every reduced rational state with odd denominator in the requested "
                "range, keep its exact dyadic orbit balanced, and compare the integer block "
                "with 2^r*Z at the denominator-forced depth."
            ),
            falsifier=(
                "A nonintegral rational state and dyadically dominated terminal bound for "
                "which the predicted reverse-triangle block escape fails."
            ),
            stop_condition=(
                "Once Lean proves the cofinal equivalence, retire this producer; do not "
                "extend the rational grid as if it could prove Erdős 251."
            ),
            survival_consequence=(
                "A failure would reopen fixed-lattice block anti-concentration as a distinct "
                "prime-word mechanism."
            ),
            falsification_consequence=(
                "Equivalence redirects the frontier away from adaptive/fixed recurrence "
                "pullbacks and back to a genuinely external prime-tail mechanism."
            ),
            consumer_ref=LEAN_REF,
            consumer_declarations=THEOREMS,
            analysis_refs=[ANALYSIS_REF],
            source_refs=[SCRIPT_REF, UTILITY_REF, LEAN_REF, ANALYSIS_REF],
            result_status="exact_one_way_result",
            result_summary=result_summary,
        ),
        "sources": [
            source_record(REPO_ROOT, SCRIPT_REF),
            source_record(REPO_ROOT, UTILITY_REF),
            source_record(REPO_ROOT, LEAN_REF),
            source_record(REPO_ROOT, ANALYSIS_REF),
        ],
    }


def emit(result: dict[str, object], output: Path, check: bool) -> int:
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    output = output.resolve()
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
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-odd-denominator", type=int, default=199)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    return emit(build_result(args.max_odd_denominator), args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
