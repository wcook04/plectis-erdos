#!/usr/bin/env python3
"""Erdős #269 integral-branch probes: pinning windows and seed survival.

The bounded-radix dichotomy proved in
``DyadicOrderedTailRecurrence.lean`` / ``BoundedRadixTailEscape.lean``
leaves exactly one branch between the genuine infinite tail and
irrationality-shaped escape: some normalized state ``X_a`` being an exact
integer.  This experiment attacks that branch with three discriminating
computations over the shared orbit engine
(``system/lib/formal_math_erdos269_orbit_engine.py``):

* Pinning-window census: how many indices have no integer in their window
  at all (killed outright), including the zero-gap sub-census where
  ``d_a / b_a`` is itself an integer so integrality would force the
  impossible ``X_(a+1) = 0``.
* Seed survival: for each candidate first integral index ``A``, propagate
  every integer seed through ``w' = b_a w - d_a`` requiring positivity and
  membership in every later pinning window; wrong seeds die in O(log A)
  steps because deviations multiply by ``b_a >= 2`` while window widths
  grow polynomially.
* Parity census of literal shell cardinalities ``N_a``, feeding the
  stabilized-denominator congruence gate: under rationality with even
  stabilized denominator, ``N_a`` must be eventually even, because
  ``b_a`` is always even so ``X_(a+1) = b_a X_a - d_a`` forces
  ``d_a ≡ N_a (mod 2)`` to absorb the lattice.

Every finite result here is evidence routing an analytic proof target; it
is not itself an irrationality theorem.
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_erdos269_orbit_engine import (  # noqa: E402
    integers_in_window,
    integral_seed_report,
    load_block_sequence,
    pinning_window,
    regression_check,
    shell_cardinality_parity_census,
    state_enclosure,
    zero_gap_census,
)
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)

SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/check_erdos269_integral_branch.py"
)
ENGINE_REF = "system/lib/formal_math_erdos269_orbit_engine.py"
RECURRENCE_LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "DyadicOrderedTailRecurrence.lean"
)
RADIX_LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "BoundedRadixTailEscape.lean"
)
CONSUMER_LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "ResidueEscape.lean"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "DyadicWindowComputationalLab.md"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos269_integral_branch_receipt.json"
)


def frac(value: Fraction) -> dict[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


def run_probe(
    max_first_index: int,
    survival_depth: int,
    parity_scale: int,
    horizon_terms: int,
) -> dict[str, object]:
    regression = regression_check(max_a=min(48, max_first_index + 8))
    if regression["failures"]:
        raise AssertionError(f"engine regression failed: {regression['failures']}")

    blocks = load_block_sequence(max_first_index + survival_depth + 4)

    killed_no_integer = []
    zero_gap_killed = []
    candidate_counts = []
    for a in range(1, max_first_index + 1):
        window = pinning_window(blocks, a, horizon_terms)
        candidates = integers_in_window(window)
        candidate_counts.append(len(candidates))
        anchor = window[0]
        if (-blocks[a - 1][2]) % blocks[a - 1][1] == 0:
            zero_gap_killed.append(a)
        if not candidates:
            killed_no_integer.append(a)

    death_histogram: dict[str, int] = {}
    survivors_by_index: dict[int, list[int]] = {}
    deepest_death = 0
    deepest_death_index = 0
    for a in range(1, max_first_index + 1):
        report = integral_seed_report(blocks, a, survival_depth, horizon_terms)
        for seed, depth in report["deaths"].items():
            key = "survivor" if depth is None else str(depth)
            death_histogram[key] = death_histogram.get(key, 0) + 1
            if depth is not None and depth > deepest_death:
                deepest_death = depth
                deepest_death_index = a
        if report["survivors"]:
            survivors_by_index[a] = report["survivors"]

    parity = shell_cardinality_parity_census(parity_scale)
    odd_shells = [a for a, p in parity if p == 1]
    max_even_run = 0
    run = 0
    for _, p in parity:
        run = 0 if p == 1 else run + 1
        max_even_run = max(max_even_run, run)

    # Rigorous enclosure comparison at a fixed late index: the true state's
    # distance to the nearest integer versus its pinning slack.
    probe_a = min(max_first_index, 240)
    lo, hi = state_enclosure(blocks, probe_a, horizon_terms=200)

    return {
        "regression": regression,
        "window_census": {
            "indices_checked": max_first_index,
            "no_integer_windows": len(killed_no_integer),
            "zero_gap_killed": len(zero_gap_killed),
            "max_candidates_per_index": max(candidate_counts),
            "mean_candidates_per_index": (
                sum(candidate_counts) / len(candidate_counts)
            ),
        },
        "seed_survival": {
            "depth": survival_depth,
            "death_histogram": death_histogram,
            "deepest_death": deepest_death,
            "deepest_death_index": deepest_death_index,
            "survivor_indices": sorted(survivors_by_index),
            "survivors": {str(a): w for a, w in survivors_by_index.items()},
        },
        "parity_census": {
            "scale": parity_scale,
            "odd_shell_count": len(odd_shells),
            "first_odd_shells": odd_shells[:24],
            "max_consecutive_even_run": max_even_run,
        },
        "late_state_enclosure": {
            "index": probe_a,
            "low": frac(lo),
            "high": frac(hi),
        },
    }


def build_payload(args: argparse.Namespace) -> dict[str, object]:
    results = run_probe(
        max_first_index=args.max_first_index,
        survival_depth=args.survival_depth,
        parity_scale=args.parity_scale,
        horizon_terms=args.horizon_terms,
    )
    survivors = results["seed_survival"]["survivors"]
    if survivors:
        result_status = "finite_counterexample"
        progress_class = "mechanism_opened"
        decision_basis = (
            "Surviving seeds are forced-equality candidates: each must be "
            "compared against deeper enclosures of the true state."
        )
        next_analytic_target = (
            "Decide survivor equality with deeper Cantor enclosures; "
            "agreement would prove the series rational."
        )
        result_summary = (
            "Surviving integer seeds exist at first-integral indices "
            f"{results['seed_survival']['survivor_indices']}; each survivor "
            "is a forced equality candidate X_A = w and must next be compared "
            "against deeper enclosures."
        )
    elif results["seed_survival"]["death_histogram"]:
        result_status = "exact_one_way_result"
        progress_class = "mechanism_eliminated"
        decision_basis = (
            "Exact window arithmetic eliminates every integer seed in range; "
            "the extinction-depth histogram discriminates pinned-seed "
            "extinction from unbounded-trap mechanisms retired earlier "
            "(delay caps through 199 are false; cylinders exist)."
        )
        next_analytic_target = (
            "Formalize upward closure plus pinning-window extinction as a "
            "Lean theorem, and prove rationality forces an integral state "
            "(denominator collapse Q | 2v via H(x) | H(y) monotonicity)."
        )
        result_summary = (
            "Every integer seed at every candidate first integral index "
            f"1..{args.max_first_index} died within "
            f"{results['seed_survival']['deepest_death']} propagation steps; "
            "the uniform death-depth mechanism is the analytic proof target."
        )
    else:
        result_status = "not_run"
        progress_class = "mechanism_eliminated"
        decision_basis = "No candidates generated; widen the horizon."
        next_analytic_target = "Widen window horizon or survival depth."
        result_summary = "No candidates were generated."

    contract = build_experiment_contract(
        problem_id="erdos_269",
        target_statement=(
            "Irrationality of the running-LCM series with prime support "
            "{2,3,5}: T_0 = sum_{x 235-smooth} 1/H(x), H(x)=2^floor(log2 x)"
            "3^floor(log3 x)5^floor(log5 x)."
        ),
        claim_ceiling=(
            "#269 remains open. This receipt only classifies which integer "
            "seeds could realize the dichotomy's integral-state branch."
        ),
        hypothesis_id="integral_branch_pinned_seed_extinction",
        hypothesis_statement=(
            "The integral-index set is upward closed (integer recurrence "
            "coefficients), every true state lies in the half-open pinning "
            "window (d_a/b_a, d_a/b_a + Lambda_a], and wrong seeds die in "
            "O(log A) steps because deviations multiply by b_a >= 2 while "
            "window widths grow polynomially; hence any integral state is a "
            "forced equality decidable by enclosure comparison."
        ),
        probe_id="integral_branch_seed_survival_v1",
        probe_question=(
            "Does any candidate first integral index admit an integer seed "
            "that tracks the pinning windows for the full survival depth, "
            "and what uniform depth bound governs seed extinction?"
        ),
        computation=(
            "Exact Fraction Cantor-series enclosures from the shared engine, "
            "per-index integer seed enumeration inside rigorous pinning "
            "windows, forward propagation with window-membership pruning, "
            "literal smooth-point shell parity census."
        ),
        falsifier=(
            "Either a surviving seed that equals the true state enclosure "
            "(making T_0 rational and settling #269 negatively), or a seed "
            "whose survival depth grows without bound with A (killing the "
            "uniform-extinction proof route)."
        ),
        stop_condition=(
            "Uniform bounded extinction depth across all probed first "
            "indices with zero survivors."
        ),
        survival_consequence=(
            "Uniform bounded seed death becomes the statement to formalize: "
            "no integral state exists, closing the remaining dichotomy "
            "branch once rationality is shown to force one."
        ),
        falsification_consequence=(
            "A forced equality survivor proves the series rational; unbounded "
            "survival depth redirects analysis to the residue-escape lane."
        ),
        consumer_ref=CONSUMER_LEAN_REF,
        analysis_refs=[ANALYSIS_REF],
        source_refs=[ENGINE_REF, SOURCE_REF],
        input_receipt_refs=[
            "state/formal_math/erdos257_period_noncollapse/erdos269_ordered_tail_recurrence_receipt.json"
        ],
        result_status=result_status,
        result_summary=result_summary,
        consumer_declarations=[
            "ErdosProblems.Erdos269.dyadicNormalizedTailStateQ235_succ",
            "ErdosProblems.Erdos269.dyadicBlockBase235_cases",
            "ErdosProblems.Erdos269.half_threePrimeHeight_mul_dyadicShellMassQ235",
        ],
        resource_bounds={
            "max_first_index": args.max_first_index,
            "survival_depth": args.survival_depth,
            "parity_scale": args.parity_scale,
            "horizon_terms": args.horizon_terms,
        },
        progress_class=progress_class,
        decision_basis=decision_basis,
        next_analytic_target=next_analytic_target,
    )

    payload = {
        "experiment_contract": contract,
        "computation_source": source_record(REPO_ROOT, SOURCE_REF),
        "engine_source": source_record(REPO_ROOT, ENGINE_REF),
        "results": results,
    }
    validate_experiment_contract(contract)
    return payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-first-index", type=int, default=400)
    parser.add_argument("--survival-depth", type=int, default=256)
    parser.add_argument("--parity-scale", type=int, default=4000)
    parser.add_argument("--horizon-terms", type=int, default=160)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument(
        "--check",
        action="store_true",
        help="Replay mode: recompute and compare against the stored receipt.",
    )
    args = parser.parse_args(argv)

    payload = build_payload(args)
    rendered = json.dumps(payload, indent=2, sort_keys=True, default=str) + "\n"
    if args.check:
        if not args.output.exists() or args.output.read_text() != rendered:
            print("stale receipt", file=sys.stderr)
            return 1
        print(json.dumps({"status": "current", "output": str(args.output)}))
        return 0
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(rendered)
    results = payload["results"]
    print(json.dumps({
        "status": payload["experiment_contract"]["result"]["status"],
        "windows_without_integer": results["window_census"]["no_integer_windows"],
        "zero_gap_killed": results["window_census"]["zero_gap_killed"],
        "deepest_death": results["seed_survival"]["deepest_death"],
        "survivors": len(results["seed_survival"]["survivors"]),
        "odd_shells": results["parity_census"]["odd_shell_count"],
        "max_even_run": results["parity_census"]["max_consecutive_even_run"],
    }, indent=2))
    print(f"wrote {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
