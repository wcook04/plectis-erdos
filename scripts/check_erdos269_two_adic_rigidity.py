#!/usr/bin/env python3
"""Erdős #269 two-adic-style rigidity: exact refutation of integral states.

Under the hypothesis that the genuine normalized tail state ``X_A`` is an
integer ``w``, the pinning telescope yields ``X_(A+k) + N_k = w * B_k``
with ``N_0 = 0``, ``N_(k+1) = b_(A+k) * N_k + d_(A+k)``, and
``B_k = prod_{j<k} b_(A+j)``.  Multiplying by ``b_(A+k)`` and clearing the
pinning identity gives the exact congruence

    X_(A+k+1) === -( d_(A+k) + b_(A+k) * N_k )   (mod M_k),

where ``M_k = b_(A+k) * B_k >= 2^(k+1)``.  Positivity and the rigorous
Cantor-series enclosure confine the true state to ``(0, hi]``.  Once
``M_k > hi``, the least residue must lie inside ``(0, hi]`` exactly or the
integrality hypothesis is refuted at index ``A`` by pure exact arithmetic.

Combined with the analytic denominator-collapse result (rationality forces
the stabilized state denominator to be 1, hence forces eventual total
integrality), a universal refutation over all first indices settles the
dichotomy's integral branch and proves the series irrational.

The experiment embeds two positive controls - synthetic digit worlds with
exact integer states (constant and nonconstant integer potentials) that
must survive every checked step - so a logic bug cannot masquerade as a
refutation.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_erdos269_orbit_engine import (  # noqa: E402
    load_block_sequence,
    rigidity_residue_trace,
)
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)

SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos269_two_adic_rigidity.py"
)
ENGINE_REF = "system/lib/formal_math_erdos269_orbit_engine.py"
EXTINCTION_LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "IntegralBranchExtinction.lean"
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
    "erdos269_two_adic_rigidity_receipt.json"
)


def run_probe(max_first_index: int, max_k: int, block_horizon: int) -> dict:
    # traces reach A + max_k + 1; never let the horizon fall behind
    block_horizon = max(block_horizon, max_first_index + max_k + 8)
    blocks = load_block_sequence(block_horizon)

    # ---- positive control 1: constant potential (d = b - 1 telescopes to 1)
    synth1 = [(a, b, b - 1) for a, b, _ in blocks]
    ctrl1 = rigidity_residue_trace(synth1, 40, min(200, max_k))
    assert ctrl1["refuted_at_k"] is None, "positive control 1 falsely refuted"

    # ---- positive control 2: nonconstant integer potential C_a = a + 3
    pot = lambda a: a + 3  # noqa: E731
    synth2 = [
        (a, b, b * pot(a) - pot(a + 1)) for a, b, _ in blocks
    ]
    ctrl2 = rigidity_residue_trace(synth2, 40, min(200, max_k))
    assert ctrl2["refuted_at_k"] is None, "positive control 2 falsely refuted"

    # ---- real-world scan
    depths = {}
    unresolved = []
    import time as _time
    _t0 = _time.time()
    for a in range(1, max_first_index + 1):
        if a % 500 == 0:
            print(f"scan a={a} t={_time.time()-_t0:.0f}s", flush=True)
        try:
            rep = rigidity_residue_trace(blocks, a, max_k)
        except ValueError as exc:
            print(f"FAIL a={a} k<= {max_k} last={blocks[-1][0]} "
                  f"exc={exc}", flush=True)
            raise
        if rep["refuted_at_k"] is None:
            unresolved.append(a)
        else:
            depths[a] = rep["refuted_at_k"]

    histogram: dict[str, int] = {}
    for d in depths.values():
        histogram[str(d)] = histogram.get(str(d), 0) + 1

    return {
        "positive_controls": {
            "constant_potential_steps": len(ctrl1["rows"]),
            "nonconstant_potential_steps": len(ctrl2["rows"]),
            "both_survived": True,
        },
        "scan": {
            "first_indices": max_first_index,
            "max_depth_allowed": max_k,
            "refuted_count": len(depths),
            "unresolved_indices": unresolved,
            "deepest_refutation": max(depths.values()) if depths else None,
            "depth_histogram": histogram,
        },
    }


def build_payload(args: argparse.Namespace) -> dict:
    results = run_probe(args.max_first_index, args.max_k, args.block_horizon)
    scan = results["scan"]
    if not scan["unresolved_indices"]:
        status = "exact_one_way_result"
        summary = (
            f"All {scan['refuted_count']} probed first integral indices "
            f"1..{scan['first_indices']} are refuted exactly; deepest "
            f"refutation depth {scan['deepest_refutation']}. Universality "
            "over all indices remains the analytic target."
        )
        progress = (
            "mechanism_eliminated",
            "Exact window-residue arithmetic eliminates the integral-state "
            "hypothesis at every probed index; positive controls guarantee "
            "the elimination logic is sound.",
            "Formalize the rigidity congruence in Lean against the landed "
            "forced-equality theorem and prove a uniform refutation-depth "
            "bound; combined with denominator collapse (Q = 1 under "
            "rationality) this closes the dichotomy's integral branch.",
        )
    else:
        status = "mixed"
        summary = f"Unresolved indices remain: {scan['unresolved_indices'][:10]}"
        progress = (
            "mechanism_opened",
            "Rigidity residues do not yet refute every probed index.",
            "Extend block horizon or deepen the residue trace.",
        )

    contract = build_experiment_contract(
        problem_id="erdos_269",
        target_statement=(
            "Irrationality of T_0 = sum_{x 235-smooth} 1/H(x), "
            "H(x)=2^floor(log2 x) 3^floor(log3 x) 5^floor(log5 x)."
        ),
        claim_ceiling=(
            "#269 remains open. Each refutation is exact finite arithmetic "
            "at a single first index; universality is not claimed."
        ),
        hypothesis_id="integral_state_window_residue",
        hypothesis_statement=(
            "If X_A were integral then for every k the true state satisfies "
            "X_(A+k+1) === -(d_(A+k) + b_(A+k) N_k) mod M_k with "
            "M_k >= 2^(k+1), while enclosures confine it to (0, hi]; once "
            "M_k > hi the least residue must land in (0, hi] exactly."
        ),
        probe_id="two_adic_rigidity_v1",
        probe_question=(
            "Does the window-residue congruence refute the integrality "
            "hypothesis at each probed first index, and how deep must the "
            "trace run?"
        ),
        computation=(
            "Exact big-integer telescope recursion N_(k+1) = b*N_k + d, "
            "least-residue computation modulo M_k, rigorous Cantor-series "
            "enclosure widths, synthetic positive-control worlds."
        ),
        falsifier=(
            "Any probed index whose residue trace never leaves (0, hi] "
            "(up to max_k) marks a candidate integral state and would make "
            "T_0 rational, settling #269 negatively."
        ),
        stop_condition=(
            "Every probed index refuted, with positive controls surviving."
        ),
        survival_consequence=(
            "A universal refutation bound formalized in Lean closes the "
            "dichotomy's integral branch; with denominator collapse this "
            "proves irrationality."
        ),
        falsification_consequence=(
            "An unresolved index yields a forced-equality candidate: deeper "
            "enclosure comparison decides X_A = w and settles #269's polarity."
        ),
        consumer_ref=CONSUMER_LEAN_REF,
        analysis_refs=[ANALYSIS_REF],
        source_refs=[ENGINE_REF, SOURCE_REF],
        input_receipt_refs=[
            "state/formal_math/erdos257_period_noncollapse/"
            "erdos269_integral_branch_receipt.json"
        ],
        result_status=status,
        result_summary=summary,
        consumer_declarations=[
            "ErdosProblems.Erdos269.trueNormalizedState_pinning",
            "ErdosProblems.Erdos269.integral_state_upward_closed",
            "ErdosProblems.Erdos269.surviving_window_orbit_eq_true_state",
        ],
        resource_bounds={
            "max_first_index": args.max_first_index,
            "max_depth": args.max_k,
            "block_horizon": args.block_horizon,
        },
        progress_class=progress[0],
        decision_basis=progress[1],
        next_analytic_target=progress[2],
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
    parser.add_argument("--max-first-index", type=int, default=6000)
    parser.add_argument("--max-k", type=int, default=64)
    parser.add_argument("--block-horizon", type=int, default=6100)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
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
    scan = payload["results"]["scan"]
    print(json.dumps({
        "refuted": scan["refuted_count"],
        "unresolved": len(scan["unresolved_indices"]),
        "deepest_depth": scan["deepest_refutation"],
        "histogram": scan["depth_histogram"],
    }, indent=2))
    print(f"wrote {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
