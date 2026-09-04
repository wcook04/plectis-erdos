#!/usr/bin/env python3
"""Exact orbit check of the cumulative-LCM overlap-debt identities.

Setting.  For a rational reciprocal tail put ``x_n = sum_{j>=n} 1/a_j = C_n/D_n``
with the fractions deliberately UNREDUCED, so that

    D_{n+1} = a_n D_n,          C_{n+1} + D_n = a_n C_n,
    E_n     = D_n - (a_n - 1) C_n = C_n - C_{n+1},
    a_n     = ceil(D_n / C_n)                      (greedy/pseudo-greedy step).

Alongside the product denominator run the cumulative LCM scale and the overlap
debt

    Lambda_0 = D_0,  Lambda_{n+1} = lcm(Lambda_n, a_n),
    M_n = D_n / Lambda_n,        rho_n = gcd(Lambda_n, a_n),   M_{n+1} = M_n rho_n.

This module checks, on every reduced rational seed with bounded denominator,
the four identities the LCM-normalised transfer argument rests on:

  (1) M_n * Lambda_n = D_n                       (already Lean-checked)
  (2) M_n | C_n  and  M_n | E_n                  (the keystone divisibility)
  (3) rho_n U_{n+1} = U_n - V_n  and  V_n = Lambda_n - (a_n - 1) U_n
      for U_n = C_n / M_n,  V_n = E_n / M_n      (the exact normalised system)
  (4) 2^R(n) <= M_n <= C_n, where R(n) counts the non-fresh steps rho_j > 1
      (the finite inequality underlying density-one LCM freshness)

and records, for every fresh pair i < j, that gcd(a_i, a_j) = 1.

Two lanes, and why both are needed.  On the GREEDY step ``a_n = ceil(D_n/C_n)``
one has ``(a_n - 1) C_n < D_n <= a_n C_n``, hence ``0 < E_n <= C_n``: the
centred state is never negative.  A greedy rational scan therefore cannot
exercise the negative-excursion regime, which is the entire subject of the
LCM-normalised transfer argument.  The PSEUDO-GREEDY lane admits any
``a_n >= ceil(D_n/C_n)`` that keeps the tail positive and the multipliers
strictly increasing; taking ``a_n`` above the greedy value drives ``E_n``
negative and reaches the states the transfer argument is about.  Both lanes are
run, and the negative lane is the one that makes the divisibility check
non-vacuous where it matters.

Boundary.  Every orbit reachable from a rational seed terminates at E = 0 and
is therefore eventually Sylvester; the interest here is not termination but
that the identities hold at every intermediate state, including states with
nontrivial overlap debt and negative centred state.  A finite orbit scan is not
a proof of the transfer theorem and says nothing about Erdos #243 itself.
"""

from __future__ import annotations

import argparse
import itertools
import json
from math import gcd, lcm
from pathlib import Path
import sys


REPO_ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
)
from system.lib.formal_math_probe_registry import mechanism_bindings  # noqa: E402


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "scripts/check_cumulative_lcm_transfer.py"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "GlobalLcmHeight.lean"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "SlowNegativePartRigidity.md"
)


def run_orbit(
    p: int, q: int, max_steps: int, offsets: tuple[int, ...] = ()
) -> dict[str, object]:
    """Unreduced tail orbit from x_0 = p/q with LCM bookkeeping.

    ``offsets[k]`` is added to the greedy multiplier at step ``k``; an empty or
    exhausted schedule means greedy from that step on.  A nonzero offset is the
    pseudo-greedy choice that can drive the centred state negative.
    """

    C, D = p, q
    Lam = D
    M = 1
    non_fresh = 0
    steps: list[dict[str, object]] = []
    fresh_multipliers: list[int] = []
    failures: list[str] = []
    terminated = False
    previous_a = 1

    for step in range(max_steps):
        if C == 0:
            terminated = True
            break
        a = -(-D // C)  # ceil(D / C)
        if step < len(offsets):
            a += offsets[step]
        if a <= previous_a:
            a = previous_a + 1
        if a < 2:
            failures.append(f"step {step}: multiplier {a} below 2")
            break
        if a * C - D <= 0 and a * C - D != 0:
            failures.append(f"step {step}: tail would go negative")
            break
        previous_a = a
        E = D - (a - 1) * C
        rho = gcd(Lam, a)

        if M * Lam != D:
            failures.append(f"step {step}: M*Lambda != D")
        if C % M != 0:
            failures.append(f"step {step}: M does not divide C")
        if E % M != 0:
            failures.append(f"step {step}: M does not divide E")

        U, V = C // M, E // M
        C_next = a * C - D
        D_next = a * D
        Lam_next = lcm(Lam, a)
        M_next = M * rho

        if C_next % M_next != 0:
            failures.append(f"step {step}: M_(n+1) does not divide C_(n+1)")
        else:
            U_next = C_next // M_next
            if rho * U_next != U - V:
                failures.append(f"step {step}: rho*U_(n+1) != U - V")
        if V != Lam - (a - 1) * U:
            failures.append(f"step {step}: V != Lambda - (a-1) U")
        if not 2**non_fresh <= M:
            failures.append(f"step {step}: 2^R exceeds M")
        if M > C:
            failures.append(f"step {step}: M exceeds C")

        if rho == 1:
            for earlier in fresh_multipliers:
                if gcd(earlier, a) != 1:
                    failures.append(f"step {step}: fresh multipliers not coprime")
                    break
            fresh_multipliers.append(a)
        else:
            non_fresh += 1

        steps.append(
            {
                "step": step,
                "a": a,
                "rho": rho,
                "overlap_debt": M,
                "U": U,
                "V": V,
                "fresh": rho == 1,
            }
        )
        C, D, Lam, M = C_next, D_next, Lam_next, M_next
    else:
        terminated = C == 0

    min_V = min((s["V"] for s in steps), default=0)
    return {
        "seed": [p, q],
        "offsets": list(offsets),
        "negative_centered_states": sum(1 for s in steps if s["V"] < 0),
        "steps_taken": len(steps),
        "terminated_at_zero_centered_state": terminated,
        "max_overlap_debt": max((s["overlap_debt"] for s in steps), default=1),
        "non_fresh_step_count": non_fresh,
        "fresh_multiplier_count": len(fresh_multipliers),
        "min_normalised_centered_state": min_V,
        "failures": failures,
    }


def compute(
    max_denominator: int, max_steps: int, offset_depth: int, offset_max: int
) -> dict[str, object]:
    orbits: list[dict[str, object]] = []
    for q in range(2, max_denominator + 1):
        for p in range(1, q):
            if gcd(p, q) != 1:
                continue
            orbits.append(run_orbit(p, q, max_steps))
    greedy_orbits = list(orbits)
    greedy_negative = sum(int(o["negative_centered_states"]) for o in greedy_orbits)

    # Pseudo-greedy lane: perturb the first `offset_depth` multipliers upward.
    pseudo: list[dict[str, object]] = []
    schedules = [
        tuple(s)
        for s in itertools.product(range(offset_max + 1), repeat=offset_depth)
        if any(s)
    ]
    for q in range(2, min(max_denominator, 30) + 1):
        for p in range(1, q):
            if gcd(p, q) != 1:
                continue
            for schedule in schedules:
                pseudo.append(run_orbit(p, q, max_steps, schedule))
    orbits = greedy_orbits + pseudo
    failing = [o for o in orbits if o["failures"]]
    nontrivial_debt = [o for o in orbits if o["max_overlap_debt"] > 1]
    pseudo_negative = [o for o in pseudo if int(o["negative_centered_states"]) > 0]
    return {
        "max_denominator": max_denominator,
        "max_steps": max_steps,
        "offset_depth": offset_depth,
        "offset_max": offset_max,
        "greedy_orbit_count": len(greedy_orbits),
        "greedy_negative_centered_state_count": greedy_negative,
        "greedy_lane_is_sign_vacuous": greedy_negative == 0,
        "pseudo_greedy_orbit_count": len(pseudo),
        "pseudo_greedy_orbits_reaching_negative_state": len(pseudo_negative),
        "most_negative_pseudo_greedy_state": min(
            (int(o["min_normalised_centered_state"]) for o in pseudo), default=0
        ),
        "orbit_count": len(orbits),
        "orbits_with_nontrivial_overlap_debt": len(nontrivial_debt),
        "largest_overlap_debt_observed": max(
            (o["max_overlap_debt"] for o in orbits), default=1
        ),
        "largest_step_count": max((o["steps_taken"] for o in orbits), default=0),
        "most_negative_normalised_centered_state": min(
            (o["min_normalised_centered_state"] for o in orbits), default=0
        ),
        "all_orbits_terminate": all(
            o["terminated_at_zero_centered_state"] for o in orbits
        ),
        "failing_orbit_count": len(failing),
        "failing_orbits": failing[:10],
        "all_identities_hold": not failing,
        "representative_nontrivial_debt_orbits": [
            {k: o[k] for k in ("seed", "steps_taken", "max_overlap_debt",
                               "non_fresh_step_count",
                               "min_normalised_centered_state")}
            for o in sorted(
                nontrivial_debt,
                key=lambda o: -int(o["max_overlap_debt"]),
            )[:8]
        ],
    }


def emit(result: dict[str, object], output: Path | None, check: bool) -> int:
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if output is None:
        print(rendered, end="")
        return 0
    resolved = output.resolve()
    if check:
        if not resolved.exists() or resolved.read_text(encoding="utf-8") != rendered:
            print(f"stale receipt: {resolved}", file=sys.stderr)
            return 1
        print(json.dumps({"status": "current", "output": str(resolved)}))
        return 0
    resolved.parent.mkdir(parents=True, exist_ok=True)
    resolved.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(resolved)}))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-denominator", type=int, default=120)
    parser.add_argument("--max-steps", type=int, default=40)
    parser.add_argument("--offset-depth", type=int, default=2)
    parser.add_argument("--offset-max", type=int, default=2)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.max_denominator < 2:
        parser.error("--max-denominator must be at least 2")
    if args.max_steps < 1:
        parser.error("--max-steps must be positive")
    if args.check and args.output is None:
        parser.error("--check requires --output")

    if not 0 <= args.offset_depth <= 4:
        parser.error("--offset-depth must lie in [0,4]")
    if not 0 <= args.offset_max <= 4:
        parser.error("--offset-max must lie in [0,4]")

    scan = compute(
        args.max_denominator, args.max_steps, args.offset_depth, args.offset_max
    )
    holds = bool(scan["all_identities_hold"])
    summary = (
        f"Across {scan['orbit_count']} reduced rational seeds with denominator "
        f"at most {args.max_denominator}, the overlap-debt identities hold at "
        "every intermediate state: M_n Lambda_n = D_n, M_n divides both C_n and "
        "E_n, the normalised system rho_n U_(n+1) = U_n - V_n with "
        "V_n = Lambda_n - (a_n-1) U_n is exact, 2^R(n) <= M_n <= C_n, and every "
        "pair of LCM-fresh multipliers is coprime. "
        f"{scan['orbits_with_nontrivial_overlap_debt']} orbits carry overlap "
        f"debt above 1 (largest {scan['largest_overlap_debt_observed']}), so the "
        "divisibility is not vacuous on this range. The greedy lane is sign "
        "vacuous: ceil(D/C) forces 0 < E_n <= C_n at every step, so it reaches "
        f"no negative centred state at all ({scan['greedy_negative_centered_state_count']} "
        "observed). The pseudo-greedy lane reaches "
        f"{scan['pseudo_greedy_orbits_reaching_negative_state']} orbits with a "
        "negative centred state (most negative normalised value "
        f"{scan['most_negative_pseudo_greedy_state']}), and the identities hold "
        "there too."
        if holds
        else
        "At least one orbit violates an overlap-debt identity; inspect "
        "failing_orbits before relying on the LCM-normalised state."
    )
    result = {
        "schema": "erdos243-cumulative-lcm-transfer/1",
        "claim_ceiling": (
            "A finite exact orbit scan of the unreduced tail dynamics and its "
            "LCM bookkeeping. It regression-tests the overlap-debt identities; "
            "it is not a proof of the cumulative-LCM transfer theorem and does "
            "not bear on the unrestricted Erdos #243 statement, since every "
            "rational seed terminates."
        ),
        "parameters": {
            "max_denominator": args.max_denominator,
            "max_steps": args.max_steps,
        },
        "scan": scan,
        "experiment_contract": build_experiment_contract(
            problem_id="erdos_243",
            target_statement=(
                "Under a_{n+1}/a_n^2 -> 1 and rational reciprocal sum, force "
                "eventual Sylvester recurrence."
            ),
            claim_ceiling=(
                "Regression evidence for the overlap-debt divisibility and the "
                "exact LCM-normalised system. Not a proof of the transfer "
                "theorem."
            ),
            hypothesis_id="overlap_debt_divides_tail_numerator_fails",
            hypothesis_statement=(
                "The cumulative overlap debt M_n = D_n / Lambda_n fails to "
                "divide the unreduced tail numerator C_n or the centred state "
                "E_n at some reachable state, so the LCM-normalised variables "
                "U_n and V_n are not integral and the transfer argument has no "
                "exact system to run on."
            ),
            probe_id="rational_seed_overlap_debt_orbit_scan",
            probe_question=(
                "Do M_n | C_n, M_n | E_n and the normalised recurrence hold at "
                "every intermediate state of every bounded-denominator rational "
                "orbit, including states with nontrivial overlap debt?"
            ),
            computation=(
                "Run the unreduced greedy tail dynamics from every reduced "
                "rational seed with bounded denominator, carrying the "
                "cumulative LCM and overlap debt, and assert the four "
                "identities plus fresh-multiplier coprimality at each step."
            ),
            falsifier=(
                "A state where M_n does not divide C_n or E_n, where "
                "rho_n U_(n+1) != U_n - V_n, or where 2^R(n) exceeds M_n."
            ),
            stop_condition=(
                "Once the identities survive the full bounded-denominator "
                "range, the remaining work is the Lean induction and the "
                "first-crossing CRT argument, not further orbit scanning."
            ),
            survival_consequence=(
                "A failure would remove the exact integral system the "
                "LCM-normalised critical profile is stated in."
            ),
            falsification_consequence=(
                "Survival makes the overlap-debt divisibility a safe Lean "
                "target and licenses stating the counterexample profile in the "
                "normalised coordinates U_n, V_n."
            ),
            consumer_ref=CONSUMER_REF,
            consumer_declarations=[
                "cumulativeOverlapDebt_mul_lcm_eq_productScale",
                "globalLcm_numerator_update",
                "returnedError_step",
            ],
            analysis_refs=[ANALYSIS_REF],
            source_refs=[SOURCE_REF],
            result_status=("exact_one_way_result" if holds else "finite_support"),
            result_summary=summary,
            resource_bounds={
                "max_denominator": args.max_denominator,
                "max_steps": args.max_steps,
                "orbit_count": int(scan["orbit_count"]),
                "offset_depth": args.offset_depth,
                "offset_max": args.offset_max,
            },
        ),
        "mechanism_bindings": mechanism_bindings(
            problem_id="erdos_243",
            motivated_by=[
                "cumulative_lcm_overlap_relocation",
                "global_lcm_pseudo_euclidean_update",
                "formalise_lcm_weighted_theorem",
            ],
            supports=[
                "cumulative_lcm_overlap_relocation",
                "bounded_lcm_negative_arithmetic_core",
                "erdos_straus_quantity_bounded_form",
            ],
            rationale=(
                "The LCM-normalised rigidity route needs M_n to divide the "
                "unreduced tail numerator, so that U_n and V_n are integers and "
                "the counterexample profile can be stated in normalised "
                "coordinates. That divisibility had no computational check and "
                "no Lean declaration; this probe is its regression test."
            ),
        ),
        "sources": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, CONSUMER_REF),
            source_record(REPO_ROOT, ANALYSIS_REF),
        ],
        "summary": summary,
    }
    return emit(result, args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
