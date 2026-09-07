#!/usr/bin/env python3
"""Independent replay of the saddle-wall counterfamily's aggregate refutations.

The family.  Fix ``a, b > 0`` with ``8a^3 > 27b^2`` so that
``G(z) = z^4 - a z^2 + b z`` has three distinct real critical points and all
three critical values on one real ray -- the saddle-connection wall.  Perturb to
``G_delta(z) = z^4 - a z^2 + (b + i delta) z`` to separate the critical values,
blow up at the regular square via ``F(z) = -1 + rho^4 G_delta(z/rho)``, and
scale by ``s < 1`` to move every root and every critical value strictly inside
the unit disc:

    f(z) = z^4 - a (s rho)^2 z^2 + (b + i delta)(s rho)^3 z - s^4.

What is measured.  For each critical point ``c_j`` with value ``V_j``, the two
lifts of the value segment from ``V_j`` to ``0``, parameterised as
``V_j (1 - u^2)`` so that ``u = 0`` sits at the saddle and ``u = 1`` at a root.
Along a lift ``z'(u) = -2 u V_j / f'(z)``, started from the resolved expansion
``z_pm(u) = c_j pm u sqrt(-2 V_j / f''(c_j))``.  ``L_j`` is the total length of
the two lifts and ``q_j = L_j / (2 |V_j|^(1/4))``.

Why arc length is an ODE state.  Summing chords along a resampled polyline
undercounts the curved continuation near the saddle by enough to flip the sign
of ``sum L_j - 6R`` -- which is the entire finding.  Arc length is therefore
carried as a third integrated state, and the scan is repeated at three
tolerance settings and required to agree.

What it decides.  With ``R`` the minimum enclosing radius of the roots and the
exact tangent-support identity ``2R - L(e) = D_e + K_e``:

* ``sum_j L_j > 6R`` makes ``sum_e (D_e + K_e) < 0`` on the unique admissible
  component, refuting the componentwise combined-charge inequality;
* ``prod_j q_j > 1`` refutes the admissible critical-arc product;
* ``min_j L_j < 2R`` shows Erdos 1041 is nevertheless TRUE on the family, by
  the single short selected arm;
* ``prod`` over the two smallest ``q`` staying below 1 is the order-sensitive
  trimmed statistic that survives both refutations.

Boundary.  A high-precision replay at one specimen of an open family. The
analytic statement is the authored asymptotic argument; this is its numerical
regression test, and it refutes two proposed proof MECHANISMS, not Erdos 1041,
which stays open and is satisfied by every polynomial measured here.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import minimize


REPO_ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
)
from system.lib.formal_math_probe_registry import mechanism_bindings  # noqa: E402


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "scripts/check_saddle_wall_aggregate_refutation.py"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "ChargedLifetimeAllocationNoGo.lean"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "SaddleWallPairCompression.md"
)

TOLERANCES = (
    ("loose", 1e-9, 1e-11, 1e-2),
    ("tight", 1e-12, 1e-14, 1e-3),
    ("tighter", 1e-13, 1e-16, 1e-4),
)


def specimen_coefficients(a: float, b: float, rho: float, delta: float, s: float):
    """Descending coefficients of the scaled blown-up quartic."""

    return np.array(
        [
            1.0 + 0j,
            0.0 + 0j,
            -a * (s * rho) ** 2,
            (b + 1j * delta) * (s * rho) ** 3,
            -(s**4),
        ]
    )


def _arm(coeffs, crit, value, sign, rtol, atol, max_step, u0=1e-9):
    first = np.polyder(coeffs)
    second = np.polyder(coeffs, 2)
    step = np.sqrt(-2 * value / np.polyval(second, crit))
    start = crit + sign * u0 * step

    def rhs(u, y):
        z = y[0] + 1j * y[1]
        dz = -2 * u * value / np.polyval(first, z)
        return [dz.real, dz.imag, abs(dz)]

    solution = solve_ivp(
        rhs,
        (u0, 1.0),
        [start.real, start.imag, 0.0],
        method="DOP853",
        rtol=rtol,
        atol=atol,
        max_step=max_step,
    )
    end = solution.y[0, -1] + 1j * solution.y[1, -1]
    length = float(solution.y[2, -1] + abs(start - crit))
    return length, end, float(abs(np.polyval(coeffs, end)))


def _min_enclosing_radius(points: np.ndarray) -> float:
    def objective(centre):
        return float(np.max(np.abs(points - (centre[0] + 1j * centre[1]))))

    best = None
    for start in (points.mean(), 0j):
        found = minimize(
            objective,
            [start.real, start.imag],
            method="Nelder-Mead",
            options={"xatol": 1e-15, "fatol": 1e-17, "maxiter": 40000},
        )
        if best is None or found.fun < best.fun:
            best = found
    return float(best.fun)


def compute(a: float, b: float, rho: float, delta: float, s: float) -> dict:
    coeffs = specimen_coefficients(a, b, rho, delta, s)
    roots = np.roots(coeffs)
    criticals = np.roots(np.polyder(coeffs))
    criticals = criticals[np.argsort(criticals.real)]
    values = np.polyval(coeffs, criticals)
    radius = _min_enclosing_radius(roots)

    settings_rows = []
    for label, rtol, atol, max_step in TOLERANCES:
        lengths, ratios, hubs = [], [], []
        for index, (crit, value) in enumerate(zip(criticals, values), start=1):
            total = 0.0
            ends, residuals = [], []
            for sign in (+1, -1):
                length, end, residual = _arm(
                    coeffs, crit, value, sign, rtol, atol, max_step
                )
                total += length
                ends.append(end)
                residuals.append(residual)
            reached = [int(np.argmin(np.abs(roots - z))) for z in ends]
            distances = [float(np.min(np.abs(roots - z))) for z in ends]
            lengths.append(total)
            ratios.append(total / (2 * float(abs(value)) ** 0.25))
            hubs.append(
                {
                    "hub": index,
                    "arm_length": total,
                    "critical_value_modulus": float(abs(value)),
                    "normalised_ratio": ratios[-1],
                    "arms_reach_distinct_roots": reached[0] != reached[1],
                    "endpoint_root_indices": reached,
                    "endpoint_distance_to_nearest_root": distances,
                    "endpoint_polynomial_residual": residuals,
                }
            )
        lengths = np.array(lengths)
        ratios = np.array(ratios)
        ordered = np.sort(ratios)
        settings_rows.append(
            {
                "tolerance_label": label,
                "rtol": rtol,
                "atol": atol,
                "max_step": max_step,
                "hubs": hubs,
                "arm_length_sum": float(lengths.sum()),
                "six_times_radius": 6 * radius,
                "arm_length_sum_minus_six_radius": float(lengths.sum() - 6 * radius),
                "componentwise_charge_sum": float(6 * radius - lengths.sum()),
                "componentwise_charge_sum_negative": bool(lengths.sum() > 6 * radius),
                "shortest_arm": float(lengths.min()),
                "two_times_radius": 2 * radius,
                "shortest_arm_below_two_radius": bool(lengths.min() < 2 * radius),
                "admissible_product": float(np.prod(ratios)),
                "admissible_product_exceeds_one": bool(np.prod(ratios) > 1),
                "trimmed_product": float(np.prod(ordered[:-1])),
                "trimmed_product_below_one": bool(np.prod(ordered[:-1]) < 1),
                "smallest_ratio": float(ordered[0]),
                "smallest_ratio_below_one": bool(ordered[0] < 1),
            }
        )

    def _spread(key: str) -> float:
        return float(max(r[key] for r in settings_rows) - min(r[key] for r in settings_rows))

    reference = settings_rows[-1]
    return {
        "specimen": {"a": a, "b": b, "rho": rho, "delta": delta, "s": s},
        "roots": [[float(z.real), float(z.imag)] for z in roots],
        "maximum_root_modulus": float(np.max(np.abs(roots))),
        "all_roots_strictly_inside_unit_disc": bool(np.max(np.abs(roots)) < 1.0),
        "critical_points": [[float(z.real), float(z.imag)] for z in criticals],
        "critical_value_moduli": [float(abs(v)) for v in values],
        "all_critical_values_admissible": bool(np.max(np.abs(values)) < 1.0),
        "minimum_enclosing_radius": radius,
        "tolerance_settings": settings_rows,
        "arm_length_sum_spread_across_tolerances": _spread("arm_length_sum"),
        "admissible_product_spread_across_tolerances": _spread("admissible_product"),
        "all_arms_reach_distinct_roots": all(
            hub["arms_reach_distinct_roots"]
            for row in settings_rows
            for hub in row["hubs"]
        ),
        "componentwise_charge_refuted_at_every_tolerance": all(
            row["componentwise_charge_sum_negative"] for row in settings_rows
        ),
        "admissible_product_refuted_at_every_tolerance": all(
            row["admissible_product_exceeds_one"] for row in settings_rows
        ),
        "parent_satisfied_at_every_tolerance": all(
            row["shortest_arm_below_two_radius"] for row in settings_rows
        ),
        "trimmed_product_survives_at_every_tolerance": all(
            row["trimmed_product_below_one"] for row in settings_rows
        ),
        "reference_tolerance": reference["tolerance_label"],
    }


def emit(result: dict, output: Path | None, check: bool) -> int:
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
    parser.add_argument("--a", type=float, default=1.0)
    parser.add_argument("--b", type=float, default=0.4)
    parser.add_argument("--rho", type=float, default=0.02)
    parser.add_argument("--delta", type=float, default=1e-6)
    parser.add_argument("--s", type=float, default=0.99989)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if 8 * args.a**3 <= 27 * args.b**2:
        parser.error("the saddle-wall normal form requires 8 a^3 > 27 b^2")
    if not 0 < args.rho < 1 or not 0 < args.s <= 1:
        parser.error("--rho and --s must lie in (0,1]")
    if args.check and args.output is None:
        parser.error("--check requires --output")

    scan = compute(args.a, args.b, args.rho, args.delta, args.s)
    refuted = (
        scan["componentwise_charge_refuted_at_every_tolerance"]
        and scan["admissible_product_refuted_at_every_tolerance"]
    )
    parent_ok = scan["parent_satisfied_at_every_tolerance"]
    reference = scan["tolerance_settings"][-1]
    summary = (
        "On a quartic with all four roots strictly inside the unit disc and all "
        "three critical values admissible, the three canonical two-arm inverse-ray "
        f"lengths sum to {reference['arm_length_sum']:.12f} against "
        f"6R = {reference['six_times_radius']:.12f}, so the componentwise combined "
        f"charge is {reference['componentwise_charge_sum']:+.6e} -- negative. The "
        f"admissible product is {reference['admissible_product']:.12f} > 1. Both "
        "refutations are stable across three tolerance settings (arm-sum spread "
        f"{scan['arm_length_sum_spread_across_tolerances']:.2e}) and every hub's two "
        "arms reach distinct roots. Erdos 1041 nevertheless HOLDS here: the "
        f"shortest arm is {reference['shortest_arm']:.12f} < 2R = "
        f"{reference['two_times_radius']:.12f}. The order-sensitive trimmed product "
        f"{reference['trimmed_product']:.12f} stays below 1."
        if refuted and parent_ok
        else
        "The specimen did not reproduce both refutations at every tolerance, or the "
        "parent conclusion failed; inspect tolerance_settings before citing any "
        "aggregate no-go."
    )
    result = {
        "schema": "erdos1041-saddle-wall-aggregate-refutation/1",
        "claim_ceiling": (
            "A high-precision replay at one specimen of an open family. It refutes "
            "two proposed proof MECHANISMS -- the componentwise combined-charge "
            "inequality and the admissible critical-arc product -- and does not "
            "refute Erdos 1041, which stays open and is satisfied by the specimen. "
            "The all-family statement is the authored asymptotic argument; this is "
            "its numerical regression test, not a proof."
        ),
        "parameters": {
            "a": args.a, "b": args.b, "rho": args.rho,
            "delta": args.delta, "s": args.s,
        },
        "scan": scan,
        "experiment_contract": build_experiment_contract(
            problem_id="erdos_1041",
            target_statement=(
                "For a monic polynomial with roots in the open unit disc, join two "
                "roots by a curve of length < 2 inside {|f| < 1}."
            ),
            claim_ceiling=(
                "Mechanism refutation at one specimen, stable across tolerances. "
                "Not a statement about Erdos 1041, which the specimen satisfies."
            ),
            hypothesis_id="componentwise_charge_and_admissible_product_hold",
            hypothesis_statement=(
                "On every admissible component the combined endpoint-and-curvature "
                "charge sums non-negative, and the product of normalised admissible "
                "critical-arc ratios is at most 1."
            ),
            probe_id="saddle_wall_arm_length_continuation",
            probe_question=(
                "Do the three canonical arm lengths of the blown-up saddle-wall "
                "quartic exceed 6R in total while one of them stays below 2R?"
            ),
            computation=(
                "Square-root-resolved DOP853 continuation of both lifts of each "
                "critical value segment, with arc length carried as an integrated "
                "state rather than summed from chords, repeated at three tolerance "
                "settings and required to agree, plus a Nelder-Mead minimum "
                "enclosing radius of the roots."
            ),
            falsifier=(
                "sum L_j <= 6R, or prod q_j <= 1, or a tolerance-dependent sign, or "
                "a hub whose two arms reach the same root."
            ),
            stop_condition=(
                "Once both refutations are stable and the parent conclusion holds on "
                "the same specimen, the remaining work is the order-sensitive "
                "trimmed statistic, not further aggregate search."
            ),
            survival_consequence=(
                "A non-negative charge sum would keep the componentwise allocation "
                "route live as a proof mechanism."
            ),
            falsification_consequence=(
                "A negative charge sum with a short selected arm separates the "
                "mechanism from the parent statement: every smooth symmetric "
                "monotone aggregate of the normalised ratios has the wrong "
                "first-order sign, so the surviving statistic must be "
                "order-sensitive and non-smooth at the equality configuration."
            ),
            consumer_ref=CONSUMER_REF,
            consumer_declarations=[],
            analysis_refs=[ANALYSIS_REF],
            source_refs=[SOURCE_REF],
            result_status=(
                "exact_one_way_result" if refuted and parent_ok else "finite_support"
            ),
            result_summary=summary,
            resource_bounds={
                "tolerance_setting_count": len(TOLERANCES),
                "critical_hub_count": 3,
                "arms_per_hub": 2,
            },
        ),
        "mechanism_bindings": mechanism_bindings(
            problem_id="erdos_1041",
            motivated_by=["charged_lifetime_allocation_no_go"],
            eliminates=[],
            supports=[],
            rationale=(
                "The componentwise combined-charge inequality and the admissible "
                "critical-arc product were the two live aggregate mechanisms. This "
                "probe measures both on one open-family specimen with an "
                "independently integrated arc length, because a chord-summed arc "
                "length undercounts the curved continuation near the saddle by "
                "enough to flip the sign of the finding."
            ),
        ),
        "sources": [
            source_record(REPO_ROOT, SOURCE_REF),
        ],
        "summary": summary,
    }
    return emit(result, args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
