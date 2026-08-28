#!/usr/bin/env python3
"""Fail-closed audit for the transverse finite quintic transfer.

The expensive geometric work is delegated to the already published mixed
atlas.  This checker reruns its cover, strengthens every strict exact interval
certificate to a common 1e-8 margin, and checks the rational budgets used to
transfer those model connectors to actual near-regular quintics.
"""

from __future__ import annotations

import importlib.util
import json
import pathlib
import sys
from fractions import Fraction


HERE = pathlib.Path(__file__).resolve().parent
ATLAS_PATH = HERE / "check_erdos1041_quintic_mixed_global_atlas.py"
SPEC = importlib.util.spec_from_file_location("erdos1041_quintic_atlas", ATLAS_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("could not load the mixed-atlas checker")
ATLAS = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = ATLAS
SPEC.loader.exec_module(ATLAS)

STRICT_MARGIN = Fraction(1, 100_000_000)
RHO_MAX = Fraction(1, 10**20)
TRANSFER_CONSTANT = 10**6
LOCAL_SPLIT = 10**9


def accepted_atlas():
    atlas = ATLAS.Atlas()
    stack = ATLAS.initial_boxes()
    certified = []
    local = []
    failures = []
    while stack:
        box = stack.pop()
        if ATLAS.local_equality_box(box):
            local.append(box)
            continue
        ok, candidate, upper = atlas.certify(box)
        if ok and candidate is not None:
            certified.append((box, candidate, upper))
            continue
        if box.depth >= ATLAS.MAX_DEPTH:
            failures.append((box, upper))
            continue
        stack.extend(ATLAS.subdivide(box))
    return atlas, certified, local, failures


def exact_group_has_margin(replay, candidate, boxes) -> bool:
    controls = replay.controls(candidate)
    radius = ATLAS.fraction_of_float(candidate.radius)
    margin_scaled = (STRICT_MARGIN.numerator * ATLAS.SCALE) // STRICT_MARGIN.denominator
    for box in boxes:
        a_value, b_value, delta_a, delta_b = replay.exact_box_coefficients(box)
        a, b = replay.point(a_value), replay.point(b_value)
        robust = ATLAS.Interval.fraction(radius * delta_a + radius**2 * delta_b)
        for control_a, control_b, control_fixed in controls:
            value = (
                ATLAS.complex_mul(a, control_a)[0]
                + ATLAS.complex_mul(b, control_b)[0]
                + control_fixed[0]
                + robust
            )
            if value.hi > -margin_scaled:
                return False
        for root_index in (candidate.first, candidate.second):
            projection_a = ATLAS.complex_mul(a, replay.roots[root_index])[0]
            projection_b = ATLAS.complex_mul(
                b, replay.root_powers[((2 * root_index) % 5, 1)]
            )[0]
            a_upper = projection_a + ATLAS.Interval.fraction(delta_a)
            b_upper = projection_b + ATLAS.Interval.fraction(delta_b)
            linear = a_upper.scale(radius)
            quadratic = b_upper.scale(radius**2)
            quintic = ATLAS.Interval.fraction(radius**5)
            if (linear + quadratic - quintic).hi > -margin_scaled:
                return False
            if quadratic.hi > 0 and (quadratic - quintic.scale(Fraction(4))).hi > -margin_scaled:
                return False
    return True


def exact_cubic_margin_lower(replay) -> float:
    w = replay.w
    w2 = ATLAS.square_interval(w)
    w3 = ATLAS.interval_power(w, 3)
    q_left = (-(
        w3.scale(Fraction(13)) - w2.scale(Fraction(40))
        - w.scale(Fraction(200)) + ATLAS.Interval.integer(520)
    )).scale(Fraction(1, 160))
    y_direction = (-(
        w3.scale(Fraction(3)) - w.scale(Fraction(40)) - ATLAS.Interval.integer(40)
    )).scale(Fraction(1, 80))
    y = ATLAS.cube_root_interval(q_left * ATLAS.interval_power(y_direction, 3))
    margin = ATLAS.interval_power(y, 3).scale(Fraction(12))
    if margin.lo * 4 <= ATLAS.SCALE:
        raise AssertionError("the exact cubic average margin did not exceed 1/4")
    return ATLAS.interval_decimal(margin.lo)


def rational_budget_checks() -> dict[str, bool]:
    delta_max = Fraction(17, 2500)
    rho = RHO_MAX

    # Strict atlas: the deliberately coarse finite-transfer error is still six
    # orders of magnitude below the exact common model slack.
    strict_absorption = TRANSFER_CONSTANT * rho < STRICT_MARGIN

    # If delta >= 1e9 rho, replace the transfer error by delta/1000 and use
    # 59/1000 - 8(17/2500) - 1/1000 = 18/5000 > 0.
    tetrahedral_coefficient = (
        Fraction(59, 1000) - 8 * delta_max - Fraction(1, 1000)
    )
    tetrahedral_absorption = (
        TRANSFER_CONSTANT <= LOCAL_SPLIT // 1000
        and tetrahedral_coefficient > 0
    )

    # If delta < 1e9 rho, the extended cubic selector supplies at least rho/4.
    # The displayed expression is the worst normalized remainder divided by rho.
    cubic_remainder_ratio = (
        8 * LOCAL_SPLIT**2 * rho
        + TRANSFER_CONSTANT * LOCAL_SPLIT * rho
        + TRANSFER_CONSTANT * rho
    )
    cubic_absorption = cubic_remainder_ratio < Fraction(1, 4)

    # On 10 rho <= t <= 1/2, absolute Fourier bounds leave more than
    # 998/1000 of the -t^5 term.  The three explicit B_4 terms use less than
    # 1/50 of t^5 (the baseline logarithm alone uses exactly at most 1/62).
    coarse_positive_ratio = (
        Fraction(1, 10_000)
        + Fraction(1, 1000)
        + Fraction(9, 100) * rho
        + Fraction(9, 10) * rho**2
        + 87 * rho**3
    )
    intermediate_model = coarse_positive_ratio < Fraction(2, 1000)
    eta_upper = Fraction(24, 5) * rho**3
    alpha_upper = 2 * eta_upper
    anchored_independent_ratio = (
        10 * eta_upper
        + 5 * alpha_upper**2 / (10**5 * rho**5)
        + Fraction(1, 62)
    )
    intermediate_remainder = anchored_independent_ratio < Fraction(1, 50)

    # The old far-half telescoping budget: 95 eta < 1/32 <= t^5.
    far_half = 95 * eta_upper < Fraction(1, 32)

    return {
        "strict_atlas_absorption": strict_absorption,
        "tetrahedral_large_delta_absorption": tetrahedral_absorption,
        "cubic_small_delta_absorption": cubic_absorption,
        "intermediate_ray_model_margin": intermediate_model,
        "intermediate_ray_remainder": intermediate_remainder,
        "far_half_telescope": far_half,
    }


def main() -> None:
    atlas, certified, local, failures = accepted_atlas()
    replay = ATLAS.ExactReplay()
    grouped = {}
    for box, candidate, _ in certified:
        grouped.setdefault(candidate, []).append(box)
    exact_margin_groups = sum(
        exact_group_has_margin(replay, candidate, boxes)
        for candidate, boxes in grouped.items()
    )
    exact_local = sum(replay.verify_local_box(box) for box in local)
    local_audit = replay.verify_local_constants()
    local_ray_margin = -float(local_audit["largest_ray_endpoint_upper"])
    cubic_margin_lower = exact_cubic_margin_lower(replay)
    budgets = rational_budget_checks()
    status = (
        not failures
        and exact_margin_groups == len(grouped)
        and exact_local == len(local)
        and bool(local_audit["pass"])
        and local_ray_margin > float(STRICT_MARGIN)
        and cubic_margin_lower > 0.25
        and all(budgets.values())
    )
    result = {
        "schema": "erdos1041_quintic_transverse_finite_transfer_check_v1",
        "rho_max": float(RHO_MAX),
        "common_strict_atlas_margin": float(STRICT_MARGIN),
        "transfer_constant": TRANSFER_CONSTANT,
        "local_split_delta_over_rho": LOCAL_SPLIT,
        "certified_strict_box_count": len(certified),
        "certified_local_box_count": len(local),
        "selected_candidate_group_count": len(grouped),
        "exact_margin_group_count": exact_margin_groups,
        "exact_local_box_count": exact_local,
        "failure_count": len(failures),
        "local_ray_endpoint_margin_lower": local_ray_margin,
        "cubic_average_margin_lower": cubic_margin_lower,
        "rational_budget_checks": budgets,
        "status": "PASS" if status else "INCOMPLETE",
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    if not status:
        raise SystemExit(2)


if __name__ == "__main__":
    main()
