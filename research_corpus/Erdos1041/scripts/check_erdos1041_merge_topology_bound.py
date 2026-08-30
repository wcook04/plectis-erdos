#!/usr/bin/env python3
"""Erdos #1041: three falsification tests around the minimum-critical hub.

What is being decided
---------------------
`CriticalBudgetLab.md` refutes the per-branch bound `L_branch <= |f(c)|^(1/n)`
over branches at *all* admissible hubs (worst factor 1.678 at n=8), and gives
the structural reason: `|f(c)|` is a **symmetric** function of the distances
from `c` to the roots, so it cannot see which root the branch actually reaches.
Its closing sentence names the constraint on every surviving route --- "a
working bound has to see the merge topology".

`MinimumCriticalNewtonHubLab.md` proves `rho <= R` for `rho = |f(c*)|^(1/n)` at
the minimum-critical hub via the discriminant/Fekete sandwich, and splits the
target into

    strong:  L_1 + L_2 <= 2 rho
    weak:    L_1 + L_2 <= 2 R      (this one implies #1041)

It records that the strong statement "may be false" and names
`critical_scale_normalized_minimum_critical_newton_hub_score` as its dedicated
one-way falsifier.  No outcome for that objective is recorded in any lab file.

Three tests, run here:

  TEST A   L(c*) <= 2 |f(c*)|^(1/n)                      (the strong statement)
  TEST B   L_branch(c -> a) <= n |f(c)| / |f'(a)|        (CONJECTURE C)
  TEST C   n |f(c*)| (1/|f'(a)| + 1/|f'(b)|) <= 2 R      (summed form of C)

TEST B is the merge-topology-aware candidate the refutation asks for: because
`f'(a) = prod_{i != a} (a - z_i)` depends on the *endpoint* root, the right-hand
side is not a symmetric function of the root positions relative to `c`, so the
recorded structural refutation does not apply to it.  B and C together would
close #1041, since C's right-hand side is `2R` and `rho <= R`.

Normalisation
-------------
Roots are translated so the circumcentre (centre of the smallest enclosing
circle) is the origin; then `R = max_j |z_j|` equals the circumradius and the
two conventions in the corpus coincide.  Translation changes no critical value,
no `f'(a)`, and no arc length, so it moves only `R`, and it moves it to the
smallest legitimate value --- the adversarial choice for TEST C.

Instruments
-----------
Primary: `descending_pair` from `system/lib/formal_math_lemniscate.py`, the
residual-gated continuation the corpus trusts.  `descend_branches` in
`formal_math/probes/erdos1041_critical_budget.py` is NOT used: its own docstring
records that it mistracks and produced three retracted counterexamples.

Secondary, independent: `independent_branch` below.  Different integrator (RK4
predictor with a Newton projection back onto the exact level set), different
length quadrature (Simpson on |z'| at projected points), and an explicit
anti-hop gate --- a corrector displacement larger than a fixed fraction of the
predictor displacement rejects the step and halves it.  The primary instrument's
level residual cannot see a hop between two preimages of the *same* value, since
both satisfy the level equation; the anti-hop gate is what closes that hole.

Every reported violation is required to pass both instruments, to agree between
them on the endpoint root index and on the length, and to survive a tolerance
sweep.  Mistrack counts are reported, not discarded silently.

Claim ceiling: numerical continuation is candidate evidence.  A ratio below
threshold proves nothing outside the configurations visited; the corpus's own
lesson is that a clean sample is not evidence in this problem.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import sys
from typing import Any

import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[5]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_lemniscate import descending_pair  # noqa: E402
from formal_math.erdos257_period_noncollapse.ErdosProblems.Erdos1041.scripts.check_erdos1041_invariant_branch_length import (  # noqa: E402
    circumcircle,
)
from formal_math.erdos257_period_noncollapse.ErdosProblems.Erdos1041.scripts.check_erdos1041_straight_spoke_hub_criterion import (  # noqa: E402
    QC_REFUTATION_WITNESSES as QC_SEED_WITNESSES,
)

SOURCE_REF = (
    "research_corpus/Erdos1041/scripts/"
    "check_erdos1041_merge_topology_bound.py"
)

RCAP = 1.0 - 1.0e-9

# ---- gates -----------------------------------------------------------------
ENDPOINT_TOL = 1.0e-7          # branch endpoint must land this close to a root
LEVEL_RESIDUAL_TOL = 1.0e-8    # max |f(z(u)) - (1-u^2) f(c)| along the branch
CRITICAL_RESIDUAL_TOL = 1.0e-8 # scale-free check that c really is critical
MIN_CRITICAL_VALUE = 1.0e-13   # below this the hub is a multiple root
CROSS_LENGTH_TOL = 1.0e-5      # relative length agreement between instruments


# --------------------------------------------------------------- basic algebra


def normalise(roots: np.ndarray) -> tuple[np.ndarray, float]:
    """Translate the circumcentre to the origin; return roots and R."""

    roots = np.asarray(roots, dtype=np.complex128)
    centre, radius = circumcircle(roots)
    return roots - centre, float(radius)


def clamp(roots: np.ndarray, cap: float = RCAP) -> np.ndarray:
    r = np.abs(roots)
    return roots * np.where(r > cap, cap / np.maximum(r, 1.0e-300), 1.0)


def f_at(roots: np.ndarray, z: complex) -> complex:
    return complex(np.prod(z - roots))


def abs_f_at(roots: np.ndarray, z: complex) -> float:
    """|f(z)| as a product over roots: better conditioned than polyval."""

    return float(np.prod(np.abs(z - roots)))


def abs_fprime_at_root(roots: np.ndarray, index: int) -> float:
    """|f'(z_index)| = prod_{i != index} |z_index - z_i|, from the roots."""

    a = roots[index]
    other = np.delete(roots, index)
    return float(np.prod(np.abs(a - other)))


def critical_residual(roots: np.ndarray, c: complex) -> float:
    """Scale-free residual of sum_i 1/(c - z_i) = 0."""

    d = c - roots
    if np.min(np.abs(d)) < 1.0e-14:
        return math.inf
    terms = 1.0 / d
    denom = float(np.sum(np.abs(terms)))
    if denom <= 0.0:
        return math.inf
    return float(abs(np.sum(terms)) / denom)


def critical_points(roots: np.ndarray) -> np.ndarray:
    der = np.polyder(np.poly(roots))
    if der.size <= 1:
        return np.array([], dtype=np.complex128)
    return np.roots(der).astype(np.complex128)


# ------------------------------------------- independent hop-gated continuation


def independent_branch(
    roots: np.ndarray,
    c: complex,
    sign: int,
    *,
    h0: float = 2.0e-3,
    hop_fraction: float = 0.2,
    newton_tol: float = 1.0e-14,
    max_steps: int = 400_000,
) -> dict[str, Any] | None:
    """Track one descending branch with an explicit anti-hop gate.

    Parametrisation `f(z(u)) = (1 - u^2) v`, `v = f(c)`, `u: 0 -> 1`, so
    `z'(u) = -2 u v / f'(z)`.  Each step is an RK4 predictor followed by a
    Newton projection onto the exact level `(1 - u^2) v`.  The step is rejected
    and halved when the projection moves the point by more than
    `hop_fraction` of the predictor displacement, which is the signature of the
    integrator having crossed to a different preimage of the same value.

    Arc length is a composite Simpson rule on `|z'(u)|` evaluated at projected
    points, which is a different quadrature from the primary instrument's
    third ODE component.
    """

    coefficients = np.poly(roots)
    derivative = np.polyder(coefficients)
    second = np.polyder(derivative)
    v = complex(np.polyval(coefficients, c))
    if v == 0:
        return None
    d2 = complex(np.polyval(second, c))
    if abs(d2) < 1.0e-12 * max(1.0, abs(v)):
        return None  # degenerate saddle: more than two branches

    def project(z: complex, u: float) -> tuple[complex, float]:
        """Newton onto f(z) = (1 - u^2) v; returns point and displacement."""

        target = (1.0 - u * u) * v
        z0 = z
        for _ in range(60):
            fp = complex(np.polyval(derivative, z))
            if abs(fp) < 1.0e-300:
                return z, math.inf
            step = (complex(np.polyval(coefficients, z)) - target) / fp
            z = z - step
            if abs(step) < newton_tol * max(1.0, abs(z)):
                break
        else:
            return z, math.inf
        return z, abs(z - z0)

    def speed(z: complex, u: float) -> float:
        fp = complex(np.polyval(derivative, z))
        if abs(fp) < 1.0e-300:
            return math.inf
        return abs(2.0 * u * v / fp)

    def field(z: complex, u: float) -> complex:
        fp = complex(np.polyval(derivative, z))
        if abs(fp) < 1.0e-300:
            return complex(math.inf, math.inf)
        return -2.0 * u * v / fp

    u = 1.0e-7
    off = sign * u * np.sqrt(-2.0 * v / d2)
    z = complex(c + off)
    z, _ = project(z, u)
    length = 0.0
    h = h0
    rejects = 0
    steps = 0
    while u < 1.0 and steps < max_steps:
        steps += 1
        h = min(h, 1.0 - u)
        if h <= 0.0:
            break
        k1 = field(z, u)
        k2 = field(z + 0.5 * h * k1, u + 0.5 * h)
        k3 = field(z + 0.5 * h * k2, u + 0.5 * h)
        k4 = field(z + h * k3, u + h)
        if not all(np.isfinite([abs(k1), abs(k2), abs(k3), abs(k4)])):
            h *= 0.5
            rejects += 1
            if h < 1.0e-13:
                return None
            continue
        predictor = z + (h / 6.0) * (k1 + 2.0 * k2 + 2.0 * k3 + k4)
        moved = abs(predictor - z)
        corrected, displacement = project(predictor, u + h)
        # anti-hop gate: the projection must be a small correction, never a jump
        if (
            not math.isfinite(displacement)
            or displacement > hop_fraction * max(moved, 1.0e-12)
        ):
            h *= 0.5
            rejects += 1
            if h < 1.0e-13:
                return None
            continue
        midpoint_guess = z + 0.5 * h * k1
        midpoint, mid_disp = project(midpoint_guess, u + 0.5 * h)
        if not math.isfinite(mid_disp):
            h *= 0.5
            rejects += 1
            if h < 1.0e-13:
                return None
            continue
        g0 = speed(z, u)
        gm = speed(midpoint, u + 0.5 * h)
        g1 = speed(corrected, u + h)
        if not all(math.isfinite(x) for x in (g0, gm, g1)):
            h *= 0.5
            rejects += 1
            if h < 1.0e-13:
                return None
            continue
        length += (h / 6.0) * (g0 + 4.0 * gm + g1)
        z, u = corrected, u + h
        if displacement < 0.02 * hop_fraction * max(moved, 1.0e-12):
            h = min(h * 1.6, h0)
    if u < 1.0 - 1.0e-12:
        return None
    index = int(np.argmin(np.abs(roots - z)))
    return {
        "root_index": index,
        "length": float(length),
        "endpoint_error": float(abs(roots[index] - z)),
        "rejected_steps": rejects,
        "accepted_steps": steps - rejects,
    }


def independent_pair(roots: np.ndarray, c: complex, **kwargs: Any) -> dict[str, Any] | None:
    left = independent_branch(roots, c, +1, **kwargs)
    right = independent_branch(roots, c, -1, **kwargs)
    if left is None or right is None:
        return None
    if left["root_index"] == right["root_index"]:
        return None
    return {"branches": [left, right]}


def ascend_from_root(
    roots: np.ndarray,
    index: int,
    c: complex,
    *,
    u_stop: float = 1.0e-3,
    rtol: float = 1.0e-11,
    atol: float = 1.0e-13,
) -> dict[str, Any] | None:
    """Continue the inverse branch UPWARD, from a root towards the hub.

    Third instrument, and the one that decides branch identity without ever
    touching the saddle expansion.  Same level family `f(z(u)) = (1-u^2) f(c)`,
    integrated from `u = 1` (at the root, where `f' != 0` and the problem is
    well conditioned) down towards `u = 0` (the hub, where `f' -> 0`).  A root
    is one of the two the hub's branches reach exactly when this ascent ends at
    the hub.  Integration stops at `u_stop` because the field is singular at the
    hub itself; the admissible miss there is the local saddle scale
    `u_stop * |sqrt(-2 f(c) / f''(c))|`.
    """

    from scipy.integrate import solve_ivp

    coefficients = np.poly(roots)
    derivative = np.polyder(coefficients)
    second = np.polyder(derivative)
    v = complex(np.polyval(coefficients, c))
    d2 = complex(np.polyval(second, c))
    if v == 0 or abs(d2) < 1.0e-12 * max(1.0, abs(v)):
        return None
    a = complex(roots[index])

    def field(u: float, state: np.ndarray) -> list[float]:
        z = state[0] + 1j * state[1]
        fp = complex(np.polyval(derivative, z))
        if abs(fp) < 1.0e-300:
            return [0.0, 0.0, 0.0]
        velocity = -2.0 * u * v / fp
        return [velocity.real, velocity.imag, abs(velocity)]

    solution = solve_ivp(
        field, (1.0, u_stop), [a.real, a.imag, 0.0], rtol=rtol, atol=atol
    )
    if not solution.success:
        return None
    endpoint = solution.y[0, -1] + 1j * solution.y[1, -1]
    sampled = solution.y[0] + 1j * solution.y[1]
    residual = float(
        np.abs(np.polyval(coefficients, sampled) - (1.0 - solution.t**2) * v).max()
    )
    saddle_scale = float(abs(np.sqrt(-2.0 * v / d2)))
    miss = float(abs(endpoint - c))
    return {
        "root_index": index,
        "reaches_hub": bool(miss < 12.0 * u_stop * saddle_scale + 1.0e-9),
        "hub_miss": miss,
        "saddle_scale": saddle_scale,
        "length_to_u_stop": float(solution.y[2, -1]),
        "maximum_level_residual": residual,
    }


def pair_from_ascent(roots: np.ndarray, c: complex, **kwargs: Any) -> dict[str, Any]:
    """Which roots reach the hub when continued upward.  Tracker-free identity."""

    hits: list[int] = []
    misses: list[float] = []
    residual = 0.0
    for index in range(len(roots)):
        row = ascend_from_root(roots, index, c, **kwargs)
        if row is None:
            return {"decided": False, "pair": None}
        residual = max(residual, row["maximum_level_residual"])
        misses.append(row["hub_miss"] / max(1.0e-300, row["saddle_scale"]))
        if row["reaches_hub"]:
            hits.append(index)
    return {
        "decided": len(hits) == 2,
        "pair": tuple(sorted(hits)) if len(hits) == 2 else None,
        "hit_count": len(hits),
        "scaled_misses": sorted(misses),
        "maximum_level_residual": residual,
    }


# ------------------------------------------------------------------ hub tables


def hub_table(
    roots: np.ndarray,
    *,
    rtol: float = 1.0e-10,
    atol: float = 1.0e-12,
    verify: bool = False,
    star_only: bool = False,
) -> dict[str, Any]:
    """Every admissible simple hub with its two gated branches and ratios."""

    n = len(roots)
    hubs: list[dict[str, Any]] = []
    rejected = 0
    disagreements = 0
    candidates = list(critical_points(roots))
    if star_only:
        # TEST A, TEST C and ratio_B_star only ever read the minimum-critical
        # hub, so tracking the other n-2 hubs is pure cost during a search.
        live = [c for c in candidates if abs_f_at(roots, c) > MIN_CRITICAL_VALUE]
        candidates = [min(live, key=lambda c: abs_f_at(roots, c))] if live else []
    for c in candidates:
        value_modulus = abs_f_at(roots, c)
        if value_modulus <= MIN_CRITICAL_VALUE or value_modulus >= 1.0:
            continue
        if critical_residual(roots, c) > CRITICAL_RESIDUAL_TOL:
            rejected += 1
            continue
        pair = descending_pair(roots, c, relative_tolerance=rtol, absolute_tolerance=atol)
        if pair is None:
            rejected += 1
            continue
        if (
            pair["maximum_endpoint_error"] > ENDPOINT_TOL
            or pair["maximum_level_residual"] > LEVEL_RESIDUAL_TOL
        ):
            rejected += 1
            continue
        branches = []
        ok = True
        for branch in pair["branches"]:
            index = int(branch["root_index"])
            fprime = abs_fprime_at_root(roots, index)
            if fprime <= 0.0:
                ok = False
                break
            branches.append(
                {
                    "root_index": index,
                    "length": float(branch["length"]),
                    "abs_fprime_root": fprime,
                    "ratio_B": float(branch["length"]) * fprime / (n * value_modulus),
                    "endpoint_error": float(branch["endpoint_error"]),
                }
            )
        if not ok:
            rejected += 1
            continue
        if verify:
            check = independent_pair(roots, c)
            if check is None:
                rejected += 1
                disagreements += 1
                continue
            matched = True
            for branch in branches:
                mate = [
                    b for b in check["branches"] if b["root_index"] == branch["root_index"]
                ]
                if not mate:
                    matched = False
                    break
                relative = abs(mate[0]["length"] - branch["length"]) / max(
                    1.0e-12, branch["length"]
                )
                if relative > CROSS_LENGTH_TOL:
                    matched = False
                    break
                branch["independent_length"] = float(mate[0]["length"])
                branch["length_relative_gap"] = float(relative)
            if not matched:
                rejected += 1
                disagreements += 1
                continue
        hubs.append(
            {
                "critical_point": [float(c.real), float(c.imag)],
                "critical_value_modulus": value_modulus,
                "total_length": float(sum(b["length"] for b in branches)),
                "branches": branches,
                "maximum_level_residual": float(pair["maximum_level_residual"]),
                "maximum_endpoint_error": float(pair["maximum_endpoint_error"]),
            }
        )
    return {
        "hubs": hubs,
        "rejected_hub_count": rejected,
        "instrument_disagreement_count": disagreements,
    }


def measure(
    roots: np.ndarray,
    *,
    rtol: float = 1.0e-10,
    atol: float = 1.0e-12,
    verify: bool = False,
    confirm: bool = False,
    star_only: bool = False,
) -> dict[str, Any] | None:
    """Ratios A, B and C for one root configuration, or None if ungated.

    With ``star_only`` the hub loop is restricted to the minimum-critical hub,
    which is all TEST A, TEST C and ``ratio_B_star`` read; ``ratio_B`` then
    reports only that hub and must not be used as the all-hub objective.
    """

    roots, radius = normalise(clamp(np.asarray(roots, dtype=np.complex128)))
    n = len(roots)
    if n < 2 or radius <= 0.0:
        return None
    table = hub_table(roots, rtol=rtol, atol=atol, verify=verify, star_only=star_only)
    hubs = table["hubs"]
    if not hubs:
        return None

    ratio_b = max(b["ratio_B"] for hub in hubs for b in hub["branches"])
    worst_b_hub = max(
        hubs, key=lambda hub: max(b["ratio_B"] for b in hub["branches"])
    )

    # the minimum-critical hub is the global minimiser over critical points,
    # not merely over the hubs that happened to pass the gates
    all_values = [
        abs_f_at(roots, c)
        for c in critical_points(roots)
        if abs_f_at(roots, c) > MIN_CRITICAL_VALUE
    ]
    if not all_values:
        return None
    global_minimum = min(all_values)
    star = min(hubs, key=lambda hub: hub["critical_value_modulus"])
    star_is_global = star["critical_value_modulus"] <= global_minimum * (1.0 + 1.0e-9)
    if not star_is_global:
        # The minimum-critical critical point failed the gates, so the hub that
        # survived is NOT c*.  Reporting A, B_star or C from it measures the
        # wrong hub, and at a loose tolerance that fabricates violations: a
        # degree-6 configuration read A = 1.0446 at rtol 1e-8 and A = 0.5462
        # once the true c* was gated in.  Refuse the configuration instead.
        return None

    mu = star["critical_value_modulus"]
    rho = mu ** (1.0 / n)
    ratio_a = star["total_length"] / (2.0 * rho)
    inverse_sum = sum(1.0 / b["abs_fprime_root"] for b in star["branches"])
    ratio_c = n * mu * inverse_sum / (2.0 * radius)

    # TEST C's only tracker-dependent input is WHICH pair the branches reach:
    # mu, |f'(a)|, |f'(b)| and R are exact algebra on the roots.  Record the
    # value under the least favourable pair choice too, because when that also
    # exceeds one the verdict is independent of every branch instrument.
    inverse_fprime = np.sort(
        np.array([1.0 / abs_fprime_at_root(roots, i) for i in range(n)])
    )
    ratio_c_worst_pair = (
        n * mu * float(inverse_fprime[0] + inverse_fprime[1]) / (2.0 * radius)
    )

    confirmation: dict[str, Any] | None = None
    if confirm:
        star_c = complex(star["critical_point"][0], star["critical_point"][1])
        ascent = pair_from_ascent(roots, star_c)
        tracked = tuple(sorted(b["root_index"] for b in star["branches"]))
        confirmation = {
            "tracked_pair": list(tracked),
            "ascent_pair": None if ascent["pair"] is None else list(ascent["pair"]),
            "ascent_decided": bool(ascent["decided"]),
            "ascent_agrees": bool(ascent["pair"] == tracked),
            "ascent_hit_count": ascent.get("hit_count"),
            "ascent_scaled_misses": ascent.get("scaled_misses", [])[:4],
            "ascent_maximum_level_residual": ascent.get("maximum_level_residual"),
        }
    return {
        "degree": n,
        "circumradius": radius,
        "roots": [[float(z.real), float(z.imag)] for z in roots],
        "rho": rho,
        "rho_le_R": bool(rho <= radius * (1.0 + 1.0e-9)),
        "minimum_critical_hub_is_global": bool(star_is_global),
        "ratio_A": float(ratio_a),
        "ratio_B": float(ratio_b),
        "ratio_C": float(ratio_c),
        "ratio_C_worst_pair": float(ratio_c_worst_pair),
        # Conjecture C restricted to the minimum-critical hub.  The symmetric
        # bound's recorded violations live almost entirely at NON-minimal hubs,
        # so this is the sub-statement the corpus's refutation leaves standing.
        "ratio_B_star": float(max(
            b["length"] * b["abs_fprime_root"] / (n * mu) for b in star["branches"]
        )),
        # the per-branch symmetric bound CriticalBudgetLab refuted, split by
        # whether the branch sits at the minimum-critical hub or elsewhere
        "symmetric_per_branch_at_star": float(
            max(b["length"] for b in star["branches"]) / rho
        ),
        "symmetric_per_branch_all_hubs": float(
            max(
                b["length"] / hub["critical_value_modulus"] ** (1.0 / n)
                for hub in hubs
                for b in hub["branches"]
            )
        ),
        "pair_confirmation": confirmation,
        "star_hub": star,
        "worst_B_hub": worst_b_hub,
        "admissible_hub_count": len(hubs),
        "rejected_hub_count": table["rejected_hub_count"],
        "instrument_disagreement_count": table["instrument_disagreement_count"],
    }


# ---------------------------------------------------------------- calibrations


def analytic_power_family(n: int, r: float) -> dict[str, Any]:
    """`z^n - r^n`: every ratio is exactly one, by hand.

    `c = 0`, `mu = r^n`, `rho = r`, `R = r`; the branch solving `z^n = r^n - t`
    has length `T^(1/n) = r`; `|f'(a)| = n r^(n-1)`.  Hence
    `L/(2 rho) = 2r/2r = 1`, `L_branch |f'(a)|/(n mu) = r n r^(n-1)/(n r^n) = 1`
    and `n mu (2/(n r^(n-1)))/(2r) = 1`.  For `n >= 3` the critical point at the
    origin is degenerate, so the simple-saddle instruments do not apply and this
    row is the ordinary computation, not a measurement.
    """

    mu = r**n
    rho = mu ** (1.0 / n)
    length_branch = r
    fprime = n * r ** (n - 1)
    return {
        "family": "z^n - r^n",
        "degree": n,
        "r": r,
        "mu": mu,
        "rho": rho,
        "ratio_A": (2.0 * length_branch) / (2.0 * rho),
        "ratio_B": length_branch * fprime / (n * mu),
        "ratio_C": n * mu * (2.0 / fprime) / (2.0 * r),
        "exact": True,
    }


def cassini_row(a: float, **kwargs: Any) -> dict[str, Any] | None:
    """`z^2 - a^2`: the one power-family member with a simple critical point."""

    row = measure(np.array([a, -a], dtype=np.complex128), **kwargs)
    if row is None:
        return None
    return {"family": "z^2 - a^2", "a": a, **row}


def hard_witness_validation() -> list[dict[str, Any]]:
    """Reproduce the exact degree-6 and degree-9 branch totals before trusting anything.

    `StraightSpokeHubCriterionLab.md` records `1.763942` and `1.545995` as the
    minimum descending-branch-pair total over admissible hubs on two exact
    witnesses stored as IEEE-754 hexadecimal literals (their separation margins
    are near 1e-5 and do not survive decimal rounding, so the literals are read
    from the verifier, never retyped).  Both instruments are required to land on
    those numbers; the independent tracker is checked against the primary one on
    the very hubs the lab pinned.
    """

    from formal_math.erdos257_period_noncollapse.ErdosProblems.Erdos1041.scripts.check_erdos1041_straight_spoke_hub_criterion import (  # noqa: E402
        QC_REFUTATION_WITNESSES,
    )

    recorded = {6: 1.763942, 9: 1.545995}
    rows: list[dict[str, Any]] = []
    for degree, literals in QC_REFUTATION_WITNESSES.items():
        roots = np.asarray(
            [complex(float.fromhex(re), float.fromhex(im)) for re, im in literals],
            dtype=np.complex128,
        )
        primary = math.inf
        secondary = math.inf
        endpoint_error = 0.0
        level_residual = 0.0
        for c in critical_points(roots):
            if abs_f_at(roots, c) >= 1.0 or abs_f_at(roots, c) <= MIN_CRITICAL_VALUE:
                continue
            pair = descending_pair(
                roots, c, relative_tolerance=1.0e-12, absolute_tolerance=1.0e-14
            )
            if pair is None or pair["maximum_endpoint_error"] > 1.0e-8:
                continue
            primary = min(primary, float(pair["total_length"]))
            endpoint_error = max(endpoint_error, float(pair["maximum_endpoint_error"]))
            level_residual = max(level_residual, float(pair["maximum_level_residual"]))
            check = independent_pair(roots, c)
            if check is not None:
                secondary = min(
                    secondary, sum(b["length"] for b in check["branches"])
                )
        target = recorded[degree]
        rows.append(
            {
                "degree": degree,
                "recorded_minimum_branch_pair_total": target,
                "primary_instrument": None if primary == math.inf else primary,
                "independent_instrument": None if secondary == math.inf else secondary,
                "primary_absolute_gap": (
                    None if primary == math.inf else abs(primary - target)
                ),
                "reproduced_to_recorded_digits": (
                    primary != math.inf and abs(primary - target) < 5.0e-7
                ),
                "maximum_endpoint_error": endpoint_error,
                "maximum_level_residual": level_residual,
                "measured": measure(roots, rtol=1.0e-12, atol=1.0e-14, confirm=True),
            }
        )
    return rows


def centre_plus_polygon(n: int, r: float) -> np.ndarray:
    """`f(z) = z (z^(n-1) - r^(n-1))`: one root at the centre, `n-1` on a circle."""

    return np.concatenate(
        [np.array([0.0 + 0.0j]), r * np.exp(2j * np.pi * np.arange(n - 1) / (n - 1))]
    )


def centre_plus_polygon_closed_form(n: int) -> float:
    """TEST C on that family, by hand: `n^((n-2)/(n-1)) / 2`, independent of `r`.

    `f'(z) = n z^(n-1) - r^(n-1)`, so every critical point satisfies
    `c^(n-1) = r^(n-1)/n` and all `n-1` critical values share the modulus

        mu = |c| r^(n-1) (n-1)/n = r^n (n-1) / n^(n/(n-1)).

    The circumradius is `r`.  The two branches at the hub reach the centre root
    and one outer root, where `|f'(0)| = r^(n-1)` and
    `|f'(r w^k)| = (n-1) r^(n-1)`, so

        n mu (1/|f'(0)| + 1/|f'(r w^k)|) / (2 r)
          = n . r^n (n-1)/n^(n/(n-1)) . (n/(n-1)) / (r^(n-1) . 2 r)
          = n^(2 - n/(n-1)) / 2
          = n^((n-2)/(n-1)) / 2,

    which is `2^(1/3) = 1.259921` at `n = 4` and grows like `n/2`.  So TEST C is
    not merely false, it is unbounded, and the only numerical input to the
    refutation is which pair the branches reach --- decided independently by
    :func:`pair_from_ascent`.
    """

    return float(n ** ((n - 2) / (n - 1)) / 2.0)


def centre_plus_polygon_rows(
    degrees: tuple[int, ...] = (3, 4, 5, 6, 8, 10, 12, 16, 20, 30),
    radii: tuple[float, ...] = (0.95, 0.999),
) -> list[dict[str, Any]]:
    """Measured against the closed form, with the pair identity confirmed."""

    rows: list[dict[str, Any]] = []
    for n in degrees:
        for r in radii:
            row = measure(
                centre_plus_polygon(n, r),
                rtol=1.0e-12,
                atol=1.0e-14,
                confirm=(n <= 12),
            )
            closed = centre_plus_polygon_closed_form(n)
            rows.append(
                {
                    "family": "z (z^(n-1) - r^(n-1))",
                    "degree": n,
                    "r": r,
                    "closed_form_ratio_C": closed,
                    "measured_ratio_C": None if row is None else row["ratio_C"],
                    "absolute_gap": (
                        None if row is None else abs(row["ratio_C"] - closed)
                    ),
                    "ratio_A": None if row is None else row["ratio_A"],
                    "ratio_B": None if row is None else row["ratio_B"],
                    "pair_confirmation": None if row is None else row["pair_confirmation"],
                }
            )
    return rows


def perturbed_polygon(n: int, r: float, epsilon: float, rng: np.random.Generator) -> np.ndarray:
    """Regular n-gon with the degenerate saddle split by an angular kick."""

    angles = 2.0 * np.pi * np.arange(n) / n + epsilon * rng.normal(size=n)
    return clamp(r * np.exp(1j * angles))


# --------------------------------------------------------------------- sampling


def random_roots(n: int, rng: np.random.Generator, style: str) -> np.ndarray:
    if style == "spread":
        radii = rng.uniform(0.2, RCAP, n)
        return clamp(radii * np.exp(2j * np.pi * rng.uniform(0.0, 1.0, n)))
    if style == "clustered":
        k = max(2, n // 2)
        centre = 0.5 * rng.uniform(-1.0, 1.0) + 0.5j * rng.uniform(-1.0, 1.0)
        scale = 10.0 ** rng.uniform(-3.0, -0.7)
        cluster = centre + scale * (rng.normal(size=k) + 1j * rng.normal(size=k))
        rest = rng.uniform(0.3, RCAP, n - k) * np.exp(
            2j * np.pi * rng.uniform(0.0, 1.0, n - k)
        )
        return clamp(np.concatenate([cluster, rest]))
    if style == "near_circle":
        radii = rng.uniform(0.97, RCAP, n)
        return clamp(radii * np.exp(2j * np.pi * rng.uniform(0.0, 1.0, n)))
    # near_polygon
    angles = 2.0 * np.pi * np.arange(n) / n + rng.uniform(0.005, 0.4) * rng.normal(size=n)
    radii = RCAP * (1.0 - rng.uniform(0.0, 0.08, n))
    return clamp(radii * np.exp(1j * angles))


STYLES = ("spread", "clustered", "near_circle", "near_polygon")


def random_sample(
    min_n: int, max_n: int, per_degree: int, rng: np.random.Generator, rtol: float
) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    attempted = 0
    ungated = 0
    for n in range(min_n, max_n + 1):
        for index in range(per_degree):
            attempted += 1
            roots = random_roots(n, rng, STYLES[index % len(STYLES)])
            row = measure(roots, rtol=rtol, atol=rtol * 1.0e-2, confirm=False)
            if row is None:
                ungated += 1
                continue
            rows.append(row)
    return {
        "attempted": attempted,
        "ungated": ungated,
        "measured": len(rows),
        "rows": rows,
    }


# ---------------------------------------------------------------- adversarial


STAR_ONLY_KEYS = ("ratio_A", "ratio_C", "ratio_B_star", "ratio_C_worst_pair")


def objective(x: np.ndarray, n: int, key: str, rtol: float) -> float:
    roots = clamp(x[:n] + 1j * x[n:])
    row = measure(
        roots, rtol=rtol, atol=rtol * 1.0e-2, star_only=key in STAR_ONLY_KEYS
    )
    if row is None:
        return -math.inf
    return float(row[key])


def near_double_root(n: int, rng: np.random.Generator, delta: float) -> np.ndarray:
    """A tight pair inside an otherwise spread configuration."""

    base = random_roots(n - 1, rng, "spread")
    return clamp(np.concatenate([base, [base[0] + delta * np.exp(2j * np.pi * rng.uniform())]]))


def cluster_and_outlier(n: int, rng: np.random.Generator, scale: float) -> np.ndarray:
    """`k` roots huddled together and the rest far away: the small-|f(c)| basin."""

    k = max(2, n - 2)
    cluster = scale * (rng.normal(size=k) + 1j * rng.normal(size=k))
    rest = 0.9 * np.exp(2j * np.pi * rng.uniform(0.0, 1.0, n - k))
    return clamp(np.concatenate([cluster, rest]))


def seeds(n: int, rng: np.random.Generator, count: int, bank: str) -> list[np.ndarray]:
    """Distinct basins.  The corpus's recorded trap is a search that visited one.

    `StraightSpokeHubCriterionLab.md` reports suprema pinned at 1.999999688 …
    1.928588184 across degrees, read as a ceiling at 2; a differently-seeded
    second search found the same objective unbounded.  So two disjoint banks are
    run and compared, and a value pinned just below threshold is reported as a
    weak search rather than as survival.
    """

    out: list[np.ndarray] = []
    if bank == "polygon":
        for epsilon in (0.0005, 0.002, 0.008, 0.03, 0.08, 0.2):
            out.append(perturbed_polygon(n, RCAP, epsilon, rng))
            out.append(perturbed_polygon(n, 0.85, epsilon, rng))
        for radius in (0.999, 0.6):
            out.append(clamp(radius * np.exp(2j * np.pi * np.arange(n) / n)))
    else:
        for delta in (1.0e-3, 1.0e-2, 0.1):
            out.append(near_double_root(n, rng, delta))
        for scale in (1.0e-3, 1.0e-2, 0.08, 0.3):
            out.append(cluster_and_outlier(n, rng, scale))
        for radius in (0.95, 0.999):  # the unbounded TEST C family
            out.append(centre_plus_polygon(n, radius))
        for literals in QC_SEED_WITNESSES.get(n, ()):  # exact recorded witnesses
            out.append(
                np.asarray(
                    [complex(float.fromhex(re), float.fromhex(im)) for re, im in literals],
                    dtype=np.complex128,
                )
            )
    while len(out) < count:
        out.append(random_roots(n, rng, STYLES[len(out) % len(STYLES)]))
    return out[:count]


def maximise(
    n: int,
    key: str,
    restarts: int,
    steps: int,
    rng: np.random.Generator,
    rtol: float,
    bank: str = "polygon",
) -> dict[str, Any]:
    """Adaptive random-walk maximisation, robust to the hub index switching."""

    best_value = -math.inf
    best_roots: np.ndarray | None = None
    trajectory: list[float] = []
    for roots in seeds(n, rng, restarts, bank):
        x = np.concatenate([roots.real, roots.imag])
        value = objective(x, n, key, rtol)
        scale = 0.12
        for _ in range(steps):
            candidate = x + scale * rng.normal(size=2 * n)
            candidate_value = objective(candidate, n, key, rtol)
            if candidate_value > value:
                x, value = candidate, candidate_value
                scale *= 1.12
            else:
                scale *= 0.94
            if scale < 1.0e-6:
                break
        if value > best_value:
            best_value, best_roots = value, clamp(x[:n] + 1j * x[n:])
        trajectory.append(float(best_value))
    out: dict[str, Any] = {
        "degree": n,
        "objective": key,
        "bank": bank,
        "best": float(best_value),
        "running_best_by_restart": trajectory,
    }
    if best_roots is not None:
        out["roots"] = [[float(z.real), float(z.imag)] for z in best_roots]
    return out


def polish(
    roots: np.ndarray, key: str, rng: np.random.Generator, rounds: int, rtol: float
) -> tuple[np.ndarray, float]:
    """Fine local refinement at the search tolerance."""

    n = len(roots)
    x = np.concatenate([roots.real, roots.imag])
    value = objective(x, n, key, rtol)
    scale = 1.0e-3
    for _ in range(rounds):
        candidate = x + scale * rng.normal(size=2 * n)
        candidate_value = objective(candidate, n, key, rtol)
        if candidate_value > value:
            x, value = candidate, candidate_value
            scale *= 1.1
        else:
            scale *= 0.95
        if scale < 1.0e-9:
            break
    return clamp(x[:n] + 1j * x[n:]), value


def tolerance_sweep(roots: np.ndarray) -> list[dict[str, Any]]:
    """Same configuration at three tolerances plus the independent instrument."""

    out: list[dict[str, Any]] = []
    for rtol, atol, verify in (
        (1.0e-8, 1.0e-10, False),
        (1.0e-10, 1.0e-12, False),
        (1.0e-12, 1.0e-14, True),
    ):
        row = measure(roots, rtol=rtol, atol=atol, verify=verify)
        out.append(
            {
                "relative_tolerance": rtol,
                "independent_instrument": verify,
                "measured": row is not None,
                "ratio_A": None if row is None else row["ratio_A"],
                "ratio_B": None if row is None else row["ratio_B"],
                "ratio_C": None if row is None else row["ratio_C"],
                "rejected_hub_count": None if row is None else row["rejected_hub_count"],
                "instrument_disagreement_count": (
                    None if row is None else row["instrument_disagreement_count"]
                ),
            }
        )
    return out


# --------------------------------------------------------------------- driver


def summarise(rows: list[dict[str, Any]], key: str) -> dict[str, Any]:
    values = [(row[key], row) for row in rows if math.isfinite(row[key])]
    if not values:
        return {"worst": None}
    worst_value, worst_row = max(values, key=lambda pair: pair[0])
    return {
        "worst": float(worst_value),
        "degree": worst_row["degree"],
        "roots": worst_row["roots"],
        "circumradius": worst_row["circumradius"],
        "sample_size": len(values),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--min-n", type=int, default=3)
    parser.add_argument("--max-n", type=int, default=10)
    parser.add_argument("--per-degree", type=int, default=48)
    parser.add_argument("--adv-min-n", type=int, default=3)
    parser.add_argument("--adv-max-n", type=int, default=8)
    parser.add_argument("--restarts", type=int, default=10)
    parser.add_argument("--steps", type=int, default=140)
    parser.add_argument("--polish-rounds", type=int, default=200)
    parser.add_argument("--search-rtol", type=float, default=1.0e-10)
    parser.add_argument("--seed", type=int, default=1041)
    parser.add_argument("--skip-random", action="store_true")
    parser.add_argument("--skip-adversarial", action="store_true")
    parser.add_argument("--objectives", type=str, default="ratio_A,ratio_B,ratio_B_star,ratio_C")
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    rng = np.random.default_rng(args.seed)
    payload: dict[str, Any] = {"source": SOURCE_REF, "gates": {
        "endpoint_tolerance": ENDPOINT_TOL,
        "level_residual_tolerance": LEVEL_RESIDUAL_TOL,
        "critical_residual_tolerance": CRITICAL_RESIDUAL_TOL,
        "cross_instrument_length_tolerance": CROSS_LENGTH_TOL,
    }}

    # calibration: the two families where every ratio must be exactly one
    calibration = [analytic_power_family(n, 0.999) for n in (2, 3, 4, 6, 8)]
    calibration += [
        row
        for row in (cassini_row(a) for a in (0.3, 0.7, 0.99, 0.999))
        if row is not None
    ]
    payload["calibration"] = calibration
    witnesses = hard_witness_validation()
    payload["hard_witness_validation"] = witnesses
    family = centre_plus_polygon_rows()
    payload["centre_plus_polygon_family"] = family
    print(json.dumps({"centre_plus_polygon": [
        {k: v for k, v in row.items() if k != "pair_confirmation"} for row in family
    ]}, indent=2), flush=True)
    print(json.dumps({"hard_witnesses": [
        {k: v for k, v in row.items() if k != "measured"} for row in witnesses
    ]}, indent=2), flush=True)
    print(json.dumps({"calibration": [
        {k: v for k, v in row.items() if k in
         ("family", "degree", "a", "r", "ratio_A", "ratio_B", "ratio_C")}
        for row in calibration
    ]}, indent=2), flush=True)

    if not args.skip_random:
        sample = random_sample(
            args.min_n, args.max_n, args.per_degree, rng, args.search_rtol
        )
        payload["random_sample"] = {
            "attempted": sample["attempted"],
            "ungated": sample["ungated"],
            "measured": sample["measured"],
            "ratio_A": summarise(sample["rows"], "ratio_A"),
            "ratio_B_star": summarise(sample["rows"], "ratio_B_star"),
            "ratio_B": summarise(sample["rows"], "ratio_B"),
            "ratio_C": summarise(sample["rows"], "ratio_C"),
            "rho_le_R_violations": sum(
                0 if row["rho_le_R"] else 1 for row in sample["rows"]
            ),
            "star_hub_not_global": sum(
                0 if row["minimum_critical_hub_is_global"] else 1
                for row in sample["rows"]
            ),
            "rejected_hub_total": sum(row["rejected_hub_count"] for row in sample["rows"]),
        }
        print(json.dumps({"random": {
            k: payload["random_sample"][k]["worst"] if isinstance(
                payload["random_sample"][k], dict) else payload["random_sample"][k]
            for k in ("ratio_A", "ratio_B", "ratio_B_star", "ratio_C", "measured", "ungated")
        }}, indent=2), flush=True)

    if not args.skip_adversarial:
        adversarial: list[dict[str, Any]] = []
        for key in [k.strip() for k in args.objectives.split(",")]:
            for n in range(args.adv_min_n, args.adv_max_n + 1):
                for bank in ("polygon", "cluster"):
                    row = maximise(
                        n, key, args.restarts, args.steps, rng, args.search_rtol, bank
                    )
                    if "roots" in row:
                        roots = np.array([complex(a, b) for a, b in row["roots"]])
                        roots, value = polish(
                            roots, key, rng, args.polish_rounds, args.search_rtol
                        )
                        if value > row["best"]:
                            row["best"] = float(value)
                            row["roots"] = [[float(z.real), float(z.imag)] for z in roots]
                        row["tolerance_sweep"] = tolerance_sweep(roots)
                        confirmed = measure(
                            roots, rtol=1.0e-12, atol=1.0e-14, verify=True, confirm=True
                        )
                        row["confirmed"] = None if confirmed is None else {
                            "ratio_A": confirmed["ratio_A"],
                            "ratio_B": confirmed["ratio_B"],
                            "ratio_C": confirmed["ratio_C"],
                            "ratio_C_worst_pair": confirmed["ratio_C_worst_pair"],
                            "symmetric_per_branch_at_star": confirmed[
                                "symmetric_per_branch_at_star"
                            ],
                            "symmetric_per_branch_all_hubs": confirmed[
                                "symmetric_per_branch_all_hubs"
                            ],
                            "star_hub_is_global": confirmed[
                                "minimum_critical_hub_is_global"
                            ],
                            "rho_le_R": confirmed["rho_le_R"],
                            "rejected_hub_count": confirmed["rejected_hub_count"],
                            "instrument_disagreement_count": confirmed[
                                "instrument_disagreement_count"
                            ],
                            "pair_confirmation": confirmed["pair_confirmation"],
                        }
                    adversarial.append(row)
                    print(json.dumps({
                        "objective": key,
                        "n": n,
                        "bank": bank,
                        "best": row["best"],
                        "confirmed": row.get("confirmed"),
                    }), flush=True)
        payload["adversarial"] = adversarial
        payload["adversarial_worst"] = {
            key: max(
                (r["best"] for r in adversarial if r["objective"] == key),
                default=None,
            )
            for key in [k.strip() for k in args.objectives.split(",")]
        }
        # bank disagreement is the pinned-supremum tripwire
        payload["bank_spread"] = {
            key: {
                bank: max(
                    (
                        r["best"]
                        for r in adversarial
                        if r["objective"] == key and r["bank"] == bank
                    ),
                    default=None,
                )
                for bank in ("polygon", "cluster")
            }
            for key in [k.strip() for k in args.objectives.split(",")]
        }
        print(json.dumps(payload["adversarial_worst"], indent=2), flush=True)
        print(json.dumps(payload["bank_spread"], indent=2), flush=True)

    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(payload, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
