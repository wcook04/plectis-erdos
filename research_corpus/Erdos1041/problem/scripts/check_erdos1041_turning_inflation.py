#!/usr/bin/env python3
"""Erdős #1041: falsification probe for the turning-inflation route.

The route under test
--------------------
``CriticalBudgetLab.md`` ("What controls the excess: the variation of arg f'")
reduces the descent construction to a statement with no arc lengths in it.
Along the constant-argument descent branch ``f(z(u)) = (1-u^2) f(c)`` the
tangent direction is ``arg T = arg f(c) - arg f'(z)`` and nothing else, so the
tangent's total turning is exactly ``TV(arg f')``.  If that variation is at
most ``alpha`` then every tangent lies in a cone of half-angle ``alpha/2`` and

    L(branch) <= chord(branch) / cos(alpha/2)              (CONE)

which is an ordinary projection argument, valid whenever ``alpha < pi``.
Combined with the landed two-nearest-root budget theorem
(``GlobalCriticalTwoNearestBudget.md``: at any critical point the two nearest
roots satisfy ``d1 + d2 <= 2R`` once the circumcentre is translated to 0), the
proposed chain is

    L(c) <= (d1 + d2) / cos(alpha/2) <= 2R                 (CHAIN)

at a well-chosen hub, and ``min_c L(c) <= 2R < 2`` would settle #1041 because
the descent path lies in ``{|f| < 1}`` by construction.

Decisive tests
--------------
  T1  (d1 + d2)         / (2R cos(alpha_max/2))  at the least-|f(c)| hub
  T2  (chord_a+chord_b) / (2R cos(alpha_max/2))  at the least-|f(c)| hub
  T3  the distribution and supremum of alpha_max
  T4  L(c) / (2R)                                at the minimum-L(c) hub
  T5  L(c) raw at the least-|f(c)| hub -- calibration against the corpus's own
      attack on that selector (1.943820 at n=3, then 1.567 / 1.351 / 1.010)

``T1 > 1`` kills (CHAIN) as stated; ``T2 > 1`` kills its honest per-branch
form; ``T4 >= 1`` would refute MIN itself, a far stronger statement.

T1, T2 and T3 are invariant under every similarity ``z -> lambda z + mu`` --
lengths and ``R`` scale together and ``TV(arg f')`` is unchanged -- while
admissibility ``|f(c)| = prod|c - z_i| < 1`` is not: shrinking a configuration
makes every hub admissible.  The unit-disk hypothesis therefore restricts T1
and T2 not at all beyond requiring some admissible hub to exist.

Instrument, and the failure it was built to avoid
-------------------------------------------------
The branch parameterization and the ``u^2`` desingularization come from
``system/lib/formal_math_lemniscate.py``.  Its branch *start* is located by
``np.roots`` on the level polynomial, which at ``u0 = 1e-6`` has a pair of
preimages ``c +- s*u0`` separated by ``~1e-7``; neither ``np.roots`` nor a
Newton polish on ``f(z) - (1-u0^2)v`` can resolve that direction, because the
residual is ``|v| u0^2 ~ 1e-14`` against a constant term ``|v| ~ 1e-2``.  Start
*directions* came out up to 50 degrees wrong.  Arc length is insensitive to
this (the level-set flow contracts the initial error by ``|f'(start)|/|f'(end)|``,
which is ``~1e-7``), which is why the repo's lengths are sound -- but
``arg f'`` is exactly the quantity that is *not* insensitive, since the error
in ``arg f'`` at the start is the position error divided by ``|z - c|``.

So this probe locates the start from the Taylor expansion of ``f`` at ``c``
instead.  With ``a_k = f^(k)(c)/k!`` obtained by repeated synthetic division
and ``a_1`` set to its exact value 0, the branch solves

    a_n d^n + ... + a_2 d^2 + u^2 v = 0,        d = z - c,

whose two roots near ``d = 0`` are ``+- u sqrt(-v/a_2) (1 + O(u))``.  Newton on
that polynomial cancels ``a_2 d^2`` against ``u^2 v`` -- both of size
``|v| u^2`` -- instead of cancelling against ``|v|``, a gain of ``1/u^2``, and
recovers the start to full double precision.  The whole branch is then tracked
in the ``d`` coordinate on the same series, which keeps ``f'`` well conditioned
near the saddle.

``TV(arg f')`` is then measured two independent ways and the two are required
to agree:

  * ODE state -- ``d(arg f')/du = Im(f''/f' * z')`` integrated as ``|.|`` by the
    same adaptive RK45 that carries the arc length, so the integrator's error
    control applies to it;
  * dense-output bisection -- recursive refinement of ``arg f'(z(u))`` until
    splitting an interval stops adding more than ``tv_tol`` and every increment
    is below 0.25 rad, which makes accumulating them exactly an unwrapped sum.
    The endpoint difference is never used.

Validation gates that must pass before any ratio is quoted
----------------------------------------------------------
  * ``z^2 - a^2``: ``L = 2a``, ``alpha = 0``, every ratio exactly 1.
  * ``z^n - r^n``: ``arg f'`` is constant on the exact radial branch.
  * the exact degree-6 and degree-9 IEEE-754 witnesses of
    ``StraightSpokeHubCriterionLab.md`` reproduce minimum branch-pair totals
    ``1.763942`` and ``1.545995``;
  * lengths agree with ``formal_math_lemniscate.descending_pair``;
  * the CONE inequality holds per branch (it is a theorem, so a violation is a
    bug in this probe).

Search discipline
-----------------
``CriticalBudgetLab.md``: "A clean sample is not evidence in this problem," and
``StraightSpokeHubCriterionLab.md`` records a supremum that looked pinned at
``1.9999997`` and was actually infinite in another basin.  So: the random sweep
is a warm-up only; every ratio is then maximised adversarially from several
distinct basins (regular, extremal-family, clustered, two-cluster, the pinned
QC witnesses, and cross-seeded best-so-far), two independent campaigns are run
per target, and a value that lands just below a threshold is reported as a weak
search rather than as survival.

Read-only dependencies; writes nothing except its own ``--out`` report.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
import time
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Any, Callable, Sequence

import numpy as np
from scipy.integrate import solve_ivp

REPO_ROOT = Path(__file__).resolve().parents[5]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_lemniscate import descending_pair  # noqa: E402

CAP = 1.0 - 1.0e-9
MIN_CRITICAL_VALUE = 1.0e-13

#: recorded by StraightSpokeHubCriterionLab.md on the exact QC witnesses
RECORDED_WITNESS_TOTALS = {6: 1.763942, 9: 1.545995}
#: CriticalBudgetLab.md, attack on the least-critical-value selector
RECORDED_LEAST_VALUE_ATTACK = {3: 1.943820, 4: 1.567, 5: 1.351, 6: 1.010}


# --------------------------------------------------------------------------- #
# tolerances
# --------------------------------------------------------------------------- #
@dataclass(frozen=True)
class Tol:
    name: str
    rtol: float
    atol: float
    max_step: float
    tv_tol: float
    tv_min_depth: int
    tv_max_depth: int
    tv_budget: int
    start_u: float
    endpoint_gate: float
    residual_gate: float
    alpha_gate: float


#: ``tv_min_depth`` matters more than ``tv_tol``: on the degree-9 QC witness the
#: bisection instrument under-reads one branch by 3.7e-4 until depth 10, while
#: the ODE instrument is already converged.  The two are kept because the
#: bisection is the one that cannot silently accumulate quadrature error; the
#: reported ``alpha`` is their maximum, which equals the ODE value.
FAST = Tol("fast", 1.0e-8, 1.0e-10, np.inf, 3.0e-4, 5, 18, 20000, 1.0e-7, 1.0e-6, 1.0e-7, 5.0e-3)
TIGHT = Tol("tight", 1.0e-11, 1.0e-13, np.inf, 1.0e-11, 9, 26, 600000, 1.0e-7, 1.0e-9, 1.0e-9, 2.0e-3)
ULTRA = Tol("ultra", 1.0e-13, 1.0e-15, 0.02, 1.0e-13, 10, 28, 4000000, 1.0e-8, 1.0e-10, 1.0e-10, 1.0e-4)


# --------------------------------------------------------------------------- #
# scalar polynomial arithmetic (python complex Horner: ~10x np.polyval on scalars)
# --------------------------------------------------------------------------- #
def horner(coefficients: Sequence[complex], z: complex) -> complex:
    accumulator = coefficients[0]
    for coefficient in coefficients[1:]:
        accumulator = accumulator * z + coefficient
    return accumulator


def synthetic_division(coefficients: Sequence[complex], centre: complex):
    """Divide by ``(z - centre)``; return ``(quotient, remainder = p(centre))``."""

    partial: list[complex] = []
    accumulator = 0.0 + 0.0j
    for coefficient in coefficients:
        accumulator = accumulator * centre + coefficient
        partial.append(accumulator)
    remainder = partial.pop()
    return partial, remainder


def taylor_ascending(coefficients: Sequence[complex], centre: complex) -> list[complex]:
    """``a_k = f^(k)(centre)/k!`` ascending, by repeated synthetic division."""

    ascending: list[complex] = []
    work = list(coefficients)
    while work:
        work, remainder = synthetic_division(work, centre)
        ascending.append(remainder)
    return ascending


# --------------------------------------------------------------------------- #
# geometry helpers
# --------------------------------------------------------------------------- #
def circumcircle(points: np.ndarray) -> tuple[complex, float]:
    """Centre and radius of the smallest enclosing circle (Welzl, incremental).

    Same routine as ``check_erdos1041_invariant_branch_length.circumcircle``,
    inlined so this probe imports nothing from a checker owned by another
    session.
    """

    values = [complex(point) for point in points]

    def two(a: complex, b: complex) -> tuple[complex, float]:
        return (a + b) / 2, abs(a - b) / 2

    def three(a: complex, b: complex, c: complex) -> tuple[complex, float]:
        ax, ay, bx, by, cx, cy = a.real, a.imag, b.real, b.imag, c.real, c.imag
        determinant = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
        if abs(determinant) < 1.0e-18:
            best: tuple[complex, float] = (0j, float("inf"))
            for left, right in ((a, b), (a, c), (b, c)):
                centre, radius = two(left, right)
                if radius < best[1] and all(
                    abs(point - centre) <= radius + 1.0e-12 for point in (a, b, c)
                ):
                    best = (centre, radius)
            return best
        ux = (
            (ax * ax + ay * ay) * (by - cy)
            + (bx * bx + by * by) * (cy - ay)
            + (cx * cx + cy * cy) * (ay - by)
        ) / determinant
        uy = (
            (ax * ax + ay * ay) * (cx - bx)
            + (bx * bx + by * by) * (ax - cx)
            + (cx * cx + cy * cy) * (bx - ax)
        ) / determinant
        centre = complex(ux, uy)
        return centre, abs(a - centre)

    centre, radius = values[0], 0.0
    for i in range(1, len(values)):
        if abs(values[i] - centre) <= radius + 1.0e-12:
            continue
        centre, radius = values[i], 0.0
        for j in range(i):
            if abs(values[j] - centre) <= radius + 1.0e-12:
                continue
            centre, radius = two(values[i], values[j])
            for k in range(j):
                if abs(values[k] - centre) <= radius + 1.0e-12:
                    continue
                centre, radius = three(values[i], values[j], values[k])
    return complex(centre), float(radius)


def sec_half(alpha: float) -> float:
    """``1/cos(alpha/2)`` with a monotone continuation past the vacuous point.

    The cone bound means nothing once ``alpha >= pi``; the continuation only
    keeps hill climbing from stalling on ``inf``, and every table flags
    ``alpha >= pi`` separately.
    """

    edge = math.pi - 1.0e-6
    if alpha < edge:
        return 1.0 / math.cos(alpha / 2.0)
    return 1.0 / math.cos(edge / 2.0) + (alpha - edge) * 1.0e9


def clamp(roots: np.ndarray, cap: float = CAP) -> np.ndarray:
    modulus = np.abs(roots)
    return roots * np.where(modulus > cap, cap / np.maximum(modulus, 1.0e-300), 1.0)


# --------------------------------------------------------------------------- #
# total variation of arg, by adaptive bisection
# --------------------------------------------------------------------------- #
class _Budget:
    __slots__ = ("left", "exhausted")

    def __init__(self, budget: int) -> None:
        self.left = budget
        self.exhausted = False


def _tv(
    g: Callable[[float], complex],
    a: float,
    b: float,
    ga: complex,
    gb: complex,
    depth: int,
    tol: Tol,
    budget: _Budget,
    stats: dict[str, float],
) -> float:
    if budget.left <= 0:
        budget.exhausted = True
        if ga == 0 or gb == 0:
            return 0.0
        ratio = gb / ga
        return abs(math.atan2(ratio.imag, ratio.real))
    middle = 0.5 * (a + b)
    gm = g(middle)
    budget.left -= 1
    stats["min_abs"] = min(stats["min_abs"], abs(gm))
    if ga == 0 or gb == 0 or gm == 0:
        return 0.0
    ratio_ab = gb / ga
    ratio_am = gm / ga
    ratio_mb = gb / gm
    d_ab = abs(math.atan2(ratio_ab.imag, ratio_ab.real))
    d_am = abs(math.atan2(ratio_am.imag, ratio_am.real))
    d_mb = abs(math.atan2(ratio_mb.imag, ratio_mb.real))
    split = d_am + d_mb
    if depth >= tol.tv_max_depth:
        return split
    if depth >= tol.tv_min_depth and (split - d_ab) <= tol.tv_tol and max(d_am, d_mb) < 0.25:
        return split
    return _tv(g, a, middle, ga, gm, depth + 1, tol, budget, stats) + _tv(
        g, middle, b, gm, gb, depth + 1, tol, budget, stats
    )


def adaptive_arg_variation(
    g: Callable[[float], complex], a: float, b: float, tol: Tol
) -> tuple[float, float, bool]:
    ga, gb = g(a), g(b)
    stats = {"min_abs": min(abs(ga), abs(gb))}
    budget = _Budget(tol.tv_budget)
    value = _tv(g, a, b, ga, gb, 0, tol, budget, stats)
    return float(value), float(stats["min_abs"]), bool(budget.exhausted)


# --------------------------------------------------------------------------- #
# branch tracking in the shifted coordinate d = z - c
# --------------------------------------------------------------------------- #
def branch_start(
    level_polynomial: Sequence[complex],
    derivative_series: Sequence[complex],
    guess: complex,
) -> tuple[complex, float]:
    """Newton on ``a_n d^n + ... + a_2 d^2 + u^2 v = 0`` from the leading guess."""

    d = guess
    for _ in range(6):
        value = horner(level_polynomial, d)
        slope = horner(derivative_series, d)
        if slope == 0:
            break
        step = value / slope
        d = d - step
        if abs(step) <= 1.0e-17 * max(abs(d), 1.0e-300):
            break
    return d, float(abs(horner(level_polynomial, d)))


def track_branch(
    roots: np.ndarray,
    hub: complex,
    value: complex,
    f_series: Sequence[complex],
    fp_series: Sequence[complex],
    fpp_series: Sequence[complex],
    start: complex,
    tangent_limit: complex,
    tol: Tol,
) -> dict[str, Any] | None:
    """One descending branch: arc length, endpoint, and TV(arg f') two ways."""

    u0 = tol.start_u

    def field(u: float, state: np.ndarray) -> list[float]:
        d = state[0] + 1j * state[1]
        fp = horner(fp_series, d)
        velocity = -2.0 * u * value / fp
        turn = (horner(fpp_series, d) / fp) * velocity
        return [velocity.real, velocity.imag, abs(velocity), abs(turn.imag)]

    solution = solve_ivp(
        field,
        (u0, 1.0),
        [start.real, start.imag, abs(start), 0.0],
        rtol=tol.rtol,
        atol=tol.atol,
        max_step=tol.max_step,
        dense_output=True,
    )
    if not solution.success:
        return None
    offsets = solution.y[0] + 1j * solution.y[1]
    endpoint = hub + offsets[-1]
    index = int(np.argmin(np.abs(roots - endpoint)))
    residual = float(
        np.abs(
            np.asarray([horner(f_series, d) for d in offsets])
            - (1.0 - solution.t**2) * value
        ).max()
    )

    dense = solution.sol

    def g(u: float) -> complex:
        state = dense(u)
        return horner(fp_series, state[0] + 1j * state[1])

    variation, min_abs_fp, exhausted = adaptive_arg_variation(g, u0, 1.0, tol)
    seed = g(u0)
    stub = 0.0
    if seed != 0 and tangent_limit != 0:
        ratio = seed / tangent_limit
        stub = abs(math.atan2(ratio.imag, ratio.real))
    return {
        "root_index": index,
        "length": float(solution.y[2, -1]),
        "alpha_grid": float(variation),
        "alpha_ode": float(solution.y[3, -1]),
        "alpha_start_offset": float(stub),
        "endpoint": endpoint,
        "endpoint_error": float(abs(roots[index] - endpoint)),
        "maximum_level_residual": residual,
        "minimum_abs_fprime": float(min_abs_fp),
        "tv_budget_exhausted": exhausted,
        "solver_steps": int(solution.t.size),
    }


def measure_hub(
    roots: np.ndarray,
    coefficients: Sequence[complex],
    critical_points: np.ndarray,
    hub_index: int,
    radius: float,
    tol: Tol,
) -> dict[str, Any] | None:
    hub = complex(critical_points[hub_index])
    ascending = taylor_ascending(coefficients, hub)
    value = ascending[0]
    modulus = abs(value)
    if modulus >= 1.0 or modulus <= MIN_CRITICAL_VALUE:
        return None
    critical_residual = abs(ascending[1])
    ascending[1] = 0.0 + 0.0j  # c is a critical point: enforce it exactly
    if len(ascending) < 3 or abs(ascending[2]) < 1.0e-9:
        return None  # degenerate saddle (f''(c) = 0)

    degree = len(ascending) - 1
    f_series = list(reversed(ascending))
    fp_series = list(reversed([k * ascending[k] for k in range(1, degree + 1)]))
    fpp_series = list(
        reversed([k * (k - 1) * ascending[k] for k in range(2, degree + 1)])
    )
    others = np.delete(np.asarray(critical_points, dtype=np.complex128), hub_index)
    hub_separation = float(np.abs(others - hub).min()) if others.size else math.inf

    u0 = tol.start_u
    level = list(f_series)
    level[-1] = (u0**2) * value  # replace a_0 by u0^2 v: no cancellation against |v|
    leading = np.sqrt(-value / ascending[2])
    branches: list[dict[str, Any]] = []
    for sign in (1.0, -1.0):
        guess = sign * complex(leading) * u0
        start, start_residual = branch_start(level, fp_series, guess)
        if abs(start) <= 0.0 or not np.isfinite(abs(start)):
            return None
        if abs(start - guess) > 0.25 * abs(guess):
            return None  # Newton left the asymptotic regime: u0 too coarse here
        tangent_limit = 2.0 * ascending[2] * (start / u0)
        row = track_branch(
            roots, hub, value, f_series, fp_series, fpp_series, start, tangent_limit, tol
        )
        if row is None:
            return None
        row["start_residual"] = start_residual
        branches.append(row)
    if branches[0]["root_index"] == branches[1]["root_index"]:
        return None

    distances = np.abs(np.asarray(roots, dtype=np.complex128) - hub)
    order = np.argsort(distances)
    nearest_two = {int(order[0]), int(order[1])}
    d1 = float(distances[order[0]])
    d2 = float(distances[order[1]])

    for row in branches:
        row["chord"] = float(abs(complex(roots[row["root_index"]]) - hub))
        row["alpha"] = max(row["alpha_grid"], row["alpha_ode"])
        row["alpha_disagreement"] = abs(row["alpha_grid"] - row["alpha_ode"])
        row["lands_on_nearest_two"] = bool(row["root_index"] in nearest_two)
        row["cone_ok"] = bool(
            row["alpha"] >= math.pi - 1.0e-6
            or row["length"] <= row["chord"] * sec_half(row["alpha"]) * (1.0 + 1.0e-7) + 1.0e-9
        )

    length = float(branches[0]["length"] + branches[1]["length"])
    chord_sum = float(branches[0]["chord"] + branches[1]["chord"])
    alpha_max = float(max(branches[0]["alpha"], branches[1]["alpha"]))
    alpha_sum = float(branches[0]["alpha"] + branches[1]["alpha"])
    two_r = 2.0 * radius
    factor = sec_half(alpha_max)

    # TURNING FLOOR.  At a simple saddle the two branches leave in exactly
    # opposite directions +-s.  Each branch's chord lies inside the cone of its
    # own tangents, so |arg(a-c) - arg(+s)| <= alpha_A and |arg(b-c) - arg(-s)|
    # <= alpha_B.  The angle phi subtended at c by the two endpoint roots
    # therefore satisfies phi >= pi - (alpha_A + alpha_B); equivalently
    #     alpha_A + alpha_B >= pi - phi   and   alpha_max >= (pi - phi)/2.
    # The cone chain can never return less than chord_sum * sec((pi - phi)/4),
    # so a hub whose endpoint roots subtend much less than pi is unusable no
    # matter how well behaved f is.
    to_a = complex(roots[branches[0]["root_index"]]) - hub
    to_b = complex(roots[branches[1]["root_index"]]) - hub
    quotient = to_b / to_a
    subtended = abs(math.atan2(quotient.imag, quotient.real))
    turning_floor = max(0.0, math.pi - subtended)
    floor_ratio = chord_sum * sec_half(turning_floor / 2.0) / two_r
    clean = bool(
        max(row["endpoint_error"] for row in branches) < tol.endpoint_gate
        and max(row["maximum_level_residual"] for row in branches) < tol.residual_gate
        and max(row["alpha_disagreement"] for row in branches) < tol.alpha_gate
        and not any(row["tv_budget_exhausted"] for row in branches)
    )
    return {
        "hub_index": hub_index,
        "hub": hub,
        "critical_value_modulus": modulus,
        "critical_residual": float(critical_residual),
        "second_derivative_modulus": float(abs(2.0 * ascending[2])),
        "hub_separation": hub_separation,
        "length": length,
        "chord_sum": chord_sum,
        "d1": d1,
        "d2": d2,
        "d_sum": d1 + d2,
        "alpha_max": alpha_max,
        "alpha_sum": alpha_sum,
        "subtended_angle": float(subtended),
        "turning_floor": float(turning_floor),
        "turning_floor_holds": bool(alpha_sum >= turning_floor - 1.0e-6),
        "cone_chain_floor_ratio": float(floor_ratio),
        "alpha_branch": [branches[0]["alpha"], branches[1]["alpha"]],
        "alpha_disagreement": max(row["alpha_disagreement"] for row in branches),
        "alpha_start_offset": max(row["alpha_start_offset"] for row in branches),
        "both_branches_nearest": bool(
            branches[0]["lands_on_nearest_two"] and branches[1]["lands_on_nearest_two"]
        ),
        "predicted_length_bound": chord_sum * factor,
        "cone_bound_holds": bool(all(row["cone_ok"] for row in branches)),
        "vacuous_cone": bool(alpha_max >= math.pi),
        "ratio_t1": (d1 + d2) * factor / two_r,
        "ratio_t2": chord_sum * factor / two_r,
        "ratio_t4": length / two_r,
        "budget_ratio": (d1 + d2) / two_r,
        "inflation": length / chord_sum if chord_sum > 0 else math.inf,
        "clean": clean,
        "max_endpoint_error": max(row["endpoint_error"] for row in branches),
        "max_level_residual": max(row["maximum_level_residual"] for row in branches),
        "max_start_residual": max(row["start_residual"] for row in branches),
        "minimum_abs_fprime": min(row["minimum_abs_fprime"] for row in branches),
        "branches": branches,
    }


def measure_config(
    roots: np.ndarray, tol: Tol, *, all_hubs: bool = True
) -> dict[str, Any] | None:
    roots = np.asarray(roots, dtype=np.complex128)
    if roots.size < 2:
        return None
    separation = min(
        abs(roots[i] - roots[j])
        for i in range(roots.size)
        for j in range(i + 1, roots.size)
    )
    if separation < 1.0e-7:
        return None
    coefficients = [complex(c) for c in np.poly(roots)]
    critical_points = np.roots(np.polyder(np.asarray(coefficients)))
    if critical_points.size == 0:
        return None
    _, radius = circumcircle(roots)
    if radius <= 1.0e-9:
        return None

    moduli = np.abs(np.polyval(np.asarray(coefficients), critical_points))
    order = [int(i) for i in np.argsort(moduli) if MIN_CRITICAL_VALUE < moduli[i] < 1.0]
    if not order:
        return None

    least_value_hub: dict[str, Any] | None = None
    hubs: list[dict[str, Any]] = []
    for position, index in enumerate(order):
        row = measure_hub(roots, coefficients, critical_points, index, radius, tol)
        if row is None:
            if not all_hubs and position == 0:
                # the least-|f(c)| rule selects a hub whose descent is degenerate,
                # so the rule is undefined there and the configuration is not evidence
                return None
            continue
        if position == 0:
            least_value_hub = row
        hubs.append(row)
        if not all_hubs and least_value_hub is not None:
            break
    if not hubs or least_value_hub is None:
        return None
    return {
        "degree": int(roots.size),
        "roots": roots,
        "radius": float(radius),
        "root_separation": float(separation),
        "hubs": hubs,
        "least_value_hub": least_value_hub,
        "minimum_length_hub": min(hubs, key=lambda row: row["length"]),
        "admissible_hub_count": len(hubs),
    }


# --------------------------------------------------------------------------- #
# objectives
# --------------------------------------------------------------------------- #
OBJECTIVES: dict[str, tuple[str, str]] = {
    "t1": ("least_value", "ratio_t1"),
    "t2": ("least_value", "ratio_t2"),
    "t3": ("any_hub", "alpha_max"),
    "t4": ("min_length", "ratio_t4"),
    "t5": ("least_value", "length"),
    # steelman: the route only needs the chain to close at SOME admissible hub.
    # t1_best > 1 means it closes at NO hub of that configuration.
    "t1_best": ("best_hub", "ratio_t1"),
    "t2_best": ("best_hub", "ratio_t2"),
}


def select_row(packet: dict[str, Any], target: str) -> dict[str, Any]:
    rule, key = OBJECTIVES[target]
    if rule == "least_value":
        return packet["least_value_hub"]
    if rule == "min_length":
        return packet["minimum_length_hub"]
    if rule == "best_hub":
        clean = [h for h in packet["hubs"] if h["clean"]] or packet["hubs"]
        return min(clean, key=lambda r: r[key])
    return max(packet["hubs"], key=lambda r: r[key])


def evaluate(roots: np.ndarray, target: str, tol: Tol) -> float:
    rule, key = OBJECTIVES[target]
    packet = measure_config(roots, tol, all_hubs=(rule != "least_value"))
    if packet is None:
        return -math.inf
    row = select_row(packet, target)
    if not row["clean"]:
        return -math.inf
    return float(row[key])


# --------------------------------------------------------------------------- #
# root generators and seed basins
# --------------------------------------------------------------------------- #
def witness_roots(degree: int) -> np.ndarray | None:
    from formal_math.erdos257_period_noncollapse.ErdosProblems.Erdos1041.scripts.check_erdos1041_straight_spoke_hub_criterion import (  # noqa: E402
        QC_REFUTATION_WITNESSES,
    )

    literals = QC_REFUTATION_WITNESSES.get(degree)
    if literals is None:
        return None
    return np.asarray(
        [complex(float.fromhex(re), float.fromhex(im)) for re, im in literals],
        dtype=np.complex128,
    )


def draw_roots(rng: np.random.Generator, degree: int, style: str) -> np.ndarray:
    if style in ("area", "annulus", "boundary"):
        if style == "area":
            radius = np.sqrt(rng.uniform(0.0, 1.0, degree))
        elif style == "annulus":
            radius = rng.uniform(0.4, 1.0, degree)
        else:
            radius = rng.uniform(0.95, 1.0, degree)
        return clamp(radius * np.exp(2j * np.pi * rng.uniform(0.0, 1.0, degree)))
    if style == "clustered":
        centres = rng.uniform(0.0, 0.8, 2) * np.exp(2j * np.pi * rng.uniform(0, 1, 2))
        pick = rng.integers(0, 2, degree)
        spread = 10.0 ** rng.uniform(-2.5, -0.7)
        return clamp(
            centres[pick] + spread * (rng.normal(size=degree) + 1j * rng.normal(size=degree))
        )
    if style == "near_regular":
        scale = rng.uniform(0.6, 1.0)
        jitter = 10.0 ** rng.uniform(-3.0, -0.7)
        angles = 2 * np.pi * (np.arange(degree) / degree + jitter * rng.normal(size=degree))
        return clamp(scale * (1 + jitter * rng.normal(size=degree)) * np.exp(1j * angles))
    if style == "two_cluster":
        gap = rng.uniform(0.5, 0.98)
        half = degree // 2
        left = -gap + 0.08 * (rng.normal(size=half) + 1j * rng.normal(size=half))
        right = gap + 0.08 * (
            rng.normal(size=degree - half) + 1j * rng.normal(size=degree - half)
        )
        return clamp(np.concatenate([left, right]))
    if style == "extremal":
        scale = rng.uniform(0.7, CAP)
        jitter = 10.0 ** rng.uniform(-4.0, -1.3)
        base = scale * np.exp(2j * np.pi * np.arange(degree) / degree)
        return clamp(base + jitter * (rng.normal(size=degree) + 1j * rng.normal(size=degree)))
    if style == "collinear":
        line = np.sort(rng.uniform(-0.98, 0.98, degree))
        phase = np.exp(1j * 2 * np.pi * rng.uniform())
        return clamp(phase * (line + 1j * 10.0 ** rng.uniform(-3.0, -0.8) * rng.normal(size=degree)))
    if style == "witness":
        base = witness_roots(6 if degree <= 7 else 9)
        if base is None:
            return draw_roots(rng, degree, "extremal")
        picked = base[rng.permutation(base.size)[: min(degree, base.size)]]
        if picked.size < degree:
            extra = draw_roots(rng, degree - picked.size, "boundary")
            picked = np.concatenate([picked, extra])
        return clamp(picked + 1.0e-3 * (rng.normal(size=degree) + 1j * rng.normal(size=degree)))
    raise ValueError(f"unknown style: {style}")


STYLES = (
    "area",
    "annulus",
    "boundary",
    "clustered",
    "near_regular",
    "two_cluster",
    "extremal",
    "collinear",
    "witness",
)


# --------------------------------------------------------------------------- #
# adversarial search
# --------------------------------------------------------------------------- #
def hill_climb(
    roots: np.ndarray, target: str, steps: int, rng: np.random.Generator, tol: Tol
) -> tuple[float, np.ndarray]:
    degree = roots.size
    value = evaluate(roots, target, tol)
    scale = 0.25
    for _ in range(steps):
        mode = rng.random()
        if mode < 0.62:
            candidate = roots + scale * (rng.normal(size=degree) + 1j * rng.normal(size=degree))
        elif mode < 0.80:
            pick = int(rng.integers(0, degree))
            candidate = roots.copy()
            candidate[pick] += 3.0 * scale * (rng.normal() + 1j * rng.normal())
        elif mode < 0.90:
            # global rescale: admissibility is the only scale-dependent gate
            candidate = roots * (1.0 + scale * rng.normal())
        else:
            pick = int(rng.integers(0, degree))
            other = int(rng.integers(0, degree))
            candidate = roots.copy()
            candidate[pick] = roots[other] + scale * (rng.normal() + 1j * rng.normal())
        candidate = clamp(candidate)
        candidate_value = evaluate(candidate, target, tol)
        if candidate_value > value:
            roots, value = candidate, candidate_value
            scale = min(0.25, scale * 1.35)
        else:
            scale *= 0.94
        if scale < 3.0e-6:
            break
    return value, roots


def adversarial(
    degree: int,
    target: str,
    restarts: int,
    steps: int,
    rng: np.random.Generator,
    tol: Tol,
    seeds: Sequence[np.ndarray] = (),
    verbose: bool = False,
) -> dict[str, Any]:
    best_value, best_roots = -math.inf, None
    per_restart: list[float] = []
    basins: list[np.ndarray] = []
    for candidate in seeds:
        if candidate is not None and candidate.size == degree:
            basins.append(clamp(np.asarray(candidate, dtype=np.complex128)))
    basins.append(CAP * np.exp(2j * np.pi * np.arange(degree) / degree))
    basins.append(0.6 * np.exp(2j * np.pi * np.arange(degree) / degree))
    witness = witness_roots(degree)
    if witness is not None:
        basins.append(clamp(witness))
    for trial in range(max(restarts, len(basins))):
        if trial < len(basins):
            roots = basins[trial].copy()
        elif trial % 5 == 4 and best_roots is not None:
            roots = clamp(
                best_roots + 0.05 * (rng.normal(size=degree) + 1j * rng.normal(size=degree))
            )
        else:
            roots = draw_roots(rng, degree, STYLES[trial % len(STYLES)])
        value, roots = hill_climb(clamp(roots), target, steps, rng, tol)
        per_restart.append(value)
        if value > best_value:
            best_value, best_roots = value, roots
            if verbose:
                print(f"    [{target} n={degree}] restart {trial}: {best_value:.6f}", flush=True)
    out: dict[str, Any] = {
        "degree": degree,
        "target": target,
        "search_best": best_value,
        "per_restart": [v for v in per_restart if math.isfinite(v)],
    }
    if best_roots is not None:
        out["roots"] = best_roots
    return out


def nelder_mead_polish(
    roots: np.ndarray, target: str, tol: Tol, iterations: int
) -> tuple[float, np.ndarray]:
    from scipy.optimize import minimize

    degree = roots.size

    def unpack(vector: np.ndarray) -> np.ndarray:
        return clamp(vector[:degree] + 1j * vector[degree:])

    def cost(vector: np.ndarray) -> float:
        value = evaluate(unpack(vector), target, tol)
        return -value if math.isfinite(value) else 1.0e6

    result = minimize(
        cost,
        np.concatenate([roots.real, roots.imag]),
        method="Nelder-Mead",
        options={"maxiter": iterations, "xatol": 1.0e-8, "fatol": 1.0e-10, "adaptive": True},
    )
    polished = unpack(result.x)
    base = evaluate(roots, target, tol)
    value = evaluate(polished, target, tol)
    return (value, polished) if value > base else (base, roots)


# --------------------------------------------------------------------------- #
# reporting
# --------------------------------------------------------------------------- #
def roots_payload(roots: np.ndarray) -> dict[str, Any]:
    return {
        "decimal": [[float(z.real), float(z.imag)] for z in roots],
        "hex": [[float(z.real).hex(), float(z.imag).hex()] for z in roots],
        "max_modulus": float(np.abs(roots).max()),
    }


HUB_KEYS = (
    "critical_value_modulus",
    "alpha_sum",
    "subtended_angle",
    "turning_floor",
    "turning_floor_holds",
    "cone_chain_floor_ratio",
    "critical_residual",
    "hub_separation",
    "length",
    "chord_sum",
    "d1",
    "d2",
    "d_sum",
    "alpha_max",
    "alpha_branch",
    "alpha_disagreement",
    "alpha_start_offset",
    "both_branches_nearest",
    "predicted_length_bound",
    "cone_bound_holds",
    "vacuous_cone",
    "ratio_t1",
    "ratio_t2",
    "ratio_t4",
    "budget_ratio",
    "inflation",
    "clean",
    "max_endpoint_error",
    "max_level_residual",
    "max_start_residual",
    "minimum_abs_fprime",
)


def hub_payload(row: dict[str, Any]) -> dict[str, Any]:
    payload = {k: row[k] for k in HUB_KEYS}
    payload["hub"] = [float(row["hub"].real), float(row["hub"].imag)]
    payload["branch_root_indices"] = [b["root_index"] for b in row["branches"]]
    payload["branch_chords"] = [b["chord"] for b in row["branches"]]
    payload["branch_lands_on_nearest_two"] = [b["lands_on_nearest_two"] for b in row["branches"]]
    payload["branch_solver_steps"] = [b["solver_steps"] for b in row["branches"]]
    return payload


def audit_witness(roots: np.ndarray, target: str) -> dict[str, Any]:
    """Re-measure at TIGHT and ULTRA, and cross-check against the repo tracker."""

    _, key = OBJECTIVES[target]
    tight = measure_config(roots, TIGHT, all_hubs=True)
    if tight is None:
        return {"ok": False, "reason": "tight measurement failed"}
    row = select_row(tight, target)
    ultra = measure_config(roots, ULTRA, all_hubs=True)
    ultra_row = select_row(ultra, target) if ultra is not None else None
    pair = descending_pair(
        roots, row["hub"], relative_tolerance=1.0e-12, absolute_tolerance=1.0e-14
    )
    repo_length = float(pair["total_length"]) if pair else None
    return {
        "ok": True,
        "value": float(row[key]),
        "value_ultra": None if ultra_row is None else float(ultra_row[key]),
        "tolerance_drift": None
        if ultra_row is None
        else abs(float(ultra_row[key]) - float(row[key])),
        "hub": hub_payload(row),
        "degree": tight["degree"],
        "radius": tight["radius"],
        "admissible_hub_count": tight["admissible_hub_count"],
        "least_value_hub_length": tight["least_value_hub"]["length"],
        "minimum_hub_length": tight["minimum_length_hub"]["length"],
        "repo_descending_pair_length": repo_length,
        "repo_length_delta": None if repo_length is None else abs(repo_length - row["length"]),
        "roots": roots_payload(np.asarray(roots)),
    }


# --------------------------------------------------------------------------- #
# families and hard validation
# --------------------------------------------------------------------------- #
def hard_witness_validation() -> list[dict[str, Any]]:
    """Reproduce the recorded exact-witness branch totals before quoting anything."""

    rows: list[dict[str, Any]] = []
    for degree, recorded in RECORDED_WITNESS_TOTALS.items():
        roots = witness_roots(degree)
        if roots is None:
            rows.append({"degree": degree, "error": "witness literals unavailable"})
            continue
        packet = measure_config(roots, TIGHT, all_hubs=True)
        if packet is None:
            rows.append({"degree": degree, "error": "tracker refused the witness"})
            continue
        minimum = packet["minimum_length_hub"]["length"]
        rows.append(
            {
                "degree": degree,
                "recorded_minimum_branch_pair_total": recorded,
                "measured": minimum,
                "absolute_delta": abs(minimum - recorded),
                "admissible_hub_count": packet["admissible_hub_count"],
                "critical_value_moduli": sorted(
                    h["critical_value_modulus"] for h in packet["hubs"]
                ),
                "max_endpoint_error": max(h["max_endpoint_error"] for h in packet["hubs"]),
                "max_level_residual": max(h["max_level_residual"] for h in packet["hubs"]),
                "max_alpha": max(h["alpha_max"] for h in packet["hubs"]),
                "max_alpha_disagreement": max(h["alpha_disagreement"] for h in packet["hubs"]),
                "ratio_t1_least_value": packet["least_value_hub"]["ratio_t1"],
                "ratio_t2_least_value": packet["least_value_hub"]["ratio_t2"],
                "ratio_t4_minimum": packet["minimum_length_hub"]["ratio_t4"],
                "radius": packet["radius"],
                "pass": bool(abs(minimum - recorded) < 5.0e-6),
            }
        )
    return rows


def family_rows() -> dict[str, Any]:
    # z^n - r^n at the degenerate central hub: the branch solves z^n = r^n u^2, i.e.
    # z = r u^(2/n) w_k, a straight radius, and arg f' = arg(n z^(n-1)) = (n-1) arg w_k
    # is constant along it.  Checked on the exact coefficient vector, and again on
    # the np.poly reconstruction away from the origin, where |f'| is above roundoff.
    radial: list[dict[str, Any]] = []
    for degree in range(2, 9):
        for r in (0.5, 0.9, 0.999):
            exact = np.zeros(degree + 1)
            exact[0] = 1.0
            exact[-1] = -(r**degree)
            built = np.poly(r * np.exp(2j * np.pi * np.arange(degree) / degree))
            samples = np.linspace(1.0e-12, 1.0, 8001)
            radius_points = r * samples  # the k = 0 radius
            exact_values = np.polyval(np.polyder(exact), radius_points)
            built_values = np.polyval(np.polyder(built), radius_points[samples >= 0.05])
            radial.append(
                {
                    "degree": degree,
                    "r": r,
                    "alpha_on_exact_radial_branch": float(
                        np.abs(np.diff(np.unwrap(np.angle(exact_values)))).sum()
                    ),
                    "alpha_np_poly_build_from_5pct": float(
                        np.abs(np.diff(np.unwrap(np.angle(built_values)))).sum()
                    ),
                    "coefficient_reconstruction_error": float(
                        np.abs(built - exact.astype(np.complex128)).max()
                    ),
                }
            )

    cassini: list[dict[str, Any]] = []
    for a in (0.3, 0.6, 0.9, 0.999):
        packet = measure_config(np.array([a, -a], dtype=np.complex128), ULTRA)
        if packet is None:
            cassini.append({"a": a, "error": "tracker refused"})
            continue
        row = packet["least_value_hub"]
        cassini.append(
            {
                "a": a,
                "radius": packet["radius"],
                **{
                    k: row[k]
                    for k in (
                        "length",
                        "chord_sum",
                        "d_sum",
                        "alpha_max",
                        "ratio_t1",
                        "ratio_t2",
                        "ratio_t4",
                        "alpha_disagreement",
                    )
                },
            }
        )

    perturbed: list[dict[str, Any]] = []
    rng = np.random.default_rng(20261041)
    for degree in (3, 4, 5, 6):
        offset = rng.normal(size=degree) + 1j * rng.normal(size=degree)
        offset = offset / np.abs(offset).max()
        for epsilon in (1.0e-1, 1.0e-2, 1.0e-3, 1.0e-4, 1.0e-5):
            roots = clamp(0.9 * np.exp(2j * np.pi * np.arange(degree) / degree) * (1 + epsilon * offset))
            packet = measure_config(roots, TIGHT)
            if packet is None:
                continue
            perturbed.append(
                {
                    "degree": degree,
                    "epsilon": epsilon,
                    "radius": packet["radius"],
                    "max_alpha_over_hubs": max(h["alpha_max"] for h in packet["hubs"]),
                    "max_ratio_t1": max(h["ratio_t1"] for h in packet["hubs"]),
                    "max_ratio_t2": max(h["ratio_t2"] for h in packet["hubs"]),
                    "min_ratio_t4": min(h["ratio_t4"] for h in packet["hubs"]),
                    "least_value_ratio_t1": packet["least_value_hub"]["ratio_t1"],
                    "least_value_ratio_t2": packet["least_value_hub"]["ratio_t2"],
                    "min_budget_ratio": min(h["budget_ratio"] for h in packet["hubs"]),
                    "max_budget_ratio": max(h["budget_ratio"] for h in packet["hubs"]),
                }
            )
    return {"radial": radial, "cassini": cassini, "perturbed": perturbed}


# --------------------------------------------------------------------------- #
# self-test
# --------------------------------------------------------------------------- #
def self_test() -> dict[str, Any]:
    checks: list[dict[str, Any]] = []

    packet = measure_config(np.array([0.7, -0.7], dtype=np.complex128), ULTRA)
    row = packet["least_value_hub"]
    checks.append(
        {
            "check": "z^2 - a^2 at a=0.7: L = 2a, alpha = 0, every ratio 1",
            "length": row["length"],
            "alpha_max": row["alpha_max"],
            "ratio_t1": row["ratio_t1"],
            "ratio_t4": row["ratio_t4"],
            "pass": bool(
                abs(row["length"] - 1.4) < 1.0e-9
                and row["alpha_max"] < 1.0e-8
                and abs(row["ratio_t4"] - 1.0) < 1.0e-9
            ),
        }
    )

    witness_rows = hard_witness_validation()
    checks.append(
        {
            "check": "exact degree-6 / degree-9 witnesses reproduce 1.763942 / 1.545995",
            "rows": witness_rows,
            "pass": bool(witness_rows and all(r.get("pass") for r in witness_rows)),
        }
    )

    rng = np.random.default_rng(7)
    cone_fail = 0
    length_delta = 0.0
    alpha_delta = 0.0
    start_offset = 0.0
    alpha_overread = 0.0
    floor_violations = 0
    floor_slack = math.inf
    tested = 0
    for _ in range(14):
        degree = int(rng.integers(3, 8))
        candidate = draw_roots(rng, degree, STYLES[tested % len(STYLES)])
        packet = measure_config(candidate, TIGHT)
        if packet is None:
            continue
        for h in packet["hubs"]:
            tested += 1
            cone_fail += 0 if h["cone_bound_holds"] else 1
            alpha_delta = max(alpha_delta, h["alpha_disagreement"])
            start_offset = max(start_offset, h["alpha_start_offset"])
            alpha_overread = max(
                alpha_overread,
                max(b["alpha_grid"] - b["alpha_ode"] for b in h["branches"]),
            )
            floor_slack = min(floor_slack, h["alpha_sum"] - h["turning_floor"])
            floor_violations += 0 if h["turning_floor_holds"] else 1
            pair = descending_pair(
                candidate, h["hub"], relative_tolerance=1.0e-12, absolute_tolerance=1.0e-14
            )
            if pair:
                length_delta = max(length_delta, abs(pair["total_length"] - h["length"]))
    checks.append(
        {
            "check": "cone bound L <= chord/cos(alpha/2) holds per branch (a theorem)",
            "hubs_tested": tested,
            "violations": cone_fail,
            "pass": cone_fail == 0,
        }
    )
    checks.append(
        {
            "check": "length agrees with formal_math_lemniscate.descending_pair",
            "max_absolute_delta": length_delta,
            "note": "the repo tracker starts from np.roots, so exact agreement is not expected",
            "pass": bool(length_delta < 1.0e-6),
        }
    )
    checks.append(
        {
            "check": "two independent alpha instruments agree (ODE state vs bisection)",
            "max_absolute_delta": alpha_delta,
            "max_bisection_overread": alpha_overread,
            "note": (
                "the bisection instrument under-reads a fast-turning branch until "
                "depth ~10 while the ODE state is already converged, so the "
                "disagreement is one-sided and the reported alpha is their maximum"
            ),
            "pass": bool(alpha_delta < 2.0e-3 and alpha_overread < 1.0e-6),
        }
    )
    checks.append(
        {
            "check": "series branch start lands on the analytic tangent limit",
            "max_arg_offset_rad": start_offset,
            "pass": bool(start_offset < 1.0e-4),
        }
    )
    checks.append(
        {
            "check": "turning floor alpha_A + alpha_B >= pi - phi holds at every hub",
            "hubs_tested": tested,
            "violations": floor_violations,
            "minimum_slack_rad": floor_slack,
            "note": (
                "a theorem: the branches leave a simple saddle in opposite "
                "directions and each chord lies inside its own tangent cone"
            ),
            "pass": bool(floor_violations == 0),
        }
    )
    families = family_rows()
    worst_radial = max(r["alpha_on_exact_radial_branch"] for r in families["radial"])
    worst_built = max(r["alpha_np_poly_build_from_5pct"] for r in families["radial"])
    checks.append(
        {
            "check": "alpha = 0 on the exact radial branch of z^n - r^n",
            "max_alpha_exact_coefficients": worst_radial,
            "max_alpha_np_poly_build_outside_5pct": worst_built,
            "note": (
                "the np.poly reconstruction carries ~1e-16 coefficient noise, which "
                "is visible in arg f' where |f'| itself is ~1e-9 near the hub"
            ),
            "pass": bool(worst_radial < 1.0e-12 and worst_built < 1.0e-6),
        }
    )
    return {"checks": checks, "families": families, "pass": all(c["pass"] for c in checks)}


# --------------------------------------------------------------------------- #
# random sweep
# --------------------------------------------------------------------------- #
def random_sweep(trials: int, min_n: int, max_n: int, seed: int, tol: Tol) -> dict[str, Any]:
    rng = np.random.default_rng(seed)
    hub_rows: list[dict[str, Any]] = []
    config_rows: list[dict[str, Any]] = []
    rejected = 0
    for index in range(trials):
        degree = int(rng.integers(min_n, max_n + 1))
        style = STYLES[index % len(STYLES)]
        roots = draw_roots(rng, degree, style)
        packet = measure_config(roots, tol)
        if packet is None:
            rejected += 1
            continue
        clean_hubs = [h for h in packet["hubs"] if h["clean"]]
        if not clean_hubs:
            rejected += 1
            continue
        for h in clean_hubs:
            hub_rows.append(
                {
                    "degree": packet["degree"],
                    "style": style,
                    "alpha_max": h["alpha_max"],
                    "ratio_t1": h["ratio_t1"],
                    "ratio_t2": h["ratio_t2"],
                    "ratio_t4": h["ratio_t4"],
                    "budget_ratio": h["budget_ratio"],
                    "inflation": h["inflation"],
                    "both_nearest": h["both_branches_nearest"],
                    "cone_ok": h["cone_bound_holds"],
                    "vacuous": h["vacuous_cone"],
                    "alpha_disagreement": h["alpha_disagreement"],
                }
            )
        lv, ml = packet["least_value_hub"], packet["minimum_length_hub"]
        config_rows.append(
            {
                "degree": packet["degree"],
                "style": style,
                "roots": roots,
                "lv_t1": lv["ratio_t1"],
                "lv_t2": lv["ratio_t2"],
                "lv_alpha": lv["alpha_max"],
                "lv_length": lv["length"],
                "lv_clean": lv["clean"],
                "min_t4": ml["ratio_t4"],
                "min_length": ml["length"],
            }
        )
    return {"hub_rows": hub_rows, "config_rows": config_rows, "rejected": rejected}


def summarise_random(sweep: dict[str, Any]) -> dict[str, Any]:
    hub_rows, config_rows = sweep["hub_rows"], sweep["config_rows"]
    if not hub_rows:
        return {"hubs": 0}
    alphas = np.array([r["alpha_max"] for r in hub_rows])
    worst: dict[str, Any] = {}
    for key in ("lv_t1", "lv_t2", "min_t4", "lv_length"):
        rows = [r for r in config_rows if r["lv_clean"] or key.startswith("min")]
        if rows:
            top = max(rows, key=lambda r: r[key])
            worst[key] = {
                "value": top[key],
                "degree": top["degree"],
                "style": top["style"],
                "roots": roots_payload(top["roots"]),
            }
    return {
        "hubs": len(hub_rows),
        "configs": len(config_rows),
        "rejected": sweep["rejected"],
        "alpha_quantiles_rad": {
            f"p{q}": float(np.percentile(alphas, q)) for q in (50, 75, 90, 95, 99, 100)
        },
        "alpha_quantiles_deg": {
            f"p{q}": float(np.degrees(np.percentile(alphas, q)))
            for q in (50, 75, 90, 95, 99, 100)
        },
        "alpha_ge_pi_count": int((alphas >= math.pi).sum()),
        "max_alpha_disagreement": float(max(r["alpha_disagreement"] for r in hub_rows)),
        "cone_violations": int(sum(1 for r in hub_rows if not r["cone_ok"])),
        "both_branches_nearest_fraction": float(
            sum(1 for r in hub_rows if r["both_nearest"]) / len(hub_rows)
        ),
        "max_hub_ratio_t1": float(max(r["ratio_t1"] for r in hub_rows)),
        "max_hub_ratio_t2": float(max(r["ratio_t2"] for r in hub_rows)),
        "max_hub_ratio_t4": float(max(r["ratio_t4"] for r in hub_rows)),
        "hub_ratio_t1_above_one": int(sum(1 for r in hub_rows if r["ratio_t1"] > 1.0)),
        "hub_ratio_t2_above_one": int(sum(1 for r in hub_rows if r["ratio_t2"] > 1.0)),
        "worst_by_rule": worst,
    }


# --------------------------------------------------------------------------- #
# main
# --------------------------------------------------------------------------- #
def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--modes", default="selftest,random,adversarial")
    parser.add_argument("--trials", type=int, default=300)
    parser.add_argument("--random-min-n", type=int, default=3)
    parser.add_argument("--random-max-n", type=int, default=10)
    parser.add_argument("--adv-min-n", type=int, default=3)
    parser.add_argument("--adv-max-n", type=int, default=8)
    parser.add_argument("--restarts", type=int, default=8)
    parser.add_argument("--steps", type=int, default=110)
    parser.add_argument("--campaigns", type=int, default=2, help="independent basin campaigns")
    parser.add_argument("--polish", type=int, default=0, help="Nelder-Mead iterations")
    parser.add_argument("--targets", default="t1,t2,t3,t4,t5")
    parser.add_argument("--seed", type=int, default=104120260823)
    parser.add_argument("--quiet", action="store_true")
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    modes = [m.strip() for m in args.modes.split(",") if m.strip()]
    report: dict[str, Any] = {
        "probe": "check_erdos1041_turning_inflation",
        "tolerances": {t.name: asdict(t) for t in (FAST, TIGHT, ULTRA)},
    }
    started = time.time()

    if "selftest" in modes:
        result = self_test()
        report["selftest"] = result
        print(
            json.dumps(
                {"selftest": {"pass": result["pass"], "checks": result["checks"]}},
                indent=2,
                default=str,
            ),
            flush=True,
        )
        print(json.dumps({"families": result["families"]}, indent=2, default=str), flush=True)
        if not result["pass"]:
            print("SELFTEST FAILED -- downstream numbers are not trustworthy", flush=True)

    if "random" in modes:
        sweep = random_sweep(args.trials, args.random_min_n, args.random_max_n, args.seed, FAST)
        summary = summarise_random(sweep)
        report["random"] = summary
        print(json.dumps({"random": summary}, indent=2, default=str), flush=True)

    if "adversarial" in modes:
        targets = [t.strip() for t in args.targets.split(",") if t.strip()]
        rows: list[dict[str, Any]] = []
        cross_seeds: dict[int, list[np.ndarray]] = {}
        for target in targets:
            for degree in range(args.adv_min_n, args.adv_max_n + 1):
                campaign_values: list[float] = []
                best_roots = None
                best_value = -math.inf
                started_at = time.time()
                for campaign in range(args.campaigns):
                    rng = np.random.default_rng(
                        args.seed + 1000 * campaign + 31 * degree + 7 * hash(target) % 1009
                    )
                    found = adversarial(
                        degree,
                        target,
                        args.restarts,
                        args.steps,
                        rng,
                        FAST,
                        seeds=cross_seeds.get(degree, []),
                        verbose=not args.quiet,
                    )
                    campaign_values.append(found["search_best"])
                    if "roots" in found and found["search_best"] > best_value:
                        best_value, best_roots = found["search_best"], found["roots"]
                if best_roots is None:
                    rows.append({"target": target, "degree": degree, "audit": {"ok": False}})
                    continue
                if args.polish:
                    best_value, best_roots = nelder_mead_polish(
                        best_roots, target, FAST, args.polish
                    )
                cross_seeds.setdefault(degree, []).append(best_roots)
                audit = audit_witness(best_roots, target)
                row = {
                    "target": target,
                    "degree": degree,
                    "search_best_fast": best_value,
                    "campaign_bests": campaign_values,
                    "campaign_spread": (
                        float(max(campaign_values) - min(campaign_values))
                        if len(campaign_values) > 1
                        and all(math.isfinite(v) for v in campaign_values)
                        else None
                    ),
                    "audit": audit,
                    "seconds": round(time.time() - started_at, 1),
                }
                rows.append(row)
                hub = audit.get("hub", {})
                print(
                    json.dumps(
                        {
                            "adversarial": {
                                "target": target,
                                "n": degree,
                                "fast": round(best_value, 6),
                                "tight": audit.get("value"),
                                "ultra": audit.get("value_ultra"),
                                "campaigns": [round(v, 6) for v in campaign_values],
                                "alpha_max": hub.get("alpha_max"),
                                "budget_ratio": hub.get("budget_ratio"),
                                "t1": hub.get("ratio_t1"),
                                "t2": hub.get("ratio_t2"),
                                "t4": hub.get("ratio_t4"),
                                "L": hub.get("length"),
                                "repo_delta": audit.get("repo_length_delta"),
                                "s": row["seconds"],
                            }
                        },
                        default=str,
                    ),
                    flush=True,
                )
        report["adversarial"] = rows

        verdict: dict[str, Any] = {}
        for target in targets:
            candidates = [
                r for r in rows if r["target"] == target and r.get("audit", {}).get("ok")
            ]
            if not candidates:
                continue
            top = max(candidates, key=lambda r: r["audit"]["value"])
            verdict[target] = {
                "worst_value_tight": top["audit"]["value"],
                "worst_value_ultra": top["audit"]["value_ultra"],
                "tolerance_drift": top["audit"]["tolerance_drift"],
                "degree": top["degree"],
                "per_degree": {
                    r["degree"]: r["audit"]["value"] for r in candidates
                },
                "campaign_spread": top["campaign_spread"],
                "hub": top["audit"]["hub"],
                "roots": top["audit"]["roots"],
                "repo_length_delta": top["audit"]["repo_length_delta"],
            }
        report["verdict"] = verdict

        def worst(target: str) -> float | None:
            return verdict.get(target, {}).get("worst_value_tight")

        def pinned(value: float | None, threshold: float = 1.0) -> bool:
            return value is not None and 0.98 * threshold <= value < threshold

        headline = {
            "T1_worst": worst("t1"),
            "T1_route_dead": worst("t1") is not None and worst("t1") > 1.0,
            "T1_pinned_below_threshold": pinned(worst("t1")),
            "T2_worst": worst("t2"),
            "T2_route_dead": worst("t2") is not None and worst("t2") > 1.0,
            "T2_pinned_below_threshold": pinned(worst("t2")),
            "T3_alpha_max": worst("t3"),
            "T3_exceeds_pi": worst("t3") is not None and worst("t3") >= math.pi,
            "T4_worst": worst("t4"),
            "MIN_refuted": worst("t4") is not None and worst("t4") >= 1.0,
            "T4_pinned_below_threshold": pinned(worst("t4")),
            "T5_least_value_hub_length": worst("t5"),
            "T5_corpus_reference": RECORDED_LEAST_VALUE_ATTACK,
            # steelman: > 1 means the chain closes at NO admissible hub
            "T1_best_hub_worst": worst("t1_best"),
            "T1_mechanism_dead_at_every_hub": (
                worst("t1_best") is not None and worst("t1_best") > 1.0
            ),
            "T2_best_hub_worst": worst("t2_best"),
            "T2_mechanism_dead_at_every_hub": (
                worst("t2_best") is not None and worst("t2_best") > 1.0
            ),
        }
        report["headline"] = headline
        print(json.dumps({"headline": headline}, indent=2, default=str), flush=True)

    report["elapsed_seconds"] = round(time.time() - started, 1)
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(report, indent=2, default=str) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
