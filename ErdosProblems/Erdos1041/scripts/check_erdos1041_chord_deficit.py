#!/usr/bin/env python3
"""Erdos #1041: the chord-deficit identity, measured.

For a descent branch from ``p`` to ``q`` with unit tangent ``T`` and chord
direction ``e = (q-p)/|q-p|``, ``int T ds = q - p`` gives the elementary identity

    L  =  |q - p|  +  int (1 - cos theta) ds,      theta(s) = angle(T(s), e).

Summed over the two branches at a simple critical point ``c`` whose branches
reach roots ``a`` and ``b``:

    L(c)  =  (d1 + d2)  +  D(c),     d1 = |a - c|, d2 = |b - c|,   D(c) >= 0.

so ``#1041`` follows from ``D(c) < 2 - (d1 + d2)`` at one admissible hub, and a
fortiori from ``D(c) < 2(1 - R)`` given a budget ``d1 + d2 <= 2R``.

WHAT THIS PROBE MEASURES

  M1  min over hubs of D(c) / (2 - (d1 + d2))     (endpoint chords)
  M2  min over hubs of D(c) / (2 (1 - R))
  M3  the distribution of D(c) and of D(c)/L(c)
  M4  the identity itself: L - (d1 + d2) - D, with D by INDEPENDENT quadrature
  M5  D -> 0 on z^n - r^n perturbed to split the degenerate hub

TWO DISTINCTIONS THAT THE SETUP HIDES, AND THAT THIS PROBE KEEPS SEPARATE

  * The proved global budget (``GlobalCriticalTwoNearestBudget.md``, B1) bounds
    the sum of the distances to the TWO NEAREST roots.  The identity above needs
    the distances to the two BRANCH ENDPOINT roots, which are a different pair
    whenever a branch runs past a near root.  ``chord_over_2R`` measures the gap;
    when it exceeds 1 the ``2(1-R)`` form of the route has no proved input.
  * ``D(c) < 2 - (d1 + d2)`` with endpoint chords is EXACTLY ``L(c) < 2`` because
    the identity is exact.  M1 < 1 is therefore not a new sufficient condition;
    it is MIN restated.  M4 is what establishes that, which is why it runs first.

INSTRUMENT

  Branch tracking, the series-based branch start, the tolerance ladder and the
  root generators are reused from ``check_erdos1041_turning_inflation.py``, whose
  ``--modes selftest`` gate is the validated instrument for this directory.
  ``system/lib/formal_math_lemniscate.descending_pair`` is NOT used: its start
  directions are up to 50 degrees wrong and every quantity here is angular.

  D is integrated three ways: composite Gauss-Legendre on the dense output at k
  and 2k nodes per solver step (the k/2k gap is the quadrature error bar), and
  optionally a second ODE pass carrying D as a state variable under the solver's
  own adaptive error control.  The integrand is written ``2 sin^2(theta/2)``
  rather than ``1 - cos theta`` so that it stays accurate on straight branches,
  where the whole question lives.

Replay:

    ./repo-python .../check_erdos1041_chord_deficit.py --modes gate
    ./repo-python .../check_erdos1041_chord_deficit.py --modes witness,family
    ./repo-python .../check_erdos1041_chord_deficit.py --modes fekete --trials 3
    ./repo-python .../check_erdos1041_chord_deficit.py --modes sweep --trials 240
    ./repo-python .../check_erdos1041_chord_deficit.py --modes attack --restarts 10
"""

from __future__ import annotations

import argparse
import json
import math
import sys
import time
from pathlib import Path
from typing import Any, Sequence

import numpy as np
from scipy.integrate import solve_ivp

REPO_ROOT = Path(__file__).resolve().parents[5]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formal_math.erdos257_period_noncollapse.ErdosProblems.Erdos1041.scripts.check_erdos1041_turning_inflation import (  # noqa: E402
    CAP,
    FAST,
    MIN_CRITICAL_VALUE,
    STYLES,
    TIGHT,
    ULTRA,
    Tol,
    branch_start,
    circumcircle,
    clamp,
    draw_roots,
    horner,
    taylor_ascending,
    witness_roots,
)

INF = math.inf


# --------------------------------------------------------------------------- #
# quadrature
# --------------------------------------------------------------------------- #
_GL: dict[int, tuple[np.ndarray, np.ndarray]] = {}


def gauss_legendre(k: int) -> tuple[np.ndarray, np.ndarray]:
    if k not in _GL:
        _GL[k] = np.polynomial.legendre.leggauss(k)
    return _GL[k]


def _deficit_quadrature(
    solution: Any,
    fp_coefficients: np.ndarray,
    value: complex,
    chord_direction: complex,
    k: int,
) -> tuple[float, float, float]:
    """Composite Gauss-Legendre for (arc length, deficit, max |theta|)."""

    steps = solution.t
    nodes, weights = gauss_legendre(k)
    left = steps[:-1][:, None]
    right = steps[1:][:, None]
    middle = 0.5 * (left + right)
    half = 0.5 * (right - left)
    points = (middle + half * nodes[None, :]).ravel()
    quad_weights = (half * weights[None, :]).ravel()
    state = solution.sol(points)
    offset = state[0] + 1j * state[1]
    derivative = np.polyval(fp_coefficients, offset)
    velocity = -2.0 * points * value / derivative
    speed = np.abs(velocity)
    rotated = np.conj(chord_direction) * velocity
    theta = np.arctan2(rotated.imag, rotated.real)
    # 2 sin^2(theta/2) == 1 - cos(theta) without the cancellation at theta ~ 0
    integrand = speed * 2.0 * np.sin(0.5 * theta) ** 2
    return (
        float(np.dot(quad_weights, speed)),
        float(np.dot(quad_weights, integrand)),
        float(np.abs(theta).max()),
    )


# --------------------------------------------------------------------------- #
# one branch
# --------------------------------------------------------------------------- #
def track_branch_deficit(
    roots: np.ndarray,
    hub: complex,
    value: complex,
    f_series: Sequence[complex],
    fp_series: Sequence[complex],
    fpp_series: Sequence[complex],
    start: complex,
    tol: Tol,
    *,
    quad_nodes: int,
    deficit_ode: bool,
) -> dict[str, Any] | None:
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

    target = complex(roots[index])
    chord_vector = target - hub
    chord = abs(chord_vector)
    if chord <= 0.0:
        return None
    chord_direction = chord_vector / chord

    fp_coefficients = np.asarray(fp_series, dtype=np.complex128)
    length_k, deficit_k, theta_max = _deficit_quadrature(
        solution, fp_coefficients, value, chord_direction, quad_nodes
    )
    length_2k, deficit_2k, _ = _deficit_quadrature(
        solution, fp_coefficients, value, chord_direction, 2 * quad_nodes
    )

    # the u in [0, u0] stub: f(c+d) = v + a2 d^2 + O(d^3) makes it a straight
    # segment of length |start| in direction arg(start) to relative O(u0)
    stub_length = abs(start)
    rotated_start = np.conj(chord_direction) * start
    stub_theta = math.atan2(rotated_start.imag, rotated_start.real)
    stub_deficit = stub_length * 2.0 * math.sin(0.5 * stub_theta) ** 2

    # solve_ivp is seeded with arclength state ``abs(start)``, so ``y[2]`` already
    # carries the u in [0, u0] stub; only the deficit accumulator starts at zero.
    length_ode = float(solution.y[2, -1])
    deficit_quad = deficit_2k + stub_deficit

    deficit_ode_value = None
    second_length_gap = None
    if deficit_ode:

        def field2(u: float, state: np.ndarray) -> list[float]:
            d = state[0] + 1j * state[1]
            fp = horner(fp_series, d)
            velocity = -2.0 * u * value / fp
            speed = abs(velocity)
            rotated = velocity / chord_direction
            angle = math.atan2(rotated.imag, rotated.real)
            return [
                velocity.real,
                velocity.imag,
                speed,
                speed * 2.0 * math.sin(0.5 * angle) ** 2,
            ]

        second = solve_ivp(
            field2,
            (u0, 1.0),
            [start.real, start.imag, abs(start), 0.0],
            rtol=tol.rtol,
            atol=tol.atol,
            max_step=tol.max_step,
        )
        if second.success:
            deficit_ode_value = float(second.y[3, -1]) + stub_deficit
            second_length_gap = abs(float(second.y[2, -1]) - length_ode)
        else:
            second_length_gap = None

    return {
        "root_index": index,
        "chord": float(chord),
        "length_ode": float(length_ode),
        "length_quad": float(length_2k + stub_length),
        "deficit_quad": float(deficit_quad),
        "deficit_quad_coarse": float(deficit_k + stub_deficit),
        "deficit_ode": deficit_ode_value,
        "stub_deficit": float(stub_deficit),
        "stub_length": float(stub_length),
        "second_pass_length_gap": second_length_gap,
        "theta_max": float(max(theta_max, abs(stub_theta))),
        "alpha_ode": float(solution.y[3, -1]),
        "endpoint": endpoint,
        "endpoint_error": float(abs(target - endpoint)),
        "maximum_level_residual": residual,
        "solver_steps": int(solution.t.size),
    }


# --------------------------------------------------------------------------- #
# one hub
# --------------------------------------------------------------------------- #
def measure_hub_deficit(
    roots: np.ndarray,
    coefficients: Sequence[complex],
    critical_points: np.ndarray,
    hub_index: int,
    radius: float,
    tol: Tol,
    *,
    quad_nodes: int,
    deficit_ode: bool,
) -> dict[str, Any] | str:
    """Return a row, or a string naming why the hub was discarded."""

    hub = complex(critical_points[hub_index])
    ascending = taylor_ascending(coefficients, hub)
    value = ascending[0]
    modulus = abs(value)
    if modulus >= 1.0:
        return "not_admissible"
    if modulus <= MIN_CRITICAL_VALUE:
        return "critical_value_underflow"
    critical_residual = abs(ascending[1])
    ascending[1] = 0.0 + 0.0j
    if len(ascending) < 3 or abs(ascending[2]) < 1.0e-9:
        return "degenerate_saddle"

    degree = len(ascending) - 1
    f_series = list(reversed(ascending))
    fp_series = list(reversed([k * ascending[k] for k in range(1, degree + 1)]))
    fpp_series = list(
        reversed([k * (k - 1) * ascending[k] for k in range(2, degree + 1)])
    )

    u0 = tol.start_u
    level = list(f_series)
    level[-1] = (u0**2) * value
    leading = np.sqrt(-value / ascending[2])
    branches: list[dict[str, Any]] = []
    for sign in (1.0, -1.0):
        guess = sign * complex(leading) * u0
        start, start_residual = branch_start(level, fp_series, guess)
        if abs(start) <= 0.0 or not np.isfinite(abs(start)):
            return "branch_start_nonfinite"
        if abs(start - guess) > 0.25 * abs(guess):
            return "branch_start_outside_asymptotic_regime"
        row = track_branch_deficit(
            roots,
            hub,
            value,
            f_series,
            fp_series,
            fpp_series,
            start,
            tol,
            quad_nodes=quad_nodes,
            deficit_ode=deficit_ode,
        )
        if row is None:
            return "solver_failed"
        row["start_residual"] = start_residual
        branches.append(row)
    if branches[0]["root_index"] == branches[1]["root_index"]:
        return "branches_merge_on_one_root"

    distances = np.abs(np.asarray(roots, dtype=np.complex128) - hub)
    order = np.argsort(distances)
    nearest_sum = float(distances[order[0]] + distances[order[1]])
    nearest_two = {int(order[0]), int(order[1])}

    d1 = branches[0]["chord"]
    d2 = branches[1]["chord"]
    chord_sum = d1 + d2
    length = branches[0]["length_ode"] + branches[1]["length_ode"]
    deficit = branches[0]["deficit_quad"] + branches[1]["deficit_quad"]
    deficit_coarse = (
        branches[0]["deficit_quad_coarse"] + branches[1]["deficit_quad_coarse"]
    )
    deficit_ode_total = None
    if all(b["deficit_ode"] is not None for b in branches):
        deficit_ode_total = branches[0]["deficit_ode"] + branches[1]["deficit_ode"]

    identity_residual = abs(length - chord_sum - deficit)
    length_quad = branches[0]["length_quad"] + branches[1]["length_quad"]

    two_r = 2.0 * radius
    slack = 2.0 - chord_sum
    m1 = deficit / slack if slack > 0.0 else INF
    crude = 2.0 * (1.0 - radius)
    m2 = deficit / crude if crude > 0.0 else INF

    endpoint_error = max(b["endpoint_error"] for b in branches)
    level_residual = max(b["maximum_level_residual"] for b in branches)
    quadrature_gap = abs(deficit - deficit_coarse)
    clean = bool(
        endpoint_error < tol.endpoint_gate
        and level_residual < tol.residual_gate
        and identity_residual <= max(1.0e-9, 1.0e-7 * length)
    )
    return {
        "hub_index": hub_index,
        "hub": hub,
        "critical_value_modulus": float(modulus),
        "critical_residual": float(critical_residual),
        "second_derivative_modulus": float(abs(2.0 * ascending[2])),
        "d1": float(d1),
        "d2": float(d2),
        "chord_sum": float(chord_sum),
        "nearest_sum": nearest_sum,
        "endpoints_are_nearest_two": bool(
            branches[0]["root_index"] in nearest_two
            and branches[1]["root_index"] in nearest_two
        ),
        "length": float(length),
        "length_quad": float(length_quad),
        "length_instrument_gap": float(abs(length - length_quad)),
        "deficit": float(deficit),
        "deficit_coarse": float(deficit_coarse),
        "deficit_ode": deficit_ode_total,
        "deficit_ode_gap": (
            None if deficit_ode_total is None else float(abs(deficit_ode_total - deficit))
        ),
        "quadrature_gap": float(quadrature_gap),
        "identity_residual": float(identity_residual),
        "identity_relative": float(identity_residual / max(length, 1.0e-300)),
        "m1": float(m1),
        "m2": float(m2),
        "deficit_over_length": float(deficit / length) if length > 0 else INF,
        "slack": float(slack),
        "crude_slack": float(crude),
        "chord_over_2R": float(chord_sum / two_r),
        "nearest_over_2R": float(nearest_sum / two_r),
        "length_over_2": float(length / 2.0),
        "alpha_max": float(max(b["alpha_ode"] for b in branches)),
        "theta_max": float(max(b["theta_max"] for b in branches)),
        "max_endpoint_error": float(endpoint_error),
        "max_level_residual": float(level_residual),
        "max_start_residual": float(max(b["start_residual"] for b in branches)),
        "clean": clean,
    }


# --------------------------------------------------------------------------- #
# one configuration
# --------------------------------------------------------------------------- #
def measure_config_deficit(
    roots: np.ndarray,
    tol: Tol,
    *,
    quad_nodes: int = 12,
    deficit_ode: bool = False,
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
    if radius <= 1.0e-9 or radius >= 1.0:
        return None

    moduli = np.abs(np.polyval(np.asarray(coefficients), critical_points))
    order = [int(i) for i in np.argsort(moduli) if MIN_CRITICAL_VALUE < moduli[i] < 1.0]
    if not order:
        return None

    hubs: list[dict[str, Any]] = []
    discards: dict[str, int] = {}
    for position, index in enumerate(order):
        row = measure_hub_deficit(
            roots,
            coefficients,
            critical_points,
            index,
            radius,
            tol,
            quad_nodes=quad_nodes,
            deficit_ode=deficit_ode,
        )
        if isinstance(row, str):
            discards[row] = discards.get(row, 0) + 1
            continue
        if not row["clean"]:
            discards["unclean_track"] = discards.get("unclean_track", 0) + 1
            continue
        # position 0 is the least-|f(c)| ("first merge") hub, the only one where
        # CriticalBudgetLab.md measures the branch endpoints to be the two nearest
        # roots, hence the only one where the proved nearest-two budget applies.
        row["is_least_value_hub"] = bool(position == 0)
        hubs.append(row)
    if not hubs:
        return None
    best_m1 = min(hubs, key=lambda r: r["m1"])
    best_m2 = min(hubs, key=lambda r: r["m2"])
    return {
        "degree": int(roots.size),
        "roots": roots,
        "radius": float(radius),
        "root_separation": float(separation),
        "hubs": hubs,
        "hub_count": len(hubs),
        "discards": discards,
        "discard_count": sum(discards.values()),
        "m1_config": float(best_m1["m1"]),
        "m2_config": float(best_m2["m2"]),
        "best_m1_hub": best_m1,
        "best_m2_hub": best_m2,
        "min_length": float(min(h["length"] for h in hubs)),
        # MIN restated: m1_config < 1 is exactly min_c L_c < 2, so the two
        # objectives are the same question and are attacked separately only to
        # keep one of them finite everywhere.
        "minlen_config": float(min(h["length"] for h in hubs)),
        "max_identity_residual": float(max(h["identity_residual"] for h in hubs)),
        "max_chord_over_2R": float(max(h["chord_over_2R"] for h in hubs)),
        "max_nearest_over_2R": float(max(h["nearest_over_2R"] for h in hubs)),
    }


# --------------------------------------------------------------------------- #
# root families
# --------------------------------------------------------------------------- #
def normalise(roots: np.ndarray) -> np.ndarray:
    roots = np.asarray(roots, dtype=np.complex128)
    centre, radius = circumcircle(roots)
    roots = roots - centre
    if radius > CAP:
        roots = roots * (CAP / radius)
    return roots


def perturbed_ngon(
    degree: int, epsilon: float, perturbation: float, rng: np.random.Generator
) -> np.ndarray:
    """z_k = r (1 + a_k) exp(i(2 pi k / n + t_k)), rescaled so R = 1 - epsilon."""

    amplitude = perturbation * rng.normal(size=degree)
    phase = perturbation * rng.normal(size=degree)
    base = (1.0 + amplitude) * np.exp(
        1j * (2.0 * np.pi * np.arange(degree) / degree + phase)
    )
    centre, radius = circumcircle(base)
    if radius <= 0.0:
        return base
    return (base - centre) * ((1.0 - epsilon) / radius)


def radial_family(degree: int, r: float, delta: float, rng: np.random.Generator) -> np.ndarray:
    """z^n - r^n perturbed: the degenerate central hub splits into n-1 simple ones."""

    base = r * np.exp(2j * np.pi * np.arange(degree) / degree)
    if delta > 0.0:
        base = base + delta * (rng.normal(size=degree) + 1j * rng.normal(size=degree))
    return clamp(base)


def linear_perturbed_power(degree: int, r: float, epsilon: float) -> np.ndarray | None:
    """Roots of ``f(z) = z^n + eps z - r^n``.

    The extremal family with its degenerate hub resolved in closed form: every
    critical point solves ``c^(n-1) = -eps/n``, so all ``n-1`` are simple and sit
    at modulus ``(eps/n)^(1/(n-1))``, and ``|f(c)| -> r^n`` as ``eps -> 0``.  This
    is the family the route has to survive, parametrised deterministically rather
    than by a random perturbation draw.
    """

    coefficients = np.zeros(degree + 1, dtype=np.complex128)
    coefficients[0] = 1.0
    coefficients[-2] = epsilon
    coefficients[-1] = -(r**degree)
    roots = np.roots(coefficients)
    if roots.size != degree or np.abs(roots).max() >= 1.0:
        return None
    return roots


def linear_family_table(
    degrees: Sequence[int], tol: Tol, quad_nodes: int
) -> dict[str, Any]:
    radii = (0.9, 0.99, 0.999, 0.9999, 1.0 - 1.0e-6, 1.0 - 1.0e-9)
    epsilons = (1e-2, 1e-3, 1e-4, 1e-5, 1e-6, 1e-8, 1e-10, 1e-12)
    rows: list[dict[str, Any]] = []
    for degree in degrees:
        for r in radii:
            series: list[dict[str, Any]] = []
            for epsilon in epsilons:
                roots = linear_perturbed_power(degree, r, epsilon)
                if roots is None:
                    series.append({"epsilon": epsilon, "status": "roots_left_open_disk"})
                    continue
                packet = measure_config_deficit(
                    roots, tol, quad_nodes=quad_nodes, deficit_ode=False
                )
                if packet is None:
                    series.append({"epsilon": epsilon, "status": "no_clean_simple_hub"})
                    continue
                hub = packet["best_m1_hub"]
                series.append(
                    {
                        "epsilon": epsilon,
                        "radius": packet["radius"],
                        "hubs": packet["hub_count"],
                        "discards": packet["discards"],
                        "hub_modulus": float(abs(hub["hub"])),
                        "predicted_hub_modulus": float(
                            (epsilon / degree) ** (1.0 / (degree - 1))
                        )
                        if degree > 1
                        else 0.0,
                        "m1_config": packet["m1_config"],
                        "m2_config": packet["m2_config"],
                        "min_length": packet["min_length"],
                        "best_m1_deficit": hub["deficit"],
                        "best_m1_slack": hub["slack"],
                        "best_m1_chord_sum": hub["chord_sum"],
                        "deficit_over_hub_modulus": (
                            hub["deficit"] / abs(hub["hub"]) if abs(hub["hub"]) > 0 else None
                        ),
                        "max_chord_over_2R": packet["max_chord_over_2R"],
                        "max_deficit": max(h["deficit"] for h in packet["hubs"]),
                        "worst_hub_m1": max(h["m1"] for h in packet["hubs"]),
                        "identity_residual": packet["max_identity_residual"],
                    }
                )
            values = [s["m1_config"] for s in series if "m1_config" in s]
            rows.append(
                {
                    "degree": degree,
                    "r": r,
                    "series": series,
                    "m1_monotone_increasing_as_eps_to_zero": (
                        bool(
                            all(
                                values[i + 1] >= values[i] - 1.0e-12
                                for i in range(len(values) - 1)
                            )
                        )
                        if len(values) >= 3
                        else None
                    ),
                    "m1_last": values[-1] if values else None,
                    "m1_max": max(values) if values else None,
                }
            )
    return {"rows": rows}


def extremal_limit_table(
    degrees: Sequence[int], tol: Tol, quad_nodes: int
) -> dict[str, Any]:
    """Walk the double limit r -> 1 with the hub held far outside the boundary gap.

    On ``z^n + eps z - r^n`` the hubs sit at ``|c| = (eps/n)^(1/(n-1))`` and the
    roots leave the unit disk once ``eps >~ n(1-r)``.  Fixing ``eps = alpha n (1-r)``
    keeps the configuration admissible while sending ``|c|/(1-r) -> infinity``, which
    is the regime where the ``2(1-r)`` term of the slack is negligible and ``M1``
    reaches whatever constant the extremal family imposes.  A constant below one is
    the route surviving the limit; a drift toward one is the route dying in it.
    """

    rows: list[dict[str, Any]] = []
    for degree in degrees:
        for alpha in (0.1, 0.3, 0.5, 0.7, 0.9):
            series: list[dict[str, Any]] = []
            for exponent in range(1, 11):
                gap = 10.0**-exponent
                r = 1.0 - gap
                epsilon = alpha * degree * gap
                roots = linear_perturbed_power(degree, r, epsilon)
                if roots is None:
                    series.append({"gap": gap, "status": "roots_left_open_disk"})
                    continue
                packet = measure_config_deficit(
                    roots, tol, quad_nodes=quad_nodes, deficit_ode=False
                )
                if packet is None:
                    series.append({"gap": gap, "status": "no_clean_simple_hub"})
                    continue
                hub = packet["best_m1_hub"]
                modulus = abs(hub["hub"])
                series.append(
                    {
                        "gap": gap,
                        "epsilon": epsilon,
                        "radius": packet["radius"],
                        "hubs": packet["hub_count"],
                        "discards": packet["discards"],
                        "hub": [float(hub["hub"].real), float(hub["hub"].imag)],
                        "hub_modulus": float(modulus),
                        "hub_modulus_over_gap": float(modulus / gap),
                        "m1_config": packet["m1_config"],
                        "m2_config": packet["m2_config"],
                        "min_length": packet["min_length"],
                        "deficit": hub["deficit"],
                        "slack": hub["slack"],
                        "chord_sum": hub["chord_sum"],
                        "deficit_over_hub_modulus": (
                            hub["deficit"] / modulus if modulus > 0 else None
                        ),
                        "theta_max": hub["theta_max"],
                        "identity_residual": packet["max_identity_residual"],
                    }
                )
            values = [s["m1_config"] for s in series if "m1_config" in s]
            rows.append(
                {
                    "degree": degree,
                    "alpha": alpha,
                    "series": series,
                    "m1_last": values[-1] if values else None,
                    "m1_max": max(values) if values else None,
                    "m1_monotone_increasing_as_gap_to_zero": (
                        bool(
                            all(
                                values[i + 1] >= values[i] - 1.0e-12
                                for i in range(len(values) - 1)
                            )
                        )
                        if len(values) >= 3
                        else None
                    ),
                }
            )
    return {"rows": rows}


# --------------------------------------------------------------------------- #
# statistics
# --------------------------------------------------------------------------- #
def quantiles(values: Sequence[float]) -> dict[str, float]:
    finite = sorted(v for v in values if math.isfinite(v))
    if not finite:
        return {}
    array = np.asarray(finite)
    return {
        "count": len(finite),
        "min": float(array.min()),
        "p10": float(np.quantile(array, 0.10)),
        "median": float(np.median(array)),
        "p90": float(np.quantile(array, 0.90)),
        "p99": float(np.quantile(array, 0.99)),
        "max": float(array.max()),
    }


def roots_payload(roots: np.ndarray) -> dict[str, Any]:
    return {
        "decimal": [[float(z.real), float(z.imag)] for z in roots],
        "hex": [[float(z.real).hex(), float(z.imag).hex()] for z in roots],
        "max_modulus": float(np.abs(roots).max()),
    }


HUB_REPORT_KEYS = (
    "critical_value_modulus",
    "d1",
    "d2",
    "chord_sum",
    "nearest_sum",
    "endpoints_are_nearest_two",
    "length",
    "deficit",
    "identity_residual",
    "quadrature_gap",
    "deficit_ode_gap",
    "m1",
    "m2",
    "deficit_over_length",
    "chord_over_2R",
    "nearest_over_2R",
    "length_over_2",
    "alpha_max",
    "theta_max",
    "max_endpoint_error",
    "max_level_residual",
)


def hub_report(row: dict[str, Any]) -> dict[str, Any]:
    out = {key: row[key] for key in HUB_REPORT_KEYS}
    out["hub"] = [float(row["hub"].real), float(row["hub"].imag)]
    return out


# --------------------------------------------------------------------------- #
# M4 / M5 gate
# --------------------------------------------------------------------------- #
def gate(tol: Tol, quad_nodes: int) -> dict[str, Any]:
    checks: list[dict[str, Any]] = []
    rng = np.random.default_rng(20260823)

    # 1. z^2 - a^2: the branches are the two radii, D = 0 exactly.
    packet = measure_config_deficit(
        np.array([0.7, -0.7], dtype=np.complex128), ULTRA, quad_nodes=quad_nodes,
        deficit_ode=True,
    )
    row = packet["hubs"][0]
    checks.append(
        {
            "check": "z^2 - a^2 at a = 0.7: L = 2a, chord_sum = 2a, D = 0",
            "length": row["length"],
            "chord_sum": row["chord_sum"],
            "deficit": row["deficit"],
            "identity_residual": row["identity_residual"],
            "pass": bool(
                abs(row["length"] - 1.4) < 1.0e-12
                and abs(row["chord_sum"] - 1.4) < 1.0e-12
                and row["deficit"] < 1.0e-14
            ),
        }
    )

    # 2. the identity, over every family this probe uses
    worst_absolute = 0.0
    worst_relative = 0.0
    worst_quadrature = 0.0
    worst_ode_gap = 0.0
    worst_length_gap = 0.0
    tested = 0
    rows: list[dict[str, Any]] = []
    families: list[tuple[str, np.ndarray]] = []
    for degree in (6, 9):
        w = witness_roots(degree)
        if w is not None:
            families.append((f"qc_witness_n{degree}", w))
    for degree in range(3, 9):
        for style in STYLES:
            families.append((f"{style}_n{degree}", normalise(draw_roots(rng, degree, style))))
        for epsilon in (1.0e-2, 1.0e-5, 1.0e-8):
            families.append(
                (
                    f"fekete_n{degree}_eps{epsilon:g}",
                    perturbed_ngon(degree, epsilon, 1.0e-3, rng),
                )
            )
    for name, candidate in families:
        packet = measure_config_deficit(
            candidate, tol, quad_nodes=quad_nodes, deficit_ode=True
        )
        if packet is None:
            continue
        for h in packet["hubs"]:
            tested += 1
            worst_absolute = max(worst_absolute, h["identity_residual"])
            worst_relative = max(worst_relative, h["identity_relative"])
            worst_quadrature = max(worst_quadrature, h["quadrature_gap"])
            worst_length_gap = max(worst_length_gap, h["length_instrument_gap"])
            if h["deficit_ode_gap"] is not None:
                worst_ode_gap = max(worst_ode_gap, h["deficit_ode_gap"])
        rows.append(
            {
                "family": name,
                "degree": packet["degree"],
                "radius": packet["radius"],
                "hubs": packet["hub_count"],
                "max_identity_residual": packet["max_identity_residual"],
                "m1_config": packet["m1_config"],
                "m2_config": packet["m2_config"],
            }
        )
    checks.append(
        {
            "check": "M4: L(c) = (d1 + d2) + D(c) with D by independent quadrature",
            "hubs_tested": tested,
            "max_absolute_residual": worst_absolute,
            "max_relative_residual": worst_relative,
            "max_gauss_legendre_k_vs_2k_gap": worst_quadrature,
            "max_deficit_ode_vs_quadrature_gap": worst_ode_gap,
            "max_arclength_ode_vs_quadrature_gap": worst_length_gap,
            "pass": bool(tested > 100 and worst_relative < 1.0e-9),
        }
    )
    return {"checks": checks, "family_rows": rows, "pass": all(c["pass"] for c in checks)}


def perturbation_limit(tol: Tol, quad_nodes: int, degrees: Sequence[int]) -> dict[str, Any]:
    """M5: D -> 0 on z^n - r^n as the splitting perturbation vanishes."""

    rng = np.random.default_rng(5150)
    rows: list[dict[str, Any]] = []
    for degree in degrees:
        for r in (0.9, 0.999):
            series: list[dict[str, Any]] = []
            for delta in (1e-2, 1e-3, 1e-4, 1e-5, 1e-6, 1e-7, 1e-8, 1e-9, 1e-10):
                local = np.random.default_rng(abs(hash((degree, r, delta))) % (2**32))
                candidate = radial_family(degree, r, delta, local)
                packet = measure_config_deficit(
                    candidate, tol, quad_nodes=quad_nodes, deficit_ode=False
                )
                if packet is None:
                    series.append({"delta": delta, "status": "no_clean_simple_hub"})
                    continue
                worst = max(packet["hubs"], key=lambda h: h["deficit"])
                best = packet["best_m1_hub"]
                series.append(
                    {
                        "delta": delta,
                        "hubs": packet["hub_count"],
                        "discards": packet["discards"],
                        "max_deficit": worst["deficit"],
                        "min_deficit": min(h["deficit"] for h in packet["hubs"]),
                        "max_hub_modulus": max(abs(h["hub"]) for h in packet["hubs"]),
                        "min_length": packet["min_length"],
                        "m1_config": packet["m1_config"],
                        "m2_config": packet["m2_config"],
                        "best_m1_chord_sum": best["chord_sum"],
                        "best_m1_deficit": best["deficit"],
                        "identity_residual": packet["max_identity_residual"],
                    }
                )
            rows.append({"degree": degree, "r": r, "series": series})
    _ = rng
    return {"rows": rows}


# --------------------------------------------------------------------------- #
# sweeps
# --------------------------------------------------------------------------- #
def random_sweep(
    trials: int, min_n: int, max_n: int, seed: int, tol: Tol, quad_nodes: int
) -> dict[str, Any]:
    rng = np.random.default_rng(seed)
    hub_rows: list[dict[str, Any]] = []
    config_rows: list[dict[str, Any]] = []
    discards: dict[str, int] = {}
    attempted = 0
    for trial in range(trials):
        degree = int(rng.integers(min_n, max_n + 1))
        style = STYLES[trial % len(STYLES)]
        candidate = normalise(draw_roots(rng, degree, style))
        attempted += 1
        packet = measure_config_deficit(
            candidate, tol, quad_nodes=quad_nodes, deficit_ode=False
        )
        if packet is None:
            discards["config_unusable"] = discards.get("config_unusable", 0) + 1
            continue
        for key, count in packet["discards"].items():
            discards[key] = discards.get(key, 0) + count
        for h in packet["hubs"]:
            hub_rows.append(
                {
                    "degree": degree,
                    "style": style,
                    "radius": packet["radius"],
                    **{
                        k: h[k]
                        for k in (
                            "deficit",
                            "deficit_over_length",
                            "m1",
                            "m2",
                            "chord_sum",
                            "chord_over_2R",
                            "nearest_over_2R",
                            "endpoints_are_nearest_two",
                            "length",
                            "identity_residual",
                            "slack",
                            "is_least_value_hub",
                        )
                        if k in h
                    },
                    "radius_config": packet["radius"],
                }
            )
        config_rows.append(
            {
                "degree": degree,
                "style": style,
                "radius": packet["radius"],
                "hub_count": packet["hub_count"],
                "m1_config": packet["m1_config"],
                "m2_config": packet["m2_config"],
                "min_length": packet["min_length"],
                "max_chord_over_2R": packet["max_chord_over_2R"],
                "max_nearest_over_2R": packet["max_nearest_over_2R"],
                "roots": packet["roots"],
            }
        )
    per_degree: dict[int, dict[str, Any]] = {}
    for degree in range(min_n, max_n + 1):
        rows = [r for r in config_rows if r["degree"] == degree]
        if not rows:
            continue
        worst_m1 = max(rows, key=lambda r: r["m1_config"])
        worst_m2 = max(rows, key=lambda r: r["m2_config"])
        per_degree[degree] = {
            "configs": len(rows),
            "worst_m1": worst_m1["m1_config"],
            "worst_m1_style": worst_m1["style"],
            "worst_m1_radius": worst_m1["radius"],
            "worst_m1_roots": roots_payload(worst_m1["roots"]),
            "worst_m2": worst_m2["m2_config"],
            "worst_m2_style": worst_m2["style"],
            "worst_m2_radius": worst_m2["radius"],
        }
    return {
        "trials": attempted,
        "configs_measured": len(config_rows),
        "hubs_measured": len(hub_rows),
        "discards": discards,
        "m1_hub_quantiles": quantiles([r["m1"] for r in hub_rows]),
        "m2_hub_quantiles": quantiles([r["m2"] for r in hub_rows]),
        "m1_config_quantiles": quantiles([r["m1_config"] for r in config_rows]),
        "m2_config_quantiles": quantiles([r["m2_config"] for r in config_rows]),
        "deficit_quantiles": quantiles([r["deficit"] for r in hub_rows]),
        "deficit_over_length_quantiles": quantiles(
            [r["deficit_over_length"] for r in hub_rows]
        ),
        "chord_over_2R_quantiles": quantiles([r["chord_over_2R"] for r in hub_rows]),
        "nearest_over_2R_quantiles": quantiles([r["nearest_over_2R"] for r in hub_rows]),
        "endpoints_nearest_two_fraction": (
            float(np.mean([r["endpoints_are_nearest_two"] for r in hub_rows]))
            if hub_rows
            else None
        ),
        "chord_over_2R_violations": int(
            sum(1 for r in hub_rows if r["chord_over_2R"] > 1.0)
        ),
        "nearest_over_2R_violations": int(
            sum(1 for r in hub_rows if r["nearest_over_2R"] > 1.0 + 1.0e-12)
        ),
        "m1_at_or_above_one": int(sum(1 for r in config_rows if r["m1_config"] >= 1.0)),
        "m2_at_or_above_one": int(sum(1 for r in config_rows if r["m2_config"] >= 1.0)),
        "hubs_with_m1_at_or_above_one": int(sum(1 for r in hub_rows if r["m1"] >= 1.0)),
        "hubs_with_chord_sum_at_or_above_two": int(
            sum(1 for r in hub_rows if r["chord_sum"] >= 2.0)
        ),
        "hubs_with_m2_at_or_above_one": int(sum(1 for r in hub_rows if r["m2"] >= 1.0)),
        "worst_chord_over_2R_config": (
            roots_payload(
                max(config_rows, key=lambda r: r["max_chord_over_2R"])["roots"]
            )
            if config_rows
            else None
        ),
        "least_value_hub_rows": len([r for r in hub_rows if r.get("is_least_value_hub")]),
        "least_value_hub_endpoints_nearest_two_fraction": (
            float(
                np.mean(
                    [
                        r["endpoints_are_nearest_two"]
                        for r in hub_rows
                        if r.get("is_least_value_hub")
                    ]
                )
            )
            if any(r.get("is_least_value_hub") for r in hub_rows)
            else None
        ),
        "least_value_hub_chord_over_2R_quantiles": quantiles(
            [r["chord_over_2R"] for r in hub_rows if r.get("is_least_value_hub")]
        ),
        "least_value_hub_m1_quantiles": quantiles(
            [r["m1"] for r in hub_rows if r.get("is_least_value_hub")]
        ),
        "least_value_hub_m2_quantiles": quantiles(
            [r["m2"] for r in hub_rows if r.get("is_least_value_hub")]
        ),
        "worst_chord_over_2R_value": (
            max(r["max_chord_over_2R"] for r in config_rows) if config_rows else None
        ),
        "per_degree": per_degree,
    }


def fekete_grid(
    degrees: Sequence[int],
    trials: int,
    seed: int,
    tol: Tol,
    quad_nodes: int,
) -> dict[str, Any]:
    """The hard regime: perturbed regular n-gons at radius r = 1 - eps."""

    epsilons = (1e-2, 1e-3, 1e-4, 1e-5, 1e-6, 1e-7, 1e-8, 1e-9)
    perturbations = (0.0, 1e-6, 1e-5, 1e-4, 1e-3, 1e-2)
    rows: list[dict[str, Any]] = []
    for degree in degrees:
        for epsilon in epsilons:
            for perturbation in perturbations:
                best: dict[str, Any] | None = None
                worst_m1 = -INF
                usable = 0
                for trial in range(trials if perturbation > 0 else 1):
                    rng = np.random.default_rng(
                        abs(hash((degree, epsilon, perturbation, trial))) % (2**32)
                    )
                    candidate = perturbed_ngon(degree, epsilon, perturbation, rng)
                    packet = measure_config_deficit(
                        candidate, tol, quad_nodes=quad_nodes, deficit_ode=False
                    )
                    if packet is None:
                        continue
                    usable += 1
                    if packet["m1_config"] > worst_m1:
                        worst_m1 = packet["m1_config"]
                        best = packet
                if best is None:
                    rows.append(
                        {
                            "degree": degree,
                            "epsilon": epsilon,
                            "perturbation": perturbation,
                            "status": "no_clean_simple_hub",
                        }
                    )
                    continue
                hub = best["best_m1_hub"]
                rows.append(
                    {
                        "degree": degree,
                        "epsilon": epsilon,
                        "perturbation": perturbation,
                        "usable_trials": usable,
                        "radius": best["radius"],
                        "hub_count": best["hub_count"],
                        "m1_config": best["m1_config"],
                        "m2_config": best["m2_config"],
                        "min_length": best["min_length"],
                        "best_m1_deficit": hub["deficit"],
                        "best_m1_slack": hub["slack"],
                        "best_m1_chord_sum": hub["chord_sum"],
                        "best_m1_chord_over_2R": hub["chord_over_2R"],
                        "best_m1_alpha": hub["alpha_max"],
                        "max_chord_over_2R": best["max_chord_over_2R"],
                        "identity_residual": best["max_identity_residual"],
                        "roots": roots_payload(best["roots"]),
                    }
                )
    trend: list[dict[str, Any]] = []
    for degree in degrees:
        for perturbation in perturbations:
            series = [
                (r["epsilon"], r["m1_config"])
                for r in rows
                if r["degree"] == degree
                and r.get("perturbation") == perturbation
                and "m1_config" in r
            ]
            series.sort(key=lambda item: -item[0])  # eps descending: eps -> 0
            if len(series) < 3:
                continue
            values = [v for _, v in series]
            increasing = all(
                values[i + 1] >= values[i] - 1.0e-12 for i in range(len(values) - 1)
            )
            trend.append(
                {
                    "degree": degree,
                    "perturbation": perturbation,
                    "epsilons_descending": [e for e, _ in series],
                    "m1_values": values,
                    "monotone_increasing_as_eps_to_zero": bool(increasing),
                    "first": values[0],
                    "last": values[-1],
                    "max": max(values),
                }
            )
    return {"rows": rows, "eps_trend": trend}


def witness_table(tol: Tol, quad_nodes: int) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for degree in (6, 9):
        roots = witness_roots(degree)
        if roots is None:
            continue
        packet = measure_config_deficit(
            roots, tol, quad_nodes=quad_nodes, deficit_ode=True
        )
        if packet is None:
            rows.append({"degree": degree, "status": "tracker_refused"})
            continue
        rows.append(
            {
                "degree": degree,
                "radius": packet["radius"],
                "hub_count": packet["hub_count"],
                "discards": packet["discards"],
                "m1_config": packet["m1_config"],
                "m2_config": packet["m2_config"],
                "min_length": packet["min_length"],
                "max_identity_residual": packet["max_identity_residual"],
                "hubs": [hub_report(h) for h in packet["hubs"]],
            }
        )
    return {"rows": rows}


# --------------------------------------------------------------------------- #
# adversarial maximisation of M1
# --------------------------------------------------------------------------- #
def objective(roots: np.ndarray, tol: Tol, quad_nodes: int, key: str) -> float:
    packet = measure_config_deficit(roots, tol, quad_nodes=quad_nodes, deficit_ode=False)
    if packet is None:
        return -INF
    value = packet[key]
    return value if math.isfinite(value) else 1.0e6


def hill_climb(
    roots: np.ndarray,
    tol: Tol,
    quad_nodes: int,
    key: str,
    steps: int,
    rng: np.random.Generator,
) -> tuple[float, np.ndarray]:
    degree = roots.size
    value = objective(roots, tol, quad_nodes, key)
    scale = 0.25
    for _ in range(steps):
        mode = rng.random()
        if mode < 0.55:
            candidate = roots + scale * (
                rng.normal(size=degree) + 1j * rng.normal(size=degree)
            )
        elif mode < 0.72:
            pick = int(rng.integers(0, degree))
            candidate = roots.copy()
            candidate[pick] += 3.0 * scale * (rng.normal() + 1j * rng.normal())
        elif mode < 0.84:
            candidate = roots * (1.0 + scale * rng.normal())
        elif mode < 0.94:
            # radial squeeze toward the boundary: the near-Fekete direction
            modulus = np.abs(roots)
            target = 1.0 - 10.0 ** rng.uniform(-9.0, -2.0)
            candidate = roots * (
                1.0 + scale * (target / np.maximum(modulus, 1e-12) - 1.0)
            )
        else:
            pick = int(rng.integers(0, degree))
            other = int(rng.integers(0, degree))
            candidate = roots.copy()
            candidate[pick] = roots[other] + scale * (rng.normal() + 1j * rng.normal())
        candidate = normalise(clamp(candidate))
        candidate_value = objective(candidate, tol, quad_nodes, key)
        if candidate_value > value:
            roots, value = candidate, candidate_value
            scale = min(0.25, scale * 1.35)
        else:
            scale *= 0.94
        if scale < 3.0e-6:
            break
    return value, roots


def attack(
    degrees: Sequence[int],
    restarts: int,
    steps: int,
    seed: int,
    tol: Tol,
    verify_tol: Tol,
    quad_nodes: int,
    key: str,
    verbose: bool,
) -> dict[str, Any]:
    rng = np.random.default_rng(seed)
    out: list[dict[str, Any]] = []
    for degree in degrees:
        basins: list[np.ndarray] = [
            normalise(CAP * np.exp(2j * np.pi * np.arange(degree) / degree)),
            normalise(0.6 * np.exp(2j * np.pi * np.arange(degree) / degree)),
        ]
        for epsilon in (1e-3, 1e-6, 1e-9):
            for perturbation in (1e-4, 1e-2):
                basins.append(
                    perturbed_ngon(
                        degree, epsilon, perturbation, np.random.default_rng(degree * 97)
                    )
                )
        w = witness_roots(degree)
        if w is not None:
            basins.append(normalise(clamp(w)))
        best_value, best_roots = -INF, None
        per_restart: list[float] = []
        for trial in range(max(restarts, len(basins))):
            if trial < len(basins):
                seed_roots = basins[trial].copy()
            elif trial % 4 == 3 and best_roots is not None:
                seed_roots = normalise(
                    clamp(
                        best_roots
                        + 0.02
                        * (rng.normal(size=degree) + 1j * rng.normal(size=degree))
                    )
                )
            else:
                seed_roots = normalise(
                    draw_roots(rng, degree, STYLES[trial % len(STYLES)])
                )
            value, found = hill_climb(seed_roots, tol, quad_nodes, key, steps, rng)
            per_restart.append(value)
            if value > best_value:
                best_value, best_roots = value, found
                if verbose:
                    print(
                        f"    [{key} n={degree}] restart {trial}: {best_value:.9f}",
                        flush=True,
                    )
        row: dict[str, Any] = {
            "degree": degree,
            "objective": key,
            "search_best_fast": best_value,
            "per_restart": [v for v in per_restart if math.isfinite(v)],
        }
        if best_roots is not None:
            packet = measure_config_deficit(
                best_roots, verify_tol, quad_nodes=quad_nodes, deficit_ode=True
            )
            row["roots"] = roots_payload(best_roots)
            if packet is not None:
                row["verified"] = {
                    "tolerance": verify_tol.name,
                    "radius": packet["radius"],
                    "hub_count": packet["hub_count"],
                    "discards": packet["discards"],
                    "m1_config": packet["m1_config"],
                    "m2_config": packet["m2_config"],
                    "min_length": packet["min_length"],
                    "max_identity_residual": packet["max_identity_residual"],
                    "max_chord_over_2R": packet["max_chord_over_2R"],
                    "best_m1_hub": hub_report(packet["best_m1_hub"]),
                }
            else:
                row["verified"] = {"status": "verification_tolerance_refused"}
        out.append(row)
    return {"rows": out}


# --------------------------------------------------------------------------- #
# near-Fekete shell attack: search in (eps, a_k, t_k), not in free root positions
# --------------------------------------------------------------------------- #
def shell_roots(vector: np.ndarray, degree: int) -> np.ndarray:
    """``z_k = (1 + a_k) exp(i(2 pi k / n + t_k))`` rescaled to circumradius 1 - eps."""

    log_eps = float(np.clip(vector[0], -12.0, -0.30103))
    epsilon = 10.0**log_eps
    amplitude = vector[1 : 1 + degree]
    phase = vector[1 + degree : 1 + 2 * degree]
    base = (1.0 + amplitude) * np.exp(
        1j * (2.0 * np.pi * np.arange(degree) / degree + phase)
    )
    centre, radius = circumcircle(base)
    if not np.isfinite(radius) or radius <= 1.0e-12:
        return base
    return (base - centre) * ((1.0 - epsilon) / radius)


def shell_attack(
    degrees: Sequence[int],
    restarts: int,
    steps: int,
    seed: int,
    tol: Tol,
    verify_tol: Tol,
    quad_nodes: int,
    key: str,
    verbose: bool,
) -> dict[str, Any]:
    rng = np.random.default_rng(seed)
    out: list[dict[str, Any]] = []
    for degree in degrees:
        seeds: list[np.ndarray] = []
        for log_eps in (-2.0, -4.0, -6.0, -8.0, -9.0):
            for scale in (0.0, 1.0e-6, 1.0e-4, 1.0e-3, 1.0e-2):
                vector = np.zeros(1 + 2 * degree)
                vector[0] = log_eps
                if scale > 0.0:
                    vector[1:] = scale * rng.normal(size=2 * degree)
                seeds.append(vector)
        best_value, best_vector = -INF, None
        per_restart: list[float] = []
        for trial in range(max(restarts, len(seeds))):
            if trial < len(seeds):
                vector = seeds[trial].copy()
            elif best_vector is not None and trial % 3 == 2:
                vector = best_vector.copy()
                vector[1:] += 10.0 ** rng.uniform(-6.0, -3.0) * rng.normal(
                    size=2 * degree
                )
            else:
                vector = np.zeros(1 + 2 * degree)
                vector[0] = rng.uniform(-9.5, -2.0)
                vector[1:] = 10.0 ** rng.uniform(-6.0, -2.0) * rng.normal(
                    size=2 * degree
                )
            value = objective(shell_roots(vector, degree), tol, quad_nodes, key)
            scale = 1.0e-3
            eps_scale = 0.6
            for _ in range(steps):
                candidate = vector.copy()
                draw = rng.random()
                if draw < 0.72:
                    candidate[1:] += scale * rng.normal(size=2 * degree)
                elif draw < 0.86:
                    candidate[0] += eps_scale * rng.normal()
                else:
                    candidate[1:] += scale * rng.normal(size=2 * degree)
                    candidate[0] += eps_scale * rng.normal()
                candidate[0] = float(np.clip(candidate[0], -12.0, -0.30103))
                candidate_value = objective(
                    shell_roots(candidate, degree), tol, quad_nodes, key
                )
                if candidate_value > value:
                    vector, value = candidate, candidate_value
                    scale = min(0.05, scale * 1.4)
                    eps_scale = min(1.0, eps_scale * 1.2)
                else:
                    scale *= 0.93
                    eps_scale *= 0.95
                if scale < 1.0e-9:
                    break
            per_restart.append(value)
            if value > best_value:
                best_value, best_vector = value, vector
                if verbose:
                    print(
                        f"    [shell {key} n={degree}] restart {trial}: "
                        f"{best_value:.9f} at eps=1e{vector[0]:.3f}",
                        flush=True,
                    )
        row: dict[str, Any] = {
            "degree": degree,
            "objective": key,
            "search_best_fast": best_value,
            "per_restart": [v for v in per_restart if math.isfinite(v)],
        }
        if best_vector is not None:
            roots = shell_roots(best_vector, degree)
            row["log10_epsilon"] = float(best_vector[0])
            row["perturbation_rms"] = float(np.sqrt(np.mean(best_vector[1:] ** 2)))
            row["roots"] = roots_payload(roots)
            packet = measure_config_deficit(
                roots, verify_tol, quad_nodes=quad_nodes, deficit_ode=True
            )
            if packet is not None:
                row["verified"] = {
                    "tolerance": verify_tol.name,
                    "radius": packet["radius"],
                    "hub_count": packet["hub_count"],
                    "discards": packet["discards"],
                    "m1_config": packet["m1_config"],
                    "m2_config": packet["m2_config"],
                    "min_length": packet["min_length"],
                    "max_identity_residual": packet["max_identity_residual"],
                    "max_chord_over_2R": packet["max_chord_over_2R"],
                    "best_m1_hub": hub_report(packet["best_m1_hub"]),
                }
            else:
                row["verified"] = {"status": "verification_tolerance_refused"}
        out.append(row)
    return {"rows": out}


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #
TOLERANCES = {"fast": FAST, "tight": TIGHT, "ultra": ULTRA}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--modes", default="gate")
    parser.add_argument("--tolerance", default="tight", choices=sorted(TOLERANCES))
    parser.add_argument("--verify-tolerance", default="tight", choices=sorted(TOLERANCES))
    parser.add_argument("--quad-nodes", type=int, default=12)
    parser.add_argument("--trials", type=int, default=120)
    parser.add_argument("--min-degree", type=int, default=3)
    parser.add_argument("--max-degree", type=int, default=8)
    parser.add_argument("--degrees", default="")
    parser.add_argument("--restarts", type=int, default=8)
    parser.add_argument("--steps", type=int, default=110)
    parser.add_argument(
        "--objective",
        default="m1_config",
        choices=("m1_config", "m2_config", "minlen_config"),
    )
    parser.add_argument("--seed", type=int, default=20261041)
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()

    tol = TOLERANCES[args.tolerance]
    verify = TOLERANCES[args.verify_tolerance]
    modes = [m.strip() for m in args.modes.split(",") if m.strip()]
    if args.degrees:
        degrees = [int(d) for d in args.degrees.split(",")]
    else:
        degrees = list(range(args.min_degree, args.max_degree + 1))

    payload: dict[str, Any] = {
        "tolerance": args.tolerance,
        "quad_nodes": args.quad_nodes,
        "modes": modes,
    }
    started = time.time()
    if "gate" in modes or "all" in modes:
        payload["gate"] = gate(tol, args.quad_nodes)
    if "family" in modes or "all" in modes:
        payload["perturbation_limit"] = perturbation_limit(tol, args.quad_nodes, degrees)
    if "linear" in modes or "all" in modes:
        payload["linear_family"] = linear_family_table(degrees, tol, args.quad_nodes)
    if "extremal_limit" in modes or "all" in modes:
        payload["extremal_limit"] = extremal_limit_table(
            degrees, tol, args.quad_nodes
        )
    if "witness" in modes or "all" in modes:
        payload["witness"] = witness_table(tol, args.quad_nodes)
    if "sweep" in modes or "all" in modes:
        payload["sweep"] = random_sweep(
            args.trials, args.min_degree, args.max_degree, args.seed, tol, args.quad_nodes
        )
    if "fekete" in modes or "all" in modes:
        payload["fekete"] = fekete_grid(
            degrees, max(1, args.trials), args.seed, tol, args.quad_nodes
        )
    if "shell" in modes or "all" in modes:
        payload["shell_attack"] = shell_attack(
            degrees,
            args.restarts,
            args.steps,
            args.seed,
            tol,
            verify,
            args.quad_nodes,
            args.objective,
            args.verbose,
        )
    if "attack" in modes or "all" in modes:
        payload["attack"] = attack(
            degrees,
            args.restarts,
            args.steps,
            args.seed,
            tol,
            verify,
            args.quad_nodes,
            args.objective,
            args.verbose,
        )
    payload["elapsed_seconds"] = round(time.time() - started, 2)
    print(json.dumps(payload, indent=2, default=str))
    if "gate" in payload:
        return 0 if payload["gate"]["pass"] else 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
