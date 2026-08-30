#!/usr/bin/env python3
"""Erdős #1041: search the descent-path objectives in near-Fekete coordinates.

Why the coordinates are the whole point
---------------------------------------
``prod_k |f(c_k)| = disc / n^n = prod_{i<j} |z_i - z_j|^2 / n^n <= 1`` by Fekete,
with equality exactly at the ``n``-th roots of unity.  So any configuration whose
*least* critical value ``T* = min_k |f(c_k)|`` is close to 1 has **every** critical
value close to 1, which forces the discriminant to its Fekete maximum, which forces
the roots to be a tiny perturbation of a regular ``n``-gon at radius just under 1.

The two exact witnesses stored in
``check_erdos1041_straight_spoke_hub_criterion.QC_REFUTATION_WITNESSES`` are exactly
that, and this probe measures it rather than asserting it:

    degree 6   every root modulus 1 - 1.5e-7, angular deviation from the regular
               hexagon at most 9.46e-4, disc/n^n = 0.999992181741
    degree 9   eight roots at 1 - 1.5e-7 and one at 1 - 5.36e-6, angular deviation
               at most 2.25e-4, disc/n^n = 0.999947120693

Every adversarial search recorded in ``CriticalBudgetLab.md`` runs in *bulk* root
coordinates: an isotropic Gaussian walk of initial scale 0.3 with a clamp to
``|z| <= 1 - 1e-9``.  One step of that walk destroys a ``1e-7``-thin angular
structure, so the near-Fekete corner is not merely under-sampled, it is unreachable.
This probe reparameterises instead:

    z_k = (1 - eps_k) * exp( i * (2*pi*k/n + dtheta_k) ),   eps_k = eps * exp(a_k)

and searches over ``(log eps, a, dtheta)``.  ``|z_k| < 1`` holds by construction, so
no clamp is needed and the search never has to fight its own feasible set.

Three objectives, and a hard ordering between them
--------------------------------------------------
OBJ-3 (gate)  at ``c*``, the admissible critical point of least critical value, the
              worst of the two straight spokes to the two *nearest* roots, measured
              as ``max |f|`` on the segment.  This is claim 3 of the retracted
              first-merge-hub theorem.  It is *known* to exceed 1 at the two stored
              witnesses (1.0000093332434161438 and 1.0000103851845920825), so a
              search in the right coordinates must rediscover values above 1.  If it
              does not, the search or the precision is broken and nothing else this
              file reports means anything.  It runs first and it gates the rest.

OBJ-1 (MIN)   ``max over configurations of min_c L_c``, ``L_c`` the combined arc
              length of the two descending branches at an admissible simple hub.
              ``min_c L_c < 2`` would settle #1041, since the descent path is
              contained by construction.

OBJ-2 (AVG)   ``max of sum_c L_c / (2 m)``, ``m`` the admissible hub count.

Second gate: the extremal family
--------------------------------
For ``f = z^n - r^n`` the only critical point is 0 with multiplicity ``n-1``, and the
constant-argument descent set from it is exactly the ``n`` radii ``[0, r*omega^k]``.
Resolving the degenerate hub into ``n-1`` simple hubs by an infinitesimal
perturbation gives two radial arms per hub, hence

    min_c L_c = 2r    and    normalized aggregate = r      at *every* degree n.

That is a closed-form statement, not a search result, so it is a correctness gate on
the tracker: a tracker that does not return ``2r`` and ``r`` on that family is wrong.
It also contradicts ``CriticalBudgetLab.md``'s own reading of its bulk table, which
records 1.852321 / 1.634226 / 1.592300 for MIN at n = 4, 5, 6 and concludes that the
ceilings "fall monotonically with degree".  They cannot: the extremal family sits at
``2r`` at every degree.  ``mode=extremal`` measures this directly.

Instruments, and why there are two of them
------------------------------------------
The search runs on the corpus tracker ``inverse_ray_aggregate_score`` from
``search_counterexample.py`` (owned by a concurrent session; imported, never written)
so the numbers are directly comparable to the recorded bulk values.  That tracker is
float64: it locates hubs with ``np.roots`` on the derivative, and near-Fekete
configurations have ``n-1`` critical points clustered at scale ``delta^(1/(n-1))``
around the origin, where float64 root-finding loses roughly ``(n-2)/(n-1)`` of its
digits.  So every reported extremum is re-measured by an independent high-precision
tracker in this file:

  * hubs from ``mp.polyroots`` on the exact derivative at ``--digits`` places;
  * branch start from the analytic expansion ``z ~ c +- u sqrt(-2 f(c) / f''(c))``,
    which fixes branch identity by construction instead of by sorting preimages --
    the sorting step is the mechanism behind all four false "counterexamples"
    (2.0068, 2.132146, 2.116316, 2.013509) recorded in the lab;
  * continuation by Newton on ``f(z) = (1-u^2) f(c)`` along composite Gauss-Legendre
    nodes, which are strictly interior, so neither endpoint is ever evaluated;
  * arc length ``L = int_0^1 2u|f(c)| / |f'(z(u))| du`` by the same quadrature,
    reported at two panel counts so the quadrature error is visible;
  * a geometric tail continuation to ``u = 1`` followed by a Newton solve of
    ``f(z) = 0``, so the recorded endpoint error is the distance to the root the
    branch actually reached, not to the nearest root of a jumped-to sheet.

Method constraint inherited from the lab
----------------------------------------
``CriticalBudgetLab.md`` records six occasions where a supremum pinned just below a
threshold was read as survival and was later false.  Every extremum below is
therefore labelled ``pinned`` or ``crossing``, and a pin is reported as evidence of
one basin unless a known extremal family explains it.

Writes only its own receipt.  Read-only against every other file.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
import time
from pathlib import Path
from typing import Any, Iterable, Sequence

import mpmath as mp
import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(REPO_ROOT))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from system.lib.formal_math_lemniscate import (  # noqa: E402
    coefficients_from_roots,
    critical_table,
    segment_max_modulus,
)
from formal_math.erdos257_period_noncollapse.ErdosProblems.Erdos1041.scripts.search_counterexample import (  # noqa: E402
    inverse_ray_aggregate_score,
)

SOURCE_REF = (
    "research_corpus/Erdos1041/scripts/"
    "check_erdos1041_near_fekete_search.py"
)
ANALYSIS_REF = (
    "research_corpus/Erdos1041/CriticalBudgetLab.md"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "source-provenance://private-authoring-project/receipts/"
    "erdos1041_near_fekete_search_receipt.json"
)

#: Recorded bulk-coordinate suprema, ``CriticalBudgetLab.md`` section
#: "Maximising MIN and AVG directly".  The comparison target of this probe.
BULK_MIN: dict[int, float] = {3: 1.999999986, 4: 1.852321, 5: 1.634226, 6: 1.592300}
BULK_AVG: dict[int, float] = {
    3: 0.999999994,
    4: 0.904177,
    5: 0.822727,
    6: 0.746591,
    7: 0.680409,
}

#: Recorded OBJ-3 excesses at the two stored exact witnesses.
WITNESS_SPOKE_MAX: dict[int, float] = {
    6: 1.0000093332434161438,
    9: 1.0000103851845920825,
}

#: eps ladder and perturbation ladder named by the coordinate mandate.
EPS_GRID: tuple[float, ...] = (1e-9, 1e-8, 1e-7, 1e-6, 1e-5, 1e-4, 1e-3, 1e-2)
PERT_GRID: tuple[float, ...] = (0.0, 1e-7, 1e-6, 1e-5, 1e-4, 1e-3, 1e-2)

LOG_EPS_FLOOR = math.log(1e-15)
LOG_EPS_CEIL = math.log(0.5)


# ---------------------------------------------------------------------------
# near-Fekete coordinates
# ---------------------------------------------------------------------------


def near_fekete_roots(n: int, log_eps: np.ndarray, dtheta: np.ndarray) -> np.ndarray:
    """``z_k = (1 - exp(log_eps_k)) * exp(i(2 pi k / n + dtheta_k))``.

    ``|z_k| < 1`` strictly for every finite ``log_eps_k``, so the feasible set is
    the whole parameter space and no clamp is ever applied.
    """

    clipped = np.clip(log_eps, LOG_EPS_FLOOR, LOG_EPS_CEIL)
    radii = 1.0 - np.exp(clipped)
    angles = 2.0 * np.pi * np.arange(n) / n + dtheta
    return radii * np.exp(1j * angles)


def fekete_ratio(roots: np.ndarray) -> float:
    """``prod_{i<j} |z_i - z_j|^2 / n^n`` -- the discriminant against its ceiling."""

    n = len(roots)
    total = 0.0
    for i in range(n):
        for j in range(i + 1, n):
            total += 2.0 * math.log(abs(roots[i] - roots[j]))
    return float(math.exp(total - n * math.log(n)))


def ngon_deviation(roots: np.ndarray) -> dict[str, float]:
    """How far the configuration is from *some* regular n-gon, after best rotation."""

    n = len(roots)
    order = np.argsort(np.angle(roots))
    ordered = roots[order]
    # best common rotation: align the mean argument residual to zero
    base = 2.0 * np.pi * np.arange(n) / n
    residual = np.angle(np.exp(1j * (np.angle(ordered) - base)))
    shift = math.atan2(float(np.sin(residual).sum()), float(np.cos(residual).sum()))
    dtheta = np.angle(np.exp(1j * (residual - shift)))
    radius = float(np.abs(ordered).mean())
    target = radius * np.exp(1j * (base + shift))
    return {
        "mean_radius": radius,
        "max_root_modulus": float(np.abs(roots).max()),
        "max_angular_deviation": float(np.abs(dtheta).max()),
        "max_radial_deviation": float(np.abs(np.abs(ordered) - radius).max()),
        "max_deviation_from_regular_ngon": float(np.abs(ordered - target).max()),
        "fekete_ratio": fekete_ratio(roots),
    }


def hex_literals(roots: np.ndarray) -> list[list[str]]:
    """IEEE-754 hex, the corpus convention: 1e-5 margins do not survive decimals."""

    return [[float(z.real).hex(), float(z.imag).hex()] for z in roots]


def roots_from_hex(literals: Iterable[Sequence[str]]) -> np.ndarray:
    return np.asarray(
        [complex(float.fromhex(a), float.fromhex(b)) for a, b in literals],
        dtype=np.complex128,
    )


# ---------------------------------------------------------------------------
# OBJ-3: the straight spokes at c*
# ---------------------------------------------------------------------------


def spoke_objective(roots: np.ndarray) -> dict[str, Any] | None:
    """Worst ``max |f|`` over the two straight spokes from ``c*`` to nearest roots.

    ``c*`` is the admissible critical point of least nonzero critical value -- the
    selector of the retracted conditional theorem.  Segment maxima are *located*
    (real roots of ``d|f|^2/dt``), never sampled, so a narrow excursion cannot be
    missed.
    """

    coefficients = coefficients_from_roots(roots)
    rows = [
        row
        for row in critical_table(roots)
        if row["admissible"] and row["critical_value_modulus"] > 1.0e-13
    ]
    if not rows:
        return None
    hub = min(rows, key=lambda row: row["critical_value_modulus"])
    centre = complex(hub["critical_point"])
    distances = np.abs(roots - centre)
    nearest = np.argsort(distances)[:2]
    spokes = []
    for index in nearest:
        maximum, parameter = segment_max_modulus(coefficients, centre, complex(roots[index]))
        spokes.append(
            {
                "root_index": int(index),
                "length": float(distances[index]),
                "segment_max_modulus": float(maximum),
                "at_parameter": float(parameter),
            }
        )
    return {
        "critical_point": [float(centre.real), float(centre.imag)],
        "critical_value_modulus": float(hub["critical_value_modulus"]),
        "nearest_pair_budget": float(distances[nearest].sum()),
        "spokes": spokes,
        "worst_segment_max_modulus": float(max(s["segment_max_modulus"] for s in spokes)),
    }


def all_spoke_containment(roots: np.ndarray) -> dict[str, Any] | None:
    """Every spoke from ``c*``, not just the two nearest.

    OBJ-3 as mandated asks only about the two *nearest* roots, which is claim 3 of
    the retracted theorem.  ``StraightSpokeHubCriterionLab.md`` makes the stronger
    statement that ``c*`` carries at most one open-contained spoke *at all*.  The two
    are different, and a crossing of the first does not by itself establish the
    second, so both are reported.
    """

    coefficients = coefficients_from_roots(roots)
    rows = [
        row
        for row in critical_table(roots)
        if row["admissible"] and row["critical_value_modulus"] > 1.0e-13
    ]
    if not rows:
        return None
    hub = min(rows, key=lambda row: row["critical_value_modulus"])
    centre = complex(hub["critical_point"])
    contained, maxima = [], []
    for index, root in enumerate(roots):
        maximum, _ = segment_max_modulus(coefficients, centre, complex(root))
        maxima.append(float(maximum))
        if maximum <= 1.0 * (1.0 + 1.0e-13):
            contained.append(index)
    return {
        "open_contained_root_indices": contained,
        "open_contained_count": len(contained),
        "at_most_one_open_contained_spoke": len(contained) < 2,
        "spoke_maxima": maxima,
    }


def spoke_score(roots: np.ndarray) -> float:
    detail = spoke_objective(roots)
    return -math.inf if detail is None else detail["worst_segment_max_modulus"]


# ---------------------------------------------------------------------------
# OBJ-1 / OBJ-2: the corpus descent tracker, reused verbatim
# ---------------------------------------------------------------------------


class TrackerCounters:
    """Discard bookkeeping, so the mistrack rate is reported rather than hidden."""

    def __init__(self) -> None:
        self.evaluations = 0
        self.exceptions = 0
        self.no_admissible_hub = 0

    def as_dict(self) -> dict[str, Any]:
        discarded = self.exceptions + self.no_admissible_hub
        return {
            "objective_evaluations": self.evaluations,
            "tracker_exceptions": self.exceptions,
            "no_admissible_hub": self.no_admissible_hub,
            "discarded": discarded,
            "discard_rate": (discarded / self.evaluations) if self.evaluations else 0.0,
        }


def descent_detail(
    roots: np.ndarray, flow_max_step: float, counters: TrackerCounters | None = None
) -> dict[str, Any] | None:
    if counters is not None:
        counters.evaluations += 1
    try:
        average, detail = inverse_ray_aggregate_score(roots, flow_max_step)
    except Exception:  # noqa: BLE001 - a failed continuation is data, not a crash
        if counters is not None:
            counters.exceptions += 1
        return None
    if int(detail.get("admissible_simple_critical_hub_count", 0)) == 0:
        if counters is not None:
            counters.no_admissible_hub += 1
        return None
    return {
        "normalized_average": float(average),
        "min_edge": float(detail["minimum_edge_length"]),
        "max_edge": float(detail["maximum_edge_length"]),
        "total_length": float(detail["total_inverse_ray_edge_length"]),
        "hubs": int(detail["admissible_simple_critical_hub_count"]),
    }


def descent_score(
    roots: np.ndarray, mode: str, flow_max_step: float, counters: TrackerCounters | None
) -> float:
    detail = descent_detail(roots, flow_max_step, counters)
    if detail is None:
        return -math.inf
    return detail["min_edge"] if mode == "min_edge" else detail["normalized_average"]


# ---------------------------------------------------------------------------
# independent high-precision tracker
# ---------------------------------------------------------------------------


def _mp_value(roots: list[mp.mpc], z: mp.mpc) -> mp.mpc:
    out = mp.mpc(1)
    for root in roots:
        out *= z - root
    return out


def _mp_derivative(roots: list[mp.mpc], z: mp.mpc) -> mp.mpc:
    total = mp.mpc(0)
    for skipped in range(len(roots)):
        term = mp.mpc(1)
        for index, root in enumerate(roots):
            if index != skipped:
                term *= z - root
        total += term
    return total


def _mp_second_derivative(roots: list[mp.mpc], z: mp.mpc) -> mp.mpc:
    total = mp.mpc(0)
    n = len(roots)
    for a in range(n):
        for b in range(n):
            if a == b:
                continue
            term = mp.mpc(1)
            for index, root in enumerate(roots):
                if index not in (a, b):
                    term *= z - root
            total += term
    return total


def _mp_critical_points(roots: list[mp.mpc]) -> list[mp.mpc]:
    """Roots of ``f'`` from the exact derivative coefficients at working precision."""

    coefficients = [mp.mpc(1)]
    for root in roots:
        nxt = [mp.mpc(0)] * (len(coefficients) + 1)
        for index, value in enumerate(coefficients):
            nxt[index] += value
            nxt[index + 1] -= value * root
        coefficients = nxt
    degree = len(coefficients) - 1
    derivative = [coefficients[k] * (degree - k) for k in range(degree)]
    if len(derivative) < 2:
        return []
    return list(mp.polyroots(derivative, maxsteps=400, extraprec=400))


def _gauss_legendre(panels: int, order: int) -> tuple[list[mp.mpf], list[mp.mpf]]:
    """Composite Gauss-Legendre on ``[0, 1]``.  Nodes are strictly interior."""

    base, weights = np.polynomial.legendre.leggauss(order)
    nodes: list[mp.mpf] = []
    scaled: list[mp.mpf] = []
    width = mp.mpf(1) / panels
    for panel in range(panels):
        left = width * panel
        for point, weight in zip(base, weights):
            nodes.append(left + width * (mp.mpf(float(point)) + 1) / 2)
            scaled.append(width * mp.mpf(float(weight)) / 2)
    order_index = sorted(range(len(nodes)), key=lambda k: nodes[k])
    return [nodes[k] for k in order_index], [scaled[k] for k in order_index]


#: Cap on the analytic head ``u_head``.  The head is the only piece of the branch
#: not covered by the graded quadrature, so it is kept small in absolute terms as
#: well as small relative to the hub cluster.
RAMP_JOIN = "1e-8"
#: Continuation resolution on the geometric ramp, points per decade of ``u``.
RAMP_PER_DECADE = 16


def _mp_newton(
    roots: list[mp.mpc], target: mp.mpc, guess: mp.mpc, tolerance: mp.mpf
) -> tuple[mp.mpc, mp.mpf, int]:
    z = guess
    for iteration in range(60):
        value = _mp_value(roots, z) - target
        if abs(value) <= tolerance:
            return z, abs(value), iteration
        derivative = _mp_derivative(roots, z)
        if derivative == 0:
            break
        z -= value / derivative
    return z, abs(_mp_value(roots, z) - target), 60


def mp_branch_pair(
    roots: list[mp.mpc],
    hub: mp.mpc,
    others: Sequence[mp.mpc],
    *,
    panels: int,
    order: int,
    mistrack_ratio: float = 5.0,
) -> dict[str, Any] | None:
    """Both descending branches at ``hub``, by residual-gated Newton continuation.

    Branch identity is fixed analytically at the start: with ``v = f(c)``,
    ``f(z) - v = (1/2) f''(c)(z-c)^2 + ...`` and ``f(z(u)) = (1-u^2) v`` give
    ``z(u) = c +- u sqrt(-2v/f''(c)) + O(u^2)``.  The two signs *are* the two
    branches.  No preimage sorting is used anywhere -- sorting the level-set
    preimages by distance to the hub is the step behind all four recorded false
    counterexamples, and it is exactly wrong near a Fekete configuration, where
    ``n-1`` critical points cluster and the two preimages nearest ``c`` routinely
    belong to a neighbouring hub.

    The asymptotic start is only used where it is provably valid: at
    ``u_head = min(0.02 d / |s|, 1e-8)``, ``d`` the distance to the nearest other
    critical point, so the quadratic term dominates by a factor of 50.

    Arc length is assembled in three pieces because the integrand
    ``|z'(u)| = 2u|f(c)|/|f'(z(u))|`` is smooth only at a hub that is not close to
    degenerate.  At a near-Fekete configuration the hubs sit in a cluster of scale
    ``delta^(1/(n-1))`` and ``|z'| ~ u^(2/n - 1)``, singular at ``u = 0``:

      head  ``[0, u_head]``      analytic, ``|s| u_head`` up to ``O(u_head)``;
      ramp  ``[u_head, 1e-8]``   composite Simpson in ``log u``, where the
                                 integrand ``|z'| u ~ u^(2/n)`` is smooth;
      main  ``[1e-8, 1]``        composite Gauss-Legendre under ``u = a + b w^n``,
                                 whose Jacobian ``n w^(n-1)`` cancels the
                                 ``u^(2/n - 1)`` boundary layer exactly.

    Without the grading the quadrature is wrong in the fourth digit, which was
    caught by the closed-form ``z^n - r^n`` gate rather than by inspection.
    """

    degree = len(roots)
    value = _mp_value(roots, hub)
    if value == 0:
        return None
    second = _mp_second_derivative(roots, hub)
    if second == 0:
        return None
    tangent = mp.sqrt(-2 * value / second)
    reference = [abs(hub - other) for other in others] or [
        abs(hub - root) for root in roots
    ]
    separation = min(reference)
    head = min(mp.mpf("0.02") * separation / abs(tangent), mp.mpf(RAMP_JOIN))
    nodes, weights = _gauss_legendre(panels, order)
    main_u = [head + (1 - head) * node**degree for node in nodes]
    main_w = [
        weight * degree * node ** (degree - 1) * (1 - head)
        for node, weight in zip(nodes, weights)
    ]
    tolerance = mp.mpf(10) ** (-(mp.mp.dps - 8))

    branches: list[dict[str, Any]] = []
    for sign in (mp.mpf(1), mp.mpf(-1)):
        worst_residual = mp.mpf(0)
        worst_ratio = mp.mpf(0)
        current = hub + sign * tangent * head
        current, residual, iterations = _mp_newton(
            roots, (1 - head**2) * value, current, tolerance
        )
        if iterations >= 60:
            return None
        worst_residual = max(worst_residual, residual)
        length = abs(tangent) * head  # head piece, analytic

        def predict(target_u: mp.mpf, history: list[tuple[mp.mpf, mp.mpc]]) -> mp.mpc:
            """Power-law predictor in ``log(z - c)`` against ``log u``.

            A linear predictor in ``u`` is wrong here by construction: near a hub of
            effective multiplicity ``m`` the branch obeys ``z - c ~ u^(2/(m+1))``,
            and the graded quadrature deliberately puts consecutive nodes hundreds
            of times apart in ``u`` near zero.  Extrapolating the complex logarithm
            is exact for a pure power law and degrades gracefully away from one.
            """

            (u1, z1) = history[-1]
            if len(history) >= 2:
                (u0, z0) = history[-2]
                ratio = (z1 - hub) / (z0 - hub)
                if ratio != 0 and u1 != u0:
                    exponent = mp.log(ratio) / (mp.log(u1) - mp.log(u0))
                    return hub + (z1 - hub) * mp.exp(
                        exponent * (mp.log(target_u) - mp.log(u1))
                    )
            return hub + (z1 - hub) * (target_u / u1)

        def advance(target_u: mp.mpf, history: list[tuple[mp.mpf, mp.mpc]]):
            """One continuation step, sub-stepped when the ``u`` jump is large."""

            worst = mp.mpf(0)
            worst_res = mp.mpf(0)
            current_u = history[-1][0]
            while True:
                span = target_u / current_u
                step_u = target_u if span <= 8 else current_u * mp.mpf(4)
                guess = predict(step_u, history)
                solved, res, iters = _mp_newton(
                    roots, (1 - step_u**2) * value, guess, tolerance
                )
                if iters >= 60:
                    return None, worst_res, 60, worst
                worst_res = max(worst_res, res)
                move = abs(solved - history[-1][1])
                if move > 0:
                    worst = max(worst, abs(solved - guess) / move)
                history.append((step_u, solved))
                if len(history) > 3:
                    history.pop(0)
                current_u = step_u
                if current_u == target_u:
                    return solved, worst_res, 0, worst

        # geometric ramp from the analytic start up to the first quadrature node.
        # This is continuation only -- it carries branch identity, not quadrature.
        # The whole interval [head, 1] is covered by one graded rule below, with no
        # interior join: an artificial join at 1e-8 puts a kink inside the first
        # Gauss panel and costs about 1e-7 in the length, which is the same size as
        # the excess it would then appear to certify.
        history: list[tuple[mp.mpf, mp.mpc]] = [(head, current)]
        first = main_u[0]
        if first > head * mp.mpf("1.3"):
            bridge = max(
                2,
                int(
                    math.ceil(
                        RAMP_PER_DECADE * float(mp.log(first / head) / mp.log(10))
                    )
                ),
            )
            factor = (first / head) ** (mp.mpf(1) / bridge)
            for index in range(1, bridge):
                solved, residual, iterations, ratio = advance(
                    head * factor**index, history
                )
                if iterations >= 60:
                    return None
                worst_residual = max(worst_residual, residual)
                worst_ratio = max(worst_ratio, ratio)
            current = history[-1][1]

        # main interval
        for target_u, weight in zip(main_u, main_w):
            solved, residual, iterations, ratio = advance(target_u, history)
            if iterations >= 60:
                return None
            worst_residual = max(worst_residual, residual)
            worst_ratio = max(worst_ratio, ratio)
            derivative = _mp_derivative(roots, solved)
            if derivative == 0:
                return None
            length += weight * 2 * target_u * abs(value) / abs(derivative)

        # geometric tail to u = 1, then a Newton solve of f(z) = 0.  The endpoint is
        # the root this branch actually reaches, not the nearest root to a point
        # that may have hopped sheets.
        tail_u, tail_z = history[-1]
        gap = 1 - tail_u
        for _ in range(52):
            gap /= 2
            node = 1 - gap
            solved, residual, iterations = _mp_newton(
                roots, (1 - node**2) * value, tail_z, tolerance
            )
            if iterations >= 60:
                return None
            worst_residual = max(worst_residual, residual)
            tail_u, tail_z = node, solved
        endpoint, endpoint_residual, iterations = _mp_newton(
            roots, mp.mpc(0), tail_z, tolerance
        )
        if iterations >= 60:
            return None
        distances = [abs(endpoint - root) for root in roots]
        index = min(range(len(roots)), key=lambda k: distances[k])
        if worst_ratio > mistrack_ratio:
            return None
        branches.append(
            {
                "root_index": index,
                "length": length,
                "endpoint_error": distances[index],
                "worst_value_ray_residual": worst_residual,
                "worst_predictor_ratio": worst_ratio,
                "endpoint_residual": endpoint_residual,
                "head_fraction": (abs(tangent) * head) / length,
            }
        )
    if branches[0]["root_index"] == branches[1]["root_index"]:
        return None
    return {
        "root_pair": [branches[0]["root_index"], branches[1]["root_index"]],
        "total_length": branches[0]["length"] + branches[1]["length"],
        "branches": branches,
        "worst_endpoint_error": max(b["endpoint_error"] for b in branches),
        "worst_value_ray_residual": max(b["worst_value_ray_residual"] for b in branches),
        "worst_predictor_ratio": max(b["worst_predictor_ratio"] for b in branches),
        "worst_head_fraction": max(b["head_fraction"] for b in branches),
    }


def mp_near_fekete_roots(
    n: int, eps: mp.mpf, log_eps: Sequence[mp.mpf], dtheta: Sequence[mp.mpf]
) -> list[mp.mpc]:
    """The same coordinates built at working precision, not through float64.

    Needed because the float64 root grid is itself a floor on this search: a
    perturbation below ``2.2e-16`` radians is lost when the angle is stored as a
    double, so the *effective* cluster radius saturates near ``(1e-16)^(1/(n-1))``
    -- 2.2e-3 at degree 7.  Every configuration deeper into the Fekete corner than
    that is unrepresentable in float64 and therefore invisible to any search, in any
    coordinates, that stores its roots as doubles.
    """

    out: list[mp.mpc] = []
    two_pi = 2 * mp.pi
    for k in range(n):
        radius = 1 - eps * mp.exp(log_eps[k])
        angle = two_pi * k / n + dtheta[k]
        out.append(mp.mpc(radius * mp.cos(angle), radius * mp.sin(angle)))
    return out


def mp_descent_report(
    roots_float: np.ndarray | None,
    *,
    digits: int,
    panels: int,
    order: int,
    simple_hub_floor: float = 1.0e-8,
    mp_roots: Sequence[mp.mpc] | None = None,
) -> dict[str, Any]:
    """MIN and AVG at ``digits`` places, with every gate reported.

    ``simple_hub_floor`` matches the corpus tracker's ``|f''(c)| >= 1e-8`` simplicity
    test so the hub sets are comparable; hubs it rejects are counted, not dropped
    silently.
    """

    previous_dps = mp.mp.dps
    mp.mp.dps = digits
    try:
        if mp_roots is not None:
            roots = list(mp_roots)
        else:
            roots = [
                mp.mpc(mp.mpf(float(z.real)), mp.mpf(float(z.imag)))
                for z in roots_float
            ]
        criticals = _mp_critical_points(roots)
        rows: list[dict[str, Any]] = []
        rejected = {"inadmissible": 0, "degenerate": 0, "branch_failure": 0}
        for index, point in enumerate(criticals):
            value = abs(_mp_value(roots, point))
            if value >= 1:
                rejected["inadmissible"] += 1
                continue
            if abs(_mp_second_derivative(roots, point)) < simple_hub_floor:
                rejected["degenerate"] += 1
                continue
            others = [other for k, other in enumerate(criticals) if k != index]
            pair = mp_branch_pair(roots, point, others, panels=panels, order=order)
            if pair is None:
                rejected["branch_failure"] += 1
                continue
            rows.append(
                {
                    "critical_point": [
                        mp.nstr(mp.re(point), 25),
                        mp.nstr(mp.im(point), 25),
                    ],
                    "critical_value_modulus": mp.nstr(value, 25),
                    "root_pair": pair["root_pair"],
                    "total_length": mp.nstr(pair["total_length"], 25),
                    "total_length_float": float(pair["total_length"]),
                    "worst_endpoint_error": mp.nstr(pair["worst_endpoint_error"], 6),
                    "worst_value_ray_residual": mp.nstr(pair["worst_value_ray_residual"], 6),
                    "worst_predictor_ratio": mp.nstr(pair["worst_predictor_ratio"], 6),
                    "worst_head_fraction": mp.nstr(pair["worst_head_fraction"], 6),
                }
            )
        if not rows:
            return {
                "decimal_digits": digits,
                "panels": panels,
                "gauss_order": order,
                "admissible_hub_count": 0,
                "rejected": rejected,
            }
        lengths = [row["total_length_float"] for row in rows]
        total = sum(lengths)
        return {
            "decimal_digits": digits,
            "panels": panels,
            "gauss_order": order,
            "admissible_hub_count": len(rows),
            "rejected": rejected,
            "min_edge": min(lengths),
            "max_edge": max(lengths),
            "total_length": total,
            "normalized_average": total / (2.0 * len(rows)),
            "worst_endpoint_error": max(float(row["worst_endpoint_error"]) for row in rows),
            "worst_value_ray_residual": max(
                float(row["worst_value_ray_residual"]) for row in rows
            ),
            "worst_predictor_ratio": max(
                float(row["worst_predictor_ratio"]) for row in rows
            ),
            "worst_head_fraction": max(float(row["worst_head_fraction"]) for row in rows),
            "hubs": rows,
        }
    finally:
        mp.mp.dps = previous_dps


def mp_spoke_report(roots_float: np.ndarray, *, digits: int) -> dict[str, Any]:
    """OBJ-3 at ``digits`` places: hub located by Newton, spoke maxima *located*."""

    previous_dps = mp.mp.dps
    mp.mp.dps = digits
    try:
        roots = [mp.mpc(mp.mpf(float(z.real)), mp.mpf(float(z.imag))) for z in roots_float]
        criticals = _mp_critical_points(roots)
        admissible = []
        for point in criticals:
            value = abs(_mp_value(roots, point))
            if value < 1 and value > mp.mpf("1e-13"):
                admissible.append((value, point))
        if not admissible:
            return {"decimal_digits": digits, "admissible": False}
        value, centre = min(admissible, key=lambda item: item[0])
        distances = sorted(
            range(len(roots)), key=lambda k: abs(roots[k] - centre)
        )[:2]
        spokes = []
        for index in distances:
            maximum = _mp_segment_max(roots, centre, roots[index])
            spokes.append(
                {
                    "root_index": index,
                    "length": mp.nstr(abs(roots[index] - centre), 20),
                    "segment_max_modulus": mp.nstr(maximum, 22),
                    "segment_max_modulus_float": float(maximum),
                }
            )
        return {
            "decimal_digits": digits,
            "admissible": True,
            "critical_value_modulus": mp.nstr(value, 22),
            "derivative_residual": mp.nstr(abs(_mp_derivative(roots, centre)), 6),
            "nearest_pair_budget": float(
                sum(abs(roots[k] - centre) for k in distances)
            ),
            "spokes": spokes,
            "worst_segment_max_modulus": max(
                s["segment_max_modulus_float"] for s in spokes
            ),
        }
    finally:
        mp.mp.dps = previous_dps


def _mp_segment_max(roots: list[mp.mpc], start: mp.mpc, end: mp.mpc) -> mp.mpf:
    """``max |f|`` on ``[start, end]``, located via the real roots of ``d|f|^2/dt``."""

    direction = end - start
    poly = [mp.mpc(1)]
    for root in roots:
        shift = start - root
        nxt = [mp.mpc(0)] * (len(poly) + 1)
        for index, coefficient in enumerate(poly):
            nxt[index] += coefficient * shift
            nxt[index + 1] += coefficient * direction
        poly = nxt
    squared = [mp.mpf(0)] * (2 * len(poly) - 1)
    for i, left in enumerate(poly):
        for j, right in enumerate(poly):
            squared[i + j] += (left * mp.conj(right)).real
    derivative = [squared[k] * k for k in range(1, len(squared))]
    while derivative and derivative[-1] == 0:
        derivative.pop()
    candidates = [mp.mpf(0), mp.mpf(1)]
    if len(derivative) > 1:
        for root in mp.polyroots(list(reversed(derivative)), maxsteps=400, extraprec=400):
            if abs(mp.im(root)) < mp.mpf("1e-25"):
                parameter = mp.re(root)
                if 0 <= parameter <= 1:
                    candidates.append(parameter)
    best = mp.mpf(0)
    for parameter in candidates:
        total = mp.mpf(0)
        power = mp.mpf(1)
        for coefficient in squared:
            total += coefficient * power
            power *= parameter
        best = max(best, total)
    return mp.sqrt(max(mp.mpf(0), best))


# ---------------------------------------------------------------------------
# the search itself
# ---------------------------------------------------------------------------


def hill_climb(
    n: int,
    evaluate,
    log_eps: np.ndarray,
    dtheta: np.ndarray,
    *,
    steps: int,
    angular_step: float,
    radial_step: float,
    rng: np.random.Generator,
) -> tuple[float, np.ndarray, np.ndarray]:
    """Adaptive Gaussian hill climb in ``(log eps, dtheta)``.

    ``dtheta[0]`` is pinned to zero: every objective here is rotation invariant, so
    the free rotation is a flat direction that would otherwise absorb search budget.
    """

    best = evaluate(near_fekete_roots(n, log_eps, dtheta))
    a_step, r_step = angular_step, radial_step
    for _ in range(steps):
        proposal_theta = dtheta + a_step * np.concatenate(
            [[0.0], rng.normal(size=n - 1)]
        )
        proposal_eps = log_eps + r_step * rng.normal(size=n)
        candidate = evaluate(near_fekete_roots(n, proposal_eps, proposal_theta))
        if candidate > best:
            best, dtheta, log_eps = candidate, proposal_theta, proposal_eps
            a_step *= 1.15
            r_step *= 1.15
        else:
            a_step *= 0.94
            r_step *= 0.94
        if a_step < 1.0e-14 and r_step < 1.0e-6:
            break
    return best, log_eps, dtheta


def run_search(
    n: int,
    evaluate,
    *,
    restarts: int,
    steps: int,
    rng: np.random.Generator,
    eps_grid: Sequence[float] = EPS_GRID,
    pert_grid: Sequence[float] = PERT_GRID,
) -> dict[str, Any]:
    """Structured seeds over the (eps, perturbation-scale) ladder, then hill climb."""

    best_value = -math.inf
    best_roots: np.ndarray | None = None
    best_seed: tuple[float, float] | None = None
    seeds: list[tuple[float, float]] = [
        (eps, pert) for eps in eps_grid for pert in pert_grid
    ]
    for eps, pert in seeds:
        log_eps = np.full(n, math.log(eps))
        dtheta = np.zeros(n)
        if pert > 0.0:
            dtheta[1:] = pert * rng.normal(size=n - 1)
            log_eps = log_eps + pert * rng.normal(size=n)
        else:
            # the exact regular n-gon carries a degenerate hub of multiplicity n-1,
            # which every simple-hub tracker rejects; split it by the smallest
            # perturbation that still resolves n-1 simple hubs.
            dtheta[1:] = 1.0e-9 * rng.normal(size=n - 1)
        angular = max(pert, 1.0e-9)
        value, log_eps, dtheta = hill_climb(
            n,
            evaluate,
            log_eps,
            dtheta,
            steps=steps,
            angular_step=angular,
            radial_step=0.35,
            rng=rng,
        )
        if value > best_value:
            best_value = value
            best_roots = near_fekete_roots(n, log_eps, dtheta)
            best_seed = (eps, pert)
    for _ in range(max(0, restarts)):
        eps = 10.0 ** rng.uniform(-9.0, -2.0)
        pert = 10.0 ** rng.uniform(-8.0, -2.0)
        log_eps = math.log(eps) + pert * rng.normal(size=n)
        dtheta = np.zeros(n)
        dtheta[1:] = pert * rng.normal(size=n - 1)
        value, log_eps, dtheta = hill_climb(
            n,
            evaluate,
            log_eps,
            dtheta,
            steps=steps,
            angular_step=pert,
            radial_step=0.35,
            rng=rng,
        )
        if value > best_value:
            best_value = value
            best_roots = near_fekete_roots(n, log_eps, dtheta)
            best_seed = (eps, pert)
    out: dict[str, Any] = {"degree": n, "best_value": float(best_value)}
    if best_roots is not None:
        out["seed_eps"] = best_seed[0]
        out["seed_perturbation_scale"] = best_seed[1]
        out["roots_hex"] = hex_literals(best_roots)
        out["geometry"] = ngon_deviation(best_roots)
    return out


# ---------------------------------------------------------------------------
# modes
# ---------------------------------------------------------------------------


def mode_gate3(args: argparse.Namespace) -> dict[str, Any]:
    """OBJ-3.  Runs first; every other number in the receipt is void if it fails."""

    import check_erdos1041_straight_spoke_hub_criterion as witness_module

    witnesses = []
    for degree, literals in witness_module.QC_REFUTATION_WITNESSES.items():
        roots = roots_from_hex(literals)
        detail = spoke_objective(roots)
        witnesses.append(
            {
                "degree": degree,
                "geometry": ngon_deviation(roots),
                "float64_worst_segment_max_modulus": detail["worst_segment_max_modulus"],
                "recorded_worst_segment_max_modulus": WITNESS_SPOKE_MAX[degree],
                "float64_minus_recorded": detail["worst_segment_max_modulus"]
                - WITNESS_SPOKE_MAX[degree],
                "nearest_pair_budget": detail["nearest_pair_budget"],
                "high_precision": mp_spoke_report(roots, digits=args.digits),
            }
        )

    rng = np.random.default_rng(args.seed)
    rows = []
    for n in args.degrees:
        started = time.time()
        row = run_search(
            n,
            spoke_score,
            restarts=args.restarts,
            steps=args.steps,
            rng=rng,
            eps_grid=args.eps_grid,
            pert_grid=args.pert_grid,
        )
        row["seconds"] = round(time.time() - started, 2)
        if "roots_hex" in row:
            roots = roots_from_hex(row["roots_hex"])
            row["float64_detail"] = spoke_objective(roots)
            row["high_precision"] = mp_spoke_report(roots, digits=args.digits)
            row["float64_minus_high_precision"] = (
                row["best_value"] - row["high_precision"]["worst_segment_max_modulus"]
            )
        row["exceeds_one"] = bool(row["best_value"] > 1.0)
        rows.append(row)
        print(json.dumps(row, default=str), flush=True)

    crossing = [row for row in rows if row["exceeds_one"]]
    return {
        "objective": "OBJ-3 worst straight spoke max |f| at c* over the two nearest roots",
        "stored_witnesses": witnesses,
        "near_fekete_rows": rows,
        "gate_passed": bool(crossing),
        "degrees_exceeding_one": [row["degree"] for row in crossing],
        "best_over_degrees": max((row["best_value"] for row in rows), default=None),
    }


def mode_extremal(args: argparse.Namespace) -> dict[str, Any]:
    """Second gate: ``z^n - r^n`` gives MIN ``= 2r`` and AVG ``= r`` at every degree."""

    rng = np.random.default_rng(args.seed + 17)
    rows = []
    for n in args.degrees:
        for r in args.radii:
            for pert in (0.0, 1e-9, 1e-7, 1e-5):
                log_eps = np.full(n, math.log(1.0 - r))
                dtheta = np.zeros(n)
                if pert > 0.0:
                    dtheta[1:] = pert * rng.normal(size=n - 1)
                    log_eps = log_eps + pert * rng.normal(size=n)
                roots = near_fekete_roots(n, log_eps, dtheta)
                detail = descent_detail(roots, args.flow_max_step)
                row: dict[str, Any] = {
                    "degree": n,
                    "radius": r,
                    "perturbation": pert,
                    "predicted_min_edge": 2.0 * r,
                    "predicted_normalized_average": r,
                }
                if detail is None:
                    row["float64"] = None
                    row["note"] = (
                        "no admissible simple hub: the unperturbed family has one "
                        "critical point of multiplicity n-1, which the simplicity "
                        "gate |f''(c)| >= 1e-8 rejects"
                    )
                else:
                    row["float64"] = detail
                    row["float64_min_edge_minus_2r"] = detail["min_edge"] - 2.0 * r
                    row["float64_avg_minus_r"] = detail["normalized_average"] - r
                if args.high_precision and pert in (0.0, 1e-9):
                    row["high_precision"] = mp_descent_report(
                        roots,
                        digits=args.digits,
                        panels=args.panels,
                        order=args.gauss_order,
                    )
                rows.append(row)
                print(json.dumps(row, default=str), flush=True)
    usable = [row for row in rows if row.get("float64")]
    return {
        "family": "z^n - r^n and its near-Fekete perturbations",
        "closed_form": "min_c L_c = 2r, normalized aggregate = r, at every degree n",
        "rows": rows,
        "worst_min_edge_deficit": max(
            (abs(row["float64_min_edge_minus_2r"]) for row in usable), default=None
        ),
        "worst_avg_deficit": max(
            (abs(row["float64_avg_minus_r"]) for row in usable), default=None
        ),
        "unperturbed_family_has_no_simple_hub_at_degrees": sorted(
            {
                row["degree"]
                for row in rows
                if row["perturbation"] == 0.0 and row["float64"] is None
            }
        ),
    }


def mode_search(args: argparse.Namespace) -> dict[str, Any]:
    """OBJ-1 and OBJ-2 in near-Fekete coordinates, against the recorded bulk values."""

    rng = np.random.default_rng(args.seed + 101)
    counters = TrackerCounters()
    rows = []
    for mode, recorded in (("min_edge", BULK_MIN), ("normalized_average", BULK_AVG)):
        for n in args.degrees:
            started = time.time()

            def evaluate(roots: np.ndarray, _mode: str = mode) -> float:
                return descent_score(roots, _mode, args.flow_max_step, counters)

            row = run_search(
                n,
                evaluate,
                restarts=args.restarts,
                steps=args.steps,
                rng=rng,
                eps_grid=args.eps_grid,
                pert_grid=args.pert_grid,
            )
            row["objective"] = "OBJ-1 MIN" if mode == "min_edge" else "OBJ-2 AVG"
            row["tracker_mode"] = mode
            row["seconds"] = round(time.time() - started, 2)
            row["recorded_bulk_value"] = recorded.get(n)
            threshold = 2.0 if mode == "min_edge" else 1.0
            row["threshold"] = threshold
            row["exceeds_threshold"] = bool(row["best_value"] > threshold)
            if row.get("recorded_bulk_value") is not None:
                row["improvement_over_bulk"] = row["best_value"] - row["recorded_bulk_value"]
            if "roots_hex" in row:
                roots = roots_from_hex(row["roots_hex"])
                row["float64_detail"] = descent_detail(roots, args.flow_max_step)
                row["float64_detail_fine_step"] = descent_detail(
                    roots, args.flow_max_step / 4.0
                )
                if args.high_precision:
                    coarse = mp_descent_report(
                        roots,
                        digits=args.digits,
                        panels=args.panels,
                        order=args.gauss_order,
                    )
                    fine = mp_descent_report(
                        roots,
                        digits=args.digits,
                        panels=2 * args.panels,
                        order=args.gauss_order,
                    )
                    row["high_precision"] = coarse
                    if coarse.get("admissible_hub_count") and fine.get(
                        "admissible_hub_count"
                    ):
                        row["quadrature_delta"] = {
                            "min_edge": abs(coarse["min_edge"] - fine["min_edge"]),
                            "normalized_average": abs(
                                coarse["normalized_average"] - fine["normalized_average"]
                            ),
                        }
                        key = "min_edge" if mode == "min_edge" else "normalized_average"
                        row["float64_minus_high_precision"] = (
                            row["best_value"] - coarse[key]
                        )
                        row["high_precision_exceeds_threshold"] = bool(
                            coarse[key] > threshold
                        )
            rows.append(row)
            print(json.dumps(row, default=str), flush=True)
    return {
        "rows": rows,
        "tracker_counters": counters.as_dict(),
        "MIN_refuted": any(
            row["exceeds_threshold"] for row in rows if row["tracker_mode"] == "min_edge"
        ),
        "AVG_refuted": any(
            row["exceeds_threshold"]
            for row in rows
            if row["tracker_mode"] == "normalized_average"
        ),
    }


def mode_verify(args: argparse.Namespace) -> dict[str, Any]:
    """Re-measure stored hex configurations at ``--digits``, both objectives.

    Every descent number is produced twice, at ``panels`` and ``2*panels``, so the
    quadrature error is reported rather than assumed.  A claimed violation whose
    ``quadrature_delta`` is the same size as its excess over the threshold is not a
    violation, it is a resolution artifact -- the shape of all four recorded false
    counterexamples.
    """

    payload = json.loads(Path(args.verify_input).read_text())
    rows = []
    for entry in payload:
        roots = roots_from_hex(entry["roots_hex"])
        coarse = mp_descent_report(
            roots,
            digits=args.digits,
            panels=args.panels,
            order=args.gauss_order,
            simple_hub_floor=args.simple_hub_floor,
        )
        fine = mp_descent_report(
            roots,
            digits=args.digits,
            panels=2 * args.panels,
            order=args.gauss_order,
            simple_hub_floor=args.simple_hub_floor,
        )
        row: dict[str, Any] = {
            "label": entry.get("label"),
            "degree": len(roots),
            "geometry": ngon_deviation(roots),
            "float64_descent": descent_detail(roots, args.flow_max_step),
            "float64_descent_fine_step": descent_detail(roots, args.flow_max_step / 4.0),
            "float64_spoke": spoke_objective(roots),
            "float64_all_spokes": all_spoke_containment(roots),
            "high_precision_descent": coarse,
            "high_precision_spoke": mp_spoke_report(roots, digits=args.digits),
        }
        if coarse.get("admissible_hub_count") and fine.get("admissible_hub_count"):
            row["quadrature_delta"] = {
                "min_edge": abs(coarse["min_edge"] - fine["min_edge"]),
                "normalized_average": abs(
                    coarse["normalized_average"] - fine["normalized_average"]
                ),
            }
            row["min_edge_minus_2"] = coarse["min_edge"] - 2.0
            row["normalized_average_minus_1"] = coarse["normalized_average"] - 1.0
            if entry.get("radius") is not None:
                row["min_edge_minus_2r"] = coarse["min_edge"] - 2.0 * entry["radius"]
                row["normalized_average_minus_r"] = (
                    coarse["normalized_average"] - entry["radius"]
                )
        rows.append(row)
        print(json.dumps(row, default=str), flush=True)
    return {"rows": rows}


def mode_ladder(args: argparse.Namespace) -> dict[str, Any]:
    """How close to the threshold MIN and AVG get as the Fekete corner is entered.

    The ``n-1`` hubs of a perturbed ``z^n - r^n`` split at cluster radius
    ``rho ~ pert^(1/(n-1))``, and the measured deficit ``2r - min_c L_c`` tracks
    ``rho``.  So the whole question "how close to 2 can MIN get" is a question about
    how small ``rho`` may be, and the answer is bounded by an *instrument* constant,
    not by the mathematics: ``|f''(c)| ~ n(n-1) rho^(n-2)``, so the corpus tracker's
    ``|f''| >= 1e-8`` simplicity gate excludes every configuration with

        rho  <  (1e-8 / (n(n-1)))^(1/(n-2))

    which is 3.4e-10 at n = 4 but 3.0e-2 at n = 7.  This mode walks the ladder with
    both trackers and with ``--simple-hub-floor`` free, so the instrument bound and
    the mathematical bound are separated.
    """

    rng = np.random.default_rng(args.seed + 991)
    rows = []
    for n in args.degrees:
        for eps in args.ladder_eps:
            for pert in args.ladder_perturbations:
                radius = 1.0 - eps
                log_eps = np.full(n, math.log(eps))
                dtheta = np.zeros(n)
                dtheta[1:] = pert * rng.normal(size=n - 1)
                log_eps = log_eps + pert * rng.normal(size=n)
                roots = near_fekete_roots(n, log_eps, dtheta)
                row: dict[str, Any] = {
                    "degree": n,
                    "eps": eps,
                    "radius": radius,
                    "perturbation": pert,
                    "predicted_cluster_radius": pert ** (1.0 / (n - 1)),
                    "float64": descent_detail(roots, args.flow_max_step),
                    "roots_built_at_working_precision": bool(args.exact_roots),
                }
                exact: list[mp.mpc] | None = None
                if args.exact_roots:
                    previous_dps = mp.mp.dps
                    mp.mp.dps = args.digits
                    try:
                        exact = mp_near_fekete_roots(
                            n,
                            mp.mpf(eps),
                            [mp.mpf(0)] * n,
                            [mp.mpf(0)]
                            + [mp.mpf(float(x)) * mp.mpf(pert) for x in rng.normal(size=n - 1)],
                        )
                        row["max_root_modulus_exact"] = mp.nstr(
                            max(abs(z) for z in exact), 25
                        )
                    finally:
                        mp.mp.dps = previous_dps
                report = mp_descent_report(
                    roots,
                    digits=args.digits,
                    panels=args.panels,
                    order=args.gauss_order,
                    simple_hub_floor=args.simple_hub_floor,
                    mp_roots=exact,
                )
                if report.get("admissible_hub_count"):
                    fine = mp_descent_report(
                        roots,
                        digits=args.digits,
                        panels=2 * args.panels,
                        order=args.gauss_order,
                        simple_hub_floor=args.simple_hub_floor,
                        mp_roots=exact,
                    )
                    row["high_precision"] = {
                        key: report[key]
                        for key in (
                            "admissible_hub_count",
                            "rejected",
                            "min_edge",
                            "normalized_average",
                            "worst_endpoint_error",
                            "worst_value_ray_residual",
                            "worst_predictor_ratio",
                            "worst_head_fraction",
                        )
                    }
                    row["quadrature_delta"] = {
                        "min_edge": abs(report["min_edge"] - fine["min_edge"]),
                        "normalized_average": abs(
                            report["normalized_average"] - fine["normalized_average"]
                        ),
                    }
                    row["min_edge_minus_2r"] = report["min_edge"] - 2.0 * radius
                    row["min_edge_minus_2"] = report["min_edge"] - 2.0
                    row["normalized_average_minus_r"] = (
                        report["normalized_average"] - radius
                    )
                    row["normalized_average_minus_1"] = (
                        report["normalized_average"] - 1.0
                    )
                else:
                    row["high_precision"] = report
                rows.append(row)
                print(json.dumps(row, default=str), flush=True)
    usable = [row for row in rows if "min_edge_minus_2" in row]
    return {
        "rows": rows,
        "best_min_edge": max(
            (row["high_precision"]["min_edge"] for row in usable), default=None
        ),
        "best_normalized_average": max(
            (row["high_precision"]["normalized_average"] for row in usable), default=None
        ),
        "MIN_refuted": any(row["min_edge_minus_2"] > 0 for row in usable),
        "AVG_refuted": any(row["normalized_average_minus_1"] > 0 for row in usable),
    }


MODES = {
    "gate3": mode_gate3,
    "extremal": mode_extremal,
    "search": mode_search,
    "ladder": mode_ladder,
    "verify": mode_verify,
}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--mode",
        default="gate3",
        choices=sorted(MODES) + ["all"],
        help="gate3 runs first and gates the rest; extremal is the second gate",
    )
    parser.add_argument("--degrees", type=int, nargs="+", default=[4, 5, 6, 7])
    parser.add_argument("--radii", type=float, nargs="+", default=[0.999, 0.99999])
    parser.add_argument("--restarts", type=int, default=6)
    parser.add_argument("--steps", type=int, default=200)
    parser.add_argument("--flow-max-step", type=float, default=0.02)
    parser.add_argument("--digits", type=int, default=60)
    parser.add_argument("--panels", type=int, default=48)
    parser.add_argument("--gauss-order", type=int, default=10)
    parser.add_argument("--seed", type=int, default=20260823)
    parser.add_argument("--high-precision", action="store_true", default=False)
    parser.add_argument(
        "--simple-hub-floor",
        type=float,
        default=1.0e-8,
        help=(
            "|f''(c)| below which a hub is treated as degenerate.  1e-8 matches the "
            "corpus tracker.  Near a Fekete configuration this floor is not neutral: "
            "the n-1 hubs split at cluster radius rho with |f''| ~ n(n-1) rho^(n-2), "
            "so at degree 7 the floor silently excludes every configuration with "
            "rho below about 0.03 -- which is exactly the near-Fekete corner."
        ),
    )
    parser.add_argument(
        "--eps-grid", type=float, nargs="+", default=list(EPS_GRID),
        help="seed ladder for the radius deficit 1 - |z|")
    parser.add_argument(
        "--pert-grid", type=float, nargs="+", default=list(PERT_GRID),
        help="seed ladder for the angular/radial perturbation scale")
    parser.add_argument(
        "--ladder-eps", type=float, nargs="+",
        default=[1e-9, 1e-7, 1e-5],
        help="mode=ladder: radius deficits to walk")
    parser.add_argument(
        "--ladder-perturbations", type=float, nargs="+",
        default=[1e-2, 1e-3, 1e-4, 1e-6, 1e-9, 1e-12, 1e-16, 1e-20],
        help="mode=ladder: perturbation scales to walk")
    parser.add_argument(
        "--ramp-per-decade", type=int, default=16,
        help=(
            "Simpson resolution, points per decade of u, on the geometric ramp "
            "[u_head, 1e-8].  Raise it when quadrature_delta is the same size as a "
            "claimed excess over the threshold -- that shape is a resolution "
            "artifact, not a counterexample."))
    parser.add_argument(
        "--exact-roots", action="store_true", default=False,
        help=(
            "mode=ladder: build the near-Fekete roots at working precision instead "
            "of through float64, so the perturbation scale is not floored by double "
            "rounding of the angles"))
    parser.add_argument("--verify-input", type=Path, default=None)
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    globals()["RAMP_PER_DECADE"] = args.ramp_per_decade
    started = time.time()
    payload: dict[str, Any] = {
        "source": SOURCE_REF,
        "analysis": ANALYSIS_REF,
        "arguments": {
            key: (str(value) if isinstance(value, Path) else value)
            for key, value in vars(args).items()
        },
    }
    order = (
        ["gate3", "extremal", "search", "ladder"]
        if args.mode == "all"
        else [args.mode]
    )
    gate_passed = None
    for name in order:
        if name == "verify" and args.verify_input is None:
            raise SystemExit("--verify-input is required for mode=verify")
        result = MODES[name](args)
        payload[name] = result
        if name == "gate3":
            gate_passed = bool(result["gate_passed"])
            if args.mode == "all" and not gate_passed:
                payload["aborted"] = (
                    "OBJ-3 did not exceed 1 in near-Fekete coordinates; the search or "
                    "the precision is broken and no OBJ-1/OBJ-2 number would be valid"
                )
                break
    payload["seconds"] = round(time.time() - started, 2)
    print(json.dumps({k: v for k, v in payload.items() if k != "arguments"}, indent=2,
                     default=str)[:4000], flush=True)
    destination = args.out or DEFAULT_OUTPUT
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(payload, indent=2, default=str) + "\n")
    print(f"receipt: {destination}", flush=True)
    if gate_passed is False:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
