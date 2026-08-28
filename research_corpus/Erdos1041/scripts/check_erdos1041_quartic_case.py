#!/usr/bin/env python3
"""Erdős #1041 in degree four: prior-art verification and mechanism sweep.

Context
-------
The degree-four case of Erdős #1041 is **not open**.  It is proved by

    V. S. Pendyala, "A Degree-Four Lemniscate Path Theorem",
    arXiv:2606.24875, submitted 23 June 2026,

whose full text is held in this repository at
``annexes/arxiv-2606-24875-erdos1041-quartic-lemniscate-path/extracted.md``.
``research_packet.json`` already records it (negative result 12, exact result 17)
and ``AdaptiveMecDichotomyLab.md`` calls it "the complete quartic theorem".

This script does four things, none of which is a new theorem:

``identity``
    Verifies, symbolically, the general-degree spoke identity that generalises
    ``CubicCriticalHub.md``'s ``P_b(tw) = 1 - t^2 - t^2(1-t) w^3``, and confirms
    that its containment condition is the **hub-sublevel** test ``|f| <= |f(c)|``
    -- the criterion ``StraightSpokeHubCriterionLab.md`` §2 kills at degree four.

``sublevel``
    Replays that exact quartic witness and shows every admissible hub carries at
    most one sublevel-contained spoke, so the identity route cannot close n = 4.
    Also sweeps normalised quartic parameter space for the crux question "does
    minimality force two normalised roots inside the closed unit disk?".

``pendyala``
    Independent verification of Pendyala's proof: adversarial and structured
    falsification of his four-point radial lemma, and an end-to-end certified
    construction of his path on random, near-Fekete and adversarial quartics.

``hubsweep``
    The surviving corpus mechanism at n = 4: the **open** criterion ``|f| < 1``
    on two straight spokes at an admissible critical point.  Adversarial and
    near-Fekete sweep of the quantity ``StraightSpokeHubCriterionLab.md`` §3
    calls ``QC``, restricted to degree four.

Every segment maximum is located from the real roots of ``d|f|^2/dt`` along the
segment.  Nothing is sampled: a sampled test can skip a narrow excursion and
report a containment that does not hold.

A dense sweep is not a proof.  Where this script reports a supremum it says
whether the value is pinned below the threshold or crosses it.

Replay::

    ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_quartic_case.py
    ./repo-python .../check_erdos1041_quartic_case.py --modes identity
    ./repo-python .../check_erdos1041_quartic_case.py --modes pendyala --trials 4000
"""

from __future__ import annotations

import argparse
import cmath
import json
import math
import sys
from typing import Any, Iterable, Sequence

import numpy as np

try:  # mpmath ships with the repo environment; the float path still works without it.
    import mpmath as mp
except Exception:  # pragma: no cover - defensive
    mp = None  # type: ignore[assignment]


# --------------------------------------------------------------------------
# the exact quartic witness of StraightSpokeHubCriterionLab.md section 2
# --------------------------------------------------------------------------

WITNESS_DENOMINATOR = 10000
WITNESS_ROOT_INTEGERS: tuple[tuple[int, int], ...] = (
    (9999, 4),
    (-125, 9998),
    (-9999, -14),
    (-23, -9999),
)


def witness_roots() -> np.ndarray:
    return np.asarray(
        [(a + 1j * b) / WITNESS_DENOMINATOR for a, b in WITNESS_ROOT_INTEGERS],
        dtype=np.complex128,
    )


def witness_roots_strictly_inside() -> bool:
    """Integer certificate that every witness root has modulus below one."""

    limit = WITNESS_DENOMINATOR * WITNESS_DENOMINATOR
    return all(a * a + b * b < limit for a, b in WITNESS_ROOT_INTEGERS)


# --------------------------------------------------------------------------
# exact segment maxima  (float path)
# --------------------------------------------------------------------------


def segment_polynomial(roots: Sequence[complex], start: complex, end: complex) -> np.ndarray:
    """Ascending-power coefficients of ``t -> f(start + t (end - start))``."""

    direction = end - start
    poly = np.array([1.0 + 0.0j], dtype=np.complex128)
    for root in roots:
        shift = start - root
        nxt = np.zeros(poly.size + 1, dtype=np.complex128)
        nxt[: poly.size] += poly * shift
        nxt[1:] += poly * direction
        poly = nxt
    return poly


def _squared_modulus_coefficients(poly: np.ndarray) -> np.ndarray:
    """Real ascending coefficients of ``|P(t)|^2`` for real ``t``."""

    size = 2 * poly.size - 1
    out = np.zeros(size, dtype=np.float64)
    for i, left in enumerate(poly):
        for j, right in enumerate(poly):
            out[i + j] += (left * np.conjugate(right)).real
    return out


def segment_max_abs(roots: Sequence[complex], start: complex, end: complex) -> float:
    """Maximum of ``|f|`` on the closed segment, from the roots of ``d|f|^2/dt``."""

    squared = _squared_modulus_coefficients(segment_polynomial(roots, start, end))
    derivative = np.array([squared[k] * k for k in range(1, squared.size)], dtype=np.float64)
    while derivative.size and abs(derivative[-1]) < 1e-300:
        derivative = derivative[:-1]
    candidates = [0.0, 1.0]
    if derivative.size > 1:
        for value in np.roots(derivative[::-1]):
            if abs(value.imag) < 1e-9 and -1e-12 <= value.real <= 1.0 + 1e-12:
                candidates.append(min(1.0, max(0.0, float(value.real))))
    best = 0.0
    for parameter in candidates:
        total = 0.0
        power = 1.0
        for coefficient in squared:
            total += coefficient * power
            power *= parameter
        best = max(best, total)
    return math.sqrt(max(0.0, best))


def segment_max_product(points: Sequence[complex], start: complex, end: complex) -> float:
    """``max_t prod_k |start + t(end-start) - points_k|``; same routine, other name."""

    return segment_max_abs(points, start, end)


# --------------------------------------------------------------------------
# exact segment maxima  (mpmath path, for anything reported as a violation)
# --------------------------------------------------------------------------


def mp_segment_max_abs(roots: Sequence[Any], start: Any, end: Any) -> Any:
    assert mp is not None
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
        for value in mp.polyroots(list(reversed(derivative)), maxsteps=400, extraprec=400):
            if abs(mp.im(value)) < mp.mpf("1e-25"):
                real = mp.re(value)
                if 0 <= real <= 1:
                    candidates.append(real)
    best = mp.mpf(0)
    for parameter in candidates:
        total = mp.mpf(0)
        power = mp.mpf(1)
        for coefficient in squared:
            total += coefficient * power
            power *= parameter
        best = max(best, total)
    return mp.sqrt(max(mp.mpf(0), best))


def mp_critical_points(roots: Sequence[Any], seeds: Iterable[complex]) -> list[Any]:
    assert mp is not None

    def derivative(point: Any) -> Any:
        total = mp.mpc(0)
        for skipped in range(len(roots)):
            term = mp.mpc(1)
            for index, root in enumerate(roots):
                if index != skipped:
                    term *= point - root
            total += term
        return total

    return [mp.findroot(derivative, mp.mpc(complex(seed))) for seed in seeds]


# --------------------------------------------------------------------------
# mode: identity
# --------------------------------------------------------------------------


def run_identity() -> dict[str, Any]:
    """Symbolic verification of the general-degree straight-spoke identity.

    Normalise the hub to ``0`` and the critical value to ``1``:

        G(w) = w^n + a_{n-1} w^{n-1} + ... + a_2 w^2 + 1,   G'(0) = 0, G(0) = 1.

    For a root ``w`` of ``G``, put ``c_k = a_k w^k`` (so ``sum_{k>=2} c_k = -1``).
    Then along the spoke ``z = t w``

        G(tw) = (1 - t^2) - t^2 (1 - t) Q(t),
        Q(t)  = sum_{k>=3} c_k (1 + t + ... + t^{k-3}).

    Consequence: ``(1-t) |Q(t)| <= 1`` on ``[0,1]`` implies ``|G| <= 1`` on the
    whole spoke.  ``|G| <= 1`` is exactly ``|f| <= |f(c)|`` -- the hub-sublevel
    criterion, not the open criterion ``|f| < 1`` the target statement needs.
    """

    try:
        import sympy as sp
    except Exception as exc:  # pragma: no cover
        return {"status": "skipped", "reason": f"sympy unavailable: {exc}"}

    t = sp.symbols("t")
    rows: list[dict[str, Any]] = []
    for n in (3, 4, 5, 6):
        w = sp.symbols("w")
        a = {k: sp.symbols(f"a{k}") for k in range(2, n)}
        a[n] = sp.Integer(1)
        G = sum(a[k] * w**k for k in range(2, n + 1)) + 1
        c = {k: sp.expand(a[k] * w**k) for k in range(2, n + 1)}

        # left-hand side G(tw), rewritten using sum_k c_k = -1 (i.e. G(w) = 0)
        lhs = sum(c[k] * t**k for k in range(2, n + 1)) + 1
        Q = sum(c[k] * sum(t**m for m in range(0, k - 2)) for k in range(3, n + 1))
        rhs = (1 - t**2) - t**2 * (1 - t) * Q

        # the identity holds MODULO the relation sum_{k>=2} c_k = -1; substitute
        # the relation by eliminating c_2 = -1 - sum_{k>=3} c_k
        relation = {a[2]: sp.solve(sp.Eq(sum(c[k] for k in range(2, n + 1)), -1), a[2])[0]}
        difference = sp.simplify(sp.expand(lhs.subs(relation) - rhs.subs(relation)))
        rows.append(
            {
                "degree": n,
                "identity_residual": str(difference),
                "identity_holds": bool(difference == 0),
                "G_is_normalised": bool(
                    sp.simplify(G.subs(w, 0) - 1) == 0
                    and sp.simplify(sp.diff(G, w).subs(w, 0)) == 0
                ),
            }
        )

    # explicit reduction to CubicCriticalHub.md at n = 3
    w = sp.symbols("w")
    b = sp.symbols("b")
    cubic_corpus = 1 - t**2 - t**2 * (1 - t) * w**3
    cubic_from_identity = (1 - t**2) - t**2 * (1 - t) * (w**3)  # Q(t) = c_3 = w^3
    cubic_reduction = bool(sp.simplify(cubic_corpus - cubic_from_identity) == 0)

    # and the corpus's own normalised cubic satisfies it verbatim
    P_b = w**3 - sp.Rational(3, 2) * b * w**2 + 1
    spoke = sp.expand(P_b.subs(w, t * w))
    target = sp.expand(1 - t**2 - t**2 * (1 - t) * w**3)
    # valid when w is a root of P_b: eliminate b via P_b(w) = 0
    b_of_w = sp.solve(sp.Eq(P_b, 0), b)[0]
    corpus_residual = sp.simplify(sp.expand(spoke.subs(b, b_of_w) - target))

    # the quartic specialisation the coordinator asked for
    a3 = sp.symbols("a3")
    Q4 = a3 * w**3 + (1 + t) * w**4
    quartic_condition = sp.simplify((1 - t) * sp.Abs(Q4))

    return {
        "status": "ok",
        "rows": rows,
        "all_degrees_verified": all(row["identity_holds"] for row in rows),
        "cubic_reduction_matches_CubicCriticalHub_md": cubic_reduction,
        "corpus_cubic_spoke_identity_residual": str(corpus_residual),
        "corpus_cubic_spoke_identity_holds": bool(corpus_residual == 0),
        "quartic_Q": str(sp.simplify(Q4)),
        "quartic_containment_condition": f"max_(0<=t<=1) {quartic_condition} <= 1",
        "criterion_this_identity_proves": "hub_sublevel  |f| <= |f(c)|",
        "criterion_the_target_needs": "open_lemniscate  |f| < 1",
        "note": (
            "The identity is correct and is the right generalisation of the cubic. "
            "But |G| <= 1 is the hub-sublevel criterion, which "
            "StraightSpokeHubCriterionLab.md section 2 refutes at degree four "
            "(research_packet negative result 13). See mode 'sublevel'."
        ),
    }


# --------------------------------------------------------------------------
# mode: sublevel
# --------------------------------------------------------------------------


CRITICAL_CLUSTER_TOLERANCE = 1e-4


def critical_points(roots: Sequence[complex]) -> np.ndarray:
    """Critical points with near-degenerate ``np.roots`` clusters collapsed.

    ``np.roots`` cannot resolve a multiple root: the ``m``-fold zero of ``f'``
    comes back as ``m`` points spread by about ``eps**(1/m)`` -- ``6e-6`` for the
    triple zero of ``z^4 - r^4``'s derivative.  ``CriticalBudgetLab.md`` records
    the repair and its bias: a spurious extra hub can only *lower* a minimum over
    hubs, so it biases toward satisfying the conjecture; collapsing raises the
    reported minimum, which is the safe direction for a violation hunt.  The
    centroid recovers a multiple root to full precision because the elementary
    symmetric sum is well conditioned.
    """

    seeds = np.roots(np.polyder(np.poly(np.asarray(roots, dtype=np.complex128))))
    remaining = list(seeds)
    collapsed: list[complex] = []
    while remaining:
        head = remaining.pop(0)
        cluster = [head]
        rest = []
        for point in remaining:
            if abs(point - head) < CRITICAL_CLUSTER_TOLERANCE:
                cluster.append(point)
            else:
                rest.append(point)
        remaining = rest
        collapsed.append(complex(np.mean(cluster)))
    return np.asarray(collapsed, dtype=np.complex128)


def hub_rows(roots: Sequence[complex], digits: int = 0) -> list[dict[str, Any]]:
    """Per-critical-point containment report, float or mpmath."""

    seeds = critical_points(roots)
    if digits and mp is not None:
        previous = mp.mp.dps
        mp.mp.dps = digits
        try:
            mroots = [mp.mpc(complex(r).real, complex(r).imag) for r in roots]
            points = mp_critical_points(mroots, seeds)
            rows = []
            for point in points:
                value = mp.mpf(1)
                for root in mroots:
                    value *= abs(point - root)
                row: dict[str, Any] = {
                    "critical_point": [float(mp.re(point)), float(mp.im(point))],
                    "critical_value_modulus": float(value),
                    "admissible": bool(value < 1),
                }
                if row["admissible"]:
                    sub, opn, dist = [], [], []
                    for index, root in enumerate(mroots):
                        maximum = mp_segment_max_abs(mroots, point, root)
                        dist.append(float(abs(root - point)))
                        if maximum <= value:
                            sub.append(index)
                        if maximum < 1:
                            opn.append(index)
                    row["sublevel_indices"] = sub
                    row["open_indices"] = opn
                    row["distances"] = dist
                rows.append(row)
            return rows
        finally:
            mp.mp.dps = previous

    rows = []
    for point in seeds:
        value = float(abs(np.prod(np.asarray(roots, dtype=np.complex128) - point)))
        row = {
            "critical_point": [float(point.real), float(point.imag)],
            "critical_value_modulus": value,
            "admissible": bool(value < 1.0),
        }
        if row["admissible"]:
            sub, opn, dist = [], [], []
            for index, root in enumerate(roots):
                maximum = segment_max_abs(roots, complex(point), complex(root))
                dist.append(float(abs(root - point)))
                if maximum <= value:
                    sub.append(index)
                if maximum < 1.0:
                    opn.append(index)
            row["sublevel_indices"] = sub
            row["open_indices"] = opn
            row["distances"] = dist
        rows.append(row)
    return rows


def best_pair_length(row: dict[str, Any], key: str) -> float | None:
    indices = row.get(key)
    if not indices or len(indices) < 2:
        return None
    lengths = sorted(row["distances"][i] for i in indices)
    return lengths[0] + lengths[1]


def normalised_quartic_sweep(grid: int, radius: float,
                             centre: tuple[complex, complex] | None = None) -> dict[str, Any]:
    """Complete grid sweep of ``P(w) = w^4 + a3 w^3 + a2 w^2 + 1`` under minimality.

    Minimality of the hub's critical value is exactly ``|P(kappa)| >= 1`` at the
    two other critical points, the roots of ``4w^2 + 3 a3 w + 2 a2``.  This is
    the degree-four analogue of the cubic's ``|1 + 4 s^3 / 27| >= 1``.

    Note the parameter count: pinning ``P(0) = 1`` already quotients out the
    plane rotation (the normalisation ``alpha^n = f(c)`` is rotation-equivariant),
    so ``(a3, a2)`` is **four** real parameters modulo a group of order four --
    not three.  A grid over four real dimensions is evidence, never a proof.
    """

    axis = np.linspace(-radius, radius, grid)
    admissible = 0
    centre3 = centre[0] if centre else 0.0 + 0.0j
    centre2 = centre[1] if centre else 0.0 + 0.0j
    worst_second_modulus = 0.0
    worst_second_at: list[float] = []
    worst_sublevel_count = 4
    worst_sublevel_at: list[float] = []
    two_small_failures = 0
    sublevel_failures = 0
    worst_pair_sum = 0.0
    for re3 in axis:
        for im3 in axis:
            a3 = centre3 + complex(re3, im3)
            for re2 in axis:
                for im2 in axis:
                    a2 = centre2 + complex(re2, im2)
                    quad = np.array([4.0 + 0j, 3.0 * a3, 2.0 * a2])
                    kappa = np.roots(quad) if abs(a2) > 0 or abs(a3) > 0 else np.array([0j, 0j])
                    poly = np.array([1.0 + 0j, a3, a2, 0.0 + 0j, 1.0 + 0j])
                    ok = True
                    for point in kappa:
                        if abs(np.polyval(poly, point)) < 1.0 - 1e-12:
                            ok = False
                            break
                    if not ok:
                        continue
                    admissible += 1
                    w = np.roots(poly)
                    moduli = np.sort(np.abs(w))
                    if moduli[1] > worst_second_modulus:
                        worst_second_modulus = float(moduli[1])
                        worst_second_at = [re3, im3, re2, im2]
                    if moduli[1] > 1.0:
                        two_small_failures += 1
                    pair = float(moduli[0] + moduli[1])
                    worst_pair_sum = max(worst_pair_sum, pair)
                    # sublevel containment on each spoke, exactly
                    contained = 0
                    for root in w:
                        if segment_max_abs(w, 0.0 + 0j, complex(root)) <= 1.0 + 1e-12:
                            contained += 1
                    if contained < worst_sublevel_count:
                        worst_sublevel_count = contained
                        worst_sublevel_at = [re3, im3, re2, im2]
                    if contained < 2:
                        sublevel_failures += 1
    return {
        "grid_points_per_axis": grid,
        "parameter_box_radius": radius,
        "box_centre_a3": [centre3.real, centre3.imag],
        "box_centre_a2": [centre2.real, centre2.imag],
        "real_parameter_count": 4,
        "admissible_parameters": admissible,
        "max_second_smallest_root_modulus": worst_second_modulus,
        "max_second_smallest_at_a3_a2": worst_second_at,
        "configurations_with_second_modulus_above_one": two_small_failures,
        "two_small_roots_lemma_survives": two_small_failures == 0,
        "min_sublevel_contained_spokes": worst_sublevel_count,
        "min_sublevel_at_a3_a2": worst_sublevel_at,
        "configurations_with_fewer_than_two_sublevel_spokes": sublevel_failures,
        "sublevel_mechanism_survives": sublevel_failures == 0,
        "max_sum_of_two_smallest_root_moduli": worst_pair_sum,
    }


def normalise_at_hub(roots: Sequence[complex], hub: complex) -> dict[str, Any]:
    """Send the hub to ``0`` and the critical value to ``1``.

    With ``u_k = z_k - c`` and ``e_j`` the elementary symmetric functions of the
    ``u_k``, a critical point is exactly ``e_3 = 0`` and ``f(c) = e_4``.  Taking
    ``alpha^4 = e_4`` gives ``P(w) = f(c + alpha w)/f(c) = w^4 + a_3 w^3 + a_2 w^2 + 1``
    with ``a_3 = -e_1/alpha`` and ``a_2 = e_2/alpha^2``.

    The plane rotation is already quotiented out: under ``z -> e^{i th} z`` the
    pair ``(a_3, a_2)`` is invariant, because ``alpha`` rotates with it.  So the
    normalised parameter space is **four** real dimensions modulo the order-four
    group ``(a_3, a_2) -> (zeta a_3, zeta^2 a_2)``, ``zeta^4 = 1`` -- not three.
    """

    u = np.asarray([complex(z) - complex(hub) for z in roots], dtype=np.complex128)
    e1 = complex(np.sum(u))
    e2 = complex(sum(u[i] * u[j] for i in range(4) for j in range(i + 1, 4)))
    e3 = complex(
        sum(u[i] * u[j] * u[k] for i in range(4) for j in range(i + 1, 4) for k in range(j + 1, 4))
    )
    e4 = complex(np.prod(u))
    alpha = e4 ** 0.25
    a3 = -e1 / alpha
    a2 = e2 / (alpha * alpha)
    poly = np.array([1.0 + 0j, a3, a2, 0.0 + 0j, 1.0 + 0j])
    w = np.roots(poly)
    kappa = np.roots(np.array([4.0 + 0j, 3.0 * a3, 2.0 * a2]))
    sublevel = [
        int(i)
        for i, root in enumerate(w)
        if segment_max_abs(w, 0.0 + 0j, complex(root)) <= 1.0 + 1e-9
    ]
    moduli = np.sort(np.abs(w))
    return {
        "hub": [complex(hub).real, complex(hub).imag],
        "critical_value_modulus": float(abs(e4)),
        "critical_point_residual_e3": float(abs(e3)),
        "a3": [a3.real, a3.imag],
        "a2": [a2.real, a2.imag],
        "abs_a3": float(abs(a3)),
        "abs_a2": float(abs(a2)),
        "other_critical_values_of_P": [float(abs(np.polyval(poly, k))) for k in kappa],
        "minimality_holds": bool(
            all(abs(np.polyval(poly, k)) >= 1.0 - 1e-12 for k in kappa)
        ),
        "normalised_root_moduli": [float(m) for m in moduli],
        "two_roots_in_closed_unit_disk": bool(moduli[1] <= 1.0 + 1e-12),
        "sum_of_two_smallest_moduli": float(moduli[0] + moduli[1]),
        "sublevel_contained_spokes": sublevel,
        "sublevel_mechanism_available": bool(len(sublevel) >= 2),
    }


SUBLEVEL_TOLERANCE = 1e-12


def monte_carlo_sublevel_failure_rate(samples: int, seed: int) -> dict[str, Any]:
    """Measure of the set where the sublevel two-spoke mechanism fails at n = 4.

    The condition tested is the sharp one, not the crude ``|w| <= 1``:

        at the minimal hub, two roots have ``max_t |P(tw)| <= 1``
        and the sum of their moduli is at most two.

    That is sufficient for #1041 at the hub -- containment gives ``|f| <= |f(c)| < 1``
    and the two spokes total ``|f(c)|^{1/4}(|w_1| + |w_2|) < 2``.

    **Tolerance is load bearing.** ``P(0) = 1``, so the spoke maximum is ``>= 1``
    identically and a contained spoke reads as exactly ``1``.  A zero-tolerance
    test therefore reports every contained spoke as a failure; a first run of
    this probe did exactly that and inflated the rate.  Anything landing in
    ``(1, 1 + 1e-8)`` is counted separately as borderline.
    """

    rng = np.random.default_rng(seed)
    rows: list[dict[str, Any]] = []
    for scale, label in ((1.5, "wide"), (0.7, "medium"), (0.2, "narrow")):
        minimal = failures = borderline = 0
        example: dict[str, Any] | None = None
        for _ in range(samples):
            a3 = scale * complex(rng.standard_normal(), rng.standard_normal())
            a2 = scale * complex(rng.standard_normal(), rng.standard_normal())
            poly = np.array([1.0 + 0j, a3, a2, 0.0 + 0j, 1.0 + 0j])
            kappa = np.roots(np.array([4.0 + 0j, 3.0 * a3, 2.0 * a2]))
            if not all(abs(np.polyval(poly, k)) >= 1.0 - 1e-12 for k in kappa):
                continue
            minimal += 1
            w = np.roots(poly)
            maxima = [segment_max_abs(w, 0.0 + 0j, complex(root)) for root in w]
            if any(1.0 + SUBLEVEL_TOLERANCE < m < 1.0 + 1e-8 for m in maxima):
                borderline += 1
            contained = [i for i, m in enumerate(maxima) if m <= 1.0 + SUBLEVEL_TOLERANCE]
            if len(contained) >= 2:
                smallest = sorted(abs(w[i]) for i in contained)
                if smallest[0] + smallest[1] <= 2.0:
                    continue
            failures += 1
            if example is None:
                example = {
                    "a3": [a3.real, a3.imag],
                    "a2": [a2.real, a2.imag],
                    "spoke_maxima": [float(m) for m in maxima],
                    "root_moduli": [float(abs(x)) for x in w],
                    "other_critical_values": [float(abs(np.polyval(poly, k))) for k in kappa],
                }
        rows.append(
            {
                "label": label,
                "gaussian_scale": scale,
                "samples": samples,
                "minimal_hub_configurations": minimal,
                "condition_failures": failures,
                "failure_rate_percent": 100.0 * failures / max(1, minimal),
                "borderline_spokes": borderline,
                "example_failure": example,
            }
        )
    return {
        "condition": (
            "two roots with max_t |P(tw)| <= 1 and |w_1| + |w_2| <= 2, "
            "at the least-critical-value hub of P(w) = w^4 + a3 w^3 + a2 w^2 + 1"
        ),
        "rows": rows,
        "condition_holds_always": all(row["condition_failures"] == 0 for row in rows),
    }


def run_sublevel(grid: int, samples: int = 40000, seed: int = 20260823) -> dict[str, Any]:
    roots = witness_roots()
    float_rows = hub_rows(roots)
    exact_rows = hub_rows(roots, digits=60) if mp is not None else float_rows
    admissible = [row for row in exact_rows if row["admissible"]]
    payload = {
        "witness_roots_strictly_inside_unit_disk": witness_roots_strictly_inside(),
        "witness_source": "StraightSpokeHubCriterionLab.md section 2 / negative result 13",
        "hubs": [
            {
                "critical_value_modulus": row["critical_value_modulus"],
                "admissible": row["admissible"],
                "sublevel_contained": row.get("sublevel_indices"),
                "open_contained": row.get("open_indices"),
                "sublevel_best_pair_length": best_pair_length(row, "sublevel_indices"),
                "open_best_pair_length": best_pair_length(row, "open_indices"),
            }
            for row in exact_rows
        ],
        "max_sublevel_spokes_at_any_admissible_hub": max(
            (len(row.get("sublevel_indices", [])) for row in admissible), default=0
        ),
        "sublevel_identity_route_dead_at_degree_four": all(
            len(row.get("sublevel_indices", [])) < 2 for row in admissible
        ),
        "open_route_survives_on_this_witness": all(
            len(row.get("open_indices", [])) >= 2 for row in admissible
        ),
        "open_best_pair_length": min(
            (
                value
                for value in (best_pair_length(row, "open_indices") for row in admissible)
                if value is not None
            ),
            default=None,
        ),
        "float_and_60_digit_agree": [
            round(a["critical_value_modulus"], 9) == round(b["critical_value_modulus"], 9)
            for a, b in zip(sorted(float_rows, key=lambda r: r["critical_value_modulus"]),
                            sorted(exact_rows, key=lambda r: r["critical_value_modulus"]))
        ],
    }
    payload["witness_normalised_at_each_admissible_hub"] = [
        normalise_at_hub(roots, complex(row["critical_point"][0], row["critical_point"][1]))
        for row in exact_rows
        if row["admissible"]
    ]
    payload["monte_carlo_failure_measure"] = monte_carlo_sublevel_failure_rate(samples, seed)
    payload["normalised_parameter_sweep_bulk"] = normalised_quartic_sweep(grid, radius=3.0)
    payload["normalised_parameter_sweep_near_origin"] = normalised_quartic_sweep(
        grid, radius=0.02
    )
    minimal = min(
        payload["witness_normalised_at_each_admissible_hub"],
        key=lambda row: row["critical_value_modulus"],
    )
    centre = (complex(*minimal["a3"]), complex(*minimal["a2"]))
    payload["normalised_parameter_sweep_at_the_witness"] = [
        normalised_quartic_sweep(grid, radius=box, centre=centre)
        for box in (1e-1, 1e-2, 1e-3)
    ]
    bulk = payload["normalised_parameter_sweep_bulk"]
    fine = payload["normalised_parameter_sweep_near_origin"]
    witness_kills = any(
        not row["sublevel_mechanism_available"]
        for row in payload["witness_normalised_at_each_admissible_hub"]
    )
    payload["sweep_verdict"] = (
        "Both grids report the sublevel mechanism surviving "
        f"(bulk failures {bulk['configurations_with_fewer_than_two_sublevel_spokes']}, "
        f"near-origin failures {fine['configurations_with_fewer_than_two_sublevel_spokes']}), "
        "and the exact witness normalised into the same coordinates "
        f"{'DOES' if witness_kills else 'does NOT'} refute it.  A grid that misses a "
        "known counterexample is not evidence; this is the corpus's own recorded "
        "failure mode reproduced on purpose."
    )
    return payload


# --------------------------------------------------------------------------
# mode: pendyala -- independent verification of the degree-four theorem
# --------------------------------------------------------------------------


def minimum_enclosing_disk(points: Sequence[complex]) -> tuple[complex, float]:
    """Exact MEC of at most four points by the two/three point construction."""

    pts = [complex(p) for p in points]
    best: tuple[complex, float] | None = None

    def covers(centre: complex, radius: float) -> bool:
        return all(abs(p - centre) <= radius + 1e-12 for p in pts)

    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            centre = (pts[i] + pts[j]) / 2.0
            radius = abs(pts[i] - pts[j]) / 2.0
            if covers(centre, radius) and (best is None or radius < best[1]):
                best = (centre, radius)
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            for k in range(j + 1, len(pts)):
                a, b, c = pts[i], pts[j], pts[k]
                d = 2.0 * (
                    a.real * (b.imag - c.imag)
                    + b.real * (c.imag - a.imag)
                    + c.real * (a.imag - b.imag)
                )
                if abs(d) < 1e-15:
                    continue
                ux = (
                    (abs(a) ** 2) * (b.imag - c.imag)
                    + (abs(b) ** 2) * (c.imag - a.imag)
                    + (abs(c) ** 2) * (a.imag - b.imag)
                ) / d
                uy = (
                    (abs(a) ** 2) * (c.real - b.real)
                    + (abs(b) ** 2) * (a.real - c.real)
                    + (abs(c) ** 2) * (b.real - a.real)
                ) / d
                centre = complex(ux, uy)
                radius = abs(a - centre)
                if covers(centre, radius) and (best is None or radius < best[1]):
                    best = (centre, radius)
    assert best is not None
    return best


def radial_arm_maxima(w: Sequence[complex]) -> list[float]:
    """``M_i = max_(0<=t<=1) prod_k |t w_i - w_k|`` for each ``i``."""

    return [segment_max_product(w, 0.0 + 0j, complex(w[i])) for i in range(len(w))]


def four_point_lemma_score(w: Sequence[complex]) -> float:
    """Second-smallest ``M_i``.  Pendyala's Lemma 1 says this is ``<= 1``."""

    return float(sorted(radial_arm_maxima(w))[1])


def separation(w: Sequence[complex]) -> float:
    return min(abs(w[i] - w[j]) for i in range(len(w)) for j in range(i + 1, len(w)))


def _lemma_objective(vector: np.ndarray) -> float:
    """Penalised objective: maximise the lemma's quantity subject to the hypotheses."""

    radii = np.clip(vector[:4], 0.0, 1.0)
    angles = vector[4:]
    w = [complex(radii[0], 0.0)] + [
        radii[k] * cmath.exp(1j * float(angles[k - 1])) for k in range(1, 4)
    ]
    gap = separation(w)
    penalty = 50.0 * max(0.0, 1.0 - gap)
    return four_point_lemma_score(w) - penalty


def attack_four_point_lemma(trials: int, steps: int, seed: int) -> dict[str, Any]:
    rng = np.random.default_rng(seed)
    best_score = -math.inf
    best_vector: np.ndarray | None = None
    for _ in range(trials):
        vector = np.concatenate(
            [rng.uniform(0.0, 1.0, 4), rng.uniform(0.0, 2.0 * math.pi, 3)]
        )
        score = _lemma_objective(vector)
        scale = 0.35
        for _ in range(steps):
            candidate = vector + rng.normal(0.0, scale, vector.size)
            candidate[:4] = np.clip(candidate[:4], 0.0, 1.0)
            value = _lemma_objective(candidate)
            if value > score:
                score, vector = value, candidate
            else:
                scale *= 0.985
        if score > best_score:
            best_score, best_vector = score, vector
    assert best_vector is not None
    radii = np.clip(best_vector[:4], 0.0, 1.0)
    angles = best_vector[4:]
    w = [complex(radii[0], 0.0)] + [
        radii[k] * cmath.exp(1j * float(angles[k - 1])) for k in range(1, 4)
    ]
    return {
        "restarts": trials,
        "steps_per_restart": steps,
        "best_penalised_score": best_score,
        "best_configuration": [[z.real, z.imag] for z in w],
        "best_separation": separation(w),
        "best_second_smallest_arm_max": four_point_lemma_score(w),
        "hypothesis_satisfied": separation(w) >= 1.0 - 1e-12,
        "lemma_violated": bool(separation(w) >= 1.0 - 1e-12 and four_point_lemma_score(w) > 1.0 + 1e-9),
    }


def sweep_four_point_lemma_boundary(grid: int) -> dict[str, Any]:
    """Structured sweep of the tight case: all four points on the unit circle.

    On ``|w| = 1`` the separation hypothesis ``|w_i - w_j| >= 1`` is exactly a
    pairwise angular gap of at least ``pi/3``.  Rotation fixes the first point,
    so this is a complete three-angle grid.
    """

    worst = -math.inf
    worst_config: list[list[float]] = []
    tested = 0
    violations = 0
    lower = math.pi / 3.0
    for i in range(grid):
        b = lower + (2.0 * math.pi - 3.0 * lower) * i / max(1, grid - 1)
        for j in range(grid):
            c = b + lower + (2.0 * math.pi - b - 2.0 * lower) * j / max(1, grid - 1)
            if c <= b:
                continue
            for k in range(grid):
                d = c + lower + (2.0 * math.pi - c - lower) * k / max(1, grid - 1)
                if d <= c or d >= 2.0 * math.pi:
                    continue
                w = [
                    complex(1.0, 0.0),
                    cmath.exp(1j * b),
                    cmath.exp(1j * c),
                    cmath.exp(1j * d),
                ]
                if separation(w) < 1.0 - 1e-12:
                    continue
                tested += 1
                score = four_point_lemma_score(w)
                if score > worst:
                    worst = score
                    worst_config = [[z.real, z.imag] for z in w]
                if score > 1.0 + 1e-9:
                    violations += 1
    return {
        "grid": grid,
        "configurations_tested": tested,
        "max_second_smallest_arm_max": worst if worst > -math.inf else None,
        "worst_configuration": worst_config,
        "violations": violations,
        "lemma_survives": violations == 0,
    }


def pendyala_path(roots: Sequence[complex]) -> dict[str, Any] | None:
    """Build the path Pendyala's proof produces, and certify it exactly."""

    n = len(roots)
    # Case 1: a close pair.
    best_close = None
    for i in range(n):
        for j in range(i + 1, n):
            gap = abs(roots[i] - roots[j])
            if gap < 1.0 and (best_close is None or gap < best_close[0]):
                best_close = (gap, i, j)
    if best_close is not None:
        _, i, j = best_close
        maximum = segment_max_abs(roots, complex(roots[i]), complex(roots[j]))
        return {
            "branch": "close_pair_chord",
            "indices": [i, j],
            "length": float(abs(roots[i] - roots[j])),
            "path_max_abs_f": float(maximum),
            "contained": bool(maximum < 1.0),
        }
    # Case 2: MEC + two safe radial arms.
    q, R = minimum_enclosing_disk(roots)
    w = [(complex(z) - q) / R for z in roots]
    maxima = radial_arm_maxima(w)
    safe = [i for i, value in enumerate(maxima) if value <= 1.0 + 1e-12]
    if len(safe) < 2:
        return {
            "branch": "mec_radial",
            "lemma_failed": True,
            "arm_maxima": [float(v) for v in maxima],
            "separation": float(separation(w)),
        }
    # Select by the arm maximum, NOT by |w_i|.  Lemma 1 promises two safe arms,
    # not that the two shortest arms are the safe ones: on the unit circle every
    # |w_i| is exactly 1, so a |w_i| tie-break picks arbitrarily and lands on the
    # unsafe pair.  That bug produced a 5e-13 "violation" of the theorem on a
    # 1e-9 angular perturbation of the 4-gon, which survived a 60-digit re-run
    # because the arithmetic was right and the *selection* was wrong.
    order = sorted(safe, key=lambda i: maxima[i])
    i, j = order[0], order[1]
    max_i = segment_max_abs(roots, complex(roots[i]), q)
    max_j = segment_max_abs(roots, q, complex(roots[j]))
    length = float(abs(roots[i] - q) + abs(roots[j] - q))
    maximum = float(max(max_i, max_j))
    return {
        "branch": "mec_radial",
        "indices": [i, j],
        "mec_centre": [q.real, q.imag],
        "mec_radius": float(R),
        "length": length,
        "path_max_abs_f": maximum,
        "contained": bool(maximum < 1.0),
        "safe_arm_count": len(safe),
    }


def _random_quartic(rng: np.random.Generator, style: str) -> np.ndarray:
    if style == "near_fekete":
        eps = 10.0 ** rng.uniform(-9.0, -2.0)
        r = 1.0 - eps
        scale = 10.0 ** rng.uniform(-9.0, -2.0)
        angles = 2.0 * math.pi * np.arange(4) / 4.0 + scale * rng.normal(0.0, 1.0, 4)
        radii = r * (1.0 + scale * rng.normal(0.0, 1.0, 4))
        radii = np.clip(radii, 0.0, 1.0 - 1e-15)
        return radii * np.exp(1j * angles)
    if style == "boundary":
        r = 1.0 - 10.0 ** rng.uniform(-12.0, -3.0)
        return r * np.exp(1j * rng.uniform(0.0, 2.0 * math.pi, 4))
    radii = rng.uniform(0.0, 1.0, 4) ** 0.5
    return radii * np.exp(1j * rng.uniform(0.0, 2.0 * math.pi, 4))


def _reverify_path_high_precision(roots: Sequence[complex], result: dict[str, Any],
                                  digits: int = 60) -> dict[str, Any]:
    """Recompute a reported violation at ``digits`` decimals.

    This directory has six recorded occasions on which a float reading was the
    instrument rather than the mathematics.  Any failure is re-run before it is
    counted.
    """

    if mp is None:
        return {"reverified": False, "reason": "mpmath unavailable"}
    previous = mp.mp.dps
    mp.mp.dps = digits
    try:
        mroots = [mp.mpc(complex(z).real, complex(z).imag) for z in roots]
        max_modulus = max(abs(z) for z in mroots)
        if result["branch"] == "close_pair_chord":
            i, j = result["indices"]
            worst = mp_segment_max_abs(mroots, mroots[i], mroots[j])
            length = abs(mroots[i] - mroots[j])
        else:
            i, j = result["indices"]
            q = mp.mpc(result["mec_centre"][0], result["mec_centre"][1])
            worst = max(
                mp_segment_max_abs(mroots, mroots[i], q),
                mp_segment_max_abs(mroots, q, mroots[j]),
            )
            length = abs(mroots[i] - q) + abs(mroots[j] - q)
        return {
            "reverified": True,
            "decimal_digits": digits,
            "max_root_modulus": float(max_modulus),
            "roots_strictly_inside": bool(max_modulus < 1),
            "path_max_abs_f": float(worst),
            "path_length": float(length),
            "still_violates": bool(max_modulus < 1 and (worst >= 1 or length >= 2)),
        }
    finally:
        mp.mp.dps = previous


def verify_pendyala_theorem(trials: int, seed: int) -> dict[str, Any]:
    rng = np.random.default_rng(seed)
    worst_length = 0.0
    worst_max = 0.0
    worst_length_config: list[list[float]] = []
    worst_max_config: list[list[float]] = []
    float_failures = 0
    confirmed_failures = 0
    reverifications: list[dict[str, Any]] = []
    lemma_failures = 0
    counts = {"close_pair_chord": 0, "mec_radial": 0}
    for index in range(trials):
        style = ("uniform", "boundary", "near_fekete")[index % 3]
        roots = _random_quartic(rng, style)
        if np.max(np.abs(roots)) >= 1.0:
            continue
        result = pendyala_path(roots)
        if result is None:
            continue
        if result.get("lemma_failed"):
            lemma_failures += 1
            continue
        counts[result["branch"]] = counts.get(result["branch"], 0) + 1
        if result["length"] > worst_length:
            worst_length = result["length"]
            worst_length_config = [[z.real, z.imag] for z in roots]
        if result["path_max_abs_f"] > worst_max:
            worst_max = result["path_max_abs_f"]
            worst_max_config = [[z.real, z.imag] for z in roots]
        if not result["contained"] or result["length"] >= 2.0:
            float_failures += 1
            row = _reverify_path_high_precision(roots, result)
            row["float_path_max_abs_f"] = result["path_max_abs_f"]
            row["float_path_length"] = result["length"]
            row["branch"] = result["branch"]
            if len(reverifications) < 12:
                reverifications.append(row)
            if row.get("still_violates"):
                confirmed_failures += 1
    return {
        "configurations": trials,
        "branch_counts": counts,
        "lemma_failures": lemma_failures,
        "max_path_length": worst_length,
        "max_path_length_configuration": worst_length_config,
        "max_abs_f_on_path": worst_max,
        "max_abs_f_configuration": worst_max_config,
        "float_failures": float_failures,
        "failures_confirmed_at_60_digits": confirmed_failures,
        "reverifications": reverifications,
        "theorem_verified_on_sample": confirmed_failures == 0 and lemma_failures == 0,
        "note": (
            "Float failures at max root modulus within 1e-12 of one are precision "
            "artifacts: the theorem's own bounds there are |f| <= R^4 and length "
            "2R with R = 1 - O(1e-15), so double precision cannot separate them "
            "from the threshold.  Each is re-run at 60 decimal digits."
        ),
    }


def run_pendyala(trials: int, restarts: int, steps: int, grid: int, seed: int) -> dict[str, Any]:
    return {
        "paper": "V. S. Pendyala, A Degree-Four Lemniscate Path Theorem, arXiv:2606.24875 (23 Jun 2026)",
        "local_copy": "annexes/arxiv-2606-24875-erdos1041-quartic-lemniscate-path/extracted.md",
        "lemma_adversarial": attack_four_point_lemma(restarts, steps, seed),
        "lemma_boundary_sweep": sweep_four_point_lemma_boundary(grid),
        "theorem_end_to_end": verify_pendyala_theorem(trials, seed + 1),
    }


# --------------------------------------------------------------------------
# mode: hubsweep -- the OPEN criterion at degree four
# --------------------------------------------------------------------------


def quartic_qc(roots: Sequence[complex], key: str = "open_indices") -> float:
    """``QC`` restricted to degree four: ``inf`` when no admissible hub has a pair."""

    best = math.inf
    for row in hub_rows(roots):
        if not row["admissible"]:
            continue
        value = best_pair_length(row, key)
        if value is not None:
            best = min(best, value)
    return best


def _qc_objective(vector: np.ndarray, key: str) -> float:
    radii = np.clip(np.abs(vector[:4]), 0.0, 1.0 - 1e-12)
    roots = radii * np.exp(1j * vector[4:])
    value = quartic_qc(roots, key)
    return 4.0 if math.isinf(value) else value


def attack_qc(restarts: int, steps: int, seed: int, key: str) -> dict[str, Any]:
    rng = np.random.default_rng(seed)
    best_score = -math.inf
    best_roots: np.ndarray | None = None
    infinite_hits = 0
    for trial in range(restarts):
        style = ("uniform", "boundary", "near_fekete")[trial % 3]
        roots = _random_quartic(rng, style)
        vector = np.concatenate([np.abs(roots), np.angle(roots)])
        score = _qc_objective(vector, key)
        scale = 0.2 if style == "uniform" else 1e-3
        for _ in range(steps):
            candidate = vector + rng.normal(0.0, scale, vector.size)
            candidate[:4] = np.clip(np.abs(candidate[:4]), 0.0, 1.0 - 1e-12)
            value = _qc_objective(candidate, key)
            if value > score:
                score, vector = value, candidate
            else:
                scale *= 0.99
        if score >= 4.0 - 1e-9:
            infinite_hits += 1
        if score > best_score:
            best_score = score
            radii = np.clip(np.abs(vector[:4]), 0.0, 1.0 - 1e-12)
            best_roots = radii * np.exp(1j * vector[4:])
    assert best_roots is not None
    return {
        "criterion": key,
        "restarts": restarts,
        "steps_per_restart": steps,
        "max_QC_found": best_score,
        "mechanism_death_hits": infinite_hits,
        "best_roots": [[z.real, z.imag] for z in best_roots],
        "best_max_root_modulus": float(np.max(np.abs(best_roots))),
        "crosses_two": bool(best_score >= 2.0 and best_score < 4.0 - 1e-9),
        "pinned_below_two": bool(best_score < 2.0),
    }


def near_fekete_sweep(scales: Sequence[float], radii: Sequence[float], seed: int,
                      per_cell: int) -> dict[str, Any]:
    """Deterministic perturbation of ``z^4 - r^4``, the family the corpus calls hard."""

    rng = np.random.default_rng(seed)
    rows: list[dict[str, Any]] = []
    worst_open = -math.inf
    worst_sub = -math.inf
    open_deaths = 0
    sub_deaths = 0
    total = 0
    for r in radii:
        for scale in scales:
            cell_open = -math.inf
            cell_sub = -math.inf
            for _ in range(per_cell):
                angles = 2.0 * math.pi * np.arange(4) / 4.0 + scale * rng.normal(0.0, 1.0, 4)
                moduli = np.clip(r * (1.0 + scale * rng.normal(0.0, 1.0, 4)), 0.0, 1.0 - 1e-15)
                roots = moduli * np.exp(1j * angles)
                total += 1
                value_open = quartic_qc(roots, "open_indices")
                value_sub = quartic_qc(roots, "sublevel_indices")
                if math.isinf(value_open):
                    open_deaths += 1
                else:
                    cell_open = max(cell_open, value_open)
                if math.isinf(value_sub):
                    sub_deaths += 1
                else:
                    cell_sub = max(cell_sub, value_sub)
            rows.append(
                {
                    "radius": r,
                    "perturbation_scale": scale,
                    "max_open_QC": None if cell_open == -math.inf else cell_open,
                    "max_sublevel_QC": None if cell_sub == -math.inf else cell_sub,
                }
            )
            worst_open = max(worst_open, cell_open)
            worst_sub = max(worst_sub, cell_sub)
    return {
        "configurations": total,
        "rows": rows,
        "max_open_QC": None if worst_open == -math.inf else worst_open,
        "max_sublevel_QC": None if worst_sub == -math.inf else worst_sub,
        "open_mechanism_deaths": open_deaths,
        "sublevel_mechanism_deaths": sub_deaths,
        "open_mechanism_survives_at_degree_four": open_deaths == 0,
    }


def max_open_spokes_at_any_hub(roots: Sequence[complex]) -> int:
    """``max`` over admissible hubs of the number of open-contained spokes.

    The mechanism is *dead* at a configuration when this is at most one -- that
    is exactly how ``StraightSpokeHubCriterionLab.md`` §3's degree-six and
    degree-nine witnesses kill it.  ``-1`` means no admissible hub at all, which
    cannot happen for roots in the open disk (Fekete).
    """

    best = -1
    for row in hub_rows(roots):
        if row["admissible"]:
            best = max(best, len(row["open_indices"]))
    return best


def hunt_open_mechanism_death(restarts: int, steps: int, seed: int) -> dict[str, Any]:
    """Minimise the contained-spoke count directly, which is how §3 found its kills.

    §3's degree-6 and degree-9 witnesses were *not* found by maximising the
    length objective; they came from a differently seeded search that landed in
    another basin.  So the length attack above is re-run here as a **count**
    attack, seeded from the §2 quartic witness and from the near-Fekete shell.
    """

    rng = np.random.default_rng(seed)
    seeds: list[np.ndarray] = [witness_roots()]
    for scale in (1e-2, 1e-3, 1e-4, 1e-5, 1e-6, 1e-7, 1e-8):
        for radius in (0.99, 0.999, 1.0 - 1e-6, 1.0 - 1e-8):
            angles = 2.0 * math.pi * np.arange(4) / 4.0 + scale * rng.normal(0.0, 1.0, 4)
            moduli = np.clip(radius * (1.0 + scale * rng.normal(0.0, 1.0, 4)), 0.0, 1.0 - 1e-15)
            seeds.append(moduli * np.exp(1j * angles))
    while len(seeds) < restarts:
        seeds.append(_random_quartic(rng, "boundary"))

    def clamp(vector: np.ndarray) -> np.ndarray:
        radii = np.clip(np.abs(vector[:4]), 0.0, 1.0 - 1e-15)
        return radii * np.exp(1j * vector[4:])

    best_count = 99
    best_roots: np.ndarray | None = None
    for start in seeds[:restarts]:
        vector = np.concatenate([np.abs(start), np.angle(start)])
        count = max_open_spokes_at_any_hub(clamp(vector))
        scale = 1e-3
        for iteration in range(steps):
            candidate = vector + rng.normal(
                0.0, scale if iteration % 2 else scale * 1e-2, vector.size
            )
            value = max_open_spokes_at_any_hub(clamp(candidate))
            if 0 <= value < count:
                count, vector = value, candidate
            else:
                scale *= 0.995
        if 0 <= count < best_count:
            best_count, best_roots = count, clamp(vector)
    assert best_roots is not None
    rows = hub_rows(best_roots)
    return {
        "restarts": restarts,
        "steps_per_restart": steps,
        "minimum_contained_spoke_count_reached": best_count,
        "mechanism_dead": bool(best_count <= 1),
        "best_roots": [[z.real, z.imag] for z in best_roots],
        "best_max_root_modulus": float(np.max(np.abs(best_roots))),
        "hubs_at_best": [
            {
                "critical_value_modulus": row["critical_value_modulus"],
                "admissible": row["admissible"],
                "open_contained": row.get("open_indices"),
                "sublevel_contained": row.get("sublevel_indices"),
                "open_best_pair_length": best_pair_length(row, "open_indices"),
            }
            for row in rows
        ],
        "reading": (
            "Reaching exactly two and stopping is the boundary of the mechanism, "
            "not a proof that it cannot reach one.  At degrees six and nine the "
            "same count does reach one, and those witnesses live in a 1e-7-thin "
            "shell that a float search does not enter by itself."
        ),
    }


def run_hubsweep(restarts: int, steps: int, seed: int, per_cell: int) -> dict[str, Any]:
    return {
        "death_hunt": hunt_open_mechanism_death(restarts, steps, seed + 29),
        "quantity": (
            "QC = min over admissible critical points c of min over root pairs "
            "with both straight spokes contained, of |z_i - c| + |z_j - c|"
        ),
        "open_criterion_attack": attack_qc(restarts, steps, seed, "open_indices"),
        "sublevel_criterion_attack": attack_qc(restarts, steps, seed + 7, "sublevel_indices"),
        "near_fekete": near_fekete_sweep(
            scales=(1e-2, 1e-3, 1e-4, 1e-5, 1e-6, 1e-7),
            radii=(0.9, 0.99, 0.999, 1.0 - 1e-6),
            seed=seed + 13,
            per_cell=per_cell,
        ),
        "reading": (
            "A supremum pinned just below two is NOT survival; this directory has "
            "six recorded false pins.  'mechanism_death_hits' and "
            "'*_mechanism_deaths' count configurations where the mechanism has no "
            "pair at all, which is how the same mechanism dies at degrees six and nine."
        ),
    }


# --------------------------------------------------------------------------
# mode: premise -- the concurrent line's second-root witnesses, re-scaled
# --------------------------------------------------------------------------


def coordinator_witnesses() -> list[np.ndarray]:
    """Read ``SECOND_ROOT_FAILURE_WITNESSES`` from the sibling checker.

    Imported rather than retyped: the stored values are IEEE-754 hexadecimal
    literals and the nearest outsider sits only ``1.028`` from the unit circle.
    """

    import importlib.util
    import pathlib

    path = pathlib.Path(__file__).with_name("check_erdos1041_second_root_premise.py")
    spec = importlib.util.spec_from_file_location("_erdos1041_second_root_premise", path)
    if spec is None or spec.loader is None:  # pragma: no cover
        raise RuntimeError(f"cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return [module.witness_coefficients(entry) for entry in module.SECOND_ROOT_FAILURE_WITNESSES]


def rescale_normalised_witness(coefficients: np.ndarray, fill: float) -> dict[str, Any]:
    """Realise a normalised witness as an actual quartic with roots in the disk.

    A normalised ``P(w) = w^4 + a_3 w^3 + a_2 w^2 + 1`` does **not** determine a
    polynomial: the family ``f(z) = alpha^4 P(z/alpha + q)`` realises it for every
    ``alpha``, with roots ``z_k = alpha (w_k - q)``.  Placing ``q`` at the minimum
    enclosing centre of the normalised roots makes ``max_k |z_k| = alpha R_w``, so
    the open-disk hypothesis is exactly ``alpha < 1 / R_w``.

    This matters because the two containment tests scale differently.
    ``|P| <= 1`` (hub-sublevel) is scale free, but the criterion the target
    statement actually needs is ``|f| < 1``, i.e. ``|P| < alpha^{-4}``, which is
    **strictly weaker whenever ``R_w > 1``**.  A normalised witness therefore
    refutes the sublevel mechanism outright and says nothing about the open one
    until a scale is chosen.  ``fill`` is the fraction of the maximal radius used.
    """

    w = np.roots(coefficients)
    q, radius = minimum_enclosing_disk([complex(x) for x in w])
    alpha = fill / radius
    roots = np.asarray([alpha * (complex(x) - q) for x in w], dtype=np.complex128)
    rows = hub_rows(roots)
    admissible = [row for row in rows if row["admissible"]]
    open_pairs = [best_pair_length(row, "open_indices") for row in admissible]
    sub_pairs = [best_pair_length(row, "sublevel_indices") for row in admissible]
    open_pairs = [v for v in open_pairs if v is not None]
    sub_pairs = [v for v in sub_pairs if v is not None]
    kappa = np.roots(np.polyder(coefficients))
    return {
        "fill_fraction_of_maximal_radius": fill,
        "normalised_root_moduli": sorted(float(abs(x)) for x in w),
        "roots_in_closed_unit_disk_normalised": int(sum(1 for x in w if abs(x) <= 1.0)),
        "minimum_enclosing_radius_of_normalised_roots": float(radius),
        "other_critical_values_of_P": sorted(
            float(abs(np.polyval(coefficients, k))) for k in kappa if abs(k) > 1e-9
        ),
        "origin_is_minimal_hub": bool(
            all(abs(np.polyval(coefficients, k)) >= 1.0 - 1e-12 for k in kappa if abs(k) > 1e-9)
        ),
        "alpha": float(alpha),
        "max_root_modulus": float(np.max(np.abs(roots))),
        "roots_strictly_inside": bool(np.max(np.abs(roots)) < 1.0),
        "admissible_hub_count": len(admissible),
        "sublevel_spokes_per_admissible_hub": [
            len(row.get("sublevel_indices", [])) for row in admissible
        ],
        "open_spokes_per_admissible_hub": [
            len(row.get("open_indices", [])) for row in admissible
        ],
        "sublevel_mechanism_available": bool(sub_pairs),
        "open_mechanism_available": bool(open_pairs),
        "best_sublevel_pair_length": min(sub_pairs) if sub_pairs else None,
        "best_open_pair_length": min(open_pairs) if open_pairs else None,
        "open_pair_under_two": bool(open_pairs and min(open_pairs) < 2.0),
    }


def run_premise() -> dict[str, Any]:
    try:
        witnesses = coordinator_witnesses()
    except Exception as exc:  # pragma: no cover
        return {"status": "skipped", "reason": str(exc)}
    rows: list[dict[str, Any]] = []
    for index, coefficients in enumerate(witnesses):
        entry: dict[str, Any] = {"witness_index": index, "scales": []}
        for fill in (1.0 - 1e-12, 0.999, 0.99, 0.9, 0.5):
            entry["scales"].append(rescale_normalised_witness(coefficients, fill))
        entry["open_mechanism_at_every_scale"] = all(
            row["open_mechanism_available"] and row["open_pair_under_two"]
            for row in entry["scales"]
        )
        entry["sublevel_mechanism_at_any_scale"] = any(
            row["sublevel_mechanism_available"] for row in entry["scales"]
        )
        rows.append(entry)
    return {
        "source": "scripts/check_erdos1041_second_root_premise.py SECOND_ROOT_FAILURE_WITNESSES",
        "question": (
            "At the stored second-root-premise witnesses, does ANY admissible hub "
            "carry two contained spokes to ANY pair?"
        ),
        "witnesses": rows,
        "answer_open_criterion": all(row["open_mechanism_at_every_scale"] for row in rows),
        "answer_sublevel_criterion": any(row["sublevel_mechanism_at_any_scale"] for row in rows),
        "reading": (
            "A normalised (a3, a2) pair fixes no polynomial; the scale alpha is free "
            "and the open criterion |f| < 1 is |P| < alpha^{-4}, weaker than the "
            "scale-free sublevel test |P| <= 1 whenever the normalised minimum "
            "enclosing radius exceeds one.  So these witnesses refute the SUBLEVEL "
            "mechanism and must be re-scaled before they say anything about the OPEN one."
        ),
    }


# --------------------------------------------------------------------------
# selftest
# --------------------------------------------------------------------------


def run_selftest() -> dict[str, Any]:
    checks: list[dict[str, Any]] = []

    # z^3 - r^3: every chord escapes for r^3 > 8/9; radial spokes are safe.
    r = 0.99
    cubic = np.array([r * cmath.exp(2j * math.pi * k / 3) for k in range(3)])
    midpoint_value = abs(np.prod(cubic - (cubic[0] + cubic[1]) / 2.0))
    spoke_max = segment_max_abs(cubic, 0.0 + 0j, complex(cubic[0]))
    checks.append(
        {
            "name": "cubic_extremal_family",
            "midpoint_abs_f": float(midpoint_value),
            "midpoint_escapes": bool(midpoint_value > 1.0),
            "radial_spoke_max": float(spoke_max),
            "radial_spoke_max_equals_r_cubed": abs(spoke_max - r**3) < 1e-12,
            "pass": bool(midpoint_value > 1.0 and abs(spoke_max - r**3) < 1e-12),
        }
    )

    # z^4 - r^4 at the origin hub: all four spokes contained, best pair 2r.
    quartic = np.array([r * cmath.exp(1j * math.pi * k / 2) for k in range(4)])
    qc_open = quartic_qc(quartic, "open_indices")
    checks.append(
        {
            "name": "quartic_extremal_family",
            "open_QC": qc_open,
            "expected_2r": 2.0 * r,
            "critical_point_count_after_collapse": int(len(critical_points(quartic))),
            "pass": bool(abs(qc_open - 2.0 * r) < 1e-9 and len(critical_points(quartic)) == 1),
        }
    )

    # segment maximum against a dense scan on a random configuration
    rng = np.random.default_rng(11)
    roots = _random_quartic(rng, "uniform")
    exact = segment_max_abs(roots, complex(roots[0]), complex(roots[1]))
    ts = np.linspace(0.0, 1.0, 200001)
    pts = roots[0] + ts[:, None] * (roots[1] - roots[0])
    sampled = float(np.max(np.abs(np.prod(pts[:, :, None] - roots[None, None, :], axis=2))))
    checks.append(
        {
            "name": "segment_max_vs_dense_scan",
            "exact": float(exact),
            "dense_scan": sampled,
            "exact_dominates": bool(exact >= sampled - 1e-9),
            "pass": bool(exact >= sampled - 1e-9 and abs(exact - sampled) < 1e-5),
        }
    )

    # MEC of the unit square is the circumscribed circle
    square = [complex(1, 0), complex(0, 1), complex(-1, 0), complex(0, -1)]
    centre, radius = minimum_enclosing_disk(square)
    checks.append(
        {
            "name": "mec_unit_square",
            "centre": [centre.real, centre.imag],
            "radius": float(radius),
            "pass": bool(abs(centre) < 1e-12 and abs(radius - 1.0) < 1e-12),
        }
    )

    # Pendyala Lemma 1 on the regular 4-gon on the circle: separation sqrt(2) >= 1
    gon = [cmath.exp(1j * math.pi * k / 2) for k in range(4)]
    checks.append(
        {
            "name": "lemma_regular_square",
            "separation": float(separation(gon)),
            "arm_maxima": [float(v) for v in radial_arm_maxima(gon)],
            "second_smallest": float(four_point_lemma_score(gon)),
            "pass": bool(four_point_lemma_score(gon) <= 1.0 + 1e-12),
        }
    )

    return {"checks": checks, "pass": all(c["pass"] for c in checks)}


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------


ALL_MODES = ("selftest", "identity", "sublevel", "premise", "pendyala", "hubsweep")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--modes", nargs="*", default=list(ALL_MODES), choices=list(ALL_MODES))
    parser.add_argument("--trials", type=int, default=900)
    parser.add_argument("--restarts", type=int, default=60)
    parser.add_argument("--steps", type=int, default=220)
    parser.add_argument("--grid", type=int, default=13)
    parser.add_argument("--lemma-grid", type=int, default=34)
    parser.add_argument("--per-cell", type=int, default=24)
    parser.add_argument("--samples", type=int, default=40000)
    parser.add_argument("--seed", type=int, default=20260823)
    parser.add_argument("--output", type=str, default=None)
    args = parser.parse_args(list(argv) if argv is not None else None)

    payload: dict[str, Any] = {
        "problem": "erdos_1041",
        "degree": 4,
        "status_of_degree_four": "PROVED IN THE LITERATURE, NOT OPEN",
        "prior_art": {
            "citation": (
                "Venkata Siddharth Pendyala, A Degree-Four Lemniscate Path Theorem, "
                "arXiv:2606.24875, submitted 23 June 2026"
            ),
            "local_full_text": (
                "annexes/arxiv-2606-24875-erdos1041-quartic-lemniscate-path/extracted.md"
            ),
            "recorded_in_packet": [
                "negative_results[12]",
                "exact_results[17] adaptive_mec_chord_or_radial_counterexample",
                "AdaptiveMecDichotomyLab.md ('the complete quartic theorem')",
            ],
        },
    }

    if "selftest" in args.modes:
        payload["selftest"] = run_selftest()
        if not payload["selftest"]["pass"]:
            print(json.dumps(payload, indent=2, default=str))
            return 1
    if "identity" in args.modes:
        payload["identity"] = run_identity()
    if "sublevel" in args.modes:
        payload["sublevel"] = run_sublevel(args.grid, args.samples, args.seed)
    if "premise" in args.modes:
        payload["premise"] = run_premise()
    if "pendyala" in args.modes:
        payload["pendyala"] = run_pendyala(
            args.trials, args.restarts, args.steps, args.lemma_grid, args.seed
        )
    if "hubsweep" in args.modes:
        payload["hubsweep"] = run_hubsweep(args.restarts, args.steps, args.seed, args.per_cell)

    text = json.dumps(payload, indent=2, default=str)
    if args.output:
        with open(args.output, "w", encoding="utf-8") as handle:
            handle.write(text + "\n")
    print(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
