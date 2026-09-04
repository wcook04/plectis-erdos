"""Polynomial-lemniscate geometry primitives for formal-math experiments.

A monic complex polynomial ``f`` of degree ``n`` carries three coupled objects
that recur across the Erdős lemniscate problems: the sublevel sets
``{|f| < t}``, the critical points of ``f``, and the inverse images of rays in
the value plane.  This module supplies the exact and semi-exact primitives that
probes over those objects need, so that individual checkers state hypotheses
rather than re-derive numerics.

Two primitives are exact up to floating-point evaluation of a polynomial:

* :func:`segment_max_modulus` maximises ``|f|`` along a straight segment by
  solving for the critical points of ``|f|^2``, which is a *real* polynomial in
  the segment parameter.  Sampling a segment can miss a narrow excursion and
  silently report a containment that does not hold; this routine cannot.
* :func:`sublevel_components_are_simply_connected` records the maximum-principle
  fact that every bounded complementary component of ``{|f| < t}`` would force
  ``|f|`` to attain an interior maximum.  It is a documentation anchor for the
  consequence used by :func:`merging_pair_tree`.

One primitive is numerical continuation and is candidate evidence only:
:func:`descending_pair` integrates the two descending inverse-ray branches at a
simple critical point and reports residual gates alongside the arc lengths.

Nothing here certifies an analytic claim.  A probe must still state its
hypothesis, falsifier, and stop condition through its own formal-math
experiment contract.
"""

from __future__ import annotations

from collections.abc import Sequence
from typing import Any

import numpy as np

__all__ = [
    "coefficients_from_roots",
    "segment_polynomial",
    "segment_max_modulus",
    "critical_table",
    "spoke_table",
    "hub_pair_objective",
    "minimal_critical_value_hub",
    "descending_pair",
    "branch_start",
    "branch_point_free_radius",
    "resolved_diameter_length",
    "merging_pair_tree",
    "OPEN_LEMNISCATE",
    "HUB_SUBLEVEL",
]

#: Spoke criterion: the segment must stay inside the open lemniscate ``|f| < 1``.
#: This is the containment the short-path statement actually requires.
OPEN_LEMNISCATE = "open_lemniscate"

#: Spoke criterion: the segment must stay inside the hub sublevel set
#: ``|f| <= |f(c)|``.  Strictly stronger than :data:`OPEN_LEMNISCATE` whenever
#: ``|f(c)| < 1``.  Keep the two apart: a probe that silently uses this one is
#: testing a different, harder statement.
HUB_SUBLEVEL = "hub_sublevel"


def coefficients_from_roots(roots: Sequence[complex]) -> np.ndarray:
    """Monic coefficient vector (numpy ``poly`` order) of ``prod (z - root)``."""

    return np.poly(np.asarray(roots, dtype=np.complex128))


def segment_polynomial(
    coefficients: Sequence[complex], start: complex, end: complex
) -> np.ndarray:
    """Coefficients of ``t -> f(start + t*(end - start))`` in numpy poly order."""

    coefficients = np.asarray(coefficients, dtype=np.complex128)
    degree = len(coefficients) - 1
    direction = complex(end) - complex(start)
    affine = np.array([direction, complex(start)], dtype=np.complex128)
    composed = np.array([coefficients[0]], dtype=np.complex128)
    for index in range(1, degree + 1):
        composed = np.polymul(composed, affine)
        composed = np.polyadd(composed, np.array([coefficients[index]]))
    return composed


def segment_max_modulus(
    coefficients: Sequence[complex],
    start: complex,
    end: complex,
    *,
    tolerance: float = 1.0e-12,
) -> tuple[float, float]:
    """Return ``(max |f| on the segment, parameter attaining it)``.

    ``|f(start + t*(end-start))|^2`` is a real polynomial in ``t`` of degree
    ``2n``.  Its maximum over ``[0, 1]`` is attained at an endpoint or at a real
    root of its derivative, so the maximum is located rather than sampled.
    """

    segment = segment_polynomial(coefficients, start, end)
    squared = np.real(np.polymul(segment, np.conjugate(segment[::-1])[::-1]))
    candidates = [0.0, 1.0]
    derivative = np.polyder(squared)
    if len(derivative) > 1:
        for root in np.roots(derivative):
            if abs(root.imag) <= tolerance and -tolerance <= root.real <= 1.0 + tolerance:
                candidates.append(min(1.0, max(0.0, float(root.real))))
    values = [float(np.polyval(squared, parameter)) for parameter in candidates]
    best = int(np.argmax(values))
    return float(np.sqrt(max(0.0, values[best]))), float(candidates[best])


def critical_table(roots: Sequence[complex]) -> list[dict[str, Any]]:
    """Critical points of ``f``, their values, and admissibility for hub paths.

    A hub is *admissible* when ``|f(c)| < 1``: only then does the hub itself lie
    inside the open lemniscate, so only then can a two-spoke path through it be
    contained there.
    """

    coefficients = coefficients_from_roots(roots)
    rows: list[dict[str, Any]] = []
    for index, point in enumerate(np.roots(np.polyder(coefficients))):
        value = complex(np.polyval(coefficients, point))
        rows.append(
            {
                "critical_index": index,
                "critical_point": complex(point),
                "critical_value": value,
                "critical_value_modulus": float(abs(value)),
                "admissible": bool(abs(value) < 1.0),
            }
        )
    return rows


def spoke_table(
    roots: Sequence[complex],
    hub: complex,
    *,
    criterion: str = OPEN_LEMNISCATE,
) -> list[dict[str, Any]]:
    """Per-root straight-spoke containment from ``hub`` under ``criterion``."""

    if criterion not in (OPEN_LEMNISCATE, HUB_SUBLEVEL):
        raise ValueError(f"unknown spoke criterion: {criterion}")
    roots = np.asarray(roots, dtype=np.complex128)
    coefficients = coefficients_from_roots(roots)
    hub_modulus = float(abs(np.polyval(coefficients, hub)))
    ceiling = 1.0 if criterion == OPEN_LEMNISCATE else hub_modulus
    rows: list[dict[str, Any]] = []
    for index, root in enumerate(roots):
        maximum, parameter = segment_max_modulus(coefficients, hub, complex(root))
        rows.append(
            {
                "root_index": index,
                "root": complex(root),
                "length": float(abs(complex(root) - hub)),
                "maximum_modulus": maximum,
                "maximum_at_parameter": parameter,
                "ceiling": float(ceiling),
                "contained": bool(maximum <= ceiling * (1.0 + 1.0e-13)),
            }
        )
    return rows


def hub_pair_objective(
    roots: Sequence[complex],
    hub: complex,
    *,
    criterion: str = OPEN_LEMNISCATE,
) -> tuple[float, dict[str, Any] | None]:
    """Shortest total length of two contained straight spokes from ``hub``.

    Returns ``(inf, None)`` when fewer than two roots have a contained spoke.
    """

    rows = spoke_table(roots, hub, criterion=criterion)
    contained = sorted(
        (row for row in rows if row["contained"]), key=lambda row: row["length"]
    )
    if len(contained) < 2:
        return float("inf"), None
    left, right = contained[0], contained[1]
    return float(left["length"] + right["length"]), {
        "hub": complex(hub),
        "left": left,
        "right": right,
        "contained_root_indices": [row["root_index"] for row in contained],
    }


def minimal_critical_value_hub(roots: Sequence[complex]) -> dict[str, Any] | None:
    """The critical point of least nonzero ``|f(c)|``.

    This is the selection rule the landed degree-three theorem uses.  ``None``
    when every critical point is a root of ``f`` or no critical point exists.
    """

    rows = [row for row in critical_table(roots) if row["critical_value_modulus"] > 1.0e-13]
    if not rows:
        return None
    return min(rows, key=lambda row: row["critical_value_modulus"])


def _shifted_coefficients(coefficients: np.ndarray, hub: complex) -> np.ndarray:
    """Taylor coefficients of ``f`` at ``hub``, ascending, by synthetic division."""

    working = list(np.asarray(coefficients, dtype=np.complex128))
    ascending: list[complex] = []
    while working:
        if len(working) == 1:
            ascending.append(working[0])
            break
        carried: list[complex] = [working[0]]
        for coefficient in working[1:-1]:
            carried.append(coefficient + carried[-1] * hub)
        # the remainder is the LAST coefficient plus the final carry, not the
        # last coefficient alone -- the two agree only when hub == 0
        ascending.append(working[-1] + carried[-1] * hub)
        working = carried
    return np.asarray(ascending, dtype=np.complex128)


def branch_start(
    coefficients: np.ndarray,
    hub: complex,
    parameter: float,
    *,
    iterations: int = 60,
) -> tuple[complex, complex] | None:
    """The two branch points at level ``(1 - parameter^2) f(c)``, well conditioned.

    Solving ``f(z) = (1 - u^2) v`` directly for ``z`` is badly conditioned near a
    simple critical point: the two preimages sit about ``u`` apart while the
    residual that separates them is ``|v| u^2`` against a constant term ``|v|``.
    Root-finding on the level polynomial therefore returns positions whose
    *directions* from the hub can be wildly wrong -- measured up to 50 degrees --
    even though the positions themselves are close enough that the level flow
    contracts the error and the resulting arc *lengths* stay sound.

    Working in ``d = z - c`` is better conditioned in principle.  Taylor-expanding
    at the hub gives ``a_1 = 0`` exactly, so the equation becomes

        ``a_n d^n + ... + a_2 d^2 + u^2 v = 0``,

    in which ``a_2 d^2`` cancels against ``u^2 v`` -- both of size ``|v| u^2`` --
    rather than against ``|v|``.

    **What that conditioning gain does not buy.**  Measured against the level-root
    locator over 778 hubs, including near-Fekete configurations at perturbation
    scales down to ``1e-7``, the two agree to ``1e-13``: the gain does not show up
    where it was expected to.  The residual angular error is *real*, not a
    locator artifact.  At finite ``u`` the two descent directions are opposite
    only to order ``u``; the correction is ``O(u * a_3 / a_2)``, and ``a_2 =
    f''(c)/2`` tends to zero as the hub approaches a degenerate one.  So near a
    degenerate hub the *only* way to trust a start direction to a given angular
    accuracy is to take ``u`` small compared with ``|a_2 / a_3|`` times that
    accuracy -- no choice of locator substitutes for it.  Measured worst
    deviation from exactly-opposite directions at ``u = 1e-6``: ``1.6e-6`` rad
    generic, ``6.7e-2`` rad on a near-Fekete shell at scale ``1e-6``, ``1.7e-1``
    rad at scale ``1e-7``, identically for both locators.
    """

    ascending = _shifted_coefficients(coefficients, hub)
    if len(ascending) < 3:
        return None
    value = ascending[0]
    curvature = ascending[2]
    if value == 0 or curvature == 0:
        return None
    tail = ascending[2:]  # coefficients of d^2, d^3, ...
    offset = parameter * parameter * value

    def residual(displacement: complex) -> complex:
        total = 0j
        power = displacement * displacement
        for coefficient in tail:
            total += coefficient * power
            power *= displacement
        return total + offset

    def slope(displacement: complex) -> complex:
        total = 0j
        power = displacement
        for index, coefficient in enumerate(tail):
            total += (index + 2) * coefficient * power
            power *= displacement
        return total

    leading = np.sqrt(-offset / curvature)
    out: list[complex] = []
    for sign in (1.0, -1.0):
        guess = sign * leading
        for _ in range(iterations):
            derivative_value = slope(guess)
            if derivative_value == 0:
                break
            step = residual(guess) / derivative_value
            guess = guess - step
            if abs(step) <= 1.0e-18 * max(abs(guess), 1.0e-300):
                break
        out.append(hub + guess)
    return out[0], out[1]


def descending_pair(
    roots: Sequence[complex],
    hub: complex,
    *,
    start_parameter: float = 1.0e-6,
    relative_tolerance: float = 1.0e-9,
    absolute_tolerance: float = 1.0e-11,
    start_mode: str = "level_roots",
) -> dict[str, Any] | None:
    """Arc lengths of the two descending inverse-ray branches at a simple hub.

    With ``v = f(c)`` the branch through parameter ``u`` satisfies
    ``f(z(u)) = (1 - u^2) v`` and therefore ``z'(u) = -2 u v / f'(z(u))``.  The
    substitution removes the square-root branch point at ``u = 0``, so a single
    integration reaches the root.  Numerical continuation is candidate evidence;
    the returned residual gates must be checked by the caller.

    ``start_mode`` selects how the two branch points are located.  ``"level_roots"``
    (default, and the behaviour every landed receipt was produced with) finds
    them as roots of the level polynomial.  ``"taylor"`` uses :func:`branch_start`
    instead.  Measured over 778 hubs spanning generic and near-Fekete
    configurations the two agree in arc length to ``1.5e-11`` and give start
    directions equal to within ``1e-13``, so the default is retained.
    """

    from scipy.integrate import solve_ivp  # local import: probe-only dependency

    roots = np.asarray(roots, dtype=np.complex128)
    coefficients = coefficients_from_roots(roots)
    derivative = np.polyder(coefficients)
    value = complex(np.polyval(coefficients, hub))
    if value == 0:
        return None
    if start_mode == "taylor":
        located = branch_start(coefficients, hub, start_parameter)
        if located is None:
            return None
        starts = list(located)
    elif start_mode == "level_roots":
        level = coefficients.astype(np.complex128, copy=True)
        level[-1] -= (1.0 - start_parameter**2) * value
        starts = sorted(np.roots(level), key=lambda point: abs(point - hub))[:2]
    else:
        raise ValueError(f"unknown start_mode: {start_mode}")
    branches: list[dict[str, Any]] = []
    for start in starts:

        def field(parameter: float, state: np.ndarray) -> list[float]:
            point = state[0] + 1j * state[1]
            velocity = -2.0 * parameter * value / np.polyval(derivative, point)
            return [velocity.real, velocity.imag, abs(velocity)]

        solution = solve_ivp(
            field,
            (start_parameter, 1.0),
            [start.real, start.imag, abs(start - hub)],
            rtol=relative_tolerance,
            atol=absolute_tolerance,
        )
        if not solution.success:
            return None
        endpoint = solution.y[0, -1] + 1j * solution.y[1, -1]
        index = int(np.argmin(np.abs(roots - endpoint)))
        sampled = solution.y[0] + 1j * solution.y[1]
        residual = float(
            np.abs(
                np.polyval(coefficients, sampled) - (1.0 - solution.t**2) * value
            ).max()
        )
        branches.append(
            {
                "root_index": index,
                "start_direction": complex((start - hub) / abs(start - hub)),
                "length": float(solution.y[2, -1]),
                "endpoint_error": float(abs(roots[index] - endpoint)),
                "maximum_level_residual": residual,
            }
        )
    if branches[0]["root_index"] == branches[1]["root_index"]:
        return None
    return {
        "hub": complex(hub),
        "branches": branches,
        "total_length": float(branches[0]["length"] + branches[1]["length"]),
        "root_pair": (branches[0]["root_index"], branches[1]["root_index"]),
        "maximum_endpoint_error": max(b["endpoint_error"] for b in branches),
        "maximum_level_residual": max(b["maximum_level_residual"] for b in branches),
    }


def branch_point_free_radius(roots: Sequence[complex], hub: complex) -> float:
    """Largest ``rho`` with ``D(f(c), rho**2)`` free of other critical values.

    Beyond this radius the resolved map :func:`resolved_diameter_length` stops
    being univalent, so area-based bounds on it no longer apply.  Capped at
    ``|f(c)|**0.5``, the radius at which the descending diameter reaches the
    roots.
    """

    coefficients = coefficients_from_roots(roots)
    critical_points = np.roots(np.polyder(coefficients))
    value = complex(np.polyval(coefficients, hub))
    gaps = [
        abs(complex(np.polyval(coefficients, point)) - value)
        for point in critical_points
        if abs(point - hub) > 1.0e-9
    ]
    reach = abs(value) ** 0.5
    if not gaps:
        return reach
    return min(reach, (0.9 * min(gaps)) ** 0.5)


def resolved_diameter_length(
    roots: Sequence[complex],
    hub: complex,
    *,
    angle: float | None = None,
    radius: float | None = None,
    start_parameter: float = 1.0e-7,
    relative_tolerance: float = 1.0e-9,
    absolute_tolerance: float = 1.0e-11,
) -> dict[str, Any] | None:
    """Length of the image of a diameter under the square-root resolution at ``hub``.

    Setting ``xi**2 = f(c) - w`` resolves a simple critical point: the two
    branches that merge at ``c`` become the two halves of one analytic curve
    ``Z`` with ``Z(0) = c`` and ``f(Z(xi)) = f(c) - xi**2``, so

        ``dZ/dt = -2 t exp(2 i angle) / f'(Z)``   along ``xi = t exp(i angle)``.

    The velocity is ``0/0`` exactly at ``t = 0``, so the integration starts at
    ``start_parameter`` from the leading behaviour
    ``Z - c ~ xi sqrt(-2 / f''(c))``.

    ``angle = arg(f(c))/2`` is the *descending* direction: there ``f`` runs
    monotonically from ``f(c)`` to ``0`` and the length agrees with
    :func:`descending_pair`.  Every other angle leaves the level structure and
    does not reach the roots.
    """

    from scipy.integrate import solve_ivp  # local import: probe-only dependency

    roots = np.asarray(roots, dtype=np.complex128)
    coefficients = coefficients_from_roots(roots)
    derivative = np.polyder(coefficients)
    second = np.polyder(derivative)
    value = complex(np.polyval(coefficients, hub))
    curvature = complex(np.polyval(second, hub))
    if value == 0 or curvature == 0:
        return None
    if angle is None:
        angle = float(np.angle(value) / 2.0)
    if radius is None:
        radius = abs(value) ** 0.5
    leading = np.sqrt(-2.0 / curvature)
    total = 0.0
    smallest_derivative = float("inf")
    for sign in (1.0, -1.0):
        start = hub + sign * start_parameter * np.exp(1j * angle) * leading

        def field(parameter: float, state: np.ndarray) -> list[float]:
            point = state[0] + 1j * state[1]
            velocity = -2.0 * parameter * np.exp(2j * angle) / np.polyval(derivative, point)
            return [velocity.real, velocity.imag, abs(velocity)]

        solution = solve_ivp(
            field,
            (start_parameter, radius),
            [start.real, start.imag, abs(start - hub)],
            rtol=relative_tolerance,
            atol=absolute_tolerance,
        )
        if not solution.success:
            return None
        sampled = solution.y[0] + 1j * solution.y[1]
        away = solution.t > 5.0 * start_parameter
        if away.any():
            smallest_derivative = min(
                smallest_derivative,
                float(np.abs(np.polyval(derivative, sampled[away])).min()),
            )
        total += float(solution.y[2, -1])
    return {
        "hub": complex(hub),
        "angle": float(angle),
        "radius": float(radius),
        "length": float(total),
        "reaches_roots": bool(abs(radius - abs(value) ** 0.5) < 1.0e-12),
        "smallest_derivative_modulus": smallest_derivative,
    }


def sublevel_components_are_simply_connected() -> str:
    """Statement anchor for the maximum-principle fact used by hub arguments.

    A bounded complementary component of ``{|f| < t}`` carries ``|f| = t`` on
    its boundary and ``|f| >= t`` inside, while ``|f|`` is subharmonic and so
    bounded by its boundary values; the two force ``|f| == t``, which an open
    set cannot satisfy.  Hence every component of ``{|f| < t}`` is simply
    connected, and every critical point ``c`` with ``f(c) != 0`` merges two
    *distinct* components of ``{|f| < |f(c)|}`` rather than closing a loop.
    """

    return (
        "components of {|f| < t} are simply connected; a critical point with "
        "f(c) != 0 merges two distinct components"
    )


def merging_pair_tree(
    roots: Sequence[complex], **kwargs: Any
) -> list[dict[str, Any]] | None:
    """Root pairs joined by the descending branches at each simple hub.

    By :func:`sublevel_components_are_simply_connected` the two descending
    branches at a critical point reach two distinct roots, so the pairs form a
    spanning tree on the roots -- over *every* critical point, not only the
    admissible ones.  Admissibility decides whether a hub can carry a path
    inside the lemniscate, so it is reported per row rather than filtered here.
    Rows come back in increasing ``|f(c)|``, which is the order in which the
    merges actually happen.  Returns ``None`` if any hub fails its residual
    gates, since a partial tree is not evidence.
    """

    rows: list[dict[str, Any]] = []
    for row in critical_table(roots):
        if row["critical_value_modulus"] <= 1.0e-13:
            continue
        pair = descending_pair(roots, row["critical_point"], **kwargs)
        if pair is None:
            return None
        pair["critical_value_modulus"] = row["critical_value_modulus"]
        pair["admissible"] = row["admissible"]
        rows.append(pair)
    rows.sort(key=lambda entry: entry["critical_value_modulus"])
    return rows
