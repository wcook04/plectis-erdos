#!/usr/bin/env python3
"""Erdos #1041: the radial deficit identity, and the near-Fekete local model.

Two things, one exact and one asymptotic.

``identity`` -- EXACT, elementary.  Let ``c`` be a simple critical point of ``f``
whose two descent branches reach roots ``a`` and ``b``, and measure angles from
the centre of the disc holding the roots.  Traversing each half OUTWARD from
``c``, write ``psi`` for the angle between the position vector and the unit
tangent, so ``cos psi = d|z|/ds``.  Integrating that over both halves gives

    L(c) = (|a| + |b|) - 2|c| + D(c),      D(c) = int (1 - cos psi) ds >= 0.

Every term on the right is signed: ``D >= 0``, ``2|c| >= 0``, and
``|a| + |b| <= 2R``.  So a SUFFICIENT condition for the target ``L(c) <= 2R`` is

    D(c) <= 2|c|.                                                        (RD)

This is the origin-centred sibling of the chord-deficit identity in
``research_packet.json::exact_results`` entry ``chord_deficit_polynomial_representation``
(``L = (d1+d2) + D_chord``) and of the tangent-support identity in
``CriticalTreeLengthCharge.md`` (``2R - L = (R + <a,U_a>) + (R + <b,U_b>) + K``).
It differs from both in that it carries no indefinite-sign term: the signed
curvature charge ``K``, measured negative at ``-0.1613`` in the recorded sweep,
is replaced by the explicit nonnegative credit ``2|c|`` and a nonnegative
deficit.  The obligation becomes an UPPER BOUND on a nonnegative quantity.

``local-model`` -- the hard regime.  ``HardRegimeIsNearFekete.md`` and
``NearFeketeCuspLaw.md`` place the surviving difficulty at
``f = z^n - m + eps*h``, whose ``n-1`` simple critical points sit on a tiny
(n-1)-gon of radius ``rho = (eps|h'(0)|/n)^(1/(n-1)) >> eps``.  Zoom ``z = rho*xi``:
the descent branches become level curves of ``Im G``, ``G = (1/f(0))(xi^n + lam*xi)``,
``lam = n f'(0)/|f'(0)|``, and matched asymptotics give

    |a| + |b| - L(c_k) = -rho * kappa_k + o(rho),
    kappa_k = D_model(k) - 2|xi_k| = lim_{Lam->inf} ( branch length at |xi|=Lam - 2 Lam ).

So (RD) in the hard regime is exactly ``min_k kappa_k <= 0``.  After the two
normalisations available (``xi -> c xi`` fixes ``|lam|`` and one phase) the model
has ONE essential real parameter per degree, of period ``2 pi / n``.  The sweep
measures ``max_beta min_k kappa_k`` on that one-parameter family.

Nothing here is a proof of #1041.  ``identity`` is an ordinary exact statement;
``local-model`` and ``near-fekete`` are finite evidence on a reduced family.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np
from scipy.integrate import solve_ivp


# --------------------------------------------------------------------------
# branch pair of a genuine polynomial, resolved parametrisation f = f(c)(1-w^2)
# --------------------------------------------------------------------------
def _start_point(coefficients: np.ndarray, hub: complex, w: complex) -> complex:
    """Series point of the branch ``f(z) = f(c)(1 - w^2)`` near ``c``.

    Deliberately NOT a Newton solve against ``f(c)(1 - w^2)``.  For the small
    ``w`` this needs, ``1 - w^2`` rounds to ``1`` in double precision, so that
    target is exactly ``f(c)``, Newton walks straight back onto the saddle, and
    the branch collapse the offset exists to prevent is reinstated silently.
    Inverting the local expansion has no cancellation:

        z = c + s w (1 + alpha w) + O(w^3),
        s = sqrt(-2 f(c)/f2(c)),   alpha = f3(c) s^3 / (12 f(c)),

    with f2, f3 the second and third derivatives at the hub.
    """
    value = complex(np.polyval(coefficients, hub))
    second = complex(np.polyval(np.polyder(coefficients, 2), hub))
    scale = np.sqrt(-2.0 * value / second)
    third = (
        complex(np.polyval(np.polyder(coefficients, 3), hub))
        if len(coefficients) > 3
        else 0.0
    )
    alpha = third * scale**3 / (12.0 * value)
    return complex(hub + scale * w * (1.0 + alpha * w))


def branch_half(
    coefficients: np.ndarray,
    hub: complex,
    sign: float,
    offset: float = 1.0e-9,
    rtol: float = 1.0e-12,
    max_step: float = 1.0e-3,
) -> tuple[float, float, complex]:
    """One descent half from ``hub``: (length, radial deficit, endpoint).

    The start is taken OFF the saddle.  Starting at ``w = 0`` is not merely
    inaccurate, it silently collapses the two halves onto the same branch: the
    resolved equation is degenerate there, and both sign choices then relax onto
    the same solution, so the pair appears to reach a single root.
    """
    value = complex(np.polyval(coefficients, hub))
    delta = offset
    derivative = np.polyder(coefficients)
    start = _start_point(coefficients, hub, sign * delta)

    def rhs(parameter: float, state: list[float]) -> list[float]:
        point = state[0] + 1j * state[1]
        step = -2.0 * parameter * value / np.polyval(derivative, point)
        speed = abs(step)
        radius = abs(point)
        cosine = (point.real * step.real + point.imag * step.imag) / (radius * speed)
        return [step.real, step.imag, speed, speed * (1.0 - cosine)]

    solution = solve_ivp(
        rhs,
        [delta, 1.0],
        # the skipped arc c -> start is straight to O(delta^2), and on a
        # straight segment int (1 - cos psi) ds = |start - c| - (|start| - |c|)
        # exactly, so seeding it keeps the identity exact instead of short by an
        # O(1) angle times the skipped length.
        [
            start.real,
            start.imag,
            abs(start - hub),
            abs(start - hub) - (abs(start) - abs(hub)),
        ],
        rtol=rtol,
        atol=1.0e-15,
        max_step=max_step,
    )
    end = complex(solution.y[0][-1], solution.y[1][-1])
    return float(solution.y[2][-1]), float(solution.y[3][-1]), end


def branch_pair(
    coefficients: np.ndarray,
    hub: complex,
    rtol: float = 1.0e-12,
    max_step: float = 1.0e-3,
) -> dict[str, Any]:
    length = 0.0
    deficit = 0.0
    ends: list[complex] = []
    for sign in (1.0, -1.0):
        piece, piece_deficit, end = branch_half(
            coefficients, hub, sign, rtol=rtol, max_step=max_step
        )
        length += piece
        deficit += piece_deficit
        ends.append(end)
    return {"length": length, "deficit": deficit, "ends": ends}


# --------------------------------------------------------------------------
# local model: descend Re(sigma * H), H = xi^n + lam*xi, level curves of Im
# --------------------------------------------------------------------------
def model_kappa(
    degree: int, lam: complex, sigma: complex, cutoff: float = 6.0e1
) -> list[dict[str, Any]]:
    """``kappa_k`` for every saddle of the local model, by the deficit formula."""
    coefficients = np.zeros(degree + 1, dtype=complex)
    coefficients[0] = sigma
    coefficients[degree - 1] = sigma * lam
    derivative = np.polyder(coefficients)
    second = np.polyder(coefficients, 2)
    saddles = [
        (-lam / degree) ** (1.0 / (degree - 1)) * np.exp(2j * np.pi * k / (degree - 1))
        for k in range(degree - 1)
    ]
    rows: list[dict[str, Any]] = []
    for index, saddle in enumerate(saddles):
        curvature = complex(np.polyval(second, saddle))
        deficit = 0.0
        for sign in (1.0, -1.0):
            direction = sign * np.sqrt(-2.0 / curvature)

            def rhs(parameter: float, state: list[float]) -> list[float]:
                point = state[0] + 1j * state[1]
                step = -2.0 * parameter / np.polyval(derivative, point)
                speed = abs(step)
                radius = abs(point)
                cosine = (point.real * step.real + point.imag * step.imag) / (
                    radius * speed
                )
                return [step.real, step.imag, speed, speed * (1.0 - cosine)]

            def event(parameter: float, state: list[float]) -> float:
                return math.hypot(state[0], state[1]) - cutoff

            event.terminal = True
            event.direction = 1.0
            tau0 = 1.0e-9
            start = saddle + direction * tau0
            solution = solve_ivp(
                rhs,
                [tau0, 10.0 * math.sqrt(cutoff**degree)],
                [start.real, start.imag, 0.0, 0.0],
                events=event,
                rtol=1.0e-11,
                atol=1.0e-14,
            )
            deficit += float(solution.y[3][-1])
        rows.append(
            {
                "index": index,
                "saddle": saddle,
                "kappa": deficit - 2.0 * abs(saddle),
                "deficit": deficit,
            }
        )
    return rows


# --------------------------------------------------------------------------
# parts
# --------------------------------------------------------------------------
def part_identity(seed: int = 5) -> dict[str, Any]:
    """L(c) = |a| + |b| - 2|c| + D(c), on ordinary polynomials, machine exact."""
    rng = np.random.default_rng(seed)
    worst = 0.0
    rows = []
    for degree in (3, 4, 5, 6, 7):
        for trial in range(4):
            roots = rng.uniform(0.2, 0.99, degree) * np.exp(
                2j * np.pi * rng.random(degree)
            )
            coefficients = np.poly(roots)
            for hub in np.roots(np.polyder(coefficients)):
                pair = branch_pair(coefficients, complex(hub))
                reached = [
                    roots[int(np.argmin(np.abs(roots - end)))] for end in pair["ends"]
                ]
                if abs(reached[0] - reached[1]) < 1.0e-9:
                    continue
                left = pair["length"]
                right = (
                    abs(reached[0]) + abs(reached[1]) - 2.0 * abs(hub) + pair["deficit"]
                )
                worst = max(worst, abs(left - right))
                rows.append(
                    {
                        "degree": degree,
                        "trial": trial,
                        "length": left,
                        "identity_value": right,
                        "gap": left - right,
                        "deficit": pair["deficit"],
                        "twice_hub_radius": 2.0 * abs(hub),
                        "radial_condition_slack": 2.0 * abs(hub) - pair["deficit"],
                    }
                )
    return {
        "claim": "L(c) = |a| + |b| - 2|c| + D(c)",
        "samples": len(rows),
        "worst_absolute_gap": worst,
        "verdict": "identity_holds" if worst < 1.0e-9 else "IDENTITY_FAILED",
        "rows": rows[:6],
    }


def part_local_model(degrees: tuple[int, ...], samples: int = 49) -> dict[str, Any]:
    """max over the one essential parameter of min_k kappa_k, per degree."""
    out = []
    for degree in degrees:
        worst = (-math.inf, 0.0, None)
        for step in range(samples):
            beta = (2.0 * math.pi / degree) * step / (samples - 1)
            rows = model_kappa(degree, np.exp(1j * beta), 1.0 + 0j)
            low = min(row["kappa"] for row in rows)
            if low > worst[0]:
                worst = (low, beta, [row["kappa"] for row in rows])
        out.append(
            {
                "degree": degree,
                "saddle_radius": degree ** (-1.0 / (degree - 1)),
                "worst_min_kappa": worst[0],
                "at_beta": worst[1],
                "kappa_at_worst": worst[2],
            }
        )
    return {
        "claim": "min_k kappa_k < 0 on the whole one-parameter local model",
        "sweep": out,
        "verdict": (
            "min_kappa_negative_at_every_sampled_parameter"
            if all(row["worst_min_kappa"] < 0.0 for row in out)
            else "MIN_KAPPA_NONNEGATIVE_SOMEWHERE"
        ),
    }


def part_near_fekete(degrees: tuple[int, ...] = (3, 4, 5)) -> dict[str, Any]:
    """The matched asymptotic: (|a|+|b|-L)/rho -> -kappa as eps -> 0."""
    rows = []
    for degree in degrees:
        rng = np.random.default_rng(11 + degree)
        perturbation = rng.standard_normal(degree) + 1j * rng.standard_normal(degree)
        for eps in (1.0e-5, 1.0e-7):
            coefficients = np.zeros(degree + 1, dtype=complex)
            coefficients[0] = 1.0
            coefficients[degree] = -(0.999**degree)
            for j in range(1, degree):
                coefficients[degree - j] += eps * perturbation[j]
            roots = np.roots(coefficients)
            zero = complex(np.polyval(coefficients, 0.0))
            slope = complex(np.polyval(np.polyder(coefficients), 0.0))
            rho = (abs(slope) / degree) ** (1.0 / (degree - 1))
            model = model_kappa(degree, degree * slope / abs(slope), 1.0 / zero)
            for hub in np.roots(np.polyder(coefficients)):
                hub = complex(hub)
                index = int(
                    np.argmin([abs(hub - rho * row["saddle"]) for row in model])
                )
                pair = branch_pair(coefficients, hub)
                reached = [
                    roots[int(np.argmin(np.abs(roots - end)))] for end in pair["ends"]
                ]
                measured = (
                    abs(reached[0]) + abs(reached[1]) - pair["length"]
                ) / rho
                rows.append(
                    {
                        "degree": degree,
                        "eps": eps,
                        "rho": rho,
                        "measured_minus_kappa": measured,
                        "model_minus_kappa": -model[index]["kappa"],
                        "absolute_error": abs(measured + model[index]["kappa"]),
                        "error_over_rho": abs(measured + model[index]["kappa"]) / rho,
                    }
                )
    # The prediction is that the residual is the O(rho) correction, so the test
    # is that error/rho stays bounded AND that shrinking rho shrinks the error
    # in proportion.  A relative-error test would be meaningless on the saddles
    # whose kappa is near zero: there the absolute agreement is as good as
    # everywhere else.  rho goes like eps^(1/(n-1)), so its shrink factor is
    # degree-dependent and each degree is compared against its own.
    ratios = [row["error_over_rho"] for row in rows]
    coarse: dict[Any, Any] = {}
    fine: dict[Any, Any] = {}
    for row in rows:
        key = (row["degree"], round(row["model_minus_kappa"], 6))
        (coarse if row["eps"] > 1.0e-6 else fine)[key] = row
    normalised = []
    for key, low in fine.items():
        high = coarse.get(key)
        if high is None or low["absolute_error"] <= 0.0:
            continue
        normalised.append(
            (high["absolute_error"] / low["absolute_error"])
            / (high["rho"] / low["rho"])
        )
    median = sorted(normalised)[len(normalised) // 2] if normalised else None
    return {
        "claim": "(|a|+|b|-L(c))/rho -> -kappa(c), with residual O(rho)",
        "rows": rows,
        "worst_error_over_rho": max(ratios),
        "median_error_shrink_over_rho_shrink": median,
        "verdict": (
            "matched_asymptotic_confirmed"
            if max(ratios) < 5.0 and median is not None and 0.5 < median < 2.0
            else "MATCHED_ASYMPTOTIC_NOT_CONFIRMED"
        ),
    }


def part_deficit_representation(seed: int = 17) -> dict[str, Any]:
    """D(c) = int 2 cos^2( arg W / 2 ) drho / |f'|,  W = z f'/f = sum_j z/(z - z_j).

    On a descent branch ``f = rho e^{i theta}`` with ``theta`` fixed,
    ``dz = e^{i theta} drho / f'``, so ``ds = drho/|f'|`` and
    ``d|z| = Re(conj(z) e^{i theta}/f') drho/|z|``.  Outward from the saddle this
    gives ``cos psi = -cos(arg(f/(z f')))``, hence ``1 - cos psi = 1 + cos(arg W)``.
    The deficit therefore vanishes exactly where ``W`` is negative real, i.e.
    exactly where the branch is radial -- which is what the extremal family
    ``z^n - r^n`` does, since there ``W = n z^n/(z^n - r^n) < 0`` on every radius.
    """
    rng = np.random.default_rng(seed)
    worst = 0.0
    rows = []
    for degree in (3, 4, 5, 6):
        for _ in range(2):
            roots = rng.uniform(0.3, 0.98, degree) * np.exp(
                2j * np.pi * rng.random(degree)
            )
            coefficients = np.poly(roots)
            derivative = np.polyder(coefficients)
            for hub in np.roots(derivative):
                hub = complex(hub)
                pair = branch_pair(coefficients, hub)
                reached = [
                    roots[int(np.argmin(np.abs(roots - end)))] for end in pair["ends"]
                ]
                if abs(reached[0] - reached[1]) < 1.0e-9:
                    continue
                value = complex(np.polyval(coefficients, hub))
                delta = 1.0e-9
                total = 0.0
                for sign in (1.0, -1.0):
                    start = _start_point(coefficients, hub, sign * delta)

                    def rhs(parameter: float, state: list[float]) -> list[float]:
                        point = state[0] + 1j * state[1]
                        slope = np.polyval(derivative, point)
                        step = -2.0 * parameter * value / slope
                        weight = z_weight(point, coefficients, derivative)
                        return [
                            step.real,
                            step.imag,
                            2.0 * parameter * abs(value) * weight / abs(slope),
                        ]

                    solution = solve_ivp(
                        rhs,
                        [delta, 1.0],
                        [
                            start.real,
                            start.imag,
                            abs(start - hub) - (abs(start) - abs(hub)),
                        ],
                        rtol=1.0e-12,
                        atol=1.0e-15,
                        max_step=1.0e-3,
                    )
                    total += float(solution.y[2][-1])
                worst = max(worst, abs(total - pair["deficit"]))
                rows.append(
                    {
                        "degree": degree,
                        "traced_deficit": pair["deficit"],
                        "representation": total,
                        "gap": pair["deficit"] - total,
                    }
                )
                break
    return {
        "claim": "D(c) = int 2 cos^2(arg(z f'/f)/2) drho/|f'|",
        "samples": len(rows),
        "worst_absolute_gap": worst,
        "verdict": (
            "representation_holds" if worst < 1.0e-8 else "REPRESENTATION_FAILED"
        ),
        "rows": rows[:4],
    }


def _hub_scores(
    roots: np.ndarray, rtol: float = 1.0e-8, max_step: float = 6.0e-3
) -> list[dict[str, Any]]:
    """Per-admissible-hub ``D - 2|c|`` and ``L - 2R``, with the reached pair."""
    coefficients = np.poly(roots)
    radius = float(np.max(np.abs(roots)))
    rows: list[dict[str, Any]] = []
    for hub in np.roots(np.polyder(coefficients)):
        hub = complex(hub)
        if abs(np.polyval(coefficients, hub)) >= 1.0:
            continue
        try:
            pair = branch_pair(coefficients, hub, rtol=rtol, max_step=max_step)
        except Exception:
            continue
        reached = [roots[int(np.argmin(np.abs(roots - end)))] for end in pair["ends"]]
        if abs(reached[0] - reached[1]) < 1.0e-9:
            continue
        rows.append(
            {
                "hub": hub,
                "strong": pair["deficit"] - 2.0 * abs(hub),
                "target": pair["length"] - 2.0 * radius,
                "slack_credit": 2.0 * radius - abs(reached[0]) - abs(reached[1]),
            }
        )
    return rows


def part_strong_form(degrees: tuple[int, ...] = (3, 4, 5), seed: int = 301) -> dict[str, Any]:
    """Adversarial refutation of the STRONG form ``D(c) <= 2|c|`` at some hub.

    The strong form drops the credit ``2R - |a| - |b|`` from (RD-slack).  It is
    cleaner and it is false: hill-climbing ``min over admissible c of (D - 2|c|)``
    breaks it at degree three by a wide margin.  The same witness is then scored
    on the TARGET ``min_c L(c) - 2R``, which must remain negative -- the strong
    form dying is not the target dying.
    """
    out = []
    for degree in degrees:
        rng = np.random.default_rng(seed + degree)
        best = (-math.inf, None)
        for _ in range(6):
            roots = rng.uniform(0.5, 1.0, degree) * np.exp(2j * np.pi * rng.random(degree))
            rows = _hub_scores(roots)
            current = min((row["strong"] for row in rows), default=None)
            if current is None:
                continue
            step = 0.3
            for _ in range(90):
                trial = roots + step * (
                    rng.standard_normal(degree) + 1j * rng.standard_normal(degree)
                )
                moduli = np.abs(trial)
                trial = np.where(moduli > 1.0, trial / moduli, trial)
                rows = _hub_scores(trial)
                value = min((row["strong"] for row in rows), default=None)
                if value is not None and value > current:
                    current, roots = value, trial
                else:
                    step *= 0.86
                if step < 1.0e-6:
                    break
            if current > best[0]:
                best = (current, roots.copy())
        witness = best[1]
        # the search runs loose; the reported numbers are re-verified tight
        rows = (
            _hub_scores(witness, rtol=1.0e-12, max_step=1.0e-3)
            if witness is not None
            else []
        )
        if rows:
            best = (min(row["strong"] for row in rows), witness)
        out.append(
            {
                "degree": degree,
                "best_min_strong": best[0],
                "strong_form_broken": bool(best[0] > 0.0),
                "target_at_witness": min((row["target"] for row in rows), default=None),
                "witness_roots": [complex(value) for value in witness]
                if witness is not None
                else None,
            }
        )
    return {
        "claim": "the strong form D(c) <= 2|c| is FALSE; the target is not",
        "rows": out,
        "verdict": (
            "strong_form_refuted_target_survives"
            if any(row["strong_form_broken"] for row in out)
            and all(
                row["target_at_witness"] is None or row["target_at_witness"] < 0.0
                for row in out
            )
            else "UNEXPECTED_STRONG_FORM_OUTCOME"
        ),
    }


def z_weight(point: complex, coefficients: np.ndarray, derivative: np.ndarray) -> float:
    """``2 cos^2(arg W / 2)`` with ``W = z f'/f``."""
    slope = np.polyval(derivative, point)
    value = np.polyval(coefficients, point)
    return 2.0 * math.cos(np.angle(point * slope / value) / 2.0) ** 2


def part_symmetric(degrees: tuple[int, ...]) -> dict[str, Any]:
    """Polar closed form at the conjugation-symmetric saddle, as a cross-check.

    There the separatrix pair is the real algebraic curve ``Im H = 0``, i.e.
    ``u(theta)^(n-1) = -lam sin(theta)/sin(n theta)`` with ``lam = +-1``.
    """
    from scipy.integrate import quad

    rows = []
    for degree in degrees:
        lam = 1.0 if degree % 2 == 0 else -1.0
        radius = degree ** (-1.0 / (degree - 1))
        base = math.pi if degree % 2 == 0 else 0.0
        stride = math.pi / degree

        def polar(theta: float) -> float:
            lower = math.sin(degree * theta)
            if lower == 0.0:
                return float("inf")
            return -lam * math.sin(theta) / lower

        def integrand(theta: float) -> float:
            value = polar(theta)
            if not np.isfinite(value) or value <= 0.0:
                return 0.0
            h = 1.0e-7
            slope = (polar(theta + h) - polar(theta - h)) / (2.0 * h)
            q = slope / ((degree - 1) * value)
            return value ** (1.0 / (degree - 1)) * (math.sqrt(1.0 + q * q) - abs(q))

        integral, _ = quad(
            integrand,
            base + 1.0e-10 * stride,
            base + stride - 1.0e-12 * stride,
            limit=800,
            epsabs=1.0e-12,
        )
        rows.append(
            {
                "degree": degree,
                "saddle_radius": radius,
                "radial_deficit": 2.0 * integral,
                "kappa_symmetric": 2.0 * (integral - radius),
            }
        )
    return {
        "claim": "closed-form polar cross-check of kappa at the symmetric saddle",
        "rows": rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--part",
        choices=(
            "identity",
            "deficit-representation",
            "local-model",
            "near-fekete",
            "symmetric",
            "strong-form",
            "all",
        ),
        default="all",
    )
    parser.add_argument("--degrees", type=int, nargs="*", default=[3, 4, 5, 6, 7, 8])
    parser.add_argument("--samples", type=int, default=49)
    parser.add_argument("--output", type=Path, default=None)
    args = parser.parse_args()

    payload: dict[str, Any] = {"schema": "erdos1041-radial-deficit-identity/1"}
    if args.part in ("identity", "all"):
        payload["identity"] = part_identity()
    if args.part in ("deficit-representation", "all"):
        payload["deficit_representation"] = part_deficit_representation()
    if args.part in ("local-model", "all"):
        payload["local_model"] = part_local_model(tuple(args.degrees), args.samples)
    if args.part in ("near-fekete", "all"):
        payload["near_fekete"] = part_near_fekete()
    if args.part in ("strong-form", "all"):
        payload["strong_form"] = part_strong_form()
    if args.part in ("symmetric", "all"):
        payload["symmetric"] = part_symmetric(tuple(args.degrees))

    text = json.dumps(payload, indent=2, default=lambda v: f"{v:.12g}")
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + "\n", encoding="utf-8")
    print(text)
    failed = [
        section.get("verdict")
        for section in payload.values()
        if isinstance(section, dict) and str(section.get("verdict", "")).isupper()
    ]
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
