#!/usr/bin/env python3
"""Free-hub two-segment mechanism: coverage at hard witnesses, plus calibration.

The mechanism admits any hub ``h`` in the closed ellipse with foci the two
chosen roots and major axis 2, so the path ``a -> h -> b`` automatically has
length at most two.  Chords (``h`` on the segment), the minimum-enclosing-disc
centre, and critical hubs are the degenerate special cases.

Two measurements, both finite evidence and neither a proof:

``coverage``
    For each recorded hard witness, count the safe chords, safe origin spokes
    and critical hubs carrying two safe spokes, then minimise
    ``max(max_[h,a]|f|, max_[h,b]|f|)`` over hubs in the ellipse.  Segment
    maxima in the verdict columns are exact: the maximum of ``|f|^2`` along a
    segment is a real polynomial of degree ``2n`` in the parameter, so the
    critical points are roots of its derivative.

``calibrate``
    Adversarial hill-climbing on the free-hub objective, and on the strictly
    weaker chord-or-origin disjunction.  The second is the negative control
    demanded by ``research_packet.json::negative_results`` entry 19: a searcher
    whose supremum sits just under a threshold is only informative if the same
    searcher can push a neighbouring false statement over it.  It can — the
    chord-or-origin disjunction breaks at n = 3, 5, 6 — and the n = 3 return is
    exactified in ``check_erdos1041_two_segment_containment.py``.
"""

from __future__ import annotations

import argparse
import itertools
import math

import numpy as np


def segment_max_exact(roots: np.ndarray, start: complex, end: complex) -> float:
    """Exact max of |f| on [start, end] via real critical points of |f|^2."""
    step = end - start
    degree = len(roots)
    if abs(step) == 0.0:
        return float(abs(np.prod(start - roots)))
    shifted = (roots - start) / step
    squared = np.array([1.0])
    for value in shifted:
        squared = np.convolve(
            squared,
            np.array([1.0, -2.0 * value.real, value.real**2 + value.imag**2]),
        )
    derivative = np.polyder(squared)
    best = max(np.polyval(squared, 0.0), np.polyval(squared, 1.0))
    if len(derivative) > 1:
        for critical in np.roots(derivative):
            if abs(critical.imag) < 1e-9 and 0.0 <= critical.real <= 1.0:
                best = max(best, np.polyval(squared, critical.real))
    return float(abs(step) ** degree * math.sqrt(max(best, 0.0)))


def segment_max_sampled(roots: np.ndarray, hubs: np.ndarray, root: complex,
                        samples: int = 65) -> np.ndarray:
    parameter = np.linspace(0.0, 1.0, samples)[None, :]
    points = hubs[:, None] * (1.0 - parameter) + root * parameter
    logs = np.zeros(points.shape)
    for value in roots:
        logs += np.log(np.abs(points - value) + 1e-300)
    return np.exp(logs.max(axis=1))


def ellipse_hubs(left: complex, right: complex, radial: int, angular: int) -> np.ndarray:
    separation = abs(left - right)
    if separation >= 2.0:
        return np.array([(left + right) / 2.0])
    along = (right - left) / separation
    across = 1j * along
    centre = (left + right) / 2.0
    minor = math.sqrt(max(1.0 - (separation / 2.0) ** 2, 0.0))
    scale = np.linspace(0.0, 1.0, radial)[:, None]
    angle = np.linspace(0.0, 2.0 * np.pi, angular, endpoint=False)[None, :]
    grid = centre + scale * (np.cos(angle) * along + minor * np.sin(angle) * across)
    return grid.ravel()


def best_hub(roots: np.ndarray, i: int, j: int, radial: int = 9, angular: int = 36,
             samples: int = 65, refine: int = 60) -> tuple[float, complex, float]:
    left, right = roots[i], roots[j]
    hubs = ellipse_hubs(left, right, radial, angular)
    scores = np.maximum(
        segment_max_sampled(roots, hubs, left, samples),
        segment_max_sampled(roots, hubs, right, samples),
    )
    index = int(np.argmin(scores))
    hub, score, step = hubs[index], float(scores[index]), 0.15
    for _ in range(refine):
        trial = hub + step * np.exp(2j * np.pi * np.arange(8) / 8)
        trial = trial[np.abs(trial - left) + np.abs(trial - right) <= 2.0 + 1e-12]
        if len(trial) == 0:
            step *= 0.7
            continue
        trial_scores = np.maximum(
            segment_max_sampled(roots, trial, left, samples),
            segment_max_sampled(roots, trial, right, samples),
        )
        k = int(np.argmin(trial_scores))
        if trial_scores[k] < score:
            score, hub = float(trial_scores[k]), trial[k]
        else:
            step *= 0.7
        if step < 1e-9:
            break
    exact = max(segment_max_exact(roots, hub, left), segment_max_exact(roots, hub, right))
    return exact, hub, abs(hub - left) + abs(hub - right)


def free_hub_score(roots: np.ndarray, nearest: int = 6, **kwargs) -> float:
    pairs = list(itertools.combinations(range(len(roots)), 2))
    if len(pairs) > nearest:
        pairs.sort(key=lambda p: abs(roots[p[0]] - roots[p[1]]))
        pairs = pairs[:nearest]
    return min(best_hub(roots, i, j, **kwargs)[0] for i, j in pairs)


def chord_or_origin_score(roots: np.ndarray) -> float:
    n = len(roots)
    chord = min(segment_max_exact(roots, roots[i], roots[j])
                for i, j in itertools.combinations(range(n), 2))
    spokes = sorted(segment_max_exact(roots, 0j, roots[j]) for j in range(n))
    return min(chord, spokes[1])


def witnesses() -> dict[str, np.ndarray]:
    def circle(s: float) -> complex:
        return complex((1 - s * s) / (1 + s * s), 2 * s / (1 + s * s))

    scale = 999 / 1000
    five = 99999 / 100000
    mec = 9999 / 10000
    hex6 = [
        ("0x1.fffffaead1dfdp-1", "-0x1.c7f97b12bedcep-15"),
        ("0x1.004ed623acd87p-1", "0x1.bb3a1b3208ad6p-1"),
        ("-0x1.ffded10fb5c87p-2", "0x1.bb713c92edfe4p-1"),
        ("-0x1.fffff9e87dd68p-1", "-0x1.0766ef919e3d1p-12"),
        ("-0x1.00485f6af598cp-1", "-0x1.bb3dd8051992dp-1"),
        ("0x1.00198d2225a68p-1", "-0x1.bb58e733c06dcp-1"),
    ]
    hex9 = [
        ("0x1.fffffadb279edp-1", "-0x1.54cbe5f38764ep-14"),
        ("0x1.882fdda9ba317p-1", "0x1.4922d6b3868dfp-1"),
        ("0x1.63e8c845cba7bp-3", "0x1.f83590b0811ebp-1"),
        ("-0x1.fffb9be200080p-2", "0x1.bb68ed350eca4p-1"),
        ("-0x1.e121a80180737p-1", "0x1.5e2df749c719cp-2"),
        ("-0x1.e11b7beb2b6bep-1", "-0x1.5e4fe150117d8p-2"),
        ("-0x1.0005816d133a1p-1", "-0x1.bb647aee76a86p-1"),
        ("0x1.637127244f7d2p-3", "-0x1.f83ad6df31cf7p-1"),
        ("0x1.8833eebb49d0cp-1", "-0x1.491f0e2e50785p-1"),
    ]
    return {
        "degree-3 witness": np.array([scale * (7 + 24j) / 25, scale * (7 - 24j) / 25, -scale]),
        "cubic z^3-(99/100)^3": np.array([0.99 * np.exp(2j * np.pi * k / 3) for k in range(3)]),
        "deg-5 origin-spoke lab": np.array([
            five, five * (-20 + 99j) / 101, five * (-20 - 99j) / 101,
            five * (-28 + 195j) / 197, five * (-28 - 195j) / 197,
        ]),
        "deg-5 adaptive-MEC": np.array([
            mec * circle(s) for s in
            (0.0, 48031 / 76394, 347397 / 99299, -203651 / 55446, -67203 / 94835)
        ]),
        "deg-6 QC=infinity": np.array(
            [complex(float.fromhex(a), float.fromhex(b)) for a, b in hex6]),
        "deg-9 QC=infinity": np.array(
            [complex(float.fromhex(a), float.fromhex(b)) for a, b in hex9]),
    }


def run_coverage() -> None:
    header = (f"{'witness':<24}{'n':>3}{'chords':>8}{'spokes':>8}{'crit':>6}"
              f"{'free hub max|f|':>18}{'length':>10}")
    print(header)
    print("-" * len(header))
    for name, roots in witnesses().items():
        n = len(roots)
        chords = sum(1 for i, j in itertools.combinations(range(n), 2)
                     if segment_max_exact(roots, roots[i], roots[j]) < 1.0)
        spokes = sum(1 for j in range(n) if segment_max_exact(roots, 0j, roots[j]) < 1.0)
        crit = 0
        for c in np.roots(np.polyder(np.poly(roots))):
            if abs(np.prod(c - roots)) < 1.0 and sum(
                    1 for j in range(n)
                    if segment_max_exact(roots, c, roots[j]) < 1.0) >= 2:
                crit += 1
        best = min((best_hub(roots, i, j, radial=11, angular=44, samples=97, refine=90)
                    for i, j in itertools.combinations(range(n), 2)), key=lambda r: r[0])
        print(f"{name:<24}{n:>3}{chords:>8}{spokes:>8}{crit:>6}{best[0]:>18.9f}{best[2]:>10.6f}")
    print("\nfree hub is feasible iff max|f| < 1; segment maxima are exact.")


def run_calibration(seed: int, degrees: range, restarts: int, iterations: int) -> None:
    rng = np.random.default_rng(seed)

    def climb(score, n: int) -> float:
        best = -np.inf
        for restart in range(restarts):
            if restart == 0:
                z = np.exp(2j * np.pi * np.arange(n) / n)
            else:
                z = np.exp(2j * np.pi * rng.random(n))
            value, step = score(z), 0.22
            for _ in range(iterations):
                w = z + step * (rng.normal(size=n) + 1j * rng.normal(size=n))
                mag = np.abs(w)
                w = np.where(mag > 1.0, w / np.maximum(mag, 1e-300), w)
                if len(set(np.round(w, 10))) < n:
                    continue
                trial = score(w)
                if trial > value:
                    value, z = trial, w
                else:
                    step *= 0.99
                    if step < 1e-6:
                        step = 0.03
            best = max(best, value)
        return best

    print(f"{'n':>3}{'free hub sup V':>18}{'chord-or-origin sup V':>24}  control")
    for n in degrees:
        free = climb(free_hub_score, n)
        weak = climb(chord_or_origin_score, n)
        control = "BROKEN (searcher has power)" if weak > 1 + 1e-9 else "not broken"
        print(f"{n:>3}{free:>18.10f}{weak:>24.10f}  {control}")
    print("\nsup V > 1 refutes the corresponding disjunction.")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("coverage", "calibrate"), nargs="?",
                        default="coverage")
    parser.add_argument("--seed", type=int, default=5)
    parser.add_argument("--min-degree", type=int, default=3)
    parser.add_argument("--max-degree", type=int, default=7)
    parser.add_argument("--restarts", type=int, default=4)
    parser.add_argument("--iterations", type=int, default=200)
    args = parser.parse_args()
    if args.mode == "coverage":
        run_coverage()
    else:
        run_calibration(args.seed, range(args.min_degree, args.max_degree + 1),
                        args.restarts, args.iterations)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
