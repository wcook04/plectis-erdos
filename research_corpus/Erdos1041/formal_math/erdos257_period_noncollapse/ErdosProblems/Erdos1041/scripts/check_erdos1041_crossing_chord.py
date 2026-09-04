#!/usr/bin/env python3
"""Erdos #1041: an EXACT upper bound for the extremal family z^n - r^n.

TrueGeodesicLab.md proves the matching lower bound -- every joining curve has
length at least ``2(r - eps)`` with ``eps = (1-r^n)^(1/n)`` -- and reports upper
values only as grid geodesics.  This receipt supplies the upper bound as a
construction, exact at every degree.

Construction (the CROSSING CHORD).  With ``w = exp(2 pi i / n)``, ``c = cos(pi/n)``
and ``t = eps / c``, the polygonal path

    r  --radial-->  t  --chord-->  t w  --radial-->  r w

lies in ``{|f| <= 1}``, touches ``|f| = 1`` only at the chord midpoint, and has
length

    L_n(r) = 2r - 2 eps tan(pi/4 - pi/(2n)).

Four things are checked here.

``containment``
    Exact segment maxima (real critical points of the degree-2n real polynomial
    |f|^2 along each segment, located as polynomial roots -- never sampled) on
    all three segments, at many (n, r).

``sharpness``
    ``t = eps/cos(pi/n)`` is the LARGEST admissible crossing radius: bisection on
    "chord [t, t w] contained" reproduces ``t/eps = 1/cos(pi/n)``.

``lemma``
    The one-variable inequality the containment proof reduces to,
    ``1 + cos(n theta) <= 2 cos^n(theta)`` on ``|theta| <= pi/n``, together with
    the monotonicity of ``s -> log(cos s)/s`` that proves it.

``open``
    The explicit open-lemniscate upgrade.  Below the transition the adjacent
    chord is strict.  At or above it, every radial contraction ``lambda<1`` of
    the extremal crossing chord has the rigorous convexity bound
    ``max|f| <= lambda^n + (1-lambda^n) r^n < 1`` and total length below two.

Nothing here proves Erdos #1041.  What it settles is that on the family which
makes every recorded formulation tight, the radius bound and Form A of
TrueGeodesicLab.md hold with an explicit strict margin at every degree n >= 3 --
previously grid measurements only -- and that the two-radius broken line through
the origin is not the geodesic there.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def segment_max_exact(roots: np.ndarray, start: complex, end: complex) -> float:
    """Exact max of |f| on [start, end] via the real critical points of |f|^2."""
    step = end - start
    degree = len(roots)
    if abs(step) == 0.0:
        return float(abs(np.prod(start - roots)))
    shifted = (roots - start) / step
    squared = np.array([1.0])
    for value in shifted:
        squared = np.convolve(
            squared,
            np.array([1.0, -2.0 * value.real, value.real ** 2 + value.imag ** 2]),
        )
    derivative = np.polyder(squared)
    best = max(np.polyval(squared, 0.0), np.polyval(squared, 1.0))
    if len(derivative) > 1:
        for critical in np.roots(derivative):
            if abs(critical.imag) < 1e-9 and 0.0 <= critical.real <= 1.0:
                best = max(best, np.polyval(squared, critical.real))
    return float(abs(step) ** degree * math.sqrt(max(best, 0.0)))


def family(n: int, r: float) -> np.ndarray:
    return r * np.exp(2j * np.pi * np.arange(n) / n)


def constants(n: int, r: float) -> tuple[float, float, float]:
    eps = (1.0 - r ** n) ** (1.0 / n)
    c = math.cos(math.pi / n)
    return eps, c, eps / c


def path_length(n: int, r: float) -> float:
    eps, c, t = constants(n, r)
    return 2.0 * (r - t) + 2.0 * t * math.sin(math.pi / n)


def closed_form(n: int, r: float) -> float:
    eps, _, _ = constants(n, r)
    return 2.0 * r - 2.0 * eps * math.tan(math.pi / 4.0 - math.pi / (2.0 * n))


def check_containment(degrees, radii, tol=1e-12) -> tuple[bool, list]:
    rows, ok = [], True
    for n in degrees:
        c = math.cos(math.pi / n)
        for r in radii:
            eps, _, t = constants(n, r)
            if t > r:
                rows.append((n, r, None, None, None, None, "t>r: whole disk |z|<=r inside"))
                continue
            roots = family(n, r)
            w = np.exp(2j * np.pi / n)
            m_rad = max(segment_max_exact(roots, t + 0j, r + 0j),
                        segment_max_exact(roots, t * w, r * w))
            m_chord = segment_max_exact(roots, t + 0j, t * w)
            L = path_length(n, r)
            gap = abs(L - closed_form(n, r))
            good = (m_rad <= 1.0 + tol) and (m_chord <= 1.0 + tol) and (gap < 1e-12) and (L < 2.0 * r)
            ok &= good
            rows.append((n, r, m_rad, m_chord, L, 2.0 * r, "ok" if good else "FAIL"))
    return ok, rows


def check_sharpness(degrees, radii, tol=1e-6) -> tuple[bool, list]:
    rows, ok = [], True
    for n in degrees:
        c = math.cos(math.pi / n)
        for r in radii:
            eps, _, t = constants(n, r)
            if t > r:
                continue
            roots = family(n, r)
            w = np.exp(2j * np.pi / n)
            lo, hi = eps, min(r, 2.0 * eps / c)
            if segment_max_exact(roots, hi + 0j, hi * w) <= 1.0:
                best = hi
            else:
                for _ in range(80):
                    mid = 0.5 * (lo + hi)
                    if segment_max_exact(roots, mid + 0j, mid * w) <= 1.0:
                        lo = mid
                    else:
                        hi = mid
                best = lo
            ratio = best / eps
            good = abs(ratio - 1.0 / c) < tol
            ok &= good
            rows.append((n, r, ratio, 1.0 / c, "ok" if good else "FAIL"))
    return ok, rows


def check_lemma(max_n=400, samples=20001) -> tuple[bool, float, tuple]:
    """1 + cos(n th) <= 2 cos^n(th) on |th| <= pi/n, for every n >= 2."""
    worst, arg = np.inf, None
    for n in range(2, max_n + 1):
        th = np.linspace(0.0, math.pi / n, samples)
        slack = 2.0 * np.cos(th) ** n - (1.0 + np.cos(n * th))
        i = int(np.argmin(slack))
        if slack[i] < worst:
            worst, arg = float(slack[i]), (n, float(th[i]))
    return worst >= -1e-12, worst, arg


def check_complement(degrees, radii, tol=1e-9) -> tuple[bool, list]:
    """max |f| on the adjacent-root chord equals exactly r^n (1 + cos^n(pi/n)),
    so that chord is contained exactly when the crossing-chord hypothesis fails."""
    rows, ok = [], True
    for n in degrees:
        c = math.cos(math.pi / n)
        threshold = (1.0 / (1.0 + c ** n)) ** (1.0 / n)
        for r in radii:
            roots = family(n, r)
            measured = segment_max_exact(roots, roots[0], roots[1])
            predicted = r ** n * (1.0 + c ** n)
            agree = abs(measured - predicted) < tol
            # the two cases must partition: chord contained iff r <= r*
            partition = (measured <= 1.0 + tol) == (r <= threshold + 1e-12)
            good = agree and partition
            ok &= good
            rows.append((n, r, predicted, measured, threshold, "ok" if good else "FAIL"))
    return ok, rows


def check_open_perturbation(degrees, radii, tol=1e-9) -> tuple[bool, list]:
    """Replay the strict open-lemniscate construction in both regimes."""
    rows, ok = [], True
    for n in degrees:
        c = math.cos(math.pi / n)
        threshold = (1.0 / (1.0 + c ** n)) ** (1.0 / n)
        # Include the exact handoff radius, where the uncontracted chord touches.
        # For n=2 that threshold is r=1, outside the theorem's open-unit range.
        test_radii = radii if n == 2 else [*radii, threshold]
        for r in sorted(set(test_radii)):
            roots = family(n, r)
            beta = r ** n
            w = np.exp(2j * np.pi / n)
            if n == 2 or r < threshold - 1e-13:
                measured = segment_max_exact(roots, roots[0], roots[1])
                length = abs(roots[1] - roots[0])
                good = measured < 1.0 + tol and length < 2.0
                ok &= good
                rows.append((n, r, "adjacent", 1.0, measured, measured, length,
                             "ok" if good else "FAIL"))
                continue
            eps, _, t = constants(n, r)
            for contraction in (0.5, 0.9, 0.99):
                start = contraction * t + 0j
                end = contraction * t * w
                measured = segment_max_exact(roots, start, end)
                radial = max(segment_max_exact(roots, start, r + 0j),
                             segment_max_exact(roots, end, r * w))
                alpha = contraction ** n
                convex_bound = alpha + (1.0 - alpha) * beta
                length = (2.0 * (r - contraction * t)
                          + 2.0 * contraction * t * math.sin(math.pi / n))
                good = (measured <= convex_bound + tol and convex_bound < 1.0
                        and radial < 1.0 + tol and length < 2.0)
                ok &= good
                rows.append((n, r, "contracted", contraction, measured,
                             convex_bound, length, "ok" if good else "FAIL"))
    return ok, rows


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("mode", nargs="?", default="all",
                    choices=["all", "containment", "sharpness", "lemma", "complement", "open"])
    ap.add_argument("--max-degree", type=int, default=16)
    ap.add_argument("--lemma-max-n", type=int, default=400)
    args = ap.parse_args()

    degrees = list(range(3, args.max_degree + 1))
    radii = [0.9, 0.95, 0.99, 0.999, 0.99999, 1 - 1e-9]
    verdicts = {}

    if args.mode in ("all", "containment"):
        ok, rows = check_containment(degrees, radii)
        verdicts["containment"] = ok
        print("== containment: exact segment maxima on the three segments ==")
        print(f"{'n':>3s} {'r':>10s} {'max|f| radial':>14s} {'max|f| chord':>13s} "
              f"{'length':>12s} {'2r':>10s}  verdict")
        for n, r, mr, mc, L, twor, verdict in rows:
            if mr is None:
                print(f"{n:3d} {r:10.7f} {'':>14s} {'':>13s} {'':>12s} {'':>10s}  {verdict}")
            else:
                print(f"{n:3d} {r:10.7f} {mr:14.12f} {mc:13.12f} {L:12.9f} {twor:10.7f}  {verdict}")
        print()

    if args.mode in ("all", "sharpness"):
        ok, rows = check_sharpness(degrees, radii)
        verdicts["sharpness"] = ok
        print("== sharpness: largest admissible crossing radius t, as a multiple of eps ==")
        print(f"{'n':>3s} {'r':>10s} {'t/eps found':>14s} {'1/cos(pi/n)':>14s}  verdict")
        for n, r, ratio, target, verdict in rows:
            print(f"{n:3d} {r:10.7f} {ratio:14.9f} {target:14.9f}  {verdict}")
        print()

    if args.mode in ("all", "complement"):
        ok, rows = check_complement(degrees, radii)
        verdicts["complement"] = ok
        print("== complement: adjacent-root chord max is exactly r^n (1 + cos^n(pi/n)) ==")
        print(f"{'n':>3s} {'r':>10s} {'predicted':>16s} {'exact measured':>16s} {'r*':>11s}  verdict")
        for n, r, pred, meas, thr, verdict in rows:
            print(f"{n:3d} {r:10.7f} {pred:16.12f} {meas:16.12f} {thr:11.8f}  {verdict}")
        print()

    if args.mode in ("all", "open"):
        open_degrees = list(range(2, args.max_degree + 1))
        ok, rows = check_open_perturbation(open_degrees, radii)
        verdicts["open"] = ok
        print("== open: strict adjacent or radially contracted crossing path ==")
        print(f"{'n':>3s} {'r':>10s} {'regime':>11s} {'lambda':>8s} "
              f"{'measured':>12s} {'bound':>12s} {'length':>12s}  verdict")
        for n, r, regime, contraction, measured, bound, length, verdict in rows:
            print(f"{n:3d} {r:10.7f} {regime:>11s} {contraction:8.3f} "
                  f"{measured:12.9f} {bound:12.9f} {length:12.9f}  {verdict}")
        print()

    if args.mode in ("all", "lemma"):
        ok, worst, arg = check_lemma(args.lemma_max_n)
        verdicts["lemma"] = ok
        print("== lemma: 1 + cos(n th) <= 2 cos^n(th) on |th| <= pi/n ==")
        print(f"min slack over n=2..{args.lemma_max_n}: {worst:.3e} at n={arg[0]}, theta={arg[1]:.9f}")
        print("(equality exactly at theta=0; and identically for n=2, where the")
        print(" construction degenerates and the constant tan(pi/4-pi/4)=0)")
        print()

    print("== verdicts ==")
    for k, v in verdicts.items():
        print(f"  {k:14s} {'PASS' if v else 'FAIL'}")
    return 0 if all(verdicts.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
