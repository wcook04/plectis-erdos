#!/usr/bin/env python3
"""Erdos #1041: the truncated-spoke reduction, in which the LENGTH obligation is free.

Reduction (Form A-cut).  Suppose that for every monic ``f`` with all roots in the
open unit disk there are distinct roots ``a, b`` and radii
``s_a in (0,|a|]``, ``s_b in (0,|b|]`` such that, writing ``a^ = a/|a|``,

    (i)   max_[s_a a^, a] |f|  <  1
    (ii)  max_[s_b b^, b] |f|  <  1
    (iii) max_[s_a a^, s_b b^] |f|  <  1.

Then Erdos #1041 holds.  The path ``a -> s_a a^ -> s_b b^ -> b`` has length

    (|a| - s_a) + |s_a a^ - s_b b^| + (|b| - s_b)  <=  |a| + |b|  <  2,

because ``|s_a a^ - s_b b^| <= s_a + s_b`` is the triangle inequality -- with
equality only when ``a^ = -b^``.  So unlike the two-segment/ellipse reduction of
TwoSegmentContainmentReduction.md, there is NO length condition to check at all:
every admissible pair of radii is automatically inside the budget.

The family interpolates two refuted families and is exactly their span:
``s_a = |a|, s_b = |b|`` is the root chord, and ``s_a, s_b -> 0`` is Form A' of
TrueGeodesicLab.md, both radii interior.  The new content is the interior of the
parameter range.

Modes.

``mechanism``
    Why truncation is the right repair.  The recorded refutation of Form A' is a
    FIRST-ORDER-AT-THE-ORIGIN sign condition -- ``d/dt log|f(t a_j)|`` at ``t=0``
    is ``-Re(conj(p_1) a_j)/L``, so only roots in one closed half plane can carry
    a full spoke, and that half plane can hold exactly one root.  Truncating at
    any ``s > 0`` deletes exactly that obstruction.  This mode prints the ENTRY
    RADIUS ``tau(a) = inf{s : |f| <= 1 on [s a^, a]}`` at the recorded witnesses.

``coverage``
    Safe chords, safe full spokes, and the Form A-cut objective at each recorded
    hard witness, including the two where chords and the centre hub are
    simultaneously empty and the two where no critical hub carries two spokes.

``calibrate``
    Adversarial maximisation of
    ``V_cut = min over pairs, min over (s_a,s_b), of max of the three segment maxima``
    against the NEGATIVE CONTROL ``V_full`` (Form A', known false).  Per
    ``research_packet.json::negative_results`` entry 19 a supremum pinned under a
    threshold is informative only if the same searcher pushes a neighbouring
    false statement over it.

Segment maxima are exact throughout: the maximum of ``|f|^2`` along a segment is
a real polynomial of degree ``2n`` in the parameter, so its critical points are
roots of the derivative -- never sampled.

Nothing here proves Erdos #1041.
"""

from __future__ import annotations

import argparse
import itertools
import math

import numpy as np


def segment_max_exact(roots: np.ndarray, start: complex, end: complex) -> float:
    step = end - start
    degree = len(roots)
    if not np.isfinite(step) or abs(step) < 1e-14:
        value = abs(np.prod(start - roots))
        return float(value) if np.isfinite(value) else 1e18
    shifted = (roots - start) / step
    squared = np.array([1.0])
    for value in shifted:
        squared = np.convolve(
            squared,
            np.array([1.0, -2.0 * value.real, value.real ** 2 + value.imag ** 2]),
        )
    if not np.all(np.isfinite(squared)):
        return 1e18
    derivative = np.polyder(squared)
    best = max(np.polyval(squared, 0.0), np.polyval(squared, 1.0))
    if len(derivative) > 1 and np.all(np.isfinite(derivative)) and np.any(derivative != 0):
        try:
            for critical in np.roots(derivative):
                if abs(critical.imag) < 1e-9 and 0.0 <= critical.real <= 1.0:
                    best = max(best, np.polyval(squared, critical.real))
        except Exception:
            return 1e18
    out = abs(step) ** degree * math.sqrt(max(best, 0.0))
    return float(out) if np.isfinite(out) else 1e18


def entry_radius(roots: np.ndarray, k: int, rounds: int = 80) -> float:
    """tau(a_k) = inf{ s : |f| <= 1 on [s a^, a_k] }."""
    a = roots[k]
    modulus = abs(a)
    if modulus < 1e-12:
        return 0.0
    unit = a / modulus
    if segment_max_exact(roots, 0j, a) <= 1.0:
        return 0.0
    lo, hi = 0.0, modulus
    for _ in range(rounds):
        mid = 0.5 * (lo + hi)
        if segment_max_exact(roots, mid * unit, a) <= 1.0:
            hi = mid
        else:
            lo = mid
    return hi


def v_cut(roots: np.ndarray, grid: int = 40) -> tuple[float, tuple | None]:
    roots = np.asarray(roots, dtype=complex)
    n = len(roots)
    moduli = np.abs(roots)
    if np.any(moduli < 1e-9):
        return 0.0, None
    units = roots / moduli
    fractions = np.linspace(0.02, 1.0, grid)
    arm = np.zeros((n, grid))
    for k in range(n):
        for m, fraction in enumerate(fractions):
            arm[k, m] = segment_max_exact(roots, fraction * moduli[k] * units[k], roots[k])
    best, argmin = np.inf, None
    for i, j in itertools.combinations(range(n), 2):
        for mi in range(grid):
            if arm[i, mi] >= best:
                continue
            left = fractions[mi] * moduli[i] * units[i]
            for mj in range(grid):
                floor = max(arm[i, mi], arm[j, mj])
                if floor >= best:
                    continue
                right = fractions[mj] * moduli[j] * units[j]
                score = max(floor, segment_max_exact(roots, left, right))
                if score < best:
                    best, argmin = score, (i, j, abs(left), abs(right))
    return float(best), argmin


def v_full(roots: np.ndarray) -> float:
    """Form A': both FULL radii interior.  Known false -- the negative control."""
    roots = np.asarray(roots, dtype=complex)
    n = len(roots)
    spokes = [segment_max_exact(roots, 0j, roots[k]) for k in range(n)]
    return float(min(max(spokes[i], spokes[j]) for i, j in itertools.combinations(range(n), 2)))


def v_chord(roots: np.ndarray) -> float:
    roots = np.asarray(roots, dtype=complex)
    n = len(roots)
    return float(min(segment_max_exact(roots, roots[i], roots[j])
                     for i, j in itertools.combinations(range(n), 2)))


def v_common(roots: np.ndarray, grid: int = 200) -> tuple[float, tuple | None]:
    """Common-radius form: V = min over pairs, min over s >= max(tau_i,tau_j),
    of the exact chord maximum.  Arms are handled exactly by the entry radii."""
    roots = np.asarray(roots, dtype=complex)
    n = len(roots)
    moduli = np.abs(roots)
    if np.any(moduli < 1e-9):
        return 0.0, None
    units = roots / moduli
    taus = np.array([entry_radius(roots, k) for k in range(n)])
    best, argmin = np.inf, None
    for i, j in itertools.combinations(range(n), 2):
        lo = max(taus[i], taus[j])
        hi = min(moduli[i], moduli[j])
        if lo > hi:
            continue
        for s in np.linspace(lo, hi, grid):
            score = segment_max_exact(roots, s * units[i], s * units[j])
            if score < best:
                best, argmin = score, (i, j, float(s))
    return float(best), argmin


def v_chord_or_origin(roots: np.ndarray) -> float:
    """The packet's recorded negative control: one safe chord OR two safe full spokes."""
    return float(min(v_chord(roots), v_full(roots)))


def witnesses() -> dict:
    L = 999 / 1000
    r5 = 99999 / 100000
    hex6 = [("0x1.fffffaead1dfdp-1", "-0x1.c7f97b12bedcep-15"),
            ("0x1.004ed623acd87p-1", "0x1.bb3a1b3208ad6p-1"),
            ("-0x1.ffded10fb5c87p-2", "0x1.bb713c92edfe4p-1"),
            ("-0x1.fffff9e87dd68p-1", "-0x1.0766ef919e3d1p-12"),
            ("-0x1.00485f6af598cp-1", "-0x1.bb3dd8051992dp-1"),
            ("0x1.00198d2225a68p-1", "-0x1.bb58e733c06dcp-1")]
    hex9 = [("0x1.fffffadb279edp-1", "-0x1.54cbe5f38764ep-14"),
            ("0x1.882fdda9ba317p-1", "0x1.4922d6b3868dfp-1"),
            ("0x1.63e8c845cba7bp-3", "0x1.f83590b0811ebp-1"),
            ("-0x1.fffb9be200080p-2", "0x1.bb68ed350eca4p-1"),
            ("-0x1.e121a80180737p-1", "0x1.5e2df749c719cp-2"),
            ("-0x1.e11b7beb2b6bep-1", "-0x1.5e4fe150117d8p-2"),
            ("-0x1.0005816d133a1p-1", "-0x1.bb647aee76a86p-1"),
            ("0x1.637127244f7d2p-3", "-0x1.f83ad6df31cf7p-1"),
            ("0x1.8833eebb49d0cp-1", "-0x1.491f0e2e50785p-1")]
    unhex = lambda H: np.array([float.fromhex(a) + 1j * float.fromhex(b) for a, b in H])
    out = {
        "deg3 two-segment witness": np.array([L * (7 + 24j) / 25, L * (7 - 24j) / 25, -L + 0j]),
        "cubic z^3-(99/100)^3": 0.99 * np.exp(2j * np.pi * np.arange(3) / 3),
        "deg5 origin-spoke lab": np.array([r5 + 0j, r5 * (-20 + 99j) / 101, r5 * (-20 - 99j) / 101,
                                           r5 * (-28 + 195j) / 197, r5 * (-28 - 195j) / 197]),
        "near-Fekete quintic": np.array([(1 - 1e-9) * np.exp(2j * np.pi * t)
                                         for t in (0.99998979, 0.2, 0.4, 0.6, 0.8)]),
        "deg6 QC=infinity": unhex(hex6),
        "deg9 QC=infinity": unhex(hex9),
    }
    for n in (3, 4, 5, 6, 8, 12):
        out[f"regular {n}-gon r=0.999"] = 0.999 * np.exp(2j * np.pi * np.arange(n) / n)
    return out


def clamp(z):
    m = np.abs(z)
    return np.where(m > 1.0, z / m, z)


def search(n, objective, restarts, iters, seed, grid):
    rng = np.random.default_rng(seed)
    best, config = -np.inf, None
    calls = {"cut": lambda z: v_cut(z, grid)[0],
             "common": lambda z: v_common(z, grid)[0],
             "full": v_full,
             "chord": v_chord,
             "chord_or_origin": v_chord_or_origin}
    call = calls[objective]
    for restart in range(restarts):
        if restart == 0:
            z = np.exp(2j * np.pi * np.arange(n) / n)
        elif restart == 1:
            z = 0.999 * np.exp(2j * np.pi * np.arange(n) / n)
        else:
            z = clamp(rng.uniform(-1, 1, n) + 1j * rng.uniform(-1, 1, n))
        current, step = call(z), 0.35
        for _ in range(iters):
            k = int(rng.integers(0, n))
            trial = z.copy()
            trial[k] = clamp(trial[k] + step * (rng.normal() + 1j * rng.normal()))
            value = call(trial)
            if value > current:
                current, z = value, trial
            else:
                step *= 0.985
            if step < 3e-4:
                break
        if current > best:
            best, config = current, z.copy()
    return best, config


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("mode", nargs="?", default="all",
                    choices=["all", "mechanism", "coverage", "calibrate"])
    ap.add_argument("--grid", type=int, default=40)
    ap.add_argument("--restarts", type=int, default=4)
    ap.add_argument("--iterations", type=int, default=90)
    ap.add_argument("--max-degree", type=int, default=6)
    args = ap.parse_args()

    W = witnesses()
    ok = None

    if args.mode in ("all", "mechanism"):
        print("== mechanism: entry radius tau(a) = inf{s : |f| <= 1 on [s a^, a]} ==")
        print("   (Form A' needs tau = 0 for two roots; Form A-cut needs only tau < |a|)")
        for name in ("deg5 origin-spoke lab", "deg3 two-segment witness",
                     "deg6 QC=infinity", "deg9 QC=infinity"):
            z = W[name]
            taus = [entry_radius(z, k) for k in range(len(z))]
            mods = np.abs(z)
            print(f"  {name}")
            print(f"     tau/|a| = {[round(t/m, 6) for t, m in zip(taus, mods)]}")
        print()

    if args.mode in ("all", "coverage"):
        print("== coverage at the recorded hard witnesses ==")
        print(f"{'witness':26s} {'n':>2s} {'safe chords':>11s} {'safe FULL spokes':>17s} "
              f"{'V (common)':>11s}  verdict")
        for name, z in W.items():
            n = len(z)
            chords = sum(1 for i, j in itertools.combinations(range(n), 2)
                         if segment_max_exact(z, z[i], z[j]) <= 1.0)
            spokes = sum(1 for a in z if segment_max_exact(z, 0j, a) <= 1.0)
            score, _ = v_common(z, 200)
            good = score <= 1.0
            ok = good if ok is None else (ok and good)
            print(f"{name:26s} {n:2d} {chords:11d} {spokes:17d} {score:11.7f}  "
                  f"{'FEASIBLE' if good else 'INFEASIBLE'}")
        print()

    if args.mode in ("all", "calibrate"):
        print("== calibration: adversarial maximisation, with the Form A' negative control ==")
        print("   feasible iff V <= 1; the control is KNOWN FALSE and must be pushed over 1")
        print(f"{'n':>3s} {'sup V (common)':>16s} {'sup V chord-or-origin (FALSE)':>31s}")
        for n in range(3, args.max_degree + 1):
            cut, _ = search(n, "common", args.restarts, args.iterations, 400 + n, 70)
            ctl, _ = search(n, "chord_or_origin", args.restarts, args.iterations * 2, 500 + n, args.grid)
            print(f"{n:3d} {cut:16.8f} {ctl:31.8f}", flush=True)
            if cut > 1.0 + 1e-6:
                print("   ** candidate break -- verify before reporting **", flush=True)
        print()

    print("== verdict ==")
    if ok is None:
        print("  coverage  not run in this mode")
        return 0
    print(f"  coverage {'PASS' if ok else 'FAIL'}  (feasibility at every recorded witness)")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
