#!/usr/bin/env python3
"""Erdos #1041: carry the whole path inside a HARMONIC function's negativity set.

Write f* for the reciprocal adjoint and B = f/f* for the Blaschke product with
the same zeros.  In the open disk |B| < 1 strictly, so

    Omega := { z in D : |f*(z)| <= 1 }   is contained in   { |f| < 1 },

and containment inside Omega is FREE.  RootCentredReciprocalSweep.md already
records f = g*h with h Blaschke; what is used here is that

    G := log|f*| = sum_j log|1 - conj(a_j) z|

is HARMONIC on a neighbourhood of the closed disk -- the zeros of f* sit at
1/conj(a_j), outside -- with G(0) = 0 and G = log|f| on the unit circle.  So G is
the harmonic extension of log|f| from the boundary, and Omega is a NODAL SET, not
a lemniscate: the logarithmic singularities at the roots are gone.  Explicitly
G(z) = - sum_{m>=1} Re(conj(p_m) z^m)/m.

Modes.

``identity``
    The one-parameter identity the truncated-spoke path needs:

        sum_k G(t a_k)  =  - sum_{m>=1} (t^m/m) |p_m|^2   <=  0,   t in [0,1].

    At t = 1 this is RootCentredReciprocalSweep.md's Theorem (RS).  Checked
    against a direct product with an explicit series tail bound.

``coverage``
    Feasibility of the path  a_i -> t a_i -> t a_j -> a_j  inside {G <= 0}, at the
    recorded hard witnesses.  Its length is (1-t)(|a_i|+|a_j|) + t|a_i-a_j|, which
    the triangle inequality puts at or below |a_i|+|a_j| < 2 for EVERY t, so the
    length obligation is free and only containment is tested.  Segment maxima of
    |f*| are exact: |f*|^2 along a segment is a real polynomial of degree 2n.

``precondition``
    RootCentredReciprocalSweep.md's Corollary gives min_k |f*(a_k)| <= 1 -- ONE
    root admits a centred sweep.  With c_{jk} = log|1 - conj(a_j) a_k| real
    symmetric, G(a_k) is row-sum k and the identity says the TOTAL is
    - sum_m |p_m|^2/m <= 0, which is exactly one nonpositive row.  This mode
    adversarially minimises the number of nonpositive rows.

Nothing here proves Erdos #1041.
"""

from __future__ import annotations

import argparse
import itertools
import math

import numpy as np
from fractions import Fraction


def segment_max_fstar(roots: np.ndarray, start: complex, end: complex) -> float:
    """Exact max of |f*| on [start, end]; |f*|^2 is a real polynomial of degree 2n."""
    step = end - start
    if abs(step) < 1e-15:
        return float(abs(np.prod(1.0 - np.conj(roots) * start)))
    squared = np.array([1.0])
    for a in roots:
        c0 = 1.0 - np.conj(a) * start
        c1 = -np.conj(a) * step
        squared = np.convolve(
            squared,
            np.array([abs(c1) ** 2, 2.0 * np.real(np.conj(c1) * c0), abs(c0) ** 2]),
        )
    derivative = np.polyder(squared)
    best = max(np.polyval(squared, 0.0), np.polyval(squared, 1.0))
    if len(derivative) > 1 and np.any(derivative != 0):
        try:
            for critical in np.roots(derivative):
                if abs(critical.imag) < 1e-9 and 0.0 <= critical.real <= 1.0:
                    best = max(best, np.polyval(squared, critical.real))
        except Exception:
            return 1e18
    return float(math.sqrt(max(best, 0.0)))


def entry_fraction(roots: np.ndarray, k: int, rounds: int = 60) -> float:
    """Least t with |f*| <= 1 on [t a_k, a_k]; 0 if the full spoke is clean."""
    a = roots[k]
    if float(abs(np.prod(1.0 - np.conj(roots) * a))) > 1.0:
        return float("inf")          # the root itself is outside Omega: unreachable
    if segment_max_fstar(roots, 0j, a) <= 1.0:
        return 0.0
    lo, hi = 0.0, 1.0
    for _ in range(rounds):
        mid = 0.5 * (lo + hi)
        if segment_max_fstar(roots, mid * a, a) <= 1.0:
            hi = mid
        else:
            lo = mid
    return hi


def v_harmonic(roots: np.ndarray, grid: int = 200) -> tuple[float, tuple | None]:
    roots = np.asarray(roots, dtype=complex)
    n = len(roots)
    taus = np.array([entry_fraction(roots, k) for k in range(n)])
    best, argmin = np.inf, None
    for i, j in itertools.combinations(range(n), 2):
        lo = max(taus[i], taus[j])
        if lo > 1.0:
            continue
        for t in np.linspace(lo, 1.0, grid):
            score = segment_max_fstar(roots, t * roots[i], t * roots[j])
            if score < best:
                best, argmin = score, (i, j, float(t))
    return float(best), argmin


def identity_gap(roots: np.ndarray, t: float, tol: float = 1e-12,
                 cap: int = 2_000_000) -> tuple[float, float, float, bool]:
    """left = sum_k G(t a_k) by direct product; right = -sum_m (t^m/m)|p_m|^2.

    The series converges like (t rho^2)^m, so as t rho^2 -> 1 the number of terms
    needed for a given tolerance blows up.  RootCentredReciprocalSweep.md records
    that stopping on a SMALL TERM rather than a tail bound reports spurious errors
    up to 5.3; the same trap fires here in the other direction, as an unreachable
    tail bound.  So the required term count is computed FIRST from the tail bound
    and the row is reported as unresolved when it exceeds the cap -- never as a
    discrepancy.
    """
    roots = np.asarray(roots, dtype=complex)
    n = len(roots)
    left = float(np.sum(np.log(np.abs(1.0 - np.conj(roots)[:, None] * (t * roots)[None, :]))))
    rho = float(np.abs(roots).max())
    q = t * rho ** 2
    if q >= 1.0:
        return left, float("nan"), float("nan"), False
    # tail after M terms is at most n^2 q^{M+1} / ((M+1)(1-q)) <= n^2 q^{M+1}/(1-q)
    needed = int(math.ceil(math.log(tol * (1.0 - q) / (n ** 2)) / math.log(q))) if q > 0 else 1
    needed = max(needed, 1)
    if needed > cap:
        return left, float("nan"), float("nan"), False
    m = np.arange(1, needed + 1)
    powers = roots[None, :] ** m[:, None]
    pm = powers.sum(axis=1)
    right = float(-np.sum((t ** m / m) * np.abs(pm) ** 2))
    return left, right, abs(left - right), True


def rowsum_good_count(roots: np.ndarray) -> int:
    a = np.asarray(roots, dtype=complex)
    matrix = np.log(np.abs(1.0 - np.conj(a)[:, None] * a[None, :]) + 1e-300)
    return int((matrix.sum(axis=0) <= 0.0).sum())


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
    for n in (3, 4, 5, 6, 8):
        out[f"regular {n}-gon r=0.999"] = 0.999 * np.exp(2j * np.pi * np.arange(n) / n)
    out["REFUTER n=2 {3/10,-9/10}"] = np.array([0.3 + 0j, -0.9 + 0j])
    return out


def refutation_exact() -> tuple[bool, list]:
    """Exact rational certificate that the majorant reaches only ONE root at n = 2.

    Roots 3/10 and -9/10 are real and in the open unit disk, so every quantity is
    an exact rational and every comparison is a comparison of integers.
    """
    a, b = Fraction(3, 10), Fraction(-9, 10)
    rows = []
    for x in (a, b):
        value = Fraction(1)
        for y in (a, b):
            value *= abs(1 - y * x)
        rows.append((x, value))
    (xa, va), (xb, vb) = rows
    ok = (va > 1) and (vb <= 1) and (va * vb <= 1)
    return ok, [(xa, va), (xb, vb), ("product", va * vb)]


def clamp(z):
    m = np.abs(z)
    return np.where(m > 1.0, z / m, z)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("mode", nargs="?", default="all",
                    choices=["all", "identity", "coverage", "precondition", "refutation"])
    ap.add_argument("--grid", type=int, default=200)
    ap.add_argument("--max-degree", type=int, default=8)
    ap.add_argument("--restarts", type=int, default=40)
    args = ap.parse_args()

    W = witnesses()
    verdicts = {}

    if args.mode in ("all", "identity"):
        worst, resolved, unresolved = 0.0, 0, 0
        print("== identity: sum_k G(t a_k) = - sum_m (t^m/m)|p_m|^2 ==")
        print("   (rows with t*rho^2 too close to 1 are UNRESOLVED by series truncation,")
        print("    not discrepancies -- the term count is derived from the tail bound first)")
        print(f"{'witness':26s} {'t':>6s} {'direct':>16s} {'series':>16s} {'gap':>10s}")
        for name, z in list(W.items()):
            for t in (0.25, 0.5, 0.75, 0.9, 1.0):
                left, right, gap, okrow = identity_gap(z, t)
                if not okrow:
                    unresolved += 1
                    print(f"{name:26s} {t:6.2f} {left:16.10f} {'unresolved':>16s} {'--':>10s}")
                    continue
                resolved += 1
                worst = max(worst, gap)
                print(f"{name:26s} {t:6.2f} {left:16.10f} {right:16.10f} {gap:10.2e}")
        verdicts["identity"] = (worst < 1e-9) and resolved > 0
        print(f"resolved rows: {resolved}; unresolved (series budget): {unresolved}; worst gap: {worst:.3e}\n")

    if args.mode in ("all", "coverage"):
        ok = True
        print("== coverage: path inside {G <= 0}, length free by the triangle inequality ==")
        print(f"{'witness':26s} {'n':>2s} {'max entry fraction':>19s} {'V (max |f*|)':>14s}  verdict")
        for name, z in W.items():
            taus = max(entry_fraction(z, k) for k in range(len(z)))
            score, _ = v_harmonic(z, args.grid)
            good = score <= 1.0 + 1e-12
            # the REFUTER row is expected to be infeasible; that IS the result
            expected = (not good) if name.startswith("REFUTER") else good
            ok &= expected
            print(f"{name:26s} {len(z):2d} {taus:19.6f} {score:14.9f}  "
                  f"{'FEASIBLE' if good else 'INFEASIBLE'}")
        verdicts["coverage"] = ok
        print("   (the REFUTER row is expected INFEASIBLE -- see §3 of HarmonicMajorantRefutation.md)")
        print()

    if args.mode in ("all", "refutation"):
        ok, rows = refutation_exact()
        verdicts["refutation"] = ok
        print("== refutation: at n = 2 the majorant reaches only ONE root (exact rationals) ==")
        for label, value in rows:
            print(f"   {str(label):>10s} : {value}  = {float(value):.10f}"
                  f"{'   > 1  (root UNREACHABLE)' if value > 1 and label != 'product' else ''}")
        print("   every comparison above is a comparison of integers; no floating point.")
        print("   consequence: RS-frac needs two roots with |f*(a_k)| <= 1 and cannot have them,")
        print("   so the harmonic majorant is refuted at the MINIMAL degree.\n")

    if args.mode in ("all", "precondition"):
        rng = np.random.default_rng(17)
        print("== precondition: how many roots satisfy |f*(a_k)| <= 1?  (identity gives >= 1) ==")
        print(f"{'n':>3s} {'min count found':>16s}")
        least = 10 ** 9
        for n in range(2, args.max_degree + 1):
            best = 10 ** 9
            for restart in range(args.restarts):
                if restart == 0:
                    z = np.exp(2j * np.pi * np.arange(n) / n)
                elif restart == 1:
                    z = 0.999 * np.exp(2j * np.pi * np.arange(n) / n)
                else:
                    z = clamp(rng.uniform(-1, 1, n) + 1j * rng.uniform(-1, 1, n))
                current, step = rowsum_good_count(z), 0.4
                for _ in range(300):
                    k = int(rng.integers(0, n))
                    trial = z.copy()
                    trial[k] = clamp(trial[k] + step * (rng.normal() + 1j * rng.normal()))
                    value = rowsum_good_count(trial)
                    if value < current or (value == current and rng.random() < 0.3):
                        current, z = value, trial
                    step *= 0.995
                    if step < 1e-4:
                        break
                best = min(best, current)
            least = min(least, best)
            print(f"{n:3d} {best:16d}", flush=True)
        verdicts["precondition"] = least >= 1
        print(f"minimum over all degrees: {least}\n")

    print("== verdicts ==")
    for k, v in verdicts.items():
        print(f"  {k:14s} {'PASS' if v else 'FAIL'}")
    return 0 if all(verdicts.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
