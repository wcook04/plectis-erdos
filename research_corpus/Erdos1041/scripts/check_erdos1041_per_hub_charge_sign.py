#!/usr/bin/env python3
"""Erdos #1041: deterministic verifier for PerHubChargeSign.md.

Three parts, each of which FAILS (non-zero exit) if the recorded claim stops
holding.  No random number generator is used, so a failure is reproducible.

  witness   an ADMISSIBLE critical point of an explicit polynomial with all
            roots in the OPEN unit disk has L(c) > 2R, where R is the exact
            circumradius of the root set.  This refutes the per-hub form of the
            surviving length obligation.  mpmath at 60 digits; the circumradius
            is computed exactly over pairs and triples, never iteratively (an
            approximate centre inflates R, which would flatter the claim).

  charge    the near-Fekete residue kappa_n of NearFeketeCuspLaw.md equals the
            support-function charge  int_Gamma p dvartheta,  where p is the
            signed distance from the origin to the tangent line and dvartheta is
            the turning.  Checked against the recorded constants.

  sign      the charge integrand's sign is  sign(F1 * F2)  after the reduction
            zeta = zeta_c t to the fixed polynomial Phi(t) = t^n - n t + (n-1):
                F1 = Im(nu (t-1)),
                F2 = (n-1) Im(nu (t-1)) - Im(nu (t - t^{2-n})).
            Checked pointwise against the geometric p * dvartheta along branches.

Why the algebraic form is never used to DECIDE the sign numerically: written as
Im(conj(Phi) E) it cancels catastrophically in the far field (both factors grow
like |t|^n while the imaginary part stays O(|t|)), so far-field nodes return
noise.  Every decision below is taken on the cancellation-free geometric form
and the algebraic form is only cross-checked where |t| is bounded.
"""

from __future__ import annotations

import argparse
import cmath
import math
import sys
from functools import lru_cache

from mpmath import exp as mexp
from mpmath import mp, mpc, mpf, pi as mpi, polyroots, sqrt as msqrt

# Recorded near-Fekete residues, min over the split direction (NearFeketeCuspLaw.md §6).
KAPPA = {3: 0.6080213113, 4: 1.030119661, 5: 1.258578348,
         6: 1.398912406, 8: 1.562228697, 12: 1.714601057}

# Recorded per-hub witnesses: (n, phi, eps) -> hub index whose L exceeds 2R.
WITNESS = ((3, "1.2", 6, 0), (3, "1.2", 8, 0), (5, "2", 6, 0))


# --------------------------------------------------------------- model side


@lru_cache(maxsize=None)
def _binom(n):
    return tuple(math.comb(n, j) for j in range(n + 1))


def _P(h, n):
    """Phi(1+h) = sum_{j>=2} C(n,j) h^j, where Phi(t) = t^n - n t + (n-1)."""
    C = _binom(n)
    acc = 0j
    for j in range(n, 1, -1):
        acc = acc * h + C[j]
    return acc * h * h


def _Pp(h, n):
    C = _binom(n)
    acc = 0j
    for j in range(n, 1, -1):
        acc = acc * h + j * C[j]
    return acc * h


def _Ppp(h, n):
    C = _binom(n)
    acc = 0j
    for j in range(n, 1, -1):
        acc = acc * h + j * (j - 1) * C[j]
    return acc


def _E1(h, n):
    """(1+h)^{n-1} - 1, from the binomial expansion.

    Evaluating it as t**(n-1) - 1 cancels catastrophically near the hub (|h| small),
    which is where the second charge factor lives; the expansion has no cancellation
    at either end.
    """
    acc = 0j
    for j in range(n - 1, 0, -1):
        acc = acc * h + math.comb(n - 1, j)
    return acc * h


def _newton(h, target, n):
    for _ in range(60):
        d = _Pp(h, n)
        if d == 0:
            return h, float("inf")
        step = (_P(h, n) - target) / d
        h -= step
        if abs(step) <= 1e-16 * max(1e-300, abs(h)):
            break
    return h, abs(_P(h, n) - target)


@lru_cache(maxsize=None)
def _other_crit(n):
    return tuple(cmath.exp(2j * math.pi * j / (n - 1)) - 1 for j in range(1, n - 1))


def _gl8():
    xs = (-0.9602898564975363, -0.7966664774136267, -0.5255324099163290,
          -0.1834346424956498, 0.1834346424956498, 0.5255324099163290,
          0.7966664774136267, 0.9602898564975363)
    ws = (0.1012285362903763, 0.2223810344533745, 0.3137066458778873,
          0.3626837833783620, 0.3626837833783620, 0.3137066458778873,
          0.2223810344533745, 0.1012285362903763)
    return xs, ws


def _trace(n, nu, sign, tau_max=1e10, tau0=1e-13):
    """Accepted intervals of the branch nu Phi(t) = tau^2 leaving t = 1.

    Step size is capped by a quarter of the distance to any OTHER critical point
    of Phi, and a step whose Newton correction exceeds 35% of the step is
    rejected and halved.  This is the guard against the branch-mistracking
    artifact class recorded in this directory's AGENTS.md.
    """
    nb = nu.conjugate()
    d0 = sign * cmath.sqrt(nb / _binom(n)[2])
    tau = tau0
    h, _ = _newton(d0 * tau0, nb * tau0 * tau0, n)
    ivals = []
    dtau = tau0
    for _ in range(200000):
        if tau >= tau_max:
            break
        dtau = min(max(dtau, tau * 1e-6), tau)
        ok = False
        for _ in range(60):
            tb = tau + dtau
            pred = h + 2 * tau * nb / _Pp(h, n) * dtau
            hb, res = _newton(pred, nb * tb * tb, n)
            d = min((abs(h - c) for c in _other_crit(n)), default=1e18)
            lim = 0.25 * min(d, max(abs(1 + h), 1e-3))
            if (abs(hb - h) <= lim
                    and abs(hb - pred) <= 0.35 * max(abs(hb - h), 1e-300) + 1e-13
                    and res <= 1e-9 * max(1.0, abs(nb * tb * tb))):
                ok = True
                break
            dtau *= 0.5
        if not ok:
            break
        ivals.append((tau, tb, h, hb))
        h = hb
        tau = tb
        dtau *= 1.6
    return ivals


def branch_quantities(n, nu, sign, tau_max=1e10, tau0=1e-13):
    """Return (ex, pos_charge_mass, neg_charge_mass, worst_identity_error).

    The charge integrand's sign is decided ONLY on the cancellation-free
    geometric product p * dvartheta.  The algebraic identity

        p dvartheta = ((n-1)|t| / n) * Im(G) Im(G^2 conj(X)) / |G|^5 * ds,
        G = nu (t^n - t),  X = nu t^n,  ds = 2 tau d tau,

    is verified as an identity (ratio to 1), not used to decide anything, and
    only where |t| is bounded so that Im(G^2 conj(X)) is not lost to rounding.
    """
    nb = nu.conjugate()
    xs, ws = _gl8()
    ivals = _trace(n, nu, sign, tau_max, tau0)
    if not ivals:
        return None
    d0 = sign * cmath.sqrt(nb / _binom(n)[2])
    ex = 0.0
    pos = 0.0
    neg = 0.0
    worst_id = 0.0
    for (ta, tb, ha, hb) in [(0.0, tau0, 0j, ivals[0][2])] + ivals:
        half = 0.5 * (tb - ta)
        mid = 0.5 * (tb + ta)
        for x, w in zip(xs, ws):
            tau = mid + half * x
            pred = ha + (hb - ha) * (tau - ta) / (tb - ta) if tb > ta else ha
            if pred == 0:
                pred = d0 * tau
            hh, _ = _newton(pred, nb * tau * tau, n)
            t = 1 + hh
            Php = _Pp(hh, n)
            if Php == 0:
                continue
            dt = 2 * tau * nb / Php
            theta = -cmath.phase(nu * t * Php)
            ex += w * half * (1 - math.cos(theta)) * abs(dt)
            p = -abs(t) * math.sin(theta)
            dvt = -(_Ppp(hh, n) / Php * dt).imag
            v = w * half * p * dvt
            if v >= 0:
                pos += v
            else:
                neg += -v
            if abs(hh) > 1e-9 and 0.2 < abs(t) < 10.0:
                # Im G = (n-1) F1  and  Im(G^2 conj(X)) = |t|^{2n} F2, with
                #     F1 = Im(nu h),   F2 = Im(nu E1^2 / t^{n-2}),  E1 = t^{n-1}-1,
                # so  p dvartheta / dtau = 2 tau (n-1)^2 F1 F2 |t|^{2n-4} / (n |E1|^5).
                # The power ratio is taken in logs: at n = 30 numerator and
                # denominator each overflow float64 on their own.
                F1 = (nu * hh).imag
                E1 = _E1(hh, n)
                F2 = (nu * E1 * E1 / t ** (n - 2)).imag
                if E1 != 0:
                    lg = (2 * n - 4) * math.log(abs(t)) - 5 * math.log(abs(E1))
                    predicted = 2 * tau * (n - 1) ** 2 * F1 * F2 * math.exp(lg) / n
                    actual = p * dvt
                    den = max(abs(predicted), abs(actual))
                    if den > 1e-20:
                        worst_id = max(worst_id, abs(predicted - actual) / den)
    return ex, pos, neg, worst_id


def kappa_model(n, nu, tau_max=1e10):
    a = branch_quantities(n, nu, +1, tau_max)
    b = branch_quantities(n, nu, -1, tau_max)
    if a is None or b is None:
        return None
    pos = a[1] + b[1]
    neg = a[2] + b[2]
    return {"kappa": 2 - (a[0] + b[0]), "charge": pos - neg,
            "neg_fraction": neg / max(pos, 1e-300), "worst_id": max(a[3], b[3])}


# ------------------------------------------------------------- witness side


def _gl_nodes(m):
    out = []
    for i in range(1, m + 1):
        x = mp.cos(mpi * (i - mpf(1) / 4) / (m + mpf(1) / 2))
        dp = mpf(1)
        for _ in range(200):
            p0, p1 = mpf(1), mpf(0)
            for j in range(1, m + 1):
                p2 = p1
                p1 = p0
                p0 = ((2 * j - 1) * x * p1 - (j - 1) * p2) / j
            dp = m * (x * p0 - p1) / (x * x - 1)
            dx = -p0 / dp
            x += dx
            if abs(dx) < mpf(10) ** (-mp.dps - 5):
                break
        out.append((x, 2 / ((1 - x * x) * dp * dp)))
    return out


def _taylor(coeffs, c):
    a = list(coeffs)
    out = []
    while a:
        b = []
        acc = mpc(0)
        for co in a:
            acc = acc * c + co
            b.append(acc)
        out.append(b[-1])
        a = b[:-1]
    return out


def branch_length_exact(coeffs, c, m_nodes=60):
    """Length of the two descent branches at c via f(z) = f(c)(1 - xi^2).

    Shifted coordinates (constant term exactly zero) and a geometric mesh in xi,
    because both of the defects recorded in NearFeketeCuspLaw.md §5 UNDER-report
    length, i.e. both would flatter the claim being tested here.
    """
    T = _taylor(coeffs, c)
    v = T[0]
    P = T[1:]

    def evP(w):
        acc = mpc(0)
        for co in reversed(P):
            acc = (acc + co) * w
        return acc

    def evPp(w):
        acc = mpc(0)
        for k in range(len(P), 0, -1):
            acc = acc * w + k * P[k - 1]
        return acc

    gl = _gl_nodes(m_nodes)
    total = mpf(0)
    for sign in (1, -1):
        d0 = sign * msqrt(-v / P[1])
        edges = [mpf(0)]
        e = mpf(10) ** (-40)
        while e < 1:
            edges.append(e)
            e *= mpf("1.25")
        edges.append(mpf(1))
        w = mpc(0)
        prev = mpf(0)
        for xa, xb in zip(edges[:-1], edges[1:]):
            half = (xb - xa) / 2
            mid = (xb + xa) / 2
            for x, wq in gl:
                xi = mid + half * x
                target = -v * xi * xi
                z = d0 * xi if prev == 0 else w + (-2 * v * prev / evPp(w)) * (xi - prev)
                for _ in range(200):
                    dd = evPp(z)
                    st = (evP(z) - target) / dd
                    z -= st
                    if abs(st) <= mpf(10) ** (-mp.dps + 5) * max(abs(z), mpf(1)):
                        break
                w = z
                prev = xi
                total += wq * half * abs(-2 * v * xi / evPp(w))
    return total


def circumradius_exact(pts):
    """Minimal enclosing circle over pairs and triples.  Exact, not iterative:
    an approximate centre inflates R, and R sits on the safe side here."""
    tolf = 1 + mpf(10) ** (-40)
    best = None
    k = len(pts)
    for i in range(k):
        for j in range(i + 1, k):
            ctr = (pts[i] + pts[j]) / 2
            r = abs(pts[i] - ctr)
            if all(abs(p - ctr) <= r * tolf for p in pts) and (best is None or r < best[0]):
                best = (r, ctr)
    for i in range(k):
        for j in range(i + 1, k):
            for l in range(j + 1, k):
                a, b, c = pts[i], pts[j], pts[l]
                d = 2 * (a.real * (b.imag - c.imag) + b.real * (c.imag - a.imag)
                         + c.real * (a.imag - b.imag))
                if abs(d) < mpf(10) ** (-40):
                    continue
                ux = ((abs(a) ** 2) * (b.imag - c.imag) + (abs(b) ** 2) * (c.imag - a.imag)
                      + (abs(c) ** 2) * (a.imag - b.imag)) / d
                uy = ((abs(a) ** 2) * (c.real - b.real) + (abs(b) ** 2) * (a.real - c.real)
                      + (abs(c) ** 2) * (b.real - a.real)) / d
                ctr = mpc(ux, uy)
                r = abs(a - ctr)
                if all(abs(p - ctr) <= r * tolf for p in pts) and (best is None or r < best[0]):
                    best = (r, ctr)
    return best


# ------------------------------------------------------------------- parts


def part_witness(verbose):
    mp.dps = 60
    fails = []
    for (n, phi_s, epow, hub) in WITNESS:
        phi = mpf(phi_s)
        eps = mpf(10) ** (-epow)
        R0 = mpf("0.9")
        coeffs = [mpf(1)] + [mpf(0)] * (n - 2) + [eps * mexp(mpc(0, 1) * phi), -(R0 ** n)]
        roots = list(polyroots(coeffs, maxsteps=300, extraprec=300))
        if max(abs(r) for r in roots) >= 1:
            fails.append(f"n={n} phi={phi_s}: a root left the open unit disk")
            continue
        R, _ = circumradius_exact(roots)
        rho = (eps / n) ** (mpf(1) / (n - 1))
        c = rho * mexp(mpc(0, 1) * (mpi + phi + 2 * mpi * hub) / (n - 1))
        fc = mpc(0)
        for co in coeffs:
            fc = fc * c + co
        if abs(fc) >= 1:
            fails.append(f"n={n} phi={phi_s}: hub {hub} is not admissible, |f(c)|={abs(fc)}")
            continue
        L = branch_length_exact(coeffs, c)
        if verbose:
            print(f"  n={n} phi={phi_s} eps=1e-{epow} hub={hub}: |f(c)|={mp.nstr(abs(fc),8)} "
                  f"max|root|={mp.nstr(max(abs(r) for r in roots),12)} "
                  f"R={mp.nstr(R,20)} L={mp.nstr(L,20)} L-2R={mp.nstr(L-2*R,8)}")
        if not L > 2 * R:
            fails.append(f"n={n} phi={phi_s} hub {hub}: L={mp.nstr(L,20)} "
                         f"no longer exceeds 2R={mp.nstr(2*R,20)}")
    return fails


def part_charge(verbose):
    fails = []
    for n, ref in KAPPA.items():
        nu = cmath.exp(1j * n * math.pi / (n - 1))
        d = kappa_model(n, nu)
        if d is None:
            fails.append(f"n={n}: tracer failed")
            continue
        if verbose:
            print(f"  n={n:>3}: kappa={d['kappa']:.10f} ref={ref:.10f} "
                  f"charge={d['charge']:.10f} |kappa-charge|={abs(d['kappa']-d['charge']):.2e}")
        if abs(d["kappa"] - ref) > 5e-9:
            fails.append(f"n={n}: kappa {d['kappa']:.10f} != recorded {ref:.10f}")
        if abs(d["kappa"] - d["charge"]) > 5e-8:
            fails.append(f"n={n}: support-function charge {d['charge']:.10f} "
                         f"!= 2-(ex1+ex2) {d['kappa']:.10f}")
    return fails


def part_sign(verbose):
    """At the ALIGNED hub the charge integrand is pointwise nonnegative, so the
    residue is positive termwise there.  That is exactly what fails at other
    hubs, which is the content of PerHubChargeSign.md."""
    fails = []
    for n in (3, 4, 5, 6, 8, 12, 20, 30):
        nu = cmath.exp(1j * n * math.pi / (n - 1))
        d = kappa_model(n, nu)
        if d is None:
            fails.append(f"n={n}: tracer failed")
            continue
        if verbose:
            print(f"  n={n:>3}: negative charge mass fraction {d['neg_fraction']:.2e}, "
                  f"worst algebraic identity error {d['worst_id']:.2e}")
        if d["neg_fraction"] > 1e-11:
            fails.append(f"n={n}: charge integrand carries negative mass at the aligned "
                         f"hub (fraction {d['neg_fraction']:.2e})")
        if d["worst_id"] > 1e-6:
            fails.append(f"n={n}: algebraic charge identity failed "
                         f"(relative error {d['worst_id']:.2e})")
    return fails


PARTS = {"witness": part_witness, "charge": part_charge, "sign": part_sign}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--part", choices=sorted(PARTS) + ["all"], default="all")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args()
    chosen = sorted(PARTS) if args.part == "all" else [args.part]
    all_fails = []
    for name in chosen:
        if not args.quiet:
            print(f"[{name}]")
        fails = PARTS[name](not args.quiet)
        if fails:
            all_fails.extend(fails)
    if all_fails:
        print("\nFAIL")
        for f in all_fails:
            print("  " + f)
        return 1
    print("\nOK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
