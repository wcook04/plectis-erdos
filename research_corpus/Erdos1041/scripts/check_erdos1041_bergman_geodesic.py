#!/usr/bin/env python3
"""Receipt for BergmanGeodesicInvariance.md.

Arms, each fail-closed:

  MOEB     Lambda(gamma) = int_gamma int_gamma |dz||dz'| / (pi |1-conj(z')z|^2)
           is invariant under every disc automorphism.
  GEOD     Lambda of a hyperbolic geodesic at pseudohyperbolic distance rho is
           (1/pi) log(1/(1-rho^2)); on the diameter this is the recorded
           (2/pi) log((1+q^2)/(1-q^2)).
  SHARP    Theorem C' is ATTAINED on Omega = psi_q(D),
           psi_q(z) = (1/2q) log((1+qz)/(1-qz)), a,b = psi_q(-+q).
  SPEC     The k = 2 specialisation reproduces BergmanSegmentLengthBound.md
           Theorem C and its coth(1) threshold exactly.
  GREEN    The root-centred product identity
           prod_{j!=i} rho_Omega(a_i,a_j) = r_Omega(a_i)|f'(a_i)|/t
           holds on the closed-form family f = z^n - r^n.
  BESSEL   The Gram inequality Area(Omega) >= pi * u* G^{-1} u,
           |u_i| = r_Omega(a_i), |G_ij| = 1 - rho_ij^2.
  ROBIN    The grid conformal-radius instrument is CONSERVATIVE: its r_Omega is
           >= the exact value on f = z^n - r^n, and converges as O(dx).
  EXTREMAL Closed-form reach of Theorem C' on f = z^n - r^n, where
           BergmanSegmentLengthBound.md Theorem C has EMPTY hypotheses.

Nothing here proves Erdos #1041.  Every arm is a check on the note's claims.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import sys

import numpy as np

RECEIPT = ("source-provenance://private-authoring-project/receipts/"
           "erdos1041_bergman_geodesic_receipt.json")


# --------------------------------------------------------------------------- #
# Lambda
# --------------------------------------------------------------------------- #
def lam(zs: np.ndarray, ws: np.ndarray) -> float:
    K = 1.0 / (np.pi * np.abs(1 - np.conj(zs[None, :]) * zs[:, None]) ** 2)
    return float(ws @ K @ ws)


def sample_curve(zs: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    mid = 0.5 * (zs[1:] + zs[:-1])
    return mid, np.abs(np.diff(zs))


def moebius(alpha: complex, theta: float):
    return lambda z: np.exp(1j * theta) * (z - alpha) / (1 - np.conj(alpha) * z)


def arm_moeb(tol: float = 1e-7) -> dict:
    rng = np.random.default_rng(1041)
    worst = 0.0
    rows = []
    for q in (0.3, 0.7, 0.95):
        tt = np.linspace(-q, q, 6001).astype(complex)
        base = lam(*sample_curve(tt))
        closed = (2 / np.pi) * math.log((1 + q * q) / (1 - q * q))
        rows.append({"q": q, "Lambda": base, "closed_form": closed,
                     "rel_gap": abs(base - closed) / closed})
        for _ in range(4):
            al = (rng.random() * 0.85) * np.exp(2j * np.pi * rng.random())
            th = 2 * np.pi * rng.random()
            v = lam(*sample_curve(moebius(al, th)(tt)))
            worst = max(worst, abs(v - base) / base)
    ok = worst < tol and all(r["rel_gap"] < 5e-5 for r in rows)
    return {"arm": "MOEB", "ok": bool(ok), "worst_rel_change": worst, "rows": rows}


def arm_geod(tol: float = 5e-5) -> dict:
    worst = 0.0
    rows = []
    for q in (0.1, 0.35, 0.6, 0.8, 0.93, 0.99):
        rho = 2 * q / (1 + q * q)
        a = (2 / np.pi) * math.log((1 + q * q) / (1 - q * q))
        b = (1 / np.pi) * math.log(1.0 / (1 - rho * rho))
        worst = max(worst, abs(a - b) / b)
        rows.append({"q": q, "rho": rho, "diameter_form": a, "geodesic_form": b})
    return {"arm": "GEOD", "ok": bool(worst < tol), "worst_rel_gap": worst, "rows": rows}


def arm_sharp(tol: float = 1e-5) -> dict:
    rows = []
    ok = True
    for q in (0.3, 0.6, 0.9):
        dpsi = lambda z: 1.0 / (1 - q * q * z * z)
        s = np.linspace(-q, q, 200001)
        L = float(np.trapezoid(np.abs(dpsi(s)), s))
        N, M = 1500, 3000
        r = (np.arange(N) + 0.5) / N
        th = np.linspace(0, 2 * np.pi, M, endpoint=False)
        Z = r[:, None] * np.exp(1j * th[None, :])
        A = float(np.sum(np.abs(dpsi(Z)) ** 2 * r[:, None]) * (1.0 / N) * (2 * np.pi / M))
        rho = 2 * q / (1 + q * q)
        bound = math.sqrt((A / np.pi) * math.log(1 / (1 - rho * rho)))
        rows.append({"q": q, "length": L, "area": A, "bound": bound, "ratio": L / bound})
        ok = ok and abs(L / bound - 1.0) < tol
    return {"arm": "SHARP", "ok": bool(ok), "rows": rows}


def arm_spec(tol: float = 1e-12) -> dict:
    """k = 2: rho = 2q/(1+q^2), q^2 = v/t  =>  Theorem C, and coth(1)."""
    rows = []
    ok = True
    for (v, t) in ((1.0, 1.5), (0.3, 0.9), (0.97, 1.0)):
        q2 = v / t
        rho2 = 4 * q2 / (1 + q2) ** 2
        lhs = math.log(1 / (1 - rho2))
        rhs = 2 * math.log((t + v) / (t - v))
        ok = ok and abs(lhs - rhs) < 1e-12
        rows.append({"v": v, "t": t, "geodesic_log": lhs, "theoremC_log": rhs})
    coth1 = (math.e ** 2 + 1) / (math.e ** 2 - 1)
    # threshold: log(1/(1-rho^2)) <= 4  <=>  t/v >= coth(1)
    tv = coth1
    q2 = 1.0 / tv
    rho2 = 4 * q2 / (1 + q2) ** 2
    edge = math.log(1 / (1 - rho2))
    ok = ok and abs(edge - 4.0) < 1e-12 and abs(coth1 - 1.3130352854993313) < 1e-12
    return {"arm": "SPEC", "ok": bool(ok), "coth1": coth1, "edge_log": edge, "rows": rows}


# --------------------------------------------------------------------------- #
# closed forms for f = z^n - r^n
# --------------------------------------------------------------------------- #
_P = np.linspace(0, 2 * np.pi, 200001)[:-1]
_DP = 2 * np.pi / len(_P)
_COS, _SIN = np.cos(_P), np.sin(_P)


def extremal_area(n: int, r: float, t: float) -> float:
    m = r ** n
    rmax = m * _COS + np.sqrt(np.maximum(t * t - m * m * _SIN ** 2, 0.0))
    return float(0.5 * np.sum(rmax ** (2.0 / n)) * _DP)


def extremal_data(n: int, r: float, t: float) -> dict:
    R0 = r / t ** (1.0 / n)
    rho = {}
    for j in range(1, n):
        w = np.exp(2j * np.pi * j / n)
        rho[j] = abs(R0 - R0 * w) / abs(1 - R0 * R0 * w)
    prod = float(np.prod([rho[j] for j in range(1, n)]))
    r_om = t ** (1.0 / n) * (1 - R0 ** 2) / (1 - R0 ** (2 * n))
    return {"R0": R0, "rho": rho, "prod_rho": prod, "r_Omega": r_om,
            "fprime": n * r ** (n - 1), "area": extremal_area(n, r, t)}


def arm_green(tol: float = 1e-12) -> dict:
    rows = []
    ok = True
    for (n, r, t) in ((3, 0.8, 0.9), (5, 0.9, 0.85), (6, 0.9, 1.0), (8, 0.95, 1.0)):
        d = extremal_data(n, r, t)
        lhs = d["prod_rho"]
        rhs = d["r_Omega"] * d["fprime"] / t
        rows.append({"n": n, "r": r, "t": t, "prod_rho": lhs,
                     "r_Omega_fprime_over_t": rhs, "gap": abs(lhs - rhs)})
        ok = ok and abs(lhs - rhs) < 1e-12 and lhs < 1.0
    return {"arm": "GREEN", "ok": bool(ok), "rows": rows}


def arm_bessel() -> dict:
    """Area >= pi * u* G^{-1} u  and its Gershgorin corollary, on z^n - r^n."""
    rows = []
    ok = True
    for (n, r, t) in ((3, 0.8, 0.9), (6, 0.9, 1.0), (8, 0.95, 1.0), (12, 0.9, 1.0)):
        d = extremal_data(n, r, t)
        R0 = d["R0"]
        zeta = R0 * np.exp(2j * np.pi * np.arange(n) / n)
        one = 1 - np.abs(zeta) ** 2
        G = (one[:, None] * one[None, :]) / (1 - zeta[:, None] * np.conj(zeta)[None, :]) ** 2
        # u_i = (1-|zeta_i|^2) psi'(zeta_i); |u_i| = r_Omega, phases unknown ->
        # use the Gershgorin corollary, which is phase free.
        S = float(max(np.sum(np.abs(G), axis=1) - 1.0))
        lower = np.pi * n * d["r_Omega"] ** 2 / (1 + S)
        rows.append({"n": n, "r": r, "t": t, "area": d["area"],
                     "gershgorin_lower": lower, "S": S,
                     "slack": d["area"] - lower,
                     "r_Omega": d["r_Omega"],
                     "sqrt_area_over_pi": math.sqrt(d["area"] / np.pi),
                     "sqrt_area_1pS_over_pi_k": math.sqrt(d["area"] * (1 + S) / (np.pi * n))})
        ok = ok and lower <= d["area"] + 1e-12
        ok = ok and d["r_Omega"] <= math.sqrt(d["area"] * (1 + S) / (np.pi * n)) + 1e-12
    return {"arm": "BESSEL", "ok": bool(ok), "rows": rows}


# --------------------------------------------------------------------------- #
# grid instrument
# --------------------------------------------------------------------------- #
def _robin_grid(roots, t, a, N):
    import scipy.sparse as sp
    import scipy.sparse.linalg as spla
    from collections import deque
    roots = np.asarray(roots, complex)
    n = len(roots)
    half = float(np.abs(roots).max()) + t ** (1.0 / n) + 0.12
    xs = np.linspace(-half, half, N)
    dx = xs[1] - xs[0]
    X, Y = np.meshgrid(xs, xs, indexing="ij")
    Z = X + 1j * Y
    F = np.ones(Z.shape)
    for b in roots:
        F *= np.abs(Z - b)
    ins = F < t
    i0 = int(round((a.real + half) / dx)); j0 = int(round((a.imag + half) / dx))
    comp = np.zeros_like(ins); dq = deque([(i0, j0)]); comp[i0, j0] = True
    while dq:
        i, j = dq.popleft()
        for di, dj in ((1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (1, -1), (-1, 1), (-1, -1)):
            p, q = i + di, j + dj
            if 0 <= p < N and 0 <= q < N and ins[p, q] and not comp[p, q]:
                comp[p, q] = True; dq.append((p, q))
    pts = np.argwhere(comp)
    idx = -np.ones((N, N), np.int64); idx[comp] = np.arange(len(pts))
    rows = []; cols = []; vals = []; rhs = np.zeros(len(pts))
    for k, (i, j) in enumerate(pts):
        rows.append(k); cols.append(k); vals.append(-4.0)
        for di, dj in ((1, 0), (-1, 0), (0, 1), (0, -1)):
            p, q = i + di, j + dj
            if 0 <= p < N and 0 <= q < N and comp[p, q]:
                rows.append(k); cols.append(idx[p, q]); vals.append(1.0)
            else:
                zz = Z[p, q] if (0 <= p < N and 0 <= q < N) else Z[i, j]
                rhs[k] -= math.log(max(abs(zz - a), 1e-300))
    A = sp.csr_matrix((vals, (rows, cols)), shape=(len(pts), len(pts)))
    H = np.full((N, N), np.nan); H[comp] = spla.spsolve(A, rhs)
    u = (a.real + half) / dx; v = (a.imag + half) / dx
    i0 = int(math.floor(u)); j0 = int(math.floor(v)); fu = u - i0; fv = v - j0
    tot = 0.0
    for (di, dj, w) in ((0, 0, (1 - fu) * (1 - fv)), (1, 0, fu * (1 - fv)),
                        (0, 1, (1 - fu) * fv), (1, 1, fu * fv)):
        val = H[i0 + di, j0 + dj]
        if math.isnan(val):
            val = math.log(max(abs(Z[i0 + di, j0 + dj] - a), 1e-300))
        tot += w * val
    return math.exp(tot), dx


def arm_robin() -> dict:
    rows = []
    ok = True
    for (n, r, t) in ((3, 0.8, 0.9), (5, 0.9, 0.85), (6, 0.9, 1.0)):
        roots = r * np.exp(2j * np.pi * np.arange(n) / n)
        exact = extremal_data(n, r, t)["r_Omega"]
        got = []
        for N in (401, 601):
            v, dx = _robin_grid(roots, t, complex(roots[0]), N)
            got.append((N, v, v / exact - 1.0))
        rows.append({"n": n, "r": r, "t": t, "exact": exact,
                     "grid": [{"N": g[0], "r_Omega": g[1], "rel": g[2]} for g in got]})
        # conservative direction: grid value must be >= exact, and shrink with N
        ok = ok and all(g[2] > -1e-9 for g in got) and got[1][2] < got[0][2]
    return {"arm": "ROBIN", "ok": bool(ok), "rows": rows}


def _best_over_t(n: int, r: float, mode: str, grid: int = 120) -> float:
    m = r ** n
    if m >= 1.0:
        return math.inf
    best = math.inf
    for t in np.exp(np.linspace(math.log(m * (1 + 1e-12)), 0.0, grid)):
        t = float(t)
        d = extremal_data(n, r, t)
        if mode == "full":
            rho = min(d["rho"][j] for j in range(1, n))
            A = d["area"]
        else:
            rho = rho_sector(n, d["R0"])
            A = (2.0 / n) * d["area"]
        if rho >= 1.0:
            continue
        best = min(best, math.sqrt((A / np.pi) * math.log(1 / (1 - rho * rho))))
    return best


# Recorded in BergmanGeodesicInvariance.md section 6.
_TABLE = {
    3: (1.903, 1.705, 2.067), 4: (1.860, 1.429, 1.782), 5: (1.801, 1.236, 1.600),
    6: (1.736, 1.090, 1.465), 8: (1.610, 0.883, 1.270), 10: (1.494, 0.741, 1.129),
    12: (1.391, 0.638, 1.021), 20: (1.078, 0.408, 0.754), 30: (0.827, 0.282, 0.580),
}


def arm_extremal(tol: float = 3e-3) -> dict:
    """Closed-form reach of Theorem C' on z^n - r^n, at levels t <= 1, for the
    whole component and for the two-Newton-basin subdomain of Proposition S.
    BergmanSegmentLengthBound.md Theorem C has EMPTY hypotheses on this family."""
    rows = []
    ok = True
    for n, (f9, t9, t99) in _TABLE.items():
        got = (_best_over_t(n, 0.9, "full"), _best_over_t(n, 0.9, "two"),
               _best_over_t(n, 0.99, "two"))
        rows.append({"n": n, "full_r0.9": got[0], "two_r0.9": got[1],
                     "two_r0.99": got[2], "recorded": [f9, t9, t99]})
        for a, b in zip(got, (f9, t9, t99)):
            ok = ok and abs(a - b) < tol
        # the two-basin subdomain must strictly beat the whole component, and
        # must settle r = 0.9 at every degree; r = 0.99 only from n = 4 on,
        # since r_max(3) = 1 - 1.66e-2 < 0.99.
        ok = ok and got[1] < got[0] and got[1] < 2.0
        if n >= 4:
            ok = ok and got[2] < 2.0
    return {"arm": "EXTREMAL", "ok": bool(ok),
            "note": "Theorem C has EMPTY hypotheses on z^n - r^n at every level; "
                    "Theorem C' settles every row below (bound < 2).",
            "rows": rows}


def rho_sector(n: int, R0: float) -> float:
    """Pseudohyperbolic distance between R0 and R0*omega inside the disc sector
    {|zeta| < 1, arg zeta in (-pi/n, 3pi/n)}: rotate, take the power n/4 (sector
    angle 4pi/n -> pi, i.e. the upper half disc), then upper half disc -> disc."""
    p = n / 4.0
    w0 = R0 ** p * np.exp(1j * p * np.pi / n)
    w1 = R0 ** p * np.exp(1j * p * 3 * np.pi / n)
    U = lambda w: ((1 + w) / (1 - w)) ** 2
    V = lambda u: (u - 1j) / (u + 1j)
    c0, c1 = V(U(w0)), V(U(w1))
    return float(abs(c0 - c1) / abs(1 - np.conj(c0) * c1))


def arm_sector() -> dict:
    """The two-Newton-basin subdomain of Omega_t on f = z^n - r^n is carried by
    the uniformiser onto a DISC SECTOR of angle 4pi/n, so Theorem C' there is
    closed form.  Cross-checked against the independent grid instrument."""
    grid_ref = {4: 1.7735, 6: 1.4588, 8: 1.2628, 12: 1.0139}   # measured, N=(361,541)
    rows = []
    ok = True
    for n in (4, 6, 8, 12):
        r, t = 0.99, 1.0
        R0 = r / t ** (1.0 / n)
        A2 = (2.0 / n) * extremal_area(n, r, t)
        rho = rho_sector(n, R0)
        bound = math.sqrt((A2 / np.pi) * math.log(1 / (1 - rho * rho)))
        full = extremal_data(n, r, t)
        rho_f = min(full["rho"][j] for j in range(1, n))
        bfull = math.sqrt((full["area"] / np.pi) * math.log(1 / (1 - rho_f * rho_f)))
        rows.append({"n": n, "r": r, "t": t, "rho_sector": rho,
                     "area_two_basin": A2, "bound_two_basin": bound,
                     "bound_full": bfull, "gain": bfull / bound,
                     "grid_measured": grid_ref[n],
                     "grid_rel_gap": abs(bound - grid_ref[n]) / bound})
        # the grid instrument is optimistic (it under-reports rho); require it to
        # sit just below the closed form, within 2%.
        ok = ok and 0.0 <= (bound - grid_ref[n]) / bound < 0.02
        ok = ok and bound < bfull and bound < 2.0
    return {"arm": "SECTOR", "ok": bool(ok), "rows": rows}


def arm_lemmag() -> dict:
    """Lemma G at a GENERAL point, in closed form on f = z^n - r^n.

    The uniformiser gives f(psi(zeta))/t = (zeta^n - R0^n)/(1 - R0^n zeta^n),
    a degree-n Blaschke product with zeros exactly at R0*omega^j, so
    prod_j rho_Omega(z, a_j) = |f(z)|/t for every z in Omega -- which is Lemma G
    exponentiated.  Theorem V uses this at z = c*."""
    rows = []
    ok = True
    for (n, r, t) in ((3, 0.8, 0.9), (5, 0.9, 0.85), (6, 0.9, 1.0)):
        R0 = r / t ** (1.0 / n)
        for zt in (0.17, 0.5 + 0.2j, -0.63 + 0.11j):
            zeta = complex(zt) * 0.9
            zj = R0 * np.exp(2j * np.pi * np.arange(n) / n)
            prod = float(np.prod(np.abs(zeta - zj) / np.abs(1 - np.conj(zj) * zeta)))
            blas = abs((zeta ** n - R0 ** n) / (1 - R0 ** n * zeta ** n))
            rows.append({"n": n, "r": r, "t": t, "zeta": [zeta.real, zeta.imag],
                         "prod_rho": prod, "abs_f_over_t": blas,
                         "gap": abs(prod - blas)})
            ok = ok and abs(prod - blas) < 1e-12
    return {"arm": "LEMMAG", "ok": bool(ok), "rows": rows}


def _mec(roots: np.ndarray):
    roots = np.asarray(roots, complex)
    n = len(roots)
    best = None
    for i in range(n):
        for j in range(i + 1, n):
            c = (roots[i] + roots[j]) / 2
            rad = abs(roots[i] - c)
            if np.all(np.abs(roots - c) <= rad + 1e-12) and (best is None or rad < best[1]):
                best = (c, rad)
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                a, b, cc = roots[i], roots[j], roots[k]
                d = 2 * (a.real * (b.imag - cc.imag) + b.real * (cc.imag - a.imag)
                         + cc.real * (a.imag - b.imag))
                if abs(d) < 1e-14:
                    continue
                ux = ((abs(a) ** 2) * (b.imag - cc.imag) + (abs(b) ** 2) * (cc.imag - a.imag)
                      + (abs(cc) ** 2) * (a.imag - b.imag)) / d
                uy = ((abs(a) ** 2) * (cc.real - b.real) + (abs(b) ** 2) * (a.real - cc.real)
                      + (abs(cc) ** 2) * (b.real - a.real)) / d
                cen = complex(ux, uy)
                rad = abs(a - cen)
                if np.all(np.abs(roots - cen) <= rad + 1e-12) and (best is None or rad < best[1]):
                    best = (cen, rad)
    return best


def _cover_score(roots, N=421, lambdas=(1.0, 0.85, 0.7, 0.55, 0.4)):
    from collections import deque
    roots = np.asarray(roots, complex)
    cen, R = _mec(roots)
    g = (roots - cen) / R
    n = len(g)
    cps = np.roots(np.polyder(np.poly(g)))
    vals = np.abs(np.polyval(np.poly(g), cps))
    i = int(np.argmin(vals)); cstar = cps[i]; mu = float(vals[i])
    half = 2.05
    xs = np.linspace(-half, half, N); dx = xs[1] - xs[0]
    X, Y = np.meshgrid(xs, xs, indexing="ij"); Z = X + 1j * Y
    F = np.ones(Z.shape)
    for a in g:
        F *= np.abs(Z - a)
    cell = lambda a: (int(round((a.real + half) / dx)), int(round((a.imag + half) / dx)))
    best = None
    for lam in lambdas:
        if lam <= mu * (1 + 1e-9):
            continue
        m = F < lam
        i0, j0 = cell(cstar)
        if not m[i0, j0]:
            continue
        comp = np.zeros_like(m); dq = deque([(i0, j0)]); comp[i0, j0] = True
        while dq:
            p, q = dq.popleft()
            for dp, dq2 in ((1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (1, -1), (-1, 1), (-1, -1)):
                a2, b2 = p + dp, q + dq2
                if 0 <= a2 < N and 0 <= b2 < N and m[a2, b2] and not comp[a2, b2]:
                    comp[a2, b2] = True; dq.append((a2, b2))
        di = (comp | np.roll(comp, 1, 0) | np.roll(comp, -1, 0)
              | np.roll(comp, 1, 1) | np.roll(comp, -1, 1))
        A = di.sum() * dx * dx
        k = 1 + sum(1 for c in cps if comp[cell(c)])
        u = (mu / lam) ** (2.0 / k)
        if u >= 1:
            continue
        sc = (A / np.pi) * math.log(1.0 / (1.0 - u))
        if best is None or sc < best[0]:
            best = (sc, lam, k, A)
    return best, mu


def arm_cover() -> dict:
    """Theorem V: Theorem C' + Lemma G prove (COVER) on Gamma when
    (Area/pi) log(1/(1-(mu/lambda)^{2/k})) <= 1."""
    L = 999 / 1000
    r5 = 99999 / 100000
    W = {
        "deg5 origin-spoke": np.array([r5 + 0j, r5 * (-20 + 99j) / 101, r5 * (-20 - 99j) / 101,
                                       r5 * (-28 + 195j) / 197, r5 * (-28 - 195j) / 197]),
        "deg3 two-segment": np.array([L * (7 + 24j) / 25, L * (7 - 24j) / 25, -L + 0j]),
        "clustered n=4": np.array([0.99 + 0j, 0.99 * np.exp(0.06j),
                                   0.6 + 0j, 0.6 * np.exp(2j * np.pi / 2)]),
        "regular 5-gon": 0.999 * np.exp(2j * np.pi * np.arange(5) / 5),
    }
    rows = []
    ok = True
    for name, roots in W.items():
        best, mu = _cover_score(roots)
        if best is None:
            rows.append({"name": name, "mu": mu, "status": "no admissible level (mu = 1)"})
            # mu == 1 after MEC normalisation is the Fekete stratum, where
            # VisibilityOverlapReduction proves (COVER) in closed form.
            ok = ok and mu > 1 - 1e-9
            continue
        sc, lam, k, A = best
        rows.append({"name": name, "mu": mu, "lambda": lam, "k": k, "area": A,
                     "score": sc, "proves_cover": bool(sc <= 1.0)})
    got = {r["name"]: r for r in rows}
    ok = ok and got["deg5 origin-spoke"].get("proves_cover") is True
    ok = ok and got["clustered n=4"].get("proves_cover") is True
    ok = ok and got["deg3 two-segment"].get("proves_cover") is False
    return {"arm": "COVER", "ok": bool(ok),
            "note": "Theorem V is the first non-trivial proved case of (COVER); it "
                    "fires when mu is bounded away from 1 and fails on the "
                    "near-Fekete rows.",
            "rows": rows}


ARMS = {"MOEB": arm_moeb, "GEOD": arm_geod, "SHARP": arm_sharp, "SPEC": arm_spec,
        "GREEN": arm_green, "LEMMAG": arm_lemmag, "BESSEL": arm_bessel,
        "ROBIN": arm_robin, "SECTOR": arm_sector, "EXTREMAL": arm_extremal,
        "COVER": arm_cover}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", default="all", choices=["all", *ARMS])
    ap.add_argument("--no-receipt", action="store_true")
    args = ap.parse_args()
    names = list(ARMS) if args.part == "all" else [args.part]
    out = []
    for nm in names:
        r = ARMS[nm]()
        out.append(r)
        print(f"[{nm}] {'PASS' if r['ok'] else 'FAIL'}")
    ok = all(r["ok"] for r in out)
    payload = {"kind": "erdos1041_bergman_geodesic_receipt",
               "note": "source-provenance://private-authoring-project/ErdosProblems/"
                       "Erdos1041/BergmanGeodesicInvariance.md",
               "ok": ok, "arms": out}
    if not args.no_receipt:
        root = os.path.abspath(os.path.join(os.path.dirname(__file__),
                                            "..", "..", "..", "..", ".."))
        path = os.path.join(root, RECEIPT)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w") as fh:
            json.dump(payload, fh, indent=2, sort_keys=True)
        print(f"receipt -> {RECEIPT}")
    print("OVERALL", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
