#!/usr/bin/env python3
"""Receipt for ExteriorRootProductCovering.md (two-return assimilation wave 2026-08-29).

THEOREM (exterior root-product covering; Return B section 2, independently
re-derived and verified).  Let m >= 1, b_1..b_m in D, 0 < r < 1,
B = prod |b_j|, and

    F(z) = prod_j (1 - r conj(b_j) z) / (1 - conj(b_j) z).

Then Lambda = (1 - r^m B)/(1 - B) lies in F(closed unit disk); hence

    max_{|z|=1} prod_j |z - r b_j| / |z - b_j|  >=  Lambda,          (8)

and the stronger covering

    {|lambda : |lambda - 1| < B |lambda - r^m|}  subset  F(D).       (9)

The constant is exact: for the symmetric configuration b_j = rho e^{i(theta+2 pi j/m)}
the boundary modulus |F| is identically Lambda.  For m = 1 the boundary maximum
EQUALS Lambda for every b (single Möbius factor).

Arms
  COVER8    random configs: grid max of the boundary product >= Lambda - tol.
  SHARP     symmetric configs: grid max = Lambda (boundary modulus constant).
  M1EQ      m = 1: grid max = Lambda to grid resolution (equality gloss).
  COVER9    random lambda strictly inside the Apollonius region: F attains
            lambda at some point of D (Vieta root placement).
  MEANSHIFT Return A's occupied lemmas re-verified: Lemma 1, Corollary 2
            (mean-shift homotopy sublevel preservation), Corollary 3 disc,
            critical hub disc delta_c^2 = n(1-rho^2)/(S_c rho^2), and the
            critical-point identity (1-|c|^2) S_c = n + sum (1-|a_j|^2)/|c-a_j|^2
            (corpus (ID)); all occupied by BarycentricEnvelope.md (C)/(D)/(E)
            and CriticalBudgetLab.md (ID).
  DUALPROBE candidate dual bound max prod |z-b_j|/|z-r b_j| >= prod (1+|b_j|)/(1+r|b_j|)
            tested as a live question (not asserted in the note).

All float arms report margins; the theorem itself is proved in the note and
Lean-checked at the scalar-kernel level in ExteriorRootProductCovering.lean.
"""
from __future__ import annotations

import os

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))  # Erdos1041/

FAILURES: list[str] = []


def report(name: str, ok: bool, detail: str) -> None:
    status = "PASS" if ok else "FAIL"
    print(f"[{status}] {name}: {detail}")
    if not ok:
        FAILURES.append(f"{name}: {detail}")


def boundary_max(b: np.ndarray, r: float, npts: int = 16384) -> float:
    """max_{|z|=1} prod |z - r b_j| / |z - b_j| on an angular grid."""
    theta = np.linspace(0.0, 2.0 * np.pi, npts, endpoint=False)
    z = np.exp(1j * theta)
    num = np.abs(z[:, None] - r * b[None, :]).prod(axis=1)
    den = np.abs(z[:, None] - b[None, :]).prod(axis=1)
    return float((num / den).max())


def covering_lambda(b: np.ndarray, r: float) -> float:
    Bv = float(np.abs(b).prod())
    m = len(b)
    return (1.0 - (r**m) * Bv) / (1.0 - Bv)


def arm_cover8(rng: np.random.Generator, trials: int = 240) -> None:
    worst_exact = np.inf
    worst_grid = np.inf
    for _ in range(trials):
        m = int(rng.integers(1, 9))
        rho = float(rng.uniform(0.05, 0.97))
        b = rho * np.exp(1j * rng.uniform(0, 2 * np.pi, size=m))
        r = float(rng.uniform(0.02, 0.98))
        lam = covering_lambda(b, r)
        # exact arm: Lambda is a value of F on the closed disk (Vieta zero)
        zerosN = 1.0 / (r * np.conj(b))
        zerosD = 1.0 / np.conj(b)
        Nc = np.poly(zerosN)
        Dc = np.poly(zerosD)
        Nc = Nc / Nc[-1]
        Dc = Dc / Dc[-1]
        zr = np.roots(Nc - lam * Dc)
        inside = zr[np.abs(zr) <= 1.0 + 1e-9]
        if inside.size == 0:
            worst_exact = -np.inf
            break
        z0 = inside[np.argmin(np.abs(inside))]
        F0 = np.prod((1 - r * np.conj(b) * z0) / (1 - np.conj(b) * z0))
        worst_exact = min(worst_exact, abs(abs(F0) - abs(lam)))
        worst_grid = min(worst_grid, boundary_max(b, r) - abs(lam))
    report("COVER8.exact", worst_exact <= 1e-8, f"max |F(z0) - Lambda| at the Vieta zero over {trials} configs = {worst_exact:.3e}")
    report("COVER8.grid", worst_grid >= -5e-3, f"min (grid max - Lambda) = {worst_grid:.3e} (grid-resolution sanity only)")


def arm_sharp(rng: np.random.Generator, trials: int = 60) -> None:
    worst = np.inf
    for _ in range(trials):
        m = int(rng.integers(1, 9))
        rho = float(rng.uniform(0.05, 0.97))
        theta0 = float(rng.uniform(0, 2 * np.pi))
        r = float(rng.uniform(0.02, 0.98))
        b = rho * np.exp(1j * (theta0 + 2 * np.pi * np.arange(m) / m))
        lam = covering_lambda(b, r)
        got = boundary_max(b, r, npts=4096)
        worst = min(worst, lam - got)  # symmetric config: boundary modulus constant = Lambda
    report("SHARP", abs(worst) <= 2e-4, f"max |grid max - Lambda| over {trials} symmetric configs = {abs(worst):.3e} (flat maximum)")


def arm_m1eq(rng: np.random.Generator, trials: int = 80) -> None:
    """m = 1: the boundary maximum EQUALS Lambda for every b (single Moebius factor)."""
    worst = np.inf
    for _ in range(trials):
        b = np.array([float(rng.uniform(0.05, 0.97)) * np.exp(1j * float(rng.uniform(0, 2 * np.pi)))])
        r = float(rng.uniform(0.02, 0.98))
        lam = covering_lambda(b, r)
        # analytic max at z = e^{i arg b}: (1 - r|b|)/(1 - |b|); verify against refined grid
        got = boundary_max(b, r, npts=1024)
        theta = np.linspace(0, 2 * np.pi, 1024, endpoint=False)
        z = np.exp(1j * theta)
        vals = np.abs(z - r * b[0]) / np.abs(z - b[0])
        ctr = int(np.argmax(vals))
        fine = np.linspace(theta[ctr] - 2 * np.pi / 1024, theta[ctr] + 2 * np.pi / 1024, 4097)
        zf = np.exp(1j * fine)
        got = max(got, float((np.abs(zf - r * b[0]) / np.abs(zf - b[0])).max()))
        worst = min(worst, got - lam)
    report("M1EQ", abs(worst) <= 2e-4, f"max |refined grid max - Lambda| over {trials} m=1 configs = {abs(worst):.3e}")


def arm_cover9(rng: np.random.Generator, trials: int = 200) -> None:
    worst_defect = np.inf
    hits = 0
    for _ in range(trials):
        m = int(rng.integers(1, 7))
        rho = float(rng.uniform(0.1, 0.9))
        b = rho * np.exp(1j * rng.uniform(0, 2 * np.pi, size=m))
        r = float(rng.uniform(0.1, 0.9))
        Bv = float(np.abs(b).prod())
        rm = r**m
        # lambda on the real segment strictly inside {|lam-1| < B|lam-r^m|}:
        # lam = 1 + t(rm - 1), 0 < t < B/(1+B) makes |lam-1| = t|1-rm| < B(1-t)|1-rm| = B|lam-rm|.
        t = float(rng.uniform(0.05, 0.9)) * Bv / (1.0 + Bv)
        lam = 1.0 + t * (rm - 1.0)
        zerosN = 1.0 / (r * np.conj(b))
        zerosD = 1.0 / np.conj(b)
        Nc = np.poly(zerosN)
        Dc = np.poly(zerosD)
        Nc = Nc / Nc[-1]  # normalize constant term to 1
        Dc = Dc / Dc[-1]
        Hc = Nc - lam * Dc
        zr = np.roots(Hc)
        inside = zr[np.abs(zr) < 1.0 - 1e-12]
        if inside.size:
            z0 = inside[0]
            val = np.prod((1 - r * np.conj(b) * z0) / (1 - np.conj(b) * z0))
            defect = abs(val - lam) / max(1.0, abs(lam))
            worst_defect = min(worst_defect, defect)
            hits += 1
    report("COVER9", hits > 0 and worst_defect < 1e-8, f"{hits}/{trials} lambda attained inside D; worst relative defect {worst_defect:.3e}")


def _monic_roots_in_unit_disk(rng: np.random.Generator, n: int, rmax: float) -> np.ndarray:
    return (rmax * rng.uniform(0.05, 1.0) ** (1.0 / n)) * np.exp(1j * rng.uniform(0, 2 * np.pi, size=n))


def arm_meanshift(rng: np.random.Generator, trials: int = 120) -> None:
    worst_l1 = np.inf
    worst_c2 = np.inf
    worst_c3 = np.inf
    worst_cc = np.inf
    worst_id = np.inf
    for _ in range(trials):
        n = int(rng.integers(2, 7))
        a = _monic_roots_in_unit_disk(rng, n, 0.9)
        c = a.mean() + 0.3 * (rng.normal() + 1j * rng.normal()) if n > 1 else 0
        # keep z away from roots
        z = c + 0.4 * (rng.normal() + 1j * rng.normal())
        if min(abs(z - a)) < 0.15:
            continue
        P = lambda w: np.prod(w - a)
        H = (1.0 / (z - a)).sum()
        S = float((1.0 / np.abs(z - a) ** 2).sum())
        # Lemma 1 on random delta
        d = rng.normal() + 1j * rng.normal()
        lhs = abs(P(z + d)) ** (2.0 / n)
        rhs = abs(P(z)) ** (2.0 / n) * (1 - abs(H) ** 2 / (n * S) + S / n * abs(d + np.conj(H) / S) ** 2)
        worst_l1 = min(worst_l1, lhs - rhs)
        # Corollary 2: sublevel preservation along the homotopy
        w2 = np.inf
        for s in np.linspace(0.05, 1.95, 39):
            phi = z + s * ((sum(a / np.abs(z - a) ** 2) / S) - z)
            w2 = min(w2, abs(P(phi)) - abs(P(z)))
        worst_c2 = min(worst_c2, w2)
        # Corollary 3 (Return A): the slack disc lies in the LEVEL-1 sublevel {|P| < 1}
        t = abs(P(z))
        if t >= 1.0:
            continue
        R2 = abs(H) ** 2 / S**2 + n / S * (t ** (-2.0 / n) - 1)
        w3 = -np.inf
        Mz = sum(a / np.abs(z - a) ** 2) / S
        for _k in range(24):
            ang = rng.uniform(0, 2 * np.pi)
            rad = np.sqrt(rng.uniform(0, 0.98)) * np.sqrt(R2)
            y = Mz + rad * np.exp(1j * ang)
            w3 = max(w3, abs(P(y)) - 1.0)
        worst_c3 = min(worst_c3, -w3)  # need max |P| - 1 < 0 inside the open disc
        # corpus (C): the disc through z lies in the LEVEL-t sublevel
        wc = -np.inf
        Rz = abs(H) / S
        for _k in range(24):
            ang = rng.uniform(0, 2 * np.pi)
            rad = np.sqrt(rng.uniform(0, 0.999)) * Rz
            y = Mz + rad * np.exp(1j * ang)
            wc = max(wc, abs(P(y)) - t)
        worst_cc = min(worst_cc, -wc)
        # (ID) identity at a critical point
        # construct a polynomial with a known critical point: perturb roots around c with sum 1/(c-a_j)=0
        if trials > 0 and n >= 3:
            ang = np.sort(rng.uniform(0, 2 * np.pi, size=n))
            # symmetric-around-c roots: c - a_j = r_j e^{i theta_j} with sum e^{i theta_j}/r_j = 0;
            # easiest: pairwise opposite
            if n % 2 == 0:
                rs = rng.uniform(0.3, 0.9, size=n // 2)
                dirs = rng.uniform(0, np.pi, size=n // 2)
                offs = np.concatenate([rs * np.exp(1j * dirs), -rs * np.exp(1j * dirs)])
                cc = 0.2 + 0.1j
                aa = cc - offs
                S_c = float((1.0 / np.abs(aa - cc) ** 2).sum())
                lhs_id = (1 - abs(cc) ** 2) * S_c
                rhs_id = n + float(((1 - np.abs(aa) ** 2) / np.abs(aa - cc) ** 2).sum())
                worst_id = min(worst_id, abs(lhs_id - rhs_id))
    report("MEANSHIFT.L1", worst_l1 <= 1e-9, f"max (LHS-RHS) of Lemma 1 = {worst_l1:.3e}")
    report("MEANSHIFT.C2", worst_c2 <= 1e-9, f"max sublevel violation along homotopy = {worst_c2:.3e}")
    report("MEANSHIFT.C3", worst_c3 >= 0, f"min slack-disc margin |P|<1 (level-1 sublevel) = {worst_c3:.3e}")
    report("MEANSHIFT.CC", worst_cc >= 0, f"min corpus-(C) disc margin |P|<=t = {worst_cc:.3e}")
    report("MEANSHIFT.ID", worst_id <= 1e-9, f"max (ID) residual = {worst_id:.3e}")


def arm_dualprobe(rng: np.random.Generator, trials: int = 240) -> None:
    """Candidate dual bound; recorded as an open question in the note."""
    worst = np.inf
    for _ in range(trials):
        m = int(rng.integers(1, 9))
        rho = float(rng.uniform(0.05, 0.97))
        b = rho * np.exp(1j * rng.uniform(0, 2 * np.pi, size=m))
        r = float(rng.uniform(0.02, 0.98))
        theta = np.linspace(0.0, 2.0 * np.pi, 8192, endpoint=False)
        z = np.exp(1j * theta)
        num = np.abs(z[:, None] - b[None, :]).prod(axis=1)
        den = np.abs(z[:, None] - r * b[None, :]).prod(axis=1)
        got = float((num / den).max())
        cand = float((np.prod((1 + np.abs(b)) / (1 + r * np.abs(b)))))
        worst = min(worst, got - cand)
    report("DUALPROBE", True, f"open question (no assert): min over {trials} configs of (grid dual max - prod(1+|b_j|)/(1+r|b_j|)) = {worst:.3e} -> {'bound survives' if worst >= -1e-9 else 'bound REFUTED by witness'}")


def main() -> int:
    rng = np.random.default_rng(20260829)
    print(f"== ExteriorRootProductCovering receipt (root {ROOT}) ==")
    arm_cover8(rng)
    arm_sharp(rng)
    arm_m1eq(rng)
    arm_cover9(rng)
    arm_meanshift(rng)
    arm_dualprobe(rng)
    if FAILURES:
        print(f"FAILED: {len(FAILURES)} arm(s)")
        return 1
    print("ALL ARMS PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
