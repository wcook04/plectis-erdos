#!/usr/bin/env python3
"""Structure probe for producer `concyclic_form_a_cut_objective_below_one`.

Three experiments, measurement grade (float, dense grids, refinement):
  E1  gap-restricted circle max:  min_k max_{psi in G_k} log|g(s e^{i psi})|
      compared against the regular-gon value log(1+s^n) at every s.
  E2  optimizer anatomy of the Form A-cut objective near the regular n-gon:
      winning gap, winning radius, entry radii tau_j, sigma_1 tilt balance.
  E3  topological co-connectivity: does some component of {|g| <= 1} cap D
      contain two distinct roots (grid contour labelling)?

Run:  python3 research_corpus/Erdos1041/scripts/probe_erdos1041_concyclic_structure.py
"""
import math
import numpy as np

rng = np.random.default_rng(20260825)


def potentials(w, psi_grid, s_grid):
    """Pi[s_idx, psi_idx] = log|g(s e^{i psi})|."""
    dphi = psi_grid[None, None, :] - w[None, :, None]        # (1,n,P)
    return (np.log(np.maximum(np.abs(1.0 - s_grid[:, None, None] * np.exp(1j * dphi)), 1e-300))
            .sum(axis=1))


def gap_maxima(Pi, phi, pad=400):
    """max of Pi over each gap interval [phi_k, phi_{k+1}] (dense grid)."""
    n = len(phi)
    out = np.empty(n)
    for k in range(n):
        a, b = phi[k], phi[(k + 1) % n]
        b = b + 2 * math.pi if b <= a else b
        th = np.linspace(a, b, pad)
        vals = np.interp(th, np.concatenate([np.linspace(0, 2 * math.pi, len(phi) * 0 + Pi.shape[1])]),
                         np.zeros(1)) if False else None
        out[k] = np.nan
    return out


def gap_max_exact_grid(w, phi, s, pad=600):
    n = len(phi)
    out = np.empty(n)
    th_full = np.linspace(0, 2 * math.pi, pad * n, endpoint=False)
    val = np.abs(1 - s * np.exp(1j * (th_full[:, None] - w[None, :])))
    logv = np.log(np.maximum(val.prod(axis=1), 1e-300))
    order = np.argsort(np.mod(th_full, 2 * math.pi))
    th_full, logv = th_full[order], logv[order]
    th_w = np.concatenate([th_full, th_full + 2 * math.pi])
    lv_w = np.concatenate([logv, logv])
    for k in range(n):
        a, b = phi[k], phi[(k + 1) % n]
        b = b + 2 * math.pi if b <= a else b
        m = (th_w >= a - 1e-12) & (th_w <= b + 1e-12)
        out[k] = lv_w[m].max()
    return out


def taus(w, M=4001):
    t = np.linspace(0, 1, M)
    Z = t[:, None] * w[None, :]
    L = np.log(np.maximum(np.abs(Z[:, :, None] - w[None, None, :]).prod(axis=2), 1e-300))
    out = np.zeros(len(w))
    for j in range(len(w)):
        bad = L[:, j] > 0
        if bad.any():
            out[j] = t[np.max(np.where(bad)[0])]
    return out


def chord_max_curve(w, i, j, lo, NS=220, MT=481):
    if lo >= 1.0:
        return np.array([np.inf]), np.array([1.0])
    s = np.unique(np.concatenate([np.linspace(lo, 1.0, NS),
                                  lo + (1 - lo) * np.geomspace(1e-6, 1.0, NS)]))
    tau = np.linspace(0, 1, MT)
    Z = s[:, None] * (w[i] + tau[None, :] * (w[j] - w[i]))
    vals = np.abs(Z[:, :, None] - w[None, None, :]).prod(axis=2).max(axis=1)
    return s, vals


def config_V(ph, want_anatomy=False):
    p = np.sort(ph % (2 * math.pi))
    n = len(p)
    w = np.exp(1j * p)
    tj = taus(w)
    best, rec = np.inf, None
    for i in range(n):
        j = (i + 1) % n
        lo = max(tj[i], tj[j])
        s, vals = chord_max_curve(w, i, j, lo)
        m = int(np.argmin(vals))
        if vals[m] < best:
            best = vals[m]
            rec = dict(gap=i, s=float(s[m]), B=float(lo), V=float(vals[m]))
    if want_anatomy:
        return best, rec, tj, p
    return best


print("=" * 72)
print("E1: min_k max_{G_k} log|g(s e^{i psi})|  vs  regular value log(1+s^n)")
print("=" * 72)


def brute_gapmax(w, phi, s, pad=3000):
    n = len(w)
    th = np.linspace(0, 2 * math.pi, pad, endpoint=False)
    P = np.sort(phi % (2 * math.pi))
    out = []
    for k in range(n):
        a, b = P[k], P[(k + 1) % n]
        b = b + 2 * math.pi if b <= a else b
        sel = (th >= a) & (th <= b) if b <= 2 * math.pi else ((th >= a) | (th <= b - 2 * math.pi))
        pts = s * np.exp(1j * th[sel])
        vals = np.abs(pts[:, None] - w[None, :]).prod(axis=1)
        out.append(np.log(np.maximum(vals, 1e-300)).max())
    return np.array(out)


for n in [3, 4, 5, 6, 7]:
    worst_ratio = -np.inf
    worst_info = None
    for trial in range(60):
        if trial == 0:
            ph = 2 * math.pi * np.arange(n) / n
        elif trial == 1:
            ph = 2 * math.pi * np.arange(n) / n + rng.normal(0, 1e-3, n)
        else:
            ph = rng.uniform(0, 2 * math.pi, n)
        P = np.sort(ph % (2 * math.pi))
        if np.min(np.diff(np.concatenate([P, [P[0] + 2 * math.pi]]))) < 0.05 and trial > 1:
            continue
        w = np.exp(1j * P)
        for s in [0.2, 0.5, 0.75, 0.9, 0.99]:
            gm = brute_gapmax(w, P, s)
            lhs = gm.min()
            rhs = math.log(1 + s ** n)
            if lhs - rhs > worst_ratio:
                worst_ratio = lhs - rhs
                worst_info = (trial, s, float(lhs), float(rhs), np.round(P, 3).tolist())
    print(f"n={n}:  worst (min_gap_max - log(1+s^n)) = {worst_ratio:+.6f}"
          f"   at trial/s {worst_info[0]},{worst_info[1]}  ({worst_info[2]:.6f} vs {worst_info[3]:.6f})")

print()
print("=" * 72)
print("E2: optimizer anatomy of V near the regular n-gon")
print("=" * 72)
for n in [4, 5, 6, 7]:
    print(f"-- n={n}")
    for scale in [1e-1, 1e-2, 1e-3, 1e-4]:
        ph = 2 * math.pi * np.arange(n) / n + rng.normal(0, scale, n)
        v, rec, tj, p = config_V(ph, want_anatomy=True)
        w = np.exp(1j * p)
        s1 = w.sum()
        mu = (p[:-1] + p[1:]) / 2
        mudiff = np.abs(((mu - np.angle(s1) + math.pi) % (2 * math.pi)) - math.pi)
        front = np.cos(mudiff)
        pred = (abs(s1) * max(front.max(), 1e-9) / n) ** (1.0 / (n - 1)) if abs(s1) > 0 else 0.0
        print(f"  scale={scale:g}  V={v:.10f}  win_gap={rec['gap']} s*={rec['s']:.5f} "
              f"B={rec['B']:.5f}  |sig1|={abs(s1):.4f}  s_pred={pred:.5f}  "
              f"tau={np.round(tj,4).tolist()}")

print()
print("=" * 72)
print("E3: co-connectivity of {|g|<=1} inside the closed disk (grid)")
print("=" * 72)
try:
    from scipy import ndimage
    HAVE_SCIPY = True
except Exception:
    HAVE_SCIPY = False
print("scipy:", HAVE_SCIPY)
if HAVE_SCIPY:
    for n in [3, 4, 5, 6]:
        for kind in ["cluster", "random"]:
            if kind == "cluster":
                ph = np.concatenate([rng.normal(0, 0.35, n // 2),
                                     rng.normal(math.pi, 0.35, n - n // 2)])
            else:
                ph = rng.uniform(0, 2 * math.pi, n)
            w = np.exp(1j * ph)
            gpts = 900
            x = np.linspace(-1.02, 1.02, gpts)
            X, Y = np.meshgrid(x, x)
            Z = X + 1j * Y
            inside = np.abs(Z) <= 1.0
            V = np.abs(Z[..., None] - w[None, None, :]).prod(axis=2)
            K = (V <= 1.0) & inside
            lab, nl = ndimage.label(K)
            roots_cells = ((np.clip((w.real + 1.02) / 2.04 * (gpts - 1), 0, gpts - 1).astype(int)),
                           (np.clip((w.imag + 1.02) / 2.04 * (gpts - 1), 0, gpts - 1).astype(int)))
            root_labels = [lab[roots_cells[1][k], roots_cells[0][k]] for k in range(n)]
            counts = {}
            for rl in root_labels:
                counts[rl] = counts.get(rl, 0) + 1
            mx = max(counts.values())
            print(f"n={n} {kind:7s}: components={nl:4d}  max roots sharing one component = {mx}"
                  f"  {'OK>=2' if mx >= 2 else 'SEPARATED!!'}")
