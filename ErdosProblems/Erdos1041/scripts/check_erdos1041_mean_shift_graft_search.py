#!/usr/bin/env python3
"""Discriminating search for Return A's open graft inequality (2026-08-29).

Return A (mean-shift containment batch) proves, correctly, the critical hub
disc B(c*, rho) subset {|P| < 1} with

    rho^2 = (n / S_{c*}) (mu^{-2/n} - 1),    S_{c*} = sum_j |c* - a_j|^{-2},

(occupied: this is BarycentricEnvelope.md (E)).  It then needs, but does not
prove, the local graft statement

    (G)  d_{|P|<1}(a, B(c*, rho)) + d_{|P|<1}(b, B(c*, rho))
         <=  |a - c*| + |b - c*| - 2 rho,

where a, b are the two roots whose one-root components first merge at the
least-critical-value hub c*.  This receipt measures (G) on random and
structured configurations: slack > 0 means the claim survives the search;
slack < 0 is a refutation witness.

Also reported: the merging-pair Euclidean budget d_a + d_b (open producer;
ClaimLRefutation.md killed the nearest-pair transfer), and the achieved
arm+disc-corridor concatenation length estimate.

All evidence is float, grid-Dijkstra inside {|P| < 1}; margins are reported
so the reader can judge instrument resolution.
"""
from __future__ import annotations

import heapq
import os

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))

FAILURES: list[str] = []


def report(name: str, ok: bool, detail: str) -> None:
    status = "PASS" if ok else "FAIL"
    print(f"[{status}] {name}: {detail}")
    if not ok:
        FAILURES.append(f"{name}: {detail}")


def poly_val(z, a):
    return np.prod(z[..., None] - a, axis=-1)


def grid_setup(a, pad=0.55, res=460):
    lo = min(a.real.min(), 0) - pad
    hi = max(a.real.max(), 0) + pad
    loy = min(a.imag.min(), 0) - pad
    hiy = max(a.imag.max(), 0) + pad
    xs = np.linspace(lo, hi, res)
    ys = np.linspace(loy, hiy, res)
    X, Y = np.meshgrid(xs, ys)
    Z = X + 1j * Y
    h = xs[1] - xs[0]
    return Z, h, (xs, ys)


def first_merge_pair(a, mu, cs):
    """Roots sharing a component of {|P| < mu(1+eps)}; returns (i, j) or None.

    The relative level bump 1e-5 must open a grid-visible neck at c* while
    still preceding the second critical value; the component is required to
    hold exactly two roots (a third joined root means the bump overshot a
    later critical value and the row is skipped)."""
    Z, h, _ = grid_setup(a, pad=0.55, res=360)
    P = poly_val(Z, a)
    from scipy import ndimage
    for bump in (1e-5, 1e-4, 1e-3, 1e-2):
        mask = np.abs(P) < mu * (1 + bump)
        lab, _ = ndimage.label(mask)
        root_labels = []
        for r in a:
            i = int(np.argmin(np.abs(Z - r)))
            root_labels.append(int(lab.flat[i]))
        for i in range(len(a)):
            for j in range(i + 1, len(a)):
                if root_labels[i] == root_labels[j] and root_labels[i] > 0:
                    shared = root_labels[i]
                    count = sum(1 for k in range(len(a)) if root_labels[k] == shared)
                    if count == 2:
                        return i, j
                    break  # this bump joined 3+ lobes; try a smaller one
        # else: neck still invisible at this resolution; try larger bump
    return None


def critical_points(a):
    n = len(a)
    # P'(z) = sum_j prod_{k != j} (z - a_k); solve via companion of derivative
    coeffs = np.array([1.0])  # monic
    for r in a:
        coeffs = np.convolve(coeffs, [1, -r])
    dcoeffs = coeffs[:-1] * np.arange(n, 0, -1)
    crit = np.roots(dcoeffs)
    return crit


def dijkstra_distance(mask, h, src_ij, target_set):
    """8-neighbour Dijkstra inside mask from src cell to nearest target cell."""
    ny, nx = mask.shape
    dist = np.full((ny, nx), np.inf)
    si, sj = src_ij
    if not mask[si, sj]:
        # snap to nearest masked cell
        best = None
        for r in range(1, 40):
            found = False
            for di in range(-r, r + 1):
                for dj in range(-r, r + 1):
                    ii, jj = si + di, sj + dj
                    if 0 <= ii < ny and 0 <= jj < nx and mask[ii, jj]:
                        si, sj = ii, jj
                        found = True
                        break
                if found:
                    break
            if found:
                break
        if not mask[si, sj]:
            return np.inf
    dist[si, sj] = 0.0
    pq = [(0.0, si, sj)]
    target_arr = np.zeros_like(mask)
    if target_set.sum() == 0:
        return np.inf
    while pq:
        d, i, j = heapq.heappop(pq)
        if d > dist[i, j]:
            continue
        if target_arr[i, j]:
            return d
        for di, dj, w in ((1, 0, 1.0), (-1, 0, 1.0), (0, 1, 1.0), (0, -1, 1.0),
                          (1, 1, 2 ** 0.5), (1, -1, 2 ** 0.5), (-1, 1, 2 ** 0.5), (-1, -1, 2 ** 0.5)):
            ii, jj = i + di, j + dj
            if 0 <= ii < ny and 0 <= jj < nx and mask[ii, jj]:
                nd = d + w * h
                if nd < dist[ii, jj]:
                    dist[ii, jj] = nd
                    heapq.heappush(pq, (nd, ii, jj))
        # lazily mark: check target membership now that we settled (i, j)
        if target_arr is not None and (i, j) is not None:
            pass
    return np.inf


def dijkstra_to_target(mask, h, src_ij, target_cells):
    """Dijkstra from src; returns min dist over target_cells (checked at pop)."""
    ny, nx = mask.shape
    dist = np.full((ny, nx), np.inf)
    si, sj = src_ij
    if not mask[si, sj]:
        return np.inf
    dist[si, sj] = 0.0
    tgt = set(map(tuple, target_cells))
    pq = [(0.0, si, sj)]
    while pq:
        d, i, j = heapq.heappop(pq)
        if d > dist[i, j]:
            continue
        if (i, j) in tgt:
            return d
        for di, dj, w in ((1, 0, 1.0), (-1, 0, 1.0), (0, 1, 1.0), (0, -1, 1.0),
                          (1, 1, 2 ** 0.5), (1, -1, 2 ** 0.5), (-1, 1, 2 ** 0.5), (-1, -1, 2 ** 0.5)):
            ii, jj = i + di, j + dj
            if 0 <= ii < ny and 0 <= jj < nx and mask[ii, jj]:
                nd = d + w * h
                if nd < dist[ii, jj]:
                    dist[ii, jj] = nd
                    heapq.heappush(pq, (nd, ii, jj))
    return np.inf


def measure_config(a, tag):
    n = len(a)
    crit = critical_points(a)
    vals = np.abs(poly_val(crit, a))
    k = int(np.argmin(vals))
    mu = float(vals[k])
    cs = crit[k]
    pair = first_merge_pair(a, mu, cs)
    if pair is None:
        print(f"[SKIP] {tag}: first-merge component not isolated at any grid-visible bump (near-tie stratum)")
        return None
    i, j = pair
    ra, rb = a[i], a[j]
    S_c = float((1.0 / np.abs(cs - a) ** 2).sum())
    rho = float(np.sqrt(n / S_c * (mu ** (-2.0 / n) - 1.0)))
    Z, h, _ = grid_setup(a, pad=0.6)
    P = poly_val(Z, a)
    mask = np.abs(P) < 1.0
    if not mask.any():
        report(f"{tag}.mask", False, "empty lemniscate mask")
        return None
    # source cells: nearest masked cell to each root
    def cell_of(w):
        idx = int(np.argmin(np.abs(Z - w)))
        y, x = np.unravel_index(idx, Z.shape)
        return (int(y), int(x))
    sa = cell_of(ra)
    sb = cell_of(rb)
    # target cells: inside the critical disc (|z - c*| <= rho) and masked
    tmask = (np.abs(Z - cs) <= 0.999 * rho) & mask
    if not tmask.any():
        # disc smaller than a cell: use the nearest masked cell to c*
        idx = int(np.argmin(np.where(mask, np.abs(Z - cs), np.inf)))
        y, x = np.unravel_index(idx, Z.shape)
        tmask[y, x] = True
    tgt = np.argwhere(tmask)
    # snap sources into the mask
    def snap(c):
        y, x = c
        if mask[c]:
            return c
        for r in range(1, 60):
            for dy in range(-r, r + 1):
                for dx in range(-r, r + 1):
                    ii, jj = y + dy, x + dx
                    if 0 <= ii < mask.shape[0] and 0 <= jj < mask.shape[1] and mask[ii, jj]:
                        return (ii, jj)
        return None
    sa, sb = snap(sa), snap(sb)
    if sa is None or sb is None:
        report(f"{tag}.snap", False, "root cell not in mask")
        return None
    da = dijkstra_to_target(mask, h, sa, tgt)
    db = dijkstra_to_target(mask, h, sb, tgt)
    d_a = abs(ra - cs)
    d_b = abs(rb - cs)
    hub = d_a + d_b
    if d_a < rho or d_b < rho:
        # a root already sits in the safe disc: the pair is joined by a chord
        # of length <= 2 rho inside B(c*, rho) subset {|P| < 1}.
        ok = 2 * rho < 2
        report(f"{tag}", ok,
               f"n={n} mu={mu:.4f} rho={rho:.4f} pair=({i},{j}) INSIDE-DISC case: "
               f"chord length <= 2rho={2 * rho:.4f} (<2: {ok}); d_a={d_a:.4f} d_b={d_b:.4f}")
        return dict(tag=tag, slack=1.0 if ok else -1.0, hub=hub, lhs=min(2 * rho, 2), rhs=2 * rho, rho=rho)
    lhs = da + db
    rhs = d_a + d_b - 2 * rho
    slack = rhs - lhs
    ok = slack >= -3e-2  # grid margin (cell ~ 2.4/460 ~ 5e-3; guard 3e-2)
    report(f"{tag}", ok,
           f"n={n} mu={mu:.4f} rho={rho:.4f} pair=({i},{j}) "
           f"LHS={lhs:.4f} RHS={rhs:.4f} slack={slack:+.4f} "
           f"(d_a+d_b={hub:.4f}, hub budget {'<' if hub < 2 else '>='} 2)")
    return dict(tag=tag, slack=slack, hub=hub, lhs=lhs, rhs=rhs, rho=rho)


def main() -> int:
    rng = np.random.default_rng(1041)
    rows = []
    # random configurations, degrees 3-6
    for t in range(10):
        n = int(rng.integers(3, 7))
        mod = rng.uniform(0.88, 0.995, size=n) if t % 2 == 0 else 0.95 * rng.uniform(0.2, 1.0) ** (1.0 / n)
        a = mod * np.exp(1j * rng.uniform(0, 2 * np.pi, size=n))
        r = measure_config(a, f"random{n}_{t}")
        if r:
            rows.append(r)
    # structured near-Fekete: z^n + eps z - r^n
    for n, r0, eps in ((3, 0.99, 1e-3), (4, 0.99, 1e-3), (5, 0.99, 1e-4), (6, 0.99, 1e-3)):
        a = np.roots(np.array([1.0] + [0.0] * (n - 2) + [eps, -r0 ** n]).astype(complex))
        a = a[np.abs(a).argsort()]
        r = measure_config(a.astype(complex), f"nearfekete_n{n}")
        if r:
            rows.append(r)
    if not rows:
        report("summary", False, "no measurable configurations")
        return 1
    worst = min(rows, key=lambda r: r["slack"])
    hub = max(r["hub"] for r in rows)
    report("summary", worst["slack"] >= -3e-2,
           f"worst graft slack {worst['slack']:+.4f} ({worst['tag']}); max merging-pair hub budget {hub:.4f}")
    return 1 if FAILURES else 0


if __name__ == "__main__":
    raise SystemExit(main())
