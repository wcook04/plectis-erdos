#!/usr/bin/env python3
"""Erdos #1041: concyclic-zero alternation theorem, verifier.

THEOREM (proved in ConcyclicAlternation.md).  Let w_1..w_n be distinct points on
the unit circle, g(z) = prod_k (z - w_k), and let A_1..A_n be the open arcs between
cyclically consecutive zeros.  Let q(z) = z^n - c with c = (-1)^{n+1} prod_k w_k.
Then some index k satisfies

    |g(z)| <= |q(z)|   for every z in A_k.                                  (T1)

Consequences, same k:
    (T2)  max_{A_k} |g| <= 2,                     constant 2 sharp (g = z^n - c).
    (T3)  the arc A_k has angular width <= 2 pi / n.
    (T4)  max_{[w_k,w_{k+1}]} |g| <= max_{A_k} |g|, strict for n >= 3   (chord lemma).

COROLLARY.  monic f, all zeros on a circle of radius rho, 2 rho^n <= 1  ==>
two zeros are joined by a straight segment of length <= 2 rho sin(pi/n) < 2
on which |f| < 1.  Erdos #1041 holds for such f.

Every maximum below is EXACT: max of |g|^2 along a segment / arc is a real
polynomial (resp. trigonometric polynomial) whose critical points are located as
polynomial roots, never sampled.
"""
from __future__ import annotations
import json, math, sys
from pathlib import Path

import numpy as np

TOL = 1e-9


# ---------------------------------------------------------------- exact maxima
def _seg_abs2_poly(w: np.ndarray, p: complex, q: complex) -> np.ndarray:
    """ascending real coeffs of tau -> |g(p + tau q)|^2 , g = prod (z-w_k)."""
    G = np.array([1.0 + 0j])
    for wk in w:
        G = np.convolve(G, np.array([p - wk, q]))
    return np.convolve(G, np.conjugate(G)).real


def _crit_taus(c: np.ndarray) -> list:
    d = np.polyder(c[::-1])
    cand = [0.0, 1.0, 0.5]
    if d.size and not np.allclose(d, 0.0):
        for z in np.roots(d):
            if abs(z.imag) < 1e-8 and -1e-11 <= z.real <= 1 + 1e-11:
                cand.append(min(1.0, max(0.0, z.real)))
    return cand


def chord_max(w: np.ndarray, i: int, j: int) -> float:
    """max of |g| on the straight segment [w_i, w_j]: critical parameters located
    as roots of a real polynomial, VALUES taken from the stable product form."""
    wl = [complex(x) for x in w]
    A, Dv = complex(w[i]), complex(w[j] - w[i])
    f = lambda t: absg_pt_scalar(wl, A + t * Dv)
    taus = np.unique(np.concatenate([np.array(_crit_taus(_seg_abs2_poly(w, w[i], w[j] - w[i]))),
                                     np.linspace(0.0, 1.0, 17)]))
    vals = [f(float(t)) for t in taus]
    best = max(vals)
    c0 = float(taus[int(np.argmax(vals))])
    return max(best, _golden(f, max(0.0, c0 - 2e-3), min(1.0, c0 + 2e-3)))


def _circ_laurent(w: np.ndarray, extra: np.ndarray | None = None) -> np.ndarray:
    """Descending coeffs of P with  |g(x)|^2 = x^{-n} P(x)  on |x| = 1.

    P = g * h,  h(x) = prod_k (1 - conj(w_k) x).   deg P = 2n.
    `extra` (descending, degree 2n) is added to P if given.
    """
    G = np.array([1.0 + 0j])
    for wk in w:
        G = np.convolve(G, np.array([1.0 + 0j, -wk]))          # (x - w_k)
    H = np.array([1.0 + 0j])
    for wk in w:
        H = np.convolve(H, np.array([-np.conjugate(wk), 1.0 + 0j]))  # (1 - conj(w_k) x)
    P = np.convolve(G, H)
    if extra is not None:
        P = P + extra
    return P


def _crit_psis(P: np.ndarray, n: int) -> np.ndarray:
    """psi with x = e^{i psi} a critical point of  psi -> x^{-n} P(x)  on |x|=1.

    d/dpsi [x^{-n} P] = i x^{-n} (x P' - n P);  so solve x P'(x) - n P(x) = 0.
    """
    dP = np.polyder(P)
    xdP = np.concatenate([dP, [0.0 + 0j]])          # multiply by x
    poly = xdP - n * P
    while poly.size and abs(poly[0]) < 1e-14:
        poly = poly[1:]
    if poly.size < 2:
        return np.array([])
    rs = np.roots(poly)
    rs = rs[np.abs(np.abs(rs) - 1.0) < 1e-3]
    return np.angle(rs) % (2 * math.pi)


def _eval_circ(P: np.ndarray, n: int, psi) -> np.ndarray:
    x = np.exp(1j * np.asarray(psi, float))
    return np.real(x ** (-n) * np.polyval(P, x))


def absg_psi(phis: np.ndarray, psi) -> np.ndarray:
    """|g(e^{i psi})| = prod_k |2 sin((psi-phi_k)/2)|, evaluated in log space.

    The degree-2n Laurent polynomial of _circ_laurent LOCATES critical points but
    must never EVALUATE them: for clustered zeros it cancels catastrophically and
    under-reports, which is the instrument-defect direction that flatters every
    containment claim (research_packet negative_results entries 24, 34, 41, 44).
    """
    t = np.atleast_1d(np.asarray(psi, float))
    f = np.abs(2.0 * np.sin((t[:, None] - phis[None, :]) / 2.0))
    out = np.where(np.any(f == 0.0, axis=1), 0.0,
                   np.exp(np.log(np.where(f == 0.0, 1.0, f)).sum(axis=1)))
    return out


def absg_psi_scalar(phis_list, psi: float) -> float:
    acc = 0.0
    for ph in phis_list:
        v = abs(2.0 * math.sin((psi - ph) / 2.0))
        if v == 0.0:
            return 0.0
        acc += math.log(v)
    return math.exp(acc)


def absg_pt_scalar(w_list, z: complex) -> float:
    acc = 0.0
    for wk in w_list:
        v = abs(z - wk)
        if v == 0.0:
            return 0.0
        acc += math.log(v)
    return math.exp(acc)


def absg_pts(w: np.ndarray, Z) -> np.ndarray:
    """|g(z)| for arbitrary z, in log space."""
    Zf = np.atleast_1d(np.asarray(Z, dtype=complex))
    d = np.abs(Zf[:, None] - w[None, :])
    return np.where(np.any(d == 0.0, axis=1), 0.0,
                    np.exp(np.log(np.where(d == 0.0, 1.0, d)).sum(axis=1)))


def _golden(fn, lo: float, hi: float, iters: int = 60) -> float:
    """maximise fn on [lo,hi] by golden section on the STABLE evaluator.

    The degree-2n locator gives the bracket; this removes its conditioning error,
    which for clustered zeros reaches 1e-8 relative and always UNDER-reports.
    """
    gr = (math.sqrt(5.0) - 1.0) / 2.0
    x1 = hi - gr * (hi - lo)
    x2 = lo + gr * (hi - lo)
    f1, f2 = float(fn(x1)), float(fn(x2))
    for _ in range(iters):
        if f1 < f2:
            lo, x1, f1 = x1, x2, f2
            x2 = lo + gr * (hi - lo)
            f2 = float(fn(x2))
        else:
            hi, x2, f2 = x2, x1, f1
            x1 = hi - gr * (hi - lo)
            f1 = float(fn(x1))
        if hi - lo < 1e-16 * max(1.0, abs(hi)):
            break
    return max(f1, f2)


def _in_arc(psi, a, b) -> np.ndarray:
    """psi (mod 2pi) inside the arc (a,b), b > a, b - a <= 2pi."""
    t = (np.asarray(psi, float) - a) % (2 * math.pi)
    return (t > 1e-12) & (t < (b - a) - 1e-12)


def arc_max(phis: np.ndarray, k: int) -> float:
    """EXACT max of |g| on the open arc A_k."""
    n = len(phis)
    w = np.exp(1j * phis)
    P = _circ_laurent(w)
    a = phis[k]
    b = phis[(k + 1) % n] + (2 * math.pi if k == n - 1 else 0.0)
    cps = _crit_psis(P, n)
    sel = cps[_in_arc(cps, a, b)] if cps.size else np.array([])
    # LIFT into the [a, b] branch: on the wrapping gap (k = n-1) a selected psi
    # can sit in [0, phi_0) < a, and an unlifted value inverts the refinement
    # bracket below, which returns values from OUTSIDE the arc.
    sel = a + ((sel - a) % (2 * math.pi)) if sel.size else sel
    cand = np.concatenate([sel, [a, b], a + (b - a) * np.linspace(0.0, 1.0, 601)])
    vals = absg_psi(phis, cand)
    best = float(np.max(vals))
    pl = [float(x) for x in phis]
    win = 2e-3 * (b - a)
    c0 = float(cand[int(np.argmax(vals))])
    return max(best, _golden(lambda t: absg_psi_scalar(pl, t),
                             max(a, c0 - win), min(b, c0 + win)))


def comparison_c(phis: np.ndarray) -> complex:
    n = len(phis)
    return ((-1) ** (n + 1)) * np.exp(1j * float(np.sum(phis)))


def gap_ratio_ok(phis: np.ndarray, k: int) -> bool:
    """EXACT test of  |g| <= |q|  pointwise on the open arc A_k.

    |g|^2 - |q|^2 = x^{-n} Q(x) with Q = P + conj(c) x^{2n} - 2 x^n + c.
    """
    n = len(phis)
    w = np.exp(1j * phis)
    c = comparison_c(phis)
    extra = np.zeros(2 * n + 1, dtype=complex)
    extra[0] = np.conjugate(c)          # x^{2n}
    extra[n] = -2.0                     # x^n
    extra[2 * n] = c                    # 1
    Q = _circ_laurent(w, extra)
    a = phis[k]
    b = phis[(k + 1) % n] + (2 * math.pi if k == n - 1 else 0.0)
    cps = _crit_psis(Q, n)
    sel = cps[_in_arc(cps, a, b)] if cps.size else np.array([])
    sel = a + ((sel - a) % (2 * math.pi)) if sel.size else sel
    mids = a + (b - a) * np.linspace(0.0005, 0.9995, 1200)
    cand = np.concatenate([sel, mids])
    gv = absg_psi(phis, cand)
    qv = np.abs(np.exp(1j * n * cand) - c)
    return bool(np.max(gv - qv) <= 1e-11 * max(1.0, float(np.max(qv))))


# ------------------------------------------------------------------ the checks
def good_gaps(phis: np.ndarray):
    """indices k with |g| <= |q| pointwise on A_k (exact)."""
    ph = np.sort(np.asarray(phis, float) % (2 * math.pi))
    return [k for k in range(len(ph)) if gap_ratio_ok(ph, k)], ph


def audit_config(phis: np.ndarray) -> dict:
    ks, ph = good_gaps(phis)
    n = len(ph)
    rec = {"n": n, "num_good_gaps": len(ks)}
    if not ks:
        rec["FAIL_T1"] = True
        return rec
    widths, arcs, chords = [], [], []
    for k in ks:
        b = ph[(k + 1) % n] + (2 * math.pi if k == n - 1 else 0.0)
        widths.append(b - ph[k])
        arcs.append(arc_max(ph, k))
        chords.append(chord_max(np.exp(1j * ph), k, (k + 1) % n))
    rec.update(
        max_width_over_good=max(widths),
        width_budget=2 * math.pi / n,
        best_arc_max=min(arcs),
        best_chord_max=min(chords),
        chord_minus_arc=max(c - a for c, a in zip(chords, arcs)),
    )
    rec["FAIL_T2"] = rec["best_arc_max"] > 2.0 + TOL
    rec["FAIL_T3"] = rec["max_width_over_good"] > rec["width_budget"] + TOL
    scale = max(1e-300, abs(rec["best_arc_max"]), abs(rec["best_chord_max"]))
    rec["FAIL_T4"] = rec["chord_minus_arc"] > 1e-10 * scale
    return rec


def adversarial(n: int, rng, restarts: int, iters: int, objective) -> tuple[float, np.ndarray]:
    best, bph = -np.inf, None
    seeds = [2 * math.pi * np.arange(n) / n]
    for _ in range(restarts):
        seeds.append(2 * math.pi * np.arange(n) / n + rng.normal(0, 0.15, n))
        seeds.append(np.sort(rng.uniform(0, 2 * math.pi, n)))
    for s in seeds:
        ph = np.sort(np.asarray(s) % (2 * math.pi))
        cur = objective(ph)
        step = 0.3
        for it in range(iters):
            cand = np.sort((ph + rng.normal(0, step, n)) % (2 * math.pi))
            if np.min(np.diff(np.concatenate([cand, [cand[0] + 2 * math.pi]]))) < 1e-4:
                continue
            v = objective(cand)
            if v > cur:
                ph, cur = cand, v
            if it % 120 == 119:
                step *= 0.62
        if cur > best:
            best, bph = cur, ph
    return best, bph


def main() -> int:
    rng = np.random.default_rng(20260824)
    report: dict = {"schema": "erdos1041_concyclic_alternation_receipt_v1", "arms": {}}

    # ---- arm 1: theorem holds on random + near-regular concyclic configs
    rows, failures = [], 0
    for n in range(2, 13):
        for trial in range(60):
            if trial < 20:
                ph = np.sort(rng.uniform(0, 2 * math.pi, n))
            elif trial < 40:
                ph = 2 * math.pi * np.arange(n) / n + rng.normal(0, 10.0 ** (-rng.integers(1, 7)), n)
            else:
                ph = np.sort(np.concatenate([
                    rng.uniform(0, 0.4, max(1, n // 2)),
                    rng.uniform(2.0, 2 * math.pi, n - max(1, n // 2))]))
            r = audit_config(ph)
            if any(r.get(k) for k in ("FAIL_T1", "FAIL_T2", "FAIL_T3", "FAIL_T4")):
                failures += 1
                rows.append({"phis": list(map(float, np.sort(ph % (2 * math.pi)))), **r})
    report["arms"]["theorem_sweep"] = {
        "configs": 11 * 60, "failures": failures, "failing_rows": rows[:8]}

    # ---- arm 2: sharpness of the constant 2 at the regular n-gon
    sharp = []
    for n in range(2, 11):
        ph = 2 * math.pi * np.arange(n) / n
        ks, phs = good_gaps(ph)
        sharp.append({
            "n": n,
            "min_gap_arc_max": min(arc_max(phs, k) for k in range(n)),
            "min_gap_chord_max": min(chord_max(np.exp(1j * phs), k, (k + 1) % n) for k in range(n)),
            "predicted_chord": 1.0 + math.cos(math.pi / n) ** n,
            "num_good_gaps": len(ks),
        })
    report["arms"]["regular_ngon_sharpness"] = sharp

    # ---- arm 3: adversarial pressure on the two constants
    def obj_arc(ph):
        ks, p = good_gaps(ph)
        return min((arc_max(p, k) for k in ks), default=-1.0)

    def obj_chord(ph):
        p = np.sort(np.asarray(ph) % (2 * math.pi))
        w = np.exp(1j * p)
        return min(chord_max(w, k, (k + 1) % len(p)) for k in range(len(p)))

    adv = []
    for n in range(3, 8):
        a_arc, _ = adversarial(n, rng, 2, 200, obj_arc)
        a_ch, _ = adversarial(n, rng, 2, 200, obj_chord)
        adv.append({"n": n, "adv_max_arc_constant": a_arc, "arc_budget": 2.0,
                    "adv_max_chord_constant": a_ch,
                    "regular_ngon_chord": 1.0 + math.cos(math.pi / n) ** n})
    report["arms"]["adversarial"] = adv

    # ---- arm 4: negative control demanded by negative_results entry 19.
    # The FALSE neighbouring statement "every gap arc has max |g| <= 2" must be
    # pushed over its threshold by the same searcher at the same budget.
    def obj_all_gaps(ph):
        p = np.sort(np.asarray(ph) % (2 * math.pi))
        return max(arc_max(p, k) for k in range(len(p)))

    ctrl = []
    for n in range(3, 8):
        v, _ = adversarial(n, rng, 2, 150, obj_all_gaps)
        ctrl.append({"n": n, "false_statement_max_over_all_gaps": v, "threshold": 2.0,
                     "broken": v > 2.0 + 1e-6})
    report["arms"]["negative_control"] = ctrl

    # ---- arm 5: the corollary at the extreme admissible radius rho = 2^{-1/n}
    cor = []
    for n in range(2, 11):
        rho = 2.0 ** (-1.0 / n)
        worst_level, worst_len = -np.inf, -np.inf
        for _ in range(40):
            ph = np.sort(rng.uniform(0, 2 * math.pi, n)) if _ % 2 else \
                 2 * math.pi * np.arange(n) / n + rng.normal(0, 1e-3, n)
            ks, p = good_gaps(ph)
            if not ks:
                worst_level = np.inf
                break
            w = rho * np.exp(1j * np.sort(p))
            lv = min(chord_max(w, k, (k + 1) % n) for k in ks)
            ln = min(abs(w[(k + 1) % n] - w[k]) for k in ks)
            worst_level = max(worst_level, lv)
            worst_len = max(worst_len, ln)
        cor.append({"n": n, "rho": rho, "worst_chord_level": worst_level,
                    "level_budget": 1.0, "worst_chord_length": worst_len,
                    "length_budget": 2.0,
                    "ok": worst_level <= 1.0 + 1e-9 and worst_len < 2.0})
    report["arms"]["corollary_at_threshold_radius"] = cor

    ok = (report["arms"]["theorem_sweep"]["failures"] == 0
          and all(a["adv_max_arc_constant"] <= 2.0 + 1e-6 for a in adv)
          and all(a["adv_max_chord_constant"] <= a["regular_ngon_chord"] + 1e-6 for a in adv)
          and all(c["broken"] for c in ctrl)
          and all(c["ok"] for c in cor))
    report["verdict"] = "PASS" if ok else "FAIL"

    out = Path("state/formal_math/erdos257_period_noncollapse/erdos1041_concyclic_alternation_receipt.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2, default=float) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "arms"}, indent=2))
    print(f"receipt -> {out}")
    for name, arm in report["arms"].items():
        print(f"\n--- {name} ---")
        print(json.dumps(arm, indent=1, default=float)[:2600])
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
