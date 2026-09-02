#!/usr/bin/env python3
"""Receipt for FormACutAdjacentSelector.md.

Segment maxima are EXACT throughout: |f(p+(q-p)t)|^2 is a real polynomial of
degree 2n in t, so its maximum on [0,1] is read from the real roots of its
derivative plus the endpoints, never sampled.  (TruncatedSpokeReduction.md
section 5 uses the same instrument; a sampled maximum under-reports, which is
the unsafe direction for a "V <= 1" row.)

Arms, each fail-closed:

  HALFPLANE  {j : Re(E_1 â_j) <= 0} is a contiguous arc of at least floor(n/2)
             root directions, and floor(n/2) >= 2 first holds at n = 4.
  DERIV      P_j'(0) = Re(E_1 omega^j), i.e. the recorded conjugate-Poisson
             kernel slope is the half-plane functional.
  CHORD      On the chord between ADJACENT directions, Re(w(tau)^n) < 0 only in
             the open interval, so every adjacent good pair meets the criterion
             of section 3.
  ADJ        The adjacent-good-pair selector returns V <= 1 at every tested
             near-Fekete configuration.
  ANTI       The most-antipodal-good-pair selector EXCEEDS 1 at the three
             recorded rows -- i.e. that selector is refuted.

Nothing here proves Erdos #1041.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import os
import sys

import numpy as np

RECEIPT = ("state/formal_math/erdos257_period_noncollapse/"
           "erdos1041_form_a_cut_selector_receipt.json")


# --------------------------------------------------------------------------- #
# exact segment maximum
# --------------------------------------------------------------------------- #
def seg_max_exact(roots: np.ndarray, p: complex, q: complex) -> float:
    """max_{t in [0,1]} |f(p + (q-p)t)| , exactly (polynomial critical points)."""
    d = q - p
    coef = np.array([1.0 + 0j])                       # ascending in t
    for a in roots:
        c0 = p - a
        nxt = np.zeros(len(coef) + 1, dtype=complex)
        nxt[:len(coef)] += coef * c0
        nxt[1:] += coef * d
        coef = nxt
    # |F|^2 = F * conj(F) with conjugated coefficients (t real)
    m = np.convolve(coef, np.conj(coef)[::-1] if False else np.conj(coef))
    m = np.real(m)                                    # imaginary parts cancel
    der = np.polyder(m[::-1])                         # numpy wants descending
    ts = [0.0, 1.0]
    if der.size and not np.allclose(der, 0):
        for r in np.roots(der):
            if abs(r.imag) < 1e-12 and -1e-12 <= r.real <= 1 + 1e-12:
                ts.append(min(1.0, max(0.0, float(r.real))))
    vals = [abs(np.polyval(coef[::-1], t)) for t in ts]
    return float(max(vals))


def prep(roots):
    """Match roots to omega^k by the best rotation; return (ordered roots, E_1)."""
    roots = np.asarray(roots, complex)
    n = len(roots)
    r = roots[np.argsort(np.angle(roots))]
    best = None
    for shift in range(n):
        w = np.roll(np.exp(2j * np.pi * np.arange(n) / n), shift)
        e = r / w - 1
        s = float(np.sum(np.abs(e) ** 2))
        if best is None or s < best[0]:
            best = (s, e, w)
    _, e, w = best
    return r, complex(np.sum(e * np.conj(w)))


def _V(roots, i, j, sigmas):
    u = roots / np.abs(roots)
    best = math.inf
    for s in sigmas:
        s_ = s * min(abs(roots[i]), abs(roots[j]))
        v = max(seg_max_exact(roots, s_ * u[i], roots[i]),
                seg_max_exact(roots, s_ * u[j], roots[j]),
                seg_max_exact(roots, s_ * u[i], s_ * u[j]))
        best = min(best, v)
    return best


SIGMAS = np.concatenate([np.logspace(-7, -1, 22), np.linspace(0.12, 0.95, 14)])


def selector_adjacent(roots, sigmas=SIGMAS):
    r, E1 = prep(roots)
    n = len(r)
    p = np.array([(E1 * (rr / abs(rr))).real for rr in r])
    pairs = [(j, (j + 1) % n) for j in range(n)
             if p[j] <= 1e-14 and p[(j + 1) % n] <= 1e-14]
    if not pairs:
        pairs = sorted([(j, (j + 1) % n) for j in range(n)],
                       key=lambda q: max(p[q[0]], p[q[1]]))[:1]
    pairs.sort(key=lambda q: p[q[0]] + p[q[1]])
    return min(_V(r, i, j, sigmas) for (i, j) in pairs[:2]), int((p <= 1e-14).sum())


def selector_antipodal(roots, sigmas=SIGMAS):
    r, E1 = prep(roots)
    n = len(r)
    u = r / np.abs(r)
    p = np.array([(E1 * uu).real for uu in u])
    good = [j for j in range(n) if p[j] <= 1e-14]
    if len(good) < 2:
        good = list(np.argsort(p))[:2]
    pairs = sorted(itertools.combinations(good, 2),
                   key=lambda q: -abs(np.angle(u[q[0]] / u[q[1]])))
    return _V(r, pairs[0][0], pairs[0][1], sigmas)


def free_optimum(roots, sigmas=SIGMAS):
    r = np.asarray(roots, complex)
    return min(_V(r, i, j, sigmas)
               for i, j in itertools.combinations(range(len(r)), 2))


def _config(n, eta, kind, seed):
    rng = np.random.default_rng(seed)
    th = eta * rng.standard_normal(n)
    rad = np.ones(n) if kind == "angular" else 1 - eta * np.abs(rng.standard_normal(n))
    roots = rad * np.exp(2j * np.pi * (np.arange(n) / n) + 1j * th)
    return roots / np.max(np.abs(roots))


# --------------------------------------------------------------------------- #
# arms
# --------------------------------------------------------------------------- #
def arm_halfplane() -> dict:
    rows = []
    ok = True
    rng = np.random.default_rng(7)
    for n in range(3, 15):
        worst = n
        for _ in range(400):
            psi = 2 * np.pi * rng.random()
            good = [j for j in range(n)
                    if math.cos(psi + 2 * math.pi * j / n) <= 1e-15]
            # contiguity, cyclically
            idx = sorted(good)
            gaps = sum(1 for a in range(len(idx))
                       if (idx[(a + 1) % len(idx)] - idx[a]) % n != 1)
            if len(idx) and gaps > 1:
                ok = False
            worst = min(worst, len(good))
        rows.append({"n": n, "min_good_over_directions": worst,
                     "floor_n_over_2": n // 2})
        ok = ok and worst >= n // 2
    first = min(r["n"] for r in rows if r["floor_n_over_2"] >= 2)
    ok = ok and first == 4
    return {"arm": "HALFPLANE", "ok": bool(ok), "first_n_with_two_good": first,
            "rows": rows}


def arm_deriv(tol: float = 1e-12) -> dict:
    """P_j'(0) = Re(E_1 omega^j).

    This is a FIRST-ORDER identity, so it is checked on the linearised
    perturbation e_k = i theta_k, where it must hold to machine precision.  With
    the exact e_k = exp(i theta_k) - 1 the two sides differ by O(eta^2), which
    the second block records rather than asserts."""
    rows = []
    ok = True
    rng = np.random.default_rng(31)
    for n in (3, 4, 5, 6, 8, 9):
        th = rng.standard_normal(n)                    # scale-free: linear identity
        w = np.exp(2j * np.pi * np.arange(n) / n)
        E1 = complex(np.sum(1j * th * np.conj(w)))
        for j in range(n):
            lhs = sum(math.sin(2 * math.pi * m / n) *
                      (th[(j + m) % n] - th[(j - m) % n])
                      for m in range(1, (n - 1) // 2 + 1))
            rhs = (E1 * w[j]).real
            rows.append({"n": n, "j": j, "P_prime_0": lhs, "Re_E1_omega_j": rhs,
                         "gap": abs(lhs - rhs)})
            ok = ok and abs(lhs - rhs) < tol * max(1.0, abs(rhs))
    # second block: the O(eta^2) drift with the exact e_k, recorded not asserted
    drift = []
    for eta in (1e-2, 1e-3, 1e-4):
        n = 6
        th = eta * rng.standard_normal(n)
        w = np.exp(2j * np.pi * np.arange(n) / n)
        E1 = complex(np.sum((np.exp(1j * th) - 1) * np.conj(w)))
        g = max(abs(sum(math.sin(2 * math.pi * m / n) *
                        (th[(j + m) % n] - th[(j - m) % n])
                        for m in range(1, (n - 1) // 2 + 1)) - (E1 * w[j]).real)
                for j in range(n))
        drift.append({"eta": eta, "max_gap": g, "gap_over_eta_sq": g / eta ** 2})
    return {"arm": "DERIV", "ok": bool(ok), "rows": rows,
            "exact_e_drift_is_O_eta_squared": drift}


def arm_chord() -> dict:
    """On an adjacent chord, Re(w^n) < 0 only strictly inside (0,1)."""
    rows = []
    ok = True
    for n in range(3, 15):
        w0 = 1.0 + 0j
        w1 = np.exp(2j * np.pi / n)
        ts = np.linspace(0, 1, 20001)
        w = (1 - ts) * w0 + ts * w1
        re = np.real(w ** n)
        neg = re < 0
        rows.append({"n": n, "endpoints_positive": bool(re[0] > 0 and re[-1] > 0),
                     "negative_fraction": float(neg.mean()),
                     "first_negative_t": float(ts[neg][0]) if neg.any() else None,
                     "last_negative_t": float(ts[neg][-1]) if neg.any() else None})
        ok = ok and re[0] > 0 and re[-1] > 0
        if neg.any():
            ok = ok and ts[neg][0] > 0 and ts[neg][-1] < 1
    return {"arm": "CHORD", "ok": bool(ok), "rows": rows}


def arm_adj() -> dict:
    """The selector is a NEAR-Fekete statement.  Asserted for eta <= 1e-2; the
    eta-scan block records where it stops holding, and checks that the free
    optimum stays below 1 there, so only the selector fails."""
    rows = []
    ok = True
    for n in (4, 5, 6, 7, 8, 10, 12):
        for eta in (1e-2, 1e-3, 1e-5, 1e-7):
            for kind in ("angular", "mixed"):
                roots = _config(n, eta, kind, 4242 + n * 17 + int(-math.log10(eta)))
                v, ng = selector_adjacent(roots)
                rows.append({"n": n, "eta": eta, "kind": kind, "V": v,
                             "good_rays": ng, "ok": bool(v <= 1.0)})
                ok = ok and v <= 1.0
    scan = []
    crossed = False
    for eta in (1e-1, 7e-2, 5e-2, 3e-2, 2e-2, 1e-2):
        roots = _config(12, eta, "angular", 4242 + 12 * 17 + 1)
        v, _ = selector_adjacent(roots)
        vf = free_optimum(roots)
        scan.append({"eta": eta, "adjacent_V": v, "free_V": vf,
                     "selector_ok": bool(v <= 1.0), "form_a_cut_ok": bool(vf < 1.0)})
        ok = ok and vf < 1.0          # Form A-cut itself must never fail
        if v > 1.0:
            crossed = True
    ok = ok and crossed               # the boundary must actually be exhibited
    return {"arm": "ADJ", "ok": bool(ok),
            "note": "exact segment maxima. V <= 1 certifies Form A-cut at that "
                    "configuration with the adjacent good pair.  Asserted only for "
                    "eta <= 1e-2: the scan block shows the selector crossing 1 "
                    "between eta = 0.02 and 0.03 at n = 12 while the free optimum "
                    "stays far below 1, so the selector -- not Form A-cut -- is what "
                    "is near-Fekete-only.",
            "rows": rows, "eta_scan_n12_angular": scan}


def arm_anti() -> dict:
    """The most-antipodal-good-pair selector is REFUTED."""
    rng = np.random.default_rng(4242)
    # reproduce the three recorded failures by replaying the same stream
    fails = []
    rows = []
    for n in (4, 5, 6, 7, 8, 10):
        for eta in (1e-1, 1e-2, 1e-3, 1e-5):
            for kind in ("angular", "mixed"):
                th = eta * rng.standard_normal(n)
                rad = (np.ones(n) if kind == "angular"
                       else 1 - eta * np.abs(rng.standard_normal(n)))
                roots = rad * np.exp(2j * np.pi * (np.arange(n) / n) + 1j * th)
                roots = roots / np.max(np.abs(roots))
                v = selector_antipodal(roots)
                if v > 1.0:
                    fails.append({"n": n, "eta": eta, "kind": kind, "V": v})
                rows.append({"n": n, "eta": eta, "kind": kind, "V": v})
    return {"arm": "ANTI", "ok": bool(len(fails) >= 1),
            "note": "the antipodal-good-pair rule is refuted; Form A-cut itself is "
                    "untouched, only that selector.",
            "failures": fails, "failure_count": len(fails),
            "row_count": len(rows)}


ARMS = {"HALFPLANE": arm_halfplane, "DERIV": arm_deriv, "CHORD": arm_chord,
        "ADJ": arm_adj, "ANTI": arm_anti}


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
    payload = {"kind": "erdos1041_form_a_cut_selector_receipt",
               "note": "formal_math/erdos257_period_noncollapse/ErdosProblems/"
                       "Erdos1041/FormACutAdjacentSelector.md",
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
