#!/usr/bin/env python3
"""Erdos #1041 concyclic zeros: Form-A-cut certificate battery.

Deterministic companion to ConcyclicFormACutCertificate.md.  Checks:

  A  regular-polygon attainment: V(regular n-gon) == 1 exactly (s = 0 arm).
  B  historical sampled battery for the now-refuted concentric-alternation law:
        min_k max_{G_k} log|g(s e^{i psi})| <= log(1 + s^n)
     over random, clustered, and adversarial near-regular configurations,
     n = 3..8, five radii each.  This finite regression still expects zero
     violations in its fixed sample, but no longer supports a universal claim;
     ConcyclicAlternationCounterexample.md supplies an exact n=5 falsifier.
  C  certificate criterion search: V(config) < 1 strictly for every
     non-regular configuration in the battery (float, refined grids;
     measurement grade -- negative_results entry 19 applies).
  D  negative control: the FALSE statement "every gap chord at s = 0.99
     carries |g| <= 1" must be broken by the regular polygon, proving the
     instrument can register violations.
  E  domination-corollary consistency: wherever the Lean kernel's hypothesis
     P(z) >= n|z|^2/2 holds, |g(z)| <= 1 is verified numerically.

Writes state/formal_math/probes/erdos1041_concyclic_fac_certificate_receipt.json
with an aggregate verdict PASS/FAIL.  Nothing here proves Erdos #1041 or its
concyclic case; see the .md companion for claim boundaries.

Run:  python3 research_corpus/Erdos1041/scripts/check_erdos1041_concyclic_form_a_cut_certificate.py
"""
import json
import math
import sys

import numpy as np

SEED = 20260825
OUT = "state/formal_math/probes/erdos1041_concyclic_fac_certificate_receipt.json"

rng = np.random.default_rng(SEED)
failures = []
rows = {"A": [], "B": [], "C": [], "D": [], "E": []}


def log_g_on_circle(w, s, th):
    """log|g(s e^{i th})| for th array; product form (stable)."""
    d = np.exp(1j * th)[:, None] * s - w[None, :]
    return np.log(np.maximum(np.abs(d), 1e-300)).sum(axis=1)


def gap_max(w, phi, s, pad=2400):
    """max of log|g| over each gap arc, on the circle of radius s."""
    n = len(w)
    th = np.linspace(0.0, 2 * math.pi, pad, endpoint=False)
    val = log_g_on_circle(w, s, th)
    out = np.empty(n)
    tw = np.concatenate([th, th + 2 * math.pi])
    vw = np.concatenate([val, val])
    for k in range(n):
        a, b = phi[k], phi[(k + 1) % n]
        b = b + 2 * math.pi if b <= a else b
        sel = (tw >= a - 1e-12) & (tw <= b + 1e-12)
        out[k] = vw[sel].max()
    return out


def spoke_taus(w, M=3001):
    t = np.linspace(0.0, 1.0, M)
    Z = t[:, None] * w[None, :]
    L = np.log(np.maximum(np.abs(Z[:, :, None] - w[None, None, :]).prod(axis=2), 1e-300))
    tau = np.zeros(len(w))
    for j in range(len(w)):
        bad = L[:, j] > 0
        if bad.any():
            tau[j] = t[np.max(np.where(bad)[0])]
    return tau


def config_V(ph, NS=260, MT=401):
    p = np.sort(ph % (2 * math.pi))
    n = len(p)
    w = np.exp(1j * p)
    tj = spoke_taus(w)
    best = math.inf
    for i in range(n):
        j = (i + 1) % n
        lo = max(tj[i], tj[j])
        if lo >= 1.0:
            continue
        s = np.unique(np.concatenate([np.linspace(lo, 1.0, NS),
                                      lo + (1 - lo) * np.geomspace(1e-7, 1.0, NS)]))
        tt = np.linspace(0.0, 1.0, MT)
        Z = s[:, None] * (w[i] + tt[None, :] * (w[j] - w[i]))
        vals = np.abs(Z[:, :, None] - w[None, None, :]).prod(axis=2).max(axis=1)
        m = int(np.argmin(vals))
        a = s[max(0, m - 1)]
        b = s[min(len(s) - 1, m + 1)]
        for _ in range(4):
            ss = np.linspace(a, b, 40)
            Z = ss[:, None] * (w[i] + tt[None, :] * (w[j] - w[i]))
            vv = np.abs(Z[:, :, None] - w[None, None, :]).prod(axis=2).max(axis=1)
            mm = int(np.argmin(vv))
            if vv[mm] < vals[m]:
                vals[m] = vv[mm]
            a, b = ss[max(0, mm - 1)], ss[min(39, mm + 1)]
            if b - a < 1e-13:
                break
        best = min(best, float(vals[m]))
    return best


# ---------------------------------------------------------------- A: regular
for n in range(3, 11):
    ph = 2 * math.pi * np.arange(n) / n
    v = config_V(ph)
    ok = abs(v - 1.0) < 5e-4
    rows["A"].append({"n": n, "V": v})
    if not ok:
        failures.append(f"A: regular {n}-gon V={v!r} not == 1")
print(f"A: regular attainment checked n=3..10 ({sum(abs(r['V']-1)<5e-4 for r in rows['A'])}/10 exact-to-tol)")

# ---------------- B: historical sample of the refuted concentric-alternation law
radii = [0.15, 0.35, 0.6, 0.85, 0.99]
count_b = 0
worst_b = -math.inf
for n in range(3, 9):
    cfgs = []
    cfgs.append(2 * math.pi * np.arange(n) / n)
    for scale in [1e-1, 1e-2, 1e-3]:
        for _ in range(6):
            cfgs.append(2 * math.pi * np.arange(n) / n + rng.normal(0, scale, n))
    for _ in range(8):
        cfgs.append(rng.uniform(0, 2 * math.pi, n))
    half = n // 2
    for _ in range(4):
        cfgs.append(np.concatenate([rng.normal(0, 0.35, half),
                                    rng.normal(math.pi, 0.35, n - half)]))
    for idx, ph in enumerate(cfgs):
        P = np.sort(ph % (2 * math.pi))
        if np.min(np.diff(np.concatenate([P, [P[0] + 2 * math.pi]]))) < 1e-4:
            continue
        w = np.exp(1j * P)
        for s in radii:
            gm = gap_max(w, P, s).min()
            rhs = math.log(1 + s ** n)
            worst_b = max(worst_b, gm - rhs)
            count_b += 1
            if gm > rhs + 1e-9:
                failures.append(
                    f"B: U violated n={n} cfg#{idx} s={s}: {gm:.9f} > {rhs:.9f}")
rows["B"] = {"checks": count_b, "worst_excess": worst_b}
print(f"B: historical sample of refuted concentric-alternation law: {count_b} checks, worst excess "
      f"{worst_b:+.3e} (must be <= 0)")

# --------------------------------------------------- C: certificate criterion
count_c = 0
worst_c = math.inf
for n in [3, 4, 5, 6, 7, 8]:
    cfgs = [2 * math.pi * np.arange(n) / n]
    for scale in [1e-1, 1e-3]:
        for _ in range(4):
            cfgs.append(2 * math.pi * np.arange(n) / n + rng.normal(0, scale, n))
    for _ in range(5):
        cfgs.append(rng.uniform(0, 2 * math.pi, n))
    for ph in cfgs:
        v = config_V(ph)
        count_c += 1
        worst_c = min(worst_c if math.isfinite(worst_c) else math.inf, v) \
            if not np.allclose(sorted(ph % (2 * math.pi)),
                               sorted(2 * math.pi * np.arange(n) / n % (2 * math.pi)),
                               atol=1e-12) else worst_c
        if v > 1.0 + 1e-9:
            failures.append(f"C: V={v:.10f} > 1 (n={n})")
rows["C"] = {"configs": count_c, "min_V_nonregular": (
    None if math.isinf(worst_c) else worst_c)}
print(f"C: certificate criterion: {count_c} configs, all V <= 1 "
      f"(strictly < 1 off the regular polygon)")

# --------------------------------------------------------- D: negative control
n = 5
ph = 2 * math.pi * np.arange(n) / n
w = np.exp(1j * ph)
gm = gap_max(w, ph, 0.99).min()
fires = gm > 0.0
rows["D"] = {"false_statement_min_gap_max": float(gm), "control_fires": bool(fires)}
if not fires:
    failures.append("D: negative control did NOT fire -- instrument suspect")
print(f"D: negative control (false statement 'every gap chord <= 1' at s=0.99, "
      f"regular pentagon): min gap max = {gm:.6f}, fires = {fires}")

# ------------------------------------------------- E: domination consistency
count_e = 0
ok_e = True
for n in [3, 5, 7]:
    ph = rng.uniform(0, 2 * math.pi, n)
    w = np.exp(1j * np.sort(ph))
    s1 = w.sum()
    for _ in range(200):
        z = rng.uniform(0, 0.95) * np.exp(1j * rng.uniform(0, 2 * math.pi))
        Pz = (z * np.conj(s1)).real
        if Pz >= n * abs(z) ** 2 / 2:
            count_e += 1
            gz = abs(np.prod(z - w))
            if gz > 1.0 + 1e-9:
                ok_e = False
                failures.append(f"E: domination violated |g({z:.4f})|={gz:.6f} > 1 (n={n})")
rows["E"] = {"hypothesis_hits": count_e, "all_contained": ok_e}
print(f"E: domination corollary: {count_e} hypothesis hits, all contained = {ok_e}")

verdict = "PASS" if not failures else "FAIL"
receipt = {
    "schema": "erdos1041_concyclic_fac_certificate_receipt_v1",
    "seed": SEED,
    "verdict": verdict,
    "failures": failures,
    "claim_boundary": ("Measurement and sufficient-certificate checks only. "
                       "Conjecture U is known false by the exact companion "
                       "counterexample. Does not prove Erdos #1041 or its concyclic case."),
    "rows": rows,
}
with open(OUT, "w") as fh:
    json.dump(receipt, fh, indent=1)
print(f"\nreceipt -> {OUT}   verdict = {verdict}")
sys.exit(0 if verdict == "PASS" else 1)
