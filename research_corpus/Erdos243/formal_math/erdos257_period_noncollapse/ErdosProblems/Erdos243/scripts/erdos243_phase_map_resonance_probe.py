#!/usr/bin/env python3
"""Erdos 243, wave-2 desk S3: the phase map, resonance vacuity, and the burn identity.

Central object: phi_n = E_n / C_n in [-1/2, 1/2), with the exact defect identity

    E_{n+1} = a_n^2 E_n  (mod C_{n+1}),        C_{n+1} = C_n - E_n,

equivalently, in primitive coordinates (u, e) = (C/G, E/G), G_n = gcd(C_n, D_n),
h_n = G_{n+1}/G_n:

    a_n^2 e_n = h_n e_{n+1}  (mod u_{n+1}),    gcd(e_n, u_{n+1}) = 1.

The desk's question is whether "the multiplier a_n^2 must be resonant modulo
C_{n+1}" (a_n^2 congruent to a small rational k/l) is a real constraint.  The
parts below settle it exactly and measure the frequency law it would need.

Parts
  P1  Thue vacuity.  Every unit x mod N is k*l^{-1} with |k|,|l| <= sqrt(N).
      So epsilon-resonance is EMPTY as a constraint once epsilon >= N^{-1/2}.
  P2  Orbit resonance data.  Per surviving step: the resonance index
      Pi_n = |e_n e_{n+1}| / u_{n+1}, the Thue-minimal representation of
      a_n^2 mod u_{n+1}, and the continued-fraction dichotomy (Theorem B):
      2|e_n e_{n+1}| < u_{n+1}  ==>  m_n/e_n is a CF convergent of
      (a_n^2 mod u_{n+1}) / u_{n+1}, with following partial quotient ~ 1/Pi_n.
  P3  Frequency law.  Density of steps with |phi_n| < eps, on deep steps of
      long-surviving orbits, against the conjectured O(eps).
  P4  Corpus fixtures (E = -1 blocks; the (11, 11(33+79833600k)-1) recovery
      family): the resonance mechanism must NOT exclude them.
  P5  Burn identity.  C_T/F_T = C_N/F_N - sum Theta_n/F_{n+1} with
      Theta_n = b_n C_n + E_n, checked exactly for three envelopes, including
      the two orbit-adaptive ones that make Theta_n >= 0 automatic.

Usage
  ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/scripts/erdos243_phase_map_resonance_probe.py --quick
  ./repo-python .../erdos243_phase_map_resonance_probe.py --qmax 400 --json out.json
"""

from __future__ import annotations

import argparse
import json
import random
import sys
from fractions import Fraction
from math import gcd, isqrt
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from erdos243_orbit_engine import run_orbit  # noqa: E402


# --------------------------------------------------------------------------
# helpers
# --------------------------------------------------------------------------

def centre(x: int, m: int) -> int:
    """representative of x mod m in [-m/2, m/2)."""
    r = x % m
    return r - m if 2 * r >= m else r


def cf_convergents(x: int, n: int) -> list[tuple[int, int]]:
    """(p, q) convergents of x/n, 0 <= x < n."""
    out: list[tuple[int, int]] = []
    num, den = x, n
    p_m2, q_m2 = 0, 1
    p_m1, q_m1 = 1, 0
    while den:
        a_j = num // den
        num, den = den, num - a_j * den
        p_m2, p_m1 = p_m1, a_j * p_m1 + p_m2
        q_m2, q_m1 = q_m1, a_j * q_m1 + q_m2
        out.append((p_m1, q_m1))
    return out


def thue_minimal(x: int, n: int) -> tuple[int, int]:
    """Smallest-box (l, k) with x*l = k (mod n), l > 0, via the CF of x/n.

    Returns the pair minimising max(|k|, |l|) over the CF-generated candidates,
    which by the three-distance/lattice theory attains max(|k|,|l|) <= sqrt(n).
    """
    best = None
    for _p, q in cf_convergents(x % n, n):
        if q == 0 or q >= n:
            continue
        k = centre(x * q, n)
        cand = (max(abs(k), q), q, k)
        if best is None or cand < best:
            best = cand
    if best is None:
        return (1, centre(x, n))
    return (best[1], best[2])


def primitive_frames(orb: dict) -> list[dict]:
    """Per-step frames with the exact multiplier a_n and primitive data."""
    C, E, G, Dex = orb["C"], orb["E"], orb["G"], orb["Dexact"]
    frames = []
    for n in range(len(E) - 1):
        if E[n] == 0 or n + 1 >= len(G):
            break
        if n >= len(Dex) or Dex[n] is None:
            break  # exact phase ended; a_n unavailable
        D_n = Dex[n]
        a_n = (D_n - E[n]) // C[n] + 1
        Gn, Gn1 = G[n], G[n + 1]
        h = Gn1 // Gn
        frames.append({
            "n": n,
            "C": C[n], "C1": C[n + 1], "E": E[n], "E1": E[n + 1],
            "G": Gn, "G1": Gn1, "h": h,
            "u": C[n] // Gn, "u1": C[n + 1] // Gn1,
            "e": E[n] // Gn, "e1": E[n + 1] // Gn1,
            "a": a_n,
        })
    return frames


def seeds_from_rationals(qmax: int) -> list[tuple[int, int]]:
    """(C0, D0) = (p, q) for the pseudo-greedy orbit of p/q, gcd = 1, p < q."""
    out = []
    for q in range(2, qmax + 1):
        for p in range(1, q):
            if gcd(p, q) == 1:
                out.append((p, q))
    return out


# --------------------------------------------------------------------------
# P1  Thue vacuity
# --------------------------------------------------------------------------

def p1_thue_vacuity(trials: int, seed: int = 20260905) -> dict:
    rng = random.Random(seed)
    worst_ratio = 0.0
    checked = 0
    fails = 0
    for _ in range(trials):
        n = rng.randrange(50, 10 ** 7)
        x = rng.randrange(1, n)
        if gcd(x, n) != 1:
            continue
        l, k = thue_minimal(x, n)
        if (x * l - k) % n:
            fails += 1
            continue
        checked += 1
        worst_ratio = max(worst_ratio, max(abs(k), abs(l)) / (isqrt(n) + 1))
    # exhaustive check for small n
    exhaustive_fail = 0
    exhaustive_n = 0
    for n in range(3, 400):
        for x in range(1, n):
            if gcd(x, n) != 1:
                continue
            l, k = thue_minimal(x, n)
            exhaustive_n += 1
            if (x * l - k) % n or max(abs(k), abs(l)) > isqrt(n) + 1:
                exhaustive_fail += 1
    return {
        "random_pairs_checked": checked,
        "congruence_failures": fails,
        "max_ratio_maxabs_over_sqrt_n": round(worst_ratio, 6),
        "exhaustive_pairs_n_lt_400": exhaustive_n,
        "exhaustive_violations_of_sqrt_bound": exhaustive_fail,
        "reading": ("every unit mod n admits k/l with max(|k|,|l|) <= sqrt(n); "
                    "epsilon-resonance is vacuous for epsilon >= n^{-1/2}"),
    }


# --------------------------------------------------------------------------
# P2  orbit resonance data + the CF dichotomy
# --------------------------------------------------------------------------

def collect_frames(qmax: int, step_cap: int, height_cap: int) -> list[list[dict]]:
    allf = []
    for (p, q) in seeds_from_rationals(qmax):
        orb = run_orbit(p, q, height_cap=height_cap, step_cap=step_cap,
                        exact_bits=100000, lean=False)
        fr = primitive_frames(orb)
        if fr:
            allf.append(fr)
    return allf


def p2_resonance(all_frames: list[list[dict]]) -> dict:
    steps = 0
    clean = 0
    ident_fail = 0
    coprime_fail = 0
    resonant_regime = 0            # 2|e e'| < u'  (constraint has content)
    thmB_checked = 0
    thmB_fail = 0
    thue_is_actual = 0             # the actual (e_n, e_{n+1}) IS the Thue-minimal pair
    pi_hist = {"<0.01": 0, "<0.1": 0, "<0.5": 0, ">=0.5": 0}
    pq_ratio_fail = 0
    for frames in all_frames:
        for f in frames:
            steps += 1
            u1, e, e1, h, a = f["u1"], f["e"], f["e1"], f["h"], f["a"]
            if u1 <= 1:
                continue
            if gcd(e, u1) != 1:
                coprime_fail += 1
                continue
            # exact defect identity in primitive coordinates
            if (a * a % u1 * (e % u1) - h * e1) % u1:
                ident_fail += 1
            if h == 1:
                clean += 1
            pi = Fraction(abs(e * e1), u1) if h == 1 else None
            if pi is None:
                continue
            if pi < Fraction(1, 100):
                pi_hist["<0.01"] += 1
            if pi < Fraction(1, 10):
                pi_hist["<0.1"] += 1
            if pi < Fraction(1, 2):
                pi_hist["<0.5"] += 1
            else:
                pi_hist[">=0.5"] += 1
            x = (a * a) % u1
            l_min, k_min = thue_minimal(x, u1)
            if abs(l_min) == abs(e) and abs(k_min) == abs(e1):
                thue_is_actual += 1
            if 2 * abs(e * e1) < u1 and abs(e) >= 1:
                resonant_regime += 1
                # Theorem B: m/e (lowest terms) is a CF convergent of x/u1
                m = (x * e - e1) // u1 if (x * e - e1) % u1 == 0 else None
                if m is None:
                    thmB_fail += 1
                    continue
                g = gcd(abs(m), abs(e)) or 1
                mm, ee = m // g, e // g
                if ee < 0:
                    mm, ee = -mm, -ee
                thmB_checked += 1
                convs = cf_convergents(x, u1)
                if (mm, ee) not in convs:
                    thmB_fail += 1
                # exact CF identity  q_{j+1} D_j + q_j D_{j+1} = u1,
                # with D_j = |e_{n+1}| and q_j = |e_n|; hence
                #   u1/|e_{n+1}| - |e_n| < q_{j+1} <= u1/|e_{n+1}|,
                # i.e. the following convergent denominator is 1/|phi_{n+1}|
                # and the partial quotient there is ~ 1/Pi_n.
                qs = [q for (_p, q) in convs]
                if ee in qs:
                    j = qs.index(ee)
                    if j + 1 < len(qs):
                        Dj = abs(convs[j][1] * x - convs[j][0] * u1)
                        Dj1 = abs(convs[j + 1][1] * x - convs[j + 1][0] * u1)
                        if qs[j + 1] * Dj + ee * Dj1 != u1:
                            pq_ratio_fail += 1
                        elif Dj and not (u1 // Dj - ee <= qs[j + 1] <= u1 // Dj + 1):
                            pq_ratio_fail += 1
    return {
        "orbits": len(all_frames),
        "steps": steps,
        "clean_steps_h_eq_1": clean,
        "primitive_defect_identity_failures": ident_fail,
        "gcd(e_n,u_{n+1})_ne_1_count": coprime_fail,
        "clean_steps_with_2|e e'| < u'  (resonance non-vacuous)": resonant_regime,
        "resonance_index_histogram_clean_steps": pi_hist,
        "theoremB_checked": thmB_checked,
        "theoremB_failures": thmB_fail,
        "CF_three_term_identity_failures": pq_ratio_fail,
        "steps_where_(e_n,e_{n+1})_is_the_Thue_minimal_pair": thue_is_actual,
    }


# --------------------------------------------------------------------------
# P3  frequency law
# --------------------------------------------------------------------------

def p3_density(all_frames: list[list[dict]], min_depth: int, min_len: int) -> dict:
    eps_grid = [0.01, 0.02, 0.05, 0.1, 0.2, 0.3, 0.4]
    tot = 0
    hits = {e: 0 for e in eps_grid}
    for frames in all_frames:
        if len(frames) < min_len:
            continue
        for f in frames:
            if f["n"] < min_depth:
                continue
            tot += 1
            phi = abs(f["E"] / f["C"])
            for e in eps_grid:
                if phi < e:
                    hits[e] += 1
    return {
        "deep_steps_pooled": tot,
        "min_depth": min_depth, "min_orbit_length": min_len,
        "density_of_|phi|<eps": {str(e): (round(hits[e] / tot, 5) if tot else None)
                                 for e in eps_grid},
        "uniform_prediction_2eps": {str(e): round(2 * e, 5) for e in eps_grid},
    }


# --------------------------------------------------------------------------
# P4  fixtures
# --------------------------------------------------------------------------

def p4_fixtures(step_cap: int, height_cap: int) -> dict:
    seeds = []
    for c in (5, 11, 40, 101, 1000):
        for m in (3, 7, 33, 1001):
            seeds.append(("E_minus_one", c, c * m - 1))
    for k in (0, 1, 2, 3, 5):
        seeds.append(("normalized_return_11", 11, 11 * (33 + 79833600 * k) - 1))
    out = []
    for name, C0, D0 in seeds:
        orb = run_orbit(C0, D0, height_cap=height_cap, step_cap=step_cap,
                        exact_bits=200000, lean=False)
        fr = primitive_frames(orb)
        pis = []
        ident_fail = 0
        for f in fr:
            u1, e, e1, h, a = f["u1"], f["e"], f["e1"], f["h"], f["a"]
            if u1 <= 1 or gcd(e, u1) != 1:
                continue
            if (a * a % u1 * (e % u1) - h * e1) % u1:
                ident_fail += 1
            if h == 1:
                pis.append(float(Fraction(abs(e * e1), u1)))
        out.append({
            "family": name, "seed": [C0, D0], "status": orb["status"],
            "steps": orb["steps"], "E_head": orb["E"][:10],
            "clean_resonance_indices_head": [round(x, 5) for x in pis[:10]],
            "min_Pi": (round(min(pis), 6) if pis else None),
            "max_Pi": (round(max(pis), 6) if pis else None),
            "identity_failures": ident_fail,
        })
    return {"fixtures": out,
            "reading": ("all fixtures live at small Pi (strongly resonant); a "
                        "mechanism that forbids small Pi would exclude them, so "
                        "no such mechanism is available")}


# --------------------------------------------------------------------------
# P5  burn identity
# --------------------------------------------------------------------------

def p5_burn(C0: int, D0: int, step_cap: int, height_cap: int) -> dict:
    orb = run_orbit(C0, D0, height_cap=height_cap, step_cap=step_cap,
                    exact_bits=100000, lean=False)
    C, E = orb["C"], orb["E"]
    T = min(len(E), len(C) - 1)
    res = {}

    def run(name, rfun):
        F = [Fraction(1)]
        for n in range(T):
            F.append(F[-1] * rfun(n))
        Z = [Fraction(C[n]) / F[n] for n in range(T + 1)]
        theta = [rfun(n) * C[n] - C[n + 1] for n in range(T)]
        lhs = Z[T]
        rhs = Z[0] - sum(Fraction(theta[n]) / F[n + 1] for n in range(T))
        res[name] = {
            "identity_exact": lhs == rhs,
            "min_Theta": float(min(theta)) if theta else None,
            "Theta_nonneg_all_steps": all(t >= 0 for t in theta),
            "sum_1/F_over_run": float(sum(Fraction(1) / F[n] for n in range(1, T + 1))),
            "Z_final": float(Z[T]),
        }

    # (a) regular critical envelope F_n = n log n  (orbit-independent)
    import math
    def r_reg(n):
        x, y = n + 3, n + 4
        return Fraction(int(1e9 * y * math.log(y)), int(1e9 * x * math.log(x)))
    run("regular_F_n_log_n", r_reg)
    # (b) running-rise envelope: r_n = max(1, C_{n+1}/C_n)  -> Theta_n = (E_n)_+
    run("adaptive_rises_only", lambda n: max(Fraction(1), Fraction(C[n + 1], C[n])))
    # (c) saturating envelope: r_n = (C_{n+1}+1)/C_n        -> Theta_n = 1
    run("adaptive_saturating", lambda n: Fraction(C[n + 1] + 1, C[n]))
    return {"seed": [C0, D0], "steps": T, "envelopes": res,
            "reading": ("(b) and (c) make Theta >= 0 by construction but their "
                        "sum 1/F converges, so (11) fails; (a) has sum 1/F = inf "
                        "but Theta < 0 at real steps: the hypothesis Theta >= 0 "
                        "IS the critical-envelope hypothesis")}


# --------------------------------------------------------------------------

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--qmax", type=int, default=140)
    ap.add_argument("--step-cap", type=int, default=60)
    ap.add_argument("--height-cap", type=int, default=10 ** 9)
    ap.add_argument("--trials", type=int, default=4000)
    ap.add_argument("--json", type=str, default=None)
    args = ap.parse_args()
    if args.quick:
        args.qmax, args.step_cap, args.trials = 90, 40, 1500

    out = {"probe": "erdos243_phase_map_resonance", "quick": args.quick,
           "params": {"qmax": args.qmax, "step_cap": args.step_cap,
                      "height_cap": args.height_cap, "trials": args.trials}}
    out["P1_thue_vacuity"] = p1_thue_vacuity(args.trials)
    frames = collect_frames(args.qmax, args.step_cap, args.height_cap)
    out["P2_resonance"] = p2_resonance(frames)
    out["P3_frequency"] = p3_density(frames, min_depth=3, min_len=6)
    out["P4_fixtures"] = p4_fixtures(args.step_cap, args.height_cap)
    out["P5_burn"] = p5_burn(11, 11 * (33 + 79833600) - 1, args.step_cap, args.height_cap)
    txt = json.dumps(out, indent=2)
    print(txt)
    if args.json:
        Path(args.json).write_text(txt)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
