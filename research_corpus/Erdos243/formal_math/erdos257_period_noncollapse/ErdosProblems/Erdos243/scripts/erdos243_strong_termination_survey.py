#!/usr/bin/env python3
"""Erdos #243 (Koizumi form): strong-form termination survey far beyond q <= 300.

The STRONG form tested here is

    every rational x_0 = p/q has E_n = 0 eventually
    (i.e. every pseudo-greedy orbit reaches the exact Sylvester tail),

with NO rate hypothesis.  It implies Erdos #243: a counterexample to #243 is,
after Koizumi's finite shift, a non-terminating pseudo-greedy orbit of a
rational.  The corpus survey covered q <= 300 (27,397 orbits).  This script
pushes the full sweep several orders of magnitude further and adds random
sampling at large q, seeded structural families, a tie-rule sensitivity check,
and the improper (x_0 > 1) branch.

It also measures, on the same orbits:

  * (exp 4) the empirical drift E[log(C_{n+1}/C_n)] and the empirical
    absorption rate at each height C, against the random-model predictions
    -0.0451... and 1/C;
  * (exp 5) r01's excess mass S_B(T) = sum_{n<T} (-E_n - B)_+ / C_n against
    log C_T for B = 0,1,2,3;
  * (r04) the record-excess ratio (H_{k+1} - H_k) / log2 log2 max(4, H_k) on
    the record subsequence of the heights.

Engine, tie rule and modulus method: see erdos243_orbit_engine.py.

Examples
--------
    ./repo-python .../erdos243_strong_termination_survey.py --quick
    ./repo-python .../erdos243_strong_termination_survey.py \
        --qmax 20000 --samples-per-decade 20000 --workers 8 --out receipt.json
"""

from __future__ import annotations

import argparse
import json
import math
import os
import random
import sys
import time
from collections import defaultdict
from math import gcd
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from erdos243_orbit_engine import (  # noqa: E402
    HEIGHT_CAP,
    STEP_CAP,
    TERMINATED,
    run_orbit,
)

# E uniform on [-C/2, C/2) gives
#   E[log((C-E)/C)] = int_{-1/2}^{1/2} log(1-t) dt = int_{1/2}^{3/2} log u du
#                   = (3/2)log(3/2) - (1/2)log(1/2) - 1 = -0.04522803...
RANDOM_MODEL_DRIFT = 1.5 * math.log(1.5) - 0.5 * math.log(0.5) - 1.0

MAX_TRACKED_HEIGHT = 2048
KEEP_EXTREMES = 40
# steps whose normalised error already satisfies |E|/C <= this are the ones a
# counterexample to #243 must eventually consist of (E_n/C_n -> 0); the raw
# record-excess ratio is meaningless without such a filter because a single
# unrestricted step can multiply C by 3/2.
KEMP_NORMALISED_FILTER = 0.125


def _new_acc() -> dict:
    return {
        "orbits": 0,
        "terminated": 0,
        "unresolved": 0,
        "status_counts": defaultdict(int),
        "unresolved_examples": [],
        "max_abs_C": (0, None),
        "max_ratio_C0": (0.0, None),
        "max_ratio_q": (0.0, None),
        "longest": (0, None),
        "length_hist": defaultdict(int),
        "excursion_hist": defaultdict(int),   # floor(2 * maxC/C0) bucket
        "drift_sum": 0.0,
        "drift_n": 0,
        "drift1_sum": 0.0,   # steps n >= 1
        "drift1_n": 0,
        "drift_neg_sum": 0.0,  # steps at or after the first negative E
        "drift_neg_n": 0,
        "drift_negstrict_sum": 0.0,  # steps strictly after the first negative E
        "drift_negstrict_n": 0,
        "kempf_max": (0.0, None),      # record excess under the normalised filter
        "kempf_hist": defaultdict(int),
        "kempf_records": 0,
        "SB_zero_maxCT": {B: (0, None) for B in range(4)},
        "absorb_all": defaultdict(lambda: [0, 0]),
        "absorb_tail": defaultdict(lambda: [0, 0]),  # visits with n >= 1
        "kemp_max": (0.0, None),
        "kemp_hist": defaultdict(int),
        "kemp_records": 0,
        "SB": {B: {"sum": 0.0, "n": 0, "min": (float("inf"), None),
                   "max": (0.0, None), "hist": defaultdict(int)} for B in range(4)},
        "neg_depth_max": (0, None),
        "loglog_ratio_max": (0.0, None),
    }


def _merge(a: dict, b: dict) -> None:
    for k in ("orbits", "terminated", "unresolved", "drift_n", "drift1_n",
              "drift_neg_n", "drift_negstrict_n", "kemp_records", "kempf_records"):
        a[k] += b[k]
    for k in ("drift_sum", "drift1_sum", "drift_neg_sum", "drift_negstrict_sum"):
        a[k] += b[k]
    for k, v in b["status_counts"].items():
        a["status_counts"][k] += v
    for k in ("length_hist", "excursion_hist", "kemp_hist", "kempf_hist"):
        for kk, vv in b[k].items():
            a[k][kk] += vv
    for B in range(4):
        if b["SB_zero_maxCT"][B][0] > a["SB_zero_maxCT"][B][0]:
            a["SB_zero_maxCT"][B] = b["SB_zero_maxCT"][B]
    for k in ("absorb_all", "absorb_tail"):
        for kk, vv in b[k].items():
            a[k][kk][0] += vv[0]
            a[k][kk][1] += vv[1]
    for k in ("max_abs_C", "max_ratio_C0", "max_ratio_q", "longest",
              "neg_depth_max", "loglog_ratio_max", "kemp_max", "kempf_max"):
        if b[k][0] > a[k][0]:
            a[k] = b[k]
    a["unresolved_examples"] = (a["unresolved_examples"] + b["unresolved_examples"])[:KEEP_EXTREMES]
    for B in range(4):
        sa, sb = a["SB"][B], b["SB"][B]
        sa["sum"] += sb["sum"]
        sa["n"] += sb["n"]
        if sb["min"][0] < sa["min"][0]:
            sa["min"] = sb["min"]
        if sb["max"][0] > sa["max"][0]:
            sa["max"] = sb["max"]
        for kk, vv in sb["hist"].items():
            sa["hist"][kk] += vv


def accumulate(p: int, q: int, orb: dict, acc: dict) -> None:
    C, E, status = orb["C"], orb["E"], orb["status"]
    acc["orbits"] += 1
    acc["status_counts"][status] += 1
    T = len(E) - 1
    if status == TERMINATED:
        acc["terminated"] += 1
        acc["length_hist"][T] += 1
        if T > acc["longest"][0]:
            acc["longest"] = (T, (p, q))
    else:
        acc["unresolved"] += 1
        if len(acc["unresolved_examples"]) < KEEP_EXTREMES:
            acc["unresolved_examples"].append(
                {"p": p, "q": q, "status": status, "C": C[:80], "E": E[:80],
                 "len": len(E)})

    maxC = max(C)
    if maxC > acc["max_abs_C"][0]:
        acc["max_abs_C"] = (maxC, (p, q, C.index(maxC)))
    r0 = maxC / C[0]
    if r0 > acc["max_ratio_C0"][0]:
        acc["max_ratio_C0"] = (r0, (p, q, C.index(maxC), C[0]))
    rq = maxC / q
    if rq > acc["max_ratio_q"][0]:
        acc["max_ratio_q"] = (rq, (p, q, C.index(maxC)))
    acc["excursion_hist"][min(int(4 * r0), 200)] += 1

    # drift and absorption
    first_neg = None
    for n in range(len(E)):
        Cn = E_n = None
        Cn = C[n]
        E_n = E[n]
        if E_n < 0 and first_neg is None:
            first_neg = n
        if E_n < 0:
            if -E_n > acc["neg_depth_max"][0]:
                acc["neg_depth_max"] = (-E_n, (p, q, n, Cn))
            if Cn >= 4:
                rr = (-E_n) / math.log2(math.log2(Cn))
                if rr > acc["loglog_ratio_max"][0]:
                    acc["loglog_ratio_max"] = (rr, (p, q, n, Cn, E_n))
        key = Cn if Cn <= MAX_TRACKED_HEIGHT else 0
        rec = acc["absorb_all"][key]
        rec[0] += 1
        if E_n == 0:
            rec[1] += 1
        if n >= 1:
            rec2 = acc["absorb_tail"][key]
            rec2[0] += 1
            if E_n == 0:
                rec2[1] += 1
        if n + 1 < len(C):
            dl = math.log(C[n + 1] / Cn)
            acc["drift_sum"] += dl
            acc["drift_n"] += 1
            if n >= 1:
                acc["drift1_sum"] += dl
                acc["drift1_n"] += 1
            if first_neg is not None and n >= first_neg:
                acc["drift_neg_sum"] += dl
                acc["drift_neg_n"] += 1
            if first_neg is not None and n > first_neg:
                acc["drift_negstrict_sum"] += dl
                acc["drift_negstrict_n"] += 1

    # r04 record-excess ratio on the record subsequence of heights
    rec_h = C[0]
    for n in range(1, len(C)):
        if C[n] > rec_h:
            denom = math.log2(math.log2(max(4, rec_h)))
            val = (C[n] - rec_h) / denom
            acc["kemp_records"] += 1
            acc["kemp_hist"][min(int(2 * val), 400)] += 1
            if val > acc["kemp_max"][0]:
                acc["kemp_max"] = (val, (p, q, n, rec_h, C[n]))
            # filtered variant: only count the record when the step that made it
            # was already normalisation-small, |E_{n-1}|/C_{n-1} <= filter
            if abs(E[n - 1]) <= KEMP_NORMALISED_FILTER * C[n - 1]:
                acc["kempf_records"] += 1
                acc["kempf_hist"][min(int(2 * val), 400)] += 1
                if val > acc["kempf_max"][0]:
                    acc["kempf_max"] = (val, (p, q, n, rec_h, C[n],
                                              abs(E[n - 1]) / C[n - 1]))
            rec_h = C[n]

    # r01 excess mass
    if status == TERMINATED and C[T] >= 8:
        lg = math.log(C[T])
        for B in range(4):
            s = 0.0
            for n in range(T):
                x = -E[n] - B
                if x > 0:
                    s += x / C[n]
            ratio = s / lg
            st = acc["SB"][B]
            st["sum"] += ratio
            st["n"] += 1
            st["hist"][min(int(10 * ratio), 400)] += 1
            if ratio < st["min"][0]:
                st["min"] = (ratio, (p, q, T, C[T], s))
            if ratio > st["max"][0]:
                st["max"] = (ratio, (p, q, T, C[T], s))
            if s == 0.0 and C[T] > acc["SB_zero_maxCT"][B][0]:
                acc["SB_zero_maxCT"][B] = (C[T], (p, q, T))


def _run_range(job):
    qs, opts = job
    acc = _new_acc()
    for q in qs:
        for p in range(1, q):
            if gcd(p, q) != 1:
                continue
            orb = run_orbit(p, q,
                            height_cap=max(opts["height_cap"], opts["height_mult"] * p),
                            step_cap=opts["step_cap"],
                            exact_bits=opts["exact_bits"], tie=opts["tie"],
                            lean=True)
            accumulate(p, q, orb, acc)
    return _plain(acc)


def _run_samples(job):
    lo, hi, count, seed, opts = job
    rng = random.Random(seed)
    acc = _new_acc()
    for _ in range(count):
        q = rng.randrange(lo, hi)
        p = rng.randrange(1, q)
        g = gcd(p, q)
        p //= g
        q //= g
        if p < 1 or q < 2:
            continue
        orb = run_orbit(p, q,
                        height_cap=max(opts["height_cap"], opts["height_mult"] * p),
                        step_cap=opts["step_cap"],
                        exact_bits=opts["exact_bits"], tie=opts["tie"],
                        lean=True)
        accumulate(p, q, orb, acc)
    return _plain(acc)


def _plain(acc: dict) -> dict:
    out = dict(acc)
    out["status_counts"] = dict(acc["status_counts"])
    for k in ("length_hist", "excursion_hist", "kemp_hist", "kempf_hist"):
        out[k] = dict(acc[k])
    for k in ("absorb_all", "absorb_tail"):
        out[k] = {kk: list(vv) for kk, vv in acc[k].items()}
    out["SB"] = {B: {**acc["SB"][B], "hist": dict(acc["SB"][B]["hist"])} for B in range(4)}
    return out


def _rehydrate(d: dict) -> dict:
    acc = _new_acc()
    for k, v in d.items():
        if k in ("status_counts",):
            for kk, vv in v.items():
                acc[k][kk] += vv
        elif k in ("length_hist", "excursion_hist", "kemp_hist", "kempf_hist"):
            for kk, vv in v.items():
                acc[k][int(kk)] += vv
        elif k == "SB_zero_maxCT":
            for B in range(4):
                acc[k][B] = tuple(v[B]) if B in v else tuple(v[str(B)])
        elif k in ("absorb_all", "absorb_tail"):
            for kk, vv in v.items():
                acc[k][int(kk)][0] += vv[0]
                acc[k][int(kk)][1] += vv[1]
        elif k == "SB":
            for B in range(4):
                src = v[B] if B in v else v[str(B)]
                tgt = acc["SB"][B]
                tgt["sum"] = src["sum"]
                tgt["n"] = src["n"]
                tgt["min"] = tuple(src["min"]) if src["min"][0] != float("inf") else (float("inf"), None)
                tgt["max"] = tuple(src["max"])
                for kk, vv in src["hist"].items():
                    tgt["hist"][int(kk)] += vv
        else:
            acc[k] = v
    return acc


def summarise(acc: dict, opts: dict) -> dict:
    absorb_rows = []
    for Cval in sorted(k for k in acc["absorb_tail"] if 2 <= k <= 64):
        visits, zeros = acc["absorb_tail"][Cval]
        if visits >= 200:
            absorb_rows.append({"C": Cval, "visits": visits, "zeros": zeros,
                                "empirical": zeros / visits,
                                "model_1_over_C": 1.0 / Cval,
                                "ratio_emp_over_model": (zeros / visits) * Cval})
    tot_v = sum(v[0] for k, v in acc["absorb_tail"].items() if k)
    tot_z = sum(v[1] for k, v in acc["absorb_tail"].items() if k)
    kemp_hist = {f"[{k/2:.1f},{(k+1)/2:.1f})": v
                 for k, v in sorted(acc["kemp_hist"].items())}
    return {
        "orbits": acc["orbits"],
        "terminated": acc["terminated"],
        "unresolved": acc["unresolved"],
        "status_counts": dict(acc["status_counts"]),
        "unresolved_examples": acc["unresolved_examples"],
        "max_absolute_C": {"value": acc["max_abs_C"][0], "at_p_q_n": acc["max_abs_C"][1]},
        "max_excursion_ratio_maxC_over_C0": {"value": acc["max_ratio_C0"][0],
                                             "at_p_q_n_C0": acc["max_ratio_C0"][1]},
        "max_maxC_over_q": {"value": acc["max_ratio_q"][0], "at_p_q_n": acc["max_ratio_q"][1]},
        "longest_orbit_steps_to_termination": {"steps": acc["longest"][0],
                                               "at_p_q": acc["longest"][1]},
        "orbit_length_histogram": dict(sorted(acc["length_hist"].items())),
        "excursion_ratio_histogram_quarter_buckets": dict(sorted(acc["excursion_hist"].items())),
        "deepest_negative_E": {"value": acc["neg_depth_max"][0], "at": acc["neg_depth_max"][1]},
        "max_negE_over_log2log2C": {"value": acc["loglog_ratio_max"][0],
                                    "at": acc["loglog_ratio_max"][1]},
        "drift": {
            "random_model_E_log_ratio": RANDOM_MODEL_DRIFT,
            "empirical_all_steps": acc["drift_sum"] / acc["drift_n"] if acc["drift_n"] else None,
            "steps_all": acc["drift_n"],
            "empirical_n_ge_1": acc["drift1_sum"] / acc["drift1_n"] if acc["drift1_n"] else None,
            "steps_n_ge_1": acc["drift1_n"],
            "empirical_at_or_after_first_negative": (acc["drift_neg_sum"] / acc["drift_neg_n"]
                                                     if acc["drift_neg_n"] else None),
            "steps_at_or_after_first_negative": acc["drift_neg_n"],
            "empirical_strictly_after_first_negative": (
                acc["drift_negstrict_sum"] / acc["drift_negstrict_n"]
                if acc["drift_negstrict_n"] else None),
            "steps_strictly_after_first_negative": acc["drift_negstrict_n"],
            "note": "the 'at or after' variant includes the first negative step itself and "
                    "is therefore biased upward by construction; use the strict variant",
        },
        "absorption": {
            "note": "restricted to visits with n >= 1 (the n = 0 visit is fixed by the seed "
                    "and E_0 = 0 there only when p = 1, which biases the n = 0 sample)",
            "overall_visits": tot_v, "overall_zeros": tot_z,
            "overall_rate": tot_z / tot_v if tot_v else None,
            "per_height": absorb_rows,
        },
        "r04_record_excess": {
            "definition": "(H_{k+1}-H_k)/log2 log2 max(4,H_k) on the record subsequence of C",
            "records_seen": acc["kemp_records"],
            "max": {"value": acc["kemp_max"][0], "at_p_q_n_prevrec_newrec": acc["kemp_max"][1]},
            "histogram_half_buckets": kemp_hist,
            "normalised_filter": KEMP_NORMALISED_FILTER,
            "filtered_records_seen": acc["kempf_records"],
            "filtered_max": {"value": acc["kempf_max"][0],
                             "at_p_q_n_prevrec_newrec_normerr": acc["kempf_max"][1]},
            "filtered_histogram_half_buckets": {
                f"[{k/2:.1f},{(k+1)/2:.1f})": v for k, v in sorted(acc["kempf_hist"].items())},
            "reading": "the UNFILTERED ratio is unbounded on finite orbits because one "
                       "unrestricted step can multiply C by 3/2; r04's K only becomes a "
                       "meaningful quantity once the rate hypothesis E_n/C_n -> 0 is imposed, "
                       "which is what the filtered variant approximates",
        },
        "r01_excess_mass": {
            "definition": "S_B(T)=sum_{n<T}(-E_n-B)_+/C_n over the whole finite orbit; "
                          "ratio = S_B(T)/log C_T, orbits with C_T >= 8 only",
            "by_B": {str(B): {
                "orbits": acc["SB"][B]["n"],
                "mean_ratio": (acc["SB"][B]["sum"] / acc["SB"][B]["n"]
                               if acc["SB"][B]["n"] else None),
                "min_ratio": (acc["SB"][B]["min"][0]
                              if acc["SB"][B]["min"][0] != float("inf") else None),
                "min_at_p_q_T_CT_S": acc["SB"][B]["min"][1],
                "max_ratio": acc["SB"][B]["max"][0],
                "max_at_p_q_T_CT_S": acc["SB"][B]["max"][1],
                "largest_C_T_with_S_B_exactly_zero": acc["SB_zero_maxCT"][B][0],
                "largest_C_T_with_S_B_zero_at_p_q_T": acc["SB_zero_maxCT"][B][1],
                "histogram_tenth_buckets": dict(sorted(acc["SB"][B]["hist"].items())),
            } for B in range(4)},
            "falsifier_reading": "an orbit with S_B(T) = 0 and large C_T forces "
                                 "K_B >= kappa_B * log C_T; the recorded "
                                 "largest_C_T_with_S_B_exactly_zero is the strongest "
                                 "finite lower bound on r01's additive constant",
        },
        "options": opts,
    }


def seeded_families(step_cap: int, height_cap: int, kscan: int = 20000) -> dict:
    """Run the corpus's exact structural fixtures directly as (C_0, D_0) seeds."""
    out = []
    # the (u,v) = (11, 11*(33 + 79833600 k) - 1) normalized-return family
    for k in (0, 1, 2, 3, 5, 8, 13, 21, 100, 1000, 12345):
        u = 11
        v = 11 * (33 + 79833600 * k) - 1
        orb = run_orbit(u, v, height_cap=height_cap, step_cap=step_cap,
                        exact_bits=200000, lean=True)
        out.append({"family": "normalized_return_11", "k": k,
                    "status": orb["status"], "steps": orb["steps"],
                    "max_C": max(orb["C"]), "C_head": orb["C"][:40],
                    "E_head": orb["E"][:40]})
    # the cancellation-free E = -1 block seed shape C_n = c + n
    for c in (5, 11, 40, 101, 1000):
        # D_0 = C_0 * m - 1 makes E_0 = -1 when C_0 > 2
        for m in (3, 7, 33, 1001):
            C0, D0 = c, c * m - 1
            orb = run_orbit(C0, D0, height_cap=height_cap, step_cap=step_cap,
                            exact_bits=200000, lean=True)
            out.append({"family": "E_minus_one_seed", "C0": C0, "m": m,
                        "status": orb["status"], "steps": orb["steps"],
                        "max_C": max(orb["C"]), "E_head": orb["E"][:30],
                        "C_head": orb["C"][:30]})
    # exhaustive k-scan of the normalized-return family: does ANY member of the
    # corpus's own hardest congruence family fail to reach E = 0?
    scan = {"k_range": [0, kscan], "unresolved": 0, "max_steps": (0, None),
            "max_C": (0, None), "steps_hist": defaultdict(int),
            "longest_negative_run": (0, None)}
    for k in range(kscan):
        u = 11
        v = 11 * (33 + 79833600 * k) - 1
        orb = run_orbit(u, v, height_cap=height_cap, step_cap=step_cap,
                        exact_bits=200000, lean=True)
        if orb["status"] != TERMINATED:
            scan["unresolved"] += 1
        scan["steps_hist"][orb["steps"]] += 1
        if orb["steps"] > scan["max_steps"][0]:
            scan["max_steps"] = (orb["steps"], k)
        mC = max(orb["C"])
        if mC > scan["max_C"][0]:
            scan["max_C"] = (mC, k)
        run = cur = 0
        for e in orb["E"]:
            cur = cur + 1 if e < 0 else 0
            run = max(run, cur)
        if run > scan["longest_negative_run"][0]:
            scan["longest_negative_run"] = (run, k)
    scan["steps_hist"] = dict(sorted(scan["steps_hist"].items()))
    return {"seeded_family_runs": out, "normalized_return_11_k_scan": scan}


def negative_run_search(limit_C: int, limit_D: int, step_cap: int,
                        height_cap: int, top: int = 15) -> dict:
    """Exhaustive small-seed search for the longest consecutive negative-E run
    and the largest height excursion, over primitive seeds (C_0, D_0)."""
    best_run = []
    best_exc = []
    for C0 in range(2, limit_C + 1):
        for D0 in range(C0 + 1, limit_D + 1):
            if gcd(C0, D0) != 1:
                continue
            orb = run_orbit(C0, D0, height_cap=height_cap, step_cap=step_cap,
                            exact_bits=20000, lean=True)
            E = orb["E"]
            run = cur = 0
            for e in E:
                if e < 0:
                    cur += 1
                    run = max(run, cur)
                else:
                    cur = 0
            best_run.append((run, C0, D0, orb["status"], orb["steps"], max(orb["C"])))
            best_exc.append((max(orb["C"]) / C0, C0, D0, orb["status"], orb["steps"]))
    best_run.sort(reverse=True)
    best_exc.sort(reverse=True)
    return {"longest_negative_runs": best_run[:top],
            "largest_excursions": best_exc[:top],
            "seed_box": {"C0_max": limit_C, "D0_max": limit_D}}


def improper_branch(qmax: int, step_cap: int, height_cap: int) -> dict:
    """x_0 = p/q > 1: same recursion, seeds with C_0 > D_0.  Outside Koizumi's
    normalisation (a_n = 1 or 2 occur, so the a_n are not strictly increasing),
    reported separately."""
    n = t = 0
    unres = []
    maxsteps = (0, None)
    for q in range(2, qmax + 1):
        for p in range(q + 1, 6 * q):
            if gcd(p, q) != 1:
                continue
            orb = run_orbit(p, q, height_cap=height_cap, step_cap=step_cap,
                            exact_bits=20000, lean=True)
            n += 1
            if orb["status"] == TERMINATED:
                t += 1
                if orb["steps"] > maxsteps[0]:
                    maxsteps = (orb["steps"], (p, q))
            elif len(unres) < 10:
                unres.append({"p": p, "q": q, "status": orb["status"],
                              "C": orb["C"][:40], "E": orb["E"][:40]})
    return {"orbits": n, "terminated": t, "unresolved": n - t,
            "longest": {"steps": maxsteps[0], "at_p_q": maxsteps[1]},
            "examples_unresolved": unres,
            "caveat": "a_n in {1,2} occurs, so these are not Koizumi-normalised orbits"}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--qmax", type=int, default=6000)
    ap.add_argument("--samples-per-decade", type=int, default=20000)
    ap.add_argument("--max-decade", type=int, default=11)
    ap.add_argument("--min-decade", type=int, default=4)
    ap.add_argument("--height-cap", type=int, default=10 ** 9)
    ap.add_argument("--height-mult", type=int, default=10 ** 5,
                    help="an orbit is aborted when C_n exceeds "
                         "max(--height-cap, --height-mult * C_0); the seed-relative "
                         "term matters at large q, where C_0 = p is itself huge")
    ap.add_argument("--step-cap", type=int, default=500)
    ap.add_argument("--exact-bits", type=int, default=6000)
    ap.add_argument("--tie", choices=("low", "high"), default="low")
    ap.add_argument("--tie-sensitivity-qmax", type=int, default=600)
    ap.add_argument("--seed-search-C", type=int, default=60)
    ap.add_argument("--seed-search-D", type=int, default=4000)
    ap.add_argument("--improper-qmax", type=int, default=60)
    ap.add_argument("--family-kscan", type=int, default=20000)
    ap.add_argument("--workers", type=int, default=max(1, (os.cpu_count() or 4) - 2))
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()

    if args.quick:
        args.qmax = 900
        args.samples_per_decade = 800
        args.max_decade = 8
        args.tie_sensitivity_qmax = 200
        args.seed_search_C = 25
        args.seed_search_D = 700
        args.improper_qmax = 25
        args.family_kscan = 300

    opts = {"height_cap": args.height_cap, "height_mult": args.height_mult,
            "step_cap": args.step_cap,
            "exact_bits": args.exact_bits, "tie": args.tie}
    t_start = time.perf_counter()
    timings = {}

    # ---- full sweep, sharded by q (strided so shards balance) ----
    t0 = time.perf_counter()
    nshard = max(1, args.workers)
    shards = [[q for q in range(2, args.qmax + 1) if q % nshard == i]
              for i in range(nshard)]
    jobs = [(s, opts) for s in shards if s]
    acc = _new_acc()
    if args.workers > 1:
        import multiprocessing as mp
        with mp.Pool(args.workers) as pool:
            for res in pool.imap_unordered(_run_range, jobs):
                _merge(acc, _rehydrate(res))
    else:
        for j in jobs:
            _merge(acc, _rehydrate(_run_range(j)))
    timings["full_sweep_seconds"] = time.perf_counter() - t0
    full = summarise(acc, {**opts, "qmax": args.qmax})

    # ---- random sampling at large q ----
    t0 = time.perf_counter()
    sample_reports = {}
    for k in range(args.min_decade, args.max_decade + 1):
        lo, hi = 10 ** k, 10 ** (k + 1)
        cnt = args.samples_per_decade
        per = max(1, cnt // max(1, args.workers))
        jobs = [(lo, hi, per, 1000003 * k + 17 * i, opts) for i in range(args.workers)]
        sacc = _new_acc()
        if args.workers > 1:
            import multiprocessing as mp
            with mp.Pool(args.workers) as pool:
                for res in pool.imap_unordered(_run_samples, jobs):
                    _merge(sacc, _rehydrate(res))
        else:
            for j in jobs:
                _merge(sacc, _rehydrate(_run_samples(j)))
        s = summarise(sacc, {**opts, "q_range": [lo, hi]})
        sample_reports[f"q_in_1e{k}_to_1e{k+1}"] = {
            key: s[key] for key in
            ("orbits", "terminated", "unresolved", "status_counts",
             "unresolved_examples", "max_absolute_C",
             "max_excursion_ratio_maxC_over_C0", "max_maxC_over_q",
             "longest_orbit_steps_to_termination", "orbit_length_histogram",
             "deepest_negative_E", "max_negE_over_log2log2C", "drift",
             "r04_record_excess", "r01_excess_mass")}
    timings["random_sampling_seconds"] = time.perf_counter() - t0

    # ---- tie-rule sensitivity ----
    t0 = time.perf_counter()
    tie_alt = {"tie": "high", **{k: v for k, v in opts.items() if k != "tie"}}
    tacc = _new_acc()
    for q in range(2, args.tie_sensitivity_qmax + 1):
        for p in range(1, q):
            if gcd(p, q) != 1:
                continue
            orb = run_orbit(p, q,
                            height_cap=max(opts["height_cap"], opts["height_mult"] * p),
                            step_cap=opts["step_cap"],
                            exact_bits=opts["exact_bits"], tie="high", lean=True)
            accumulate(p, q, orb, tacc)
    tie_report = {k: summarise(tacc, tie_alt)[k] for k in
                  ("orbits", "terminated", "unresolved", "status_counts",
                   "longest_orbit_steps_to_termination", "max_absolute_C",
                   "max_excursion_ratio_maxC_over_C0", "drift")}
    timings["tie_sensitivity_seconds"] = time.perf_counter() - t0

    # ---- seeded families + adversarial small-seed search + improper branch ----
    t0 = time.perf_counter()
    fam = seeded_families(args.step_cap, args.height_cap, kscan=args.family_kscan)
    timings["seeded_families_seconds"] = time.perf_counter() - t0
    t0 = time.perf_counter()
    seedsearch = negative_run_search(args.seed_search_C, args.seed_search_D,
                                     args.step_cap, args.height_cap)
    timings["seed_search_seconds"] = time.perf_counter() - t0
    t0 = time.perf_counter()
    improper = improper_branch(args.improper_qmax, args.step_cap, args.height_cap)
    timings["improper_seconds"] = time.perf_counter() - t0

    timings["total_seconds"] = time.perf_counter() - t_start

    payload = {
        "probe_id": "erdos243_strong_termination_survey",
        "quick": args.quick,
        "tie_rule": {
            "primary": "E_n in [-C_n/2, C_n/2): E = D mod C, then E -= C if 2E >= C; "
                       "ties (C even, D = C/2 mod C) round the quotient D/C UP",
            "alternative_tested": "E_n in (-C_n/2, C_n/2]",
        },
        "modulus_method": {
            "name": "shrinking suffix product (Koizumi Remark 18), hybrid with an exact prefix",
            "statement": "S_k = (prod_{j=k}^{n} C_j) * extra, S_{n+1} = extra; "
                         "D_0 mod S_0 transports to D_n mod (C_n * extra) losslessly "
                         "because C_k | D_k - E_k exactly, so knowing D_k mod (C_k*M) "
                         "determines a_k = (D_k-E_k)/C_k + 1 mod M",
            "justification": "D_n is needed only mod C_n (for E_n), mod C_{n+1} (for r_n) "
                             "and mod `extra`; every other bit of D_n is irrelevant. The "
                             "modulus is a product of the ACTUAL visited heights, so its "
                             "bit-length is sum_j log2 C_j <= N log2 H, not ~1.44*H*N as "
                             "for lcm(1..H)^{N+1}.",
            "hybrid": f"exact integer arithmetic while bit_length(D) <= {args.exact_bits}, "
                      "then the modular phase reseeded from the exact state (C_m, D_m); "
                      "the dynamics is Markov in (C, D) so the handover is lossless",
            "cross_validated_against": "formal_math/probes/erdos243_koizumi_state_probe.py "
                                       "orbit_exact and orbit_modular",
        },
        "full_sweep": full,
        "random_samples_large_q": sample_reports,
        "tie_rule_sensitivity": tie_report,
        "seeded_structural_families": fam,
        "adversarial_small_seed_search": seedsearch,
        "improper_branch_x0_gt_1": improper,
        "timings": timings,
    }
    text = json.dumps(payload, indent=1, ensure_ascii=False, default=str)
    if args.out:
        Path(args.out).write_text(text + "\n")
        print(f"wrote {args.out} ({len(text)} bytes) in {timings['total_seconds']:.1f}s")
    else:
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
