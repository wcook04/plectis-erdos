#!/usr/bin/env python3
"""Erdos #243: the classical Ahmes rationality criteria in canonical coordinates.

Wave-4 desk U1.  The classical rational-Ahmes-series toolkit (Sylvester 1880,
Erdos-Straus 1964 Thms 1 and 3, Badea 1993, Tijdeman-Yuan Indag. Math. 13 (2002)
Thm 4.1 / Cor 4.1) is a family of criteria of the shape

    limsup_n  W_n * (a_n^2/a_{n+1} - 1)  <= 0   ==>   Sylvester tail,

with a WEIGHT W_n that differs between authors:

    Koizumi Cor 20(1) (his rendering of Erdos-Straus)   W_n = Pi_{n-1}/a_n
    Erdos-Straus 1964 Thm 3, condition (ii'')           W_n = A_{n-1}
    Tijdeman-Yuan 2002 Thm 4.1 (b_n = 1)                W_n = A_{n-1}/a_n

where Pi_{n-1} = a_0 a_1 ... a_{n-1} and A_{n-1} = lcm(a_0, ..., a_{n-1}).
Since A_{n-1} <= Pi_{n-1}, the lcm-weighted criteria look strictly weaker in
hypothesis, hence strictly stronger as theorems, by the LCM DEFECT

    L_{n-1} := Pi_{n-1} / A_{n-1}   (a positive integer, non-decreasing),

which is unbounded in general.  This probe verifies that the apparent gain is
exactly the primitive reduction the corpus already performs, and therefore zero:

  Identity U1 (part 1).   With D_n = q * Pi_{n-1}, G_n = gcd(C_n, D_n),
  v_n = D_n/G_n = den(x_n) and kappa_n := q*A_{n-1}/v_n (an integer, because
  v_n | lcm(q, A_{n-1})),

        G_n = kappa_n * L_{n-1}                                      (exact)

  so L_{n-1} | G_n and E_n / L_{n-1} = kappa_n * e_n with e_n = E_n/G_n the
  PRIMITIVE error.  Dividing the criterion weight by L_{n-1} therefore replaces
  the integer E_n by the integer kappa_n e_n; "a small integer is <= 0" survives
  the reduction unchanged, and all three criteria decide the same half-space
  {E_n >= 0 eventually} = Koizumi Prop 19(2).

  Part 2 checks the exact relation Q_TY = -Q_ES / L_{n-1} and the asymptotics
  q*Q_ES_n -> E_n, q*Q_TY_n -> -kappa_n e_n.
  Part 3 replays the S4-R fixture (the E = -m cancellation-free clean-rise
  blocks) and shows L = kappa = 1 across the whole block, so on the corpus's
  surviving regime the lcm criterion IS the product criterion and its quantity
  sits at +m/q > 0, bounded away from 0 uniformly in the block length H.
  Part 4 measures Erdos-Straus Thm 1 condition (ii): A_{n-1}/a_n ~ kappa_n u_n/q,
  so "{N_k/n_{k+1}} bounded" is exactly "kappa_n u_n bounded", whose negation
  C_n -> infinity is the corpus's first necessary condition on a counterexample.
  Part 5 measures Koizumi Remark 21: gamma_n := 1 - a_n^2/a_{n+1} = eps_n + O(1/a_n).

Usage
-----
    ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/scripts/erdos243_lcm_defect_criterion_probe.py --quick
    ./repo-python .../erdos243_lcm_defect_criterion_probe.py --qmax 400 --out receipt.json
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from math import gcd
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from erdos243_orbit_engine import centre  # noqa: E402
from erdos243_clean_rise_cost_probe import s4r_seed  # noqa: E402


# --------------------------------------------------------------------------
# float helpers tolerant of doubly-exponential integers
# --------------------------------------------------------------------------

def log2_int(n: int) -> float:
    n = abs(n)
    if n == 0:
        return float("-inf")
    b = n.bit_length()
    if b <= 52:
        return math.log2(n)
    return (b - 52) + math.log2(n >> (b - 52))


def ratio(a: int, b: int) -> float:
    """a/b as a float, safe for arbitrarily large ints."""
    if a == 0:
        return 0.0
    sgn = -1.0 if ((a < 0) != (b < 0)) else 1.0
    x = log2_int(a) - log2_int(b)
    if x > 1000:
        return sgn * float("inf")
    if x < -1000:
        return sgn * 0.0
    return sgn * (2.0 ** x)


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


# --------------------------------------------------------------------------
# exact frame builder
# --------------------------------------------------------------------------

def exact_frames(C0: int, D0: int, *, step_cap: int = 40, bit_cap: int = 60000):
    """Exact pseudo-greedy frames from the seed (C_0, D_0) = (p, q).

    Each frame carries everything the classical criteria need at index n:
    C, D, E, a_n, a_{n+1}, G_n, Pi_{n-1}, A_{n-1}, v_n.
    """
    C, D = C0, D0
    q = D0
    Pi, A = 1, 1                      # Pi_{-1} = A_{-1} = 1 (empty)
    rows = []
    status = "step_cap"
    for n in range(step_cap):
        if D.bit_length() > bit_cap:
            status = "bit_cap"
            break
        e = centre(D % C, C)
        G = gcd(C, D)
        rows.append({
            "n": n, "C": C, "D": D, "E": e, "G": G,
            "Pi_prev": Pi, "A_prev": A, "a": None,
        })
        if e == 0:
            status = "terminated"
            break
        a = (D - e) // C + 1
        rows[-1]["a"] = a
        Pi = Pi * a
        A = lcm(A, a)
        D = D * a
        C = C - e
    # attach a_{n+1}
    for i in range(len(rows) - 1):
        rows[i]["a_next"] = rows[i + 1]["a"]
    if rows:
        rows[-1]["a_next"] = None
    return {"seed": (C0, D0), "q": q, "status": status, "rows": rows}


# --------------------------------------------------------------------------
# part 1: the identity G_n = kappa_n * L_{n-1}
# --------------------------------------------------------------------------

def part1_identity(orbits):
    n_frames = 0
    fail_v_divides = 0
    fail_kappa_int = 0
    fail_identity = 0
    fail_E_over_L = 0
    max_L = 1
    max_kappa = 1
    max_M = 1
    fail_M_div_G = 0
    fail_M_div_E = 0
    examples = []
    for orb in orbits:
        q = orb["q"]
        for r in orb["rows"]:
            C, D, E, G = r["C"], r["D"], r["E"], r["G"]
            Pi, A = r["Pi_prev"], r["A_prev"]
            v = D // G
            L = Pi // A
            if Pi % A != 0:
                fail_identity += 1
                continue
            if (q * A) % v != 0:
                fail_v_divides += 1
                continue
            kappa = (q * A) // v
            n_frames += 1
            if kappa <= 0:
                fail_kappa_int += 1
            if kappa * L != G:
                fail_identity += 1
                if len(examples) < 4:
                    examples.append({"seed": orb["seed"], "n": r["n"],
                                     "G": G, "kappa": kappa, "L": L})
            if E % L != 0 or (E // L) != kappa * (E // G):
                fail_E_over_L += 1
            # corpus normalisation (CumulativeLcmTransfer.lean):
            #   M_n = q*Pi_{n-1} / lcm(q, a_0..a_{n-1}) = L_{n-1} * gcd(q, A_{n-1})
            M = (q * Pi) // lcm(q, A)
            if M != L * gcd(q, A) or G % M != 0:
                fail_M_div_G += 1
            if E % M != 0:
                fail_M_div_E += 1
            max_L = max(max_L, L)
            max_kappa = max(max_kappa, kappa)
            max_M = max(max_M, M)
            r["v"], r["L"], r["kappa"], r["M"] = v, L, kappa, M
    return {
        "frames": n_frames,
        "v_divides_q_lcm_failures": fail_v_divides,
        "kappa_not_positive_integer": fail_kappa_int,
        "identity_G_eq_kappa_times_L_failures": fail_identity,
        "E_over_L_eq_kappa_times_e_failures": fail_E_over_L,
        "corpus_M_dvd_G_failures": fail_M_div_G,
        "corpus_M_dvd_E_failures": fail_M_div_E,
        "max_lcm_defect_L": max_L,
        "max_corpus_overlap_debt_M": max_M,
        "max_kappa": max_kappa,
        "counterexamples": examples,
    }


# --------------------------------------------------------------------------
# part 2: the three criterion weights and their exact relation
# --------------------------------------------------------------------------

def part2_criteria(orbits, min_a_bits: int = 40):
    """Q_ES = (Pi_{n-1}/a_n)(1 - a_n^2/a_{n+1}),  Q_TY = (A_{n-1}/a_n)(a_n^2/a_{n+1} - 1).

    Exact rational arithmetic on numerators; floats only for reporting.
    """
    n_used = 0
    exact_rel_failures = 0
    sign_mismatch_ES = 0
    worst_qQES_minus_E = 0.0
    worst_qQTY_plus_kappa_e = 0.0
    rows_out = []
    for orb in orbits:
        q = orb["q"]
        for r in orb["rows"]:
            a, an = r.get("a"), r.get("a_next")
            if a is None or an is None or "L" not in r:
                continue
            if a.bit_length() < min_a_bits:
                continue          # asymptotic statements only; skip the head
            Pi, A, L, kappa, G, E = r["Pi_prev"], r["A_prev"], r["L"], r["kappa"], r["G"], r["E"]
            e = E // G
            # Q_ES = Pi*(a_{n+1} - a^2) / (a * a_{n+1})    (exact rational num/den)
            num_es = Pi * (an - a * a)
            den = a * an
            num_ty = -A * (an - a * a)
            n_used += 1
            # exact relation  Q_TY = -Q_ES / L   <=>   num_ty * L == -num_es
            if num_ty * L != -num_es:
                exact_rel_failures += 1
            qQES = ratio(q * num_es, den)
            qQTY = ratio(q * num_ty, den)
            if (q * num_es > 0) != (E > 0) and E != 0:
                sign_mismatch_ES += 1
            # exact residuals (floats only at the very end)
            worst_qQES_minus_E = max(
                worst_qQES_minus_E, abs(ratio(q * num_es - E * den, den)))
            worst_qQTY_plus_kappa_e = max(
                worst_qQTY_plus_kappa_e, abs(ratio(q * num_ty + kappa * e * den, den)))
            if len(rows_out) < 12:
                rows_out.append({"seed": orb["seed"], "n": r["n"], "E": E, "e": e,
                                 "G": G, "L": L, "kappa": kappa,
                                 "q_Q_ES": qQES, "q_Q_TY": qQTY})
    return {
        "frames_used": n_used,
        "exact_relation_QTY_eq_minus_QES_over_L_failures": exact_rel_failures,
        "sign_mismatch_QES_vs_E": sign_mismatch_ES,
        "max_abs_qQES_minus_E": worst_qQES_minus_E,
        "max_abs_qQTY_plus_kappa_e": worst_qQTY_plus_kappa_e,
        "sample_rows": rows_out,
    }


# --------------------------------------------------------------------------
# part 3: the S4-R clean-rise fixture (E = -m, cancellation free)
# --------------------------------------------------------------------------

def part3_s4r(cases, step_cap: int, bit_cap: int):
    rows = []
    for (c, m, H, lam) in cases:
        if gcd(c, m) != 1 or 2 * m >= c:
            continue
        cs, k, a0, D0 = s4r_seed(c, m, H, lam)
        orb = exact_frames(cs[0], D0, step_cap=min(step_cap, H + 3), bit_cap=bit_cap)
        q = orb["q"]
        blk = []
        for r in orb["rows"]:
            if r.get("a") is None or r.get("a_next") is None:
                continue
            Pi, A, G, E, a, an = r["Pi_prev"], r["A_prev"], r["G"], r["E"], r["a"], r["a_next"]
            v = r["D"] // G
            L = Pi // A
            kappa = (q * A) // v if (q * A) % v == 0 else None
            num_ty = -A * (an - a * a)
            den = a * an
            blk.append({"n": r["n"], "E": E, "G": G, "L": L, "kappa": kappa,
                        "q_Q_TY": ratio(q * num_ty, den),
                        "defect_Delta": an - (a * a - a + 1)})
        rows.append({
            "c": c, "m": m, "H": H, "lam": lam,
            "steps_exact": len(blk),
            "all_E_eq_minus_m": all(b["E"] == -m for b in blk),
            "all_G_eq_1": all(b["G"] == 1 for b in blk),
            "all_L_eq_1": all(b["L"] == 1 for b in blk),
            "all_kappa_eq_1": all(b["kappa"] == 1 for b in blk),
            "min_q_Q_TY": min((b["q_Q_TY"] for b in blk), default=None),
            "max_q_Q_TY": max((b["q_Q_TY"] for b in blk), default=None),
            "all_defects_negative": all(b["defect_Delta"] < 0 for b in blk),
            "block": blk[:6],
        })
    return {
        "n_cases": len(rows),
        "all_criteria_fail_at_every_index": all(
            r["min_q_Q_TY"] is not None and r["min_q_Q_TY"] > 0 for r in rows),
        "lcm_defect_is_trivial_on_the_block": all(r["all_L_eq_1"] for r in rows),
        "rows": rows,
    }


# --------------------------------------------------------------------------
# part 4: Erdos-Straus Thm 1 condition (ii) is "kappa_n u_n bounded"
# --------------------------------------------------------------------------

def part4_es_thm1(orbits, min_a_bits: int = 40):
    worst_rel = 0.0
    n_used = 0
    growth = []
    for orb in orbits:
        q = orb["q"]
        seen = []
        for r in orb["rows"]:
            a = r.get("a")
            if a is None or "L" not in r or a.bit_length() < min_a_bits:
                continue
            A, kappa, G, C = r["A_prev"], r["kappa"], r["G"], r["C"]
            u = C // G
            lhs = ratio(A, a)                 # A_{n-1}/a_n
            rhs = kappa * u / q               # predicted
            # exact relative deviation (A*q - kappa*u*a) / (kappa*u*a)
            if kappa * u > 0:
                worst_rel = max(worst_rel,
                                abs(ratio(A * q - kappa * u * a, kappa * u * a)))
            n_used += 1
            seen.append({"n": r["n"], "A_over_a": lhs, "kappa_u_over_q": rhs, "u": u})
        if seen:
            growth.append({"seed": orb["seed"], "first": seen[0], "last": seen[-1]})
    return {
        "frames_used": n_used,
        "max_relative_error_A_over_a_vs_kappa_u_over_q": worst_rel,
        "samples": growth[:8],
    }


# --------------------------------------------------------------------------
# part 5: Koizumi Remark 21, gamma_n = eps_n + O(1/a_n)
# --------------------------------------------------------------------------

def part5_remark21(orbits, min_a_bits: int = 40):
    worst = 0.0
    n_used = 0
    for orb in orbits:
        for r in orb["rows"]:
            a, an = r.get("a"), r.get("a_next")
            if a is None or an is None or a.bit_length() < min_a_bits:
                continue
            # a_n * (gamma_n - eps_n) computed exactly, then floated once
            C, E = r["C"], r["E"]
            num = a * (C * (an - a * a) - E * an)
            den = C * an
            n_used += 1
            worst = max(worst, abs(ratio(num, den)))
    return {"frames_used": n_used, "max_a_n_times_abs_gamma_minus_eps": worst}


# --------------------------------------------------------------------------
# part 6: Erdos-Straus's c_k is exactly kappa_{k+1} * u_{k+1}
# --------------------------------------------------------------------------

def part6_es_ck(orbits, min_a_bits: int = 40):
    n_used = 0
    mismatches = 0
    samples = []
    for orb in orbits:
        q = orb["q"]
        rows = orb["rows"]
        for i in range(len(rows) - 1):
            r, rn = rows[i], rows[i + 1]
            a_next = r.get("a_next")
            if a_next is None or "kappa" not in rn or r.get("a") is None:
                continue
            if r["a"].bit_length() < min_a_bits:
                continue
            A_k = lcm(r["A_prev"], r["a"])            # lcm(a_0..a_k)
            ck = -((-q * A_k) // a_next)              # ceil(q*A_k / a_{k+1})
            u_next = rn["C"] // rn["G"]
            pred = rn["kappa"] * u_next
            n_used += 1
            if ck != pred:
                mismatches += 1
                if len(samples) < 4:
                    samples.append({"seed": orb["seed"], "k": r["n"],
                                    "c_k": ck, "kappa_u": pred})
    return {"frames_used": n_used, "c_k_ne_kappa_u_count": mismatches,
            "mismatch_samples": samples}


# --------------------------------------------------------------------------
# part 7: cancellation-free identities (h_n = 1)
# --------------------------------------------------------------------------

def part7_clean_identities(orbits):
    n_three_term = 0
    fail_three_term = 0
    n_defect = 0
    fail_defect = 0
    for orb in orbits:
        rows = orb["rows"]
        for i in range(len(rows) - 2):
            r0, r1, r2 = rows[i], rows[i + 1], rows[i + 2]
            if r0.get("a") is None or r1.get("a") is None:
                continue
            if r1["G"] != r0["G"] or r2["G"] != r1["G"]:
                continue                       # need h_n = h_{n+1} = 1
            u0, u1, u2 = (r["C"] // r["G"] for r in (r0, r1, r2))
            a0, a1 = r0["a"], r1["a"]
            n_three_term += 1
            if u2 != (a1 + a0) * u1 - a0 * a0 * u0:
                fail_three_term += 1
            e0, e1 = r0["E"] // r0["G"], r1["E"] // r1["G"]
            delta = a1 - (a0 * a0 - a0 + 1)
            n_defect += 1
            if e1 != a0 * a0 * e0 - delta * u1:
                fail_defect += 1
    return {
        "clean_triples": n_three_term,
        "three_term_recurrence_failures": fail_three_term,
        "defect_identity_pairs": n_defect,
        "defect_identity_failures": fail_defect,
    }


# --------------------------------------------------------------------------

def collect_orbits(qmax: int, step_cap: int, bit_cap: int, extra_seeds):
    orbits = []
    for q in range(2, qmax + 1):
        for p in range(1, q):
            if gcd(p, q) != 1:
                continue
            orbits.append(exact_frames(p, q, step_cap=step_cap, bit_cap=bit_cap))
    for (C0, D0) in extra_seeds:
        orbits.append(exact_frames(C0, D0, step_cap=step_cap, bit_cap=bit_cap))
    return orbits


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--qmax", type=int, default=60)
    ap.add_argument("--step-cap", type=int, default=40)
    ap.add_argument("--bit-cap", type=int, default=40000)
    ap.add_argument("--min-a-bits", type=int, default=40)
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()
    if args.quick:
        args.qmax, args.step_cap, args.bit_cap = 24, 30, 12000

    # the corpus recovery family (11, 11*(33 + 79833600k) - 1)
    extra = [(11, 11 * (33 + 79833600 * k) - 1) for k in (0, 1, 2, 5386 % 7)]
    orbits = collect_orbits(args.qmax, args.step_cap, args.bit_cap, extra)

    p1 = part1_identity(orbits)
    p2 = part2_criteria(orbits, args.min_a_bits)
    s4r_cases = ([(10, 3, 5, 1), (13, 3, 5, 1)] if args.quick
                 else [(10, 3, 6, 1), (13, 3, 6, 1), (100003, 3, 5, 1), (10, 7, 5, 1)])
    p3 = part3_s4r(s4r_cases, args.step_cap, args.bit_cap)
    p4 = part4_es_thm1(orbits, args.min_a_bits)
    p5 = part5_remark21(orbits, args.min_a_bits)

    report = {
        "probe": "erdos243_lcm_defect_criterion_probe",
        "config": {"qmax": args.qmax, "step_cap": args.step_cap,
                   "bit_cap": args.bit_cap, "min_a_bits": args.min_a_bits,
                   "quick": args.quick, "orbits": len(orbits)},
        "part1_identity_G_eq_kappa_L": p1,
        "part2_criterion_weights": p2,
        "part3_s4r_clean_rise_fixture": p3,
        "part4_erdos_straus_thm1_condition_ii": p4,
        "part5_koizumi_remark21_gamma_vs_eps": p5,
        "part6_erdos_straus_ck_is_kappa_u": part6_es_ck(orbits, args.min_a_bits),
        "part7_cancellation_free_identities": part7_clean_identities(orbits),
        "evidence_class": "exact_finite_computation",
    }
    report["verdict"] = {
        "identity_holds_everywhere": (
            p1["identity_G_eq_kappa_times_L_failures"] == 0
            and p1["v_divides_q_lcm_failures"] == 0
            and p1["E_over_L_eq_kappa_times_e_failures"] == 0),
        "lcm_criterion_is_product_criterion_divided_by_L": (
            p2["exact_relation_QTY_eq_minus_QES_over_L_failures"] == 0),
        "criteria_track_the_sign_of_E": p2["sign_mismatch_QES_vs_E"] == 0,
        "all_classical_criteria_fail_on_the_S4R_block": (
            p3["all_criteria_fail_at_every_index"]),
        "lcm_defect_trivial_on_the_surviving_regime": (
            p3["lcm_defect_is_trivial_on_the_block"]),
    }
    text = json.dumps(report, indent=2, sort_keys=False, default=str)
    if args.out:
        Path(args.out).write_text(text + "\n", encoding="utf-8")
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
