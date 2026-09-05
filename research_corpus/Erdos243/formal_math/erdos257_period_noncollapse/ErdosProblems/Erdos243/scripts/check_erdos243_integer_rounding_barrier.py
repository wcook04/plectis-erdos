#!/usr/bin/env python3
"""Exact replay of the integer-rounding linear barrier and its two inequalities.

Source note: ErdosProblems/Erdos243/EightReturnRigidityCriteria.md section 1
(return r01, sections 2 and 3).  Everything here is exact rational or exact
integer arithmetic; no floating point enters a verdict.

Part A -- the critical envelope is exact.  For F(n) = n H_n (H_n the harmonic
number) the four hypotheses (8)-(11) of r01 Theorem 2 hold as identities:

    F_{n+1} - F_n = H_n + 1,      d_n := F_{n+2} - 2 F_{n+1} + F_n = 1/(n+1),
    eta_n := n (F_{n+1}/F_n - 1) - 1 = 1/H_n,
    n^2 d_n / (F_n eta_n) = n/(n+1) -> 1,      d_{n+1}/d_n = (n+1)/(n+2),

and sum 1/F_n = sum 1/(n H_n) diverges.  Each identity is checked as an exact
Fraction equality, so the envelope used in Part B is a genuine instance of the
theorem rather than an approximation of one.

Part B -- the linear barrier (r01 (18)).  The maximal floor orbit
X_{n+1} = floor((F_{n+1}/F_n) X_n) is run in exact integer arithmetic from
index N.  The barrier predicate is M * eta_n < 1 with M = ceil(X_n / n),
equivalently M < H_n.  At the first index n0 where it holds the checker records
the predicted M and then asserts, to the end of the run,

    X_k <= M k        for every k >= n0,          (the linear barrier)
    X_{k+1} - X_k <= M for every k >= n0,         (r01 (14), the output bound)

which is the step that converts a real envelope bound on C_n into the integer
conclusion C_n = O(n) and (-E_n)_+ = O(1).

Part C -- the two load-bearing inequalities, sampled exactly.

    (15)  Psi(t) - Psi(s) <= (theta - 1/2)(t - s) + (t - s)^2 / 2,
          Psi(x) = (frac(x)^2 - frac(x))/2,  theta = frac(s).
    (16)  theta >= c + (Psi(s + Delta) - Psi(s))/A - Delta^2/(2A),
          Delta = A - B theta, R = A/B,
          with c = 1/4 (the constant printed in r01) and with the sharp
          c = 1/2 - 1/(16 R), valid for every R > 1/4.  In the application
          R_n -> 1, so the sharp divergence constant is 7/16, not 1/4.

Run:
    ./repo-python .../scripts/check_erdos243_integer_rounding_barrier.py --quick
    ./repo-python .../scripts/check_erdos243_integer_rounding_barrier.py
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction as F


# ---------------------------------------------------------------------------
# Part A: the envelope F(n) = n H_n satisfies (8)-(11) exactly
# ---------------------------------------------------------------------------


def harmonic_table(n_max: int) -> list:
    """H_0 = 0, H_n = sum_{k<=n} 1/k, as exact Fractions."""
    table = [F(0)]
    acc = F(0)
    for k in range(1, n_max + 1):
        acc += F(1, k)
        table.append(acc)
    return table


def envelope_identities(H, n_lo: int, n_hi: int) -> dict:
    """Exact verification of (8), (9), (10) for F(n) = n H_n."""
    checked = 0
    failures = []
    ratio_min = None
    ratio_max = None
    for n in range(n_lo, n_hi):
        Fn = n * H[n]
        Fn1 = (n + 1) * H[n + 1]
        Fn2 = (n + 2) * H[n + 2]
        d_n = Fn2 - 2 * Fn1 + Fn
        eta_n = n * (Fn1 / Fn - 1) - 1
        d_n1 = ((n + 3) * H[n + 3]) - 2 * Fn2 + Fn1
        checked += 1
        if Fn1 - Fn != H[n] + 1:
            failures.append(("first_difference", n))
        if d_n != F(1, n + 1):
            failures.append(("second_difference", n))
        if eta_n != F(1, 1) / H[n]:
            failures.append(("eta", n))
        if d_n <= 0:
            failures.append(("h8_positive_second_difference", n))
        ratio = n * n * d_n / (Fn * eta_n)
        if ratio != F(n, n + 1):
            failures.append(("h9_ratio", n))
        if d_n1 / d_n != F(n + 1, n + 2):
            failures.append(("h10_ratio", n))
        ratio_min = ratio if ratio_min is None or ratio < ratio_min else ratio_min
        ratio_max = ratio if ratio_max is None or ratio > ratio_max else ratio_max
    return {
        "range": [n_lo, n_hi],
        "identities_checked": checked,
        "failures": failures[:8],
        "failure_count": len(failures),
        "h9_ratio_min": str(ratio_min),
        "h9_ratio_max": str(ratio_max),
        "h11_divergence": "sum 1/(n H_n) diverges by the integral test with "
                          "antiderivative log log n; not a finite check",
    }


# ---------------------------------------------------------------------------
# Part B: the maximal floor orbit and the linear barrier
# ---------------------------------------------------------------------------


def floor_orbit(H, N: int, T: int, y0_num: int, y0_den: int) -> dict:
    """X_{n+1} = floor((F_{n+1}/F_n) X_n) in exact integer arithmetic."""
    FN = N * H[N]
    start = F(y0_num, y0_den) * FN
    X = int(start) + (1 if start != int(start) else 0)
    X_start = X
    barrier = None
    barrier_failures = []
    increment_failures = []
    max_increment_after = 0
    for n in range(N, T):
        # barrier predicate BEFORE the update: M = ceil(X_n / n), M * eta_n < 1
        M = -((-X) // n)
        if barrier is None and M * (F(1, 1) / H[n]) < 1:
            barrier = {"index": int(n), "M": int(M), "X": int(X),
                       "X_over_n": float(F(X, n)),
                       "eta_n": float(F(1, 1) / H[n]),
                       "H_n": float(H[n]),
                       "Y_n": float(F(X, 1) / (n * H[n]))}
        nxt = int(F((n + 1) * H[n + 1] * X, 1) / (n * H[n]))
        if barrier is not None:
            M0 = barrier["M"]
            if nxt > M0 * (n + 1):
                barrier_failures.append({"n": int(n + 1), "X": int(nxt),
                                         "M_times_n": int(M0 * (n + 1))})
            inc = nxt - X
            if inc > max_increment_after:
                max_increment_after = inc
            if inc > M0:
                increment_failures.append({"n": int(n), "increment": int(inc),
                                           "M": int(M0)})
        X = nxt
    return {
        "N": N, "T": T,
        "y0": f"{y0_num}/{y0_den}",
        "X_N": int(X_start),
        "X_T": int(X),
        "X_T_over_T": float(F(X, T)),
        "Y_T": float(F(X, 1) / (T * H[T])),
        "barrier": barrier,
        "barrier_engaged": barrier is not None,
        "linear_barrier_violations": len(barrier_failures),
        "linear_barrier_violation_sample": barrier_failures[:4],
        "increment_bound_violations": len(increment_failures),
        "increment_bound_violation_sample": increment_failures[:4],
        "max_increment_after_barrier": int(max_increment_after),
        "X_T_le_M_times_T": barrier is not None and X <= barrier["M"] * T,
    }


# ---------------------------------------------------------------------------
# Part C: the two inequalities, exact rational sampling
# ---------------------------------------------------------------------------


def frac_part(x: F) -> F:
    return x - (x.numerator // x.denominator)


def psi(x: F) -> F:
    f = frac_part(x)
    return (f * f - f) / 2


def slack_15(s: F, t: F) -> F:
    th = frac_part(s)
    return (th - F(1, 2)) * (t - s) + (t - s) ** 2 / 2 - (psi(t) - psi(s))


def slack_16(s: F, A: F, B: F, sharp: bool) -> F:
    th = frac_part(s)
    D = A - B * th
    R = A / B
    c = (F(1, 2) - F(1, 16) / R) if sharp else F(1, 4)
    return th - (c + (psi(s + D) - psi(s)) / A - D * D / (2 * A))


def inequality_sampling(quick: bool) -> dict:
    s_den = 12 if quick else 24
    d_den = 7 if quick else 11
    s_span = 24 if quick else 48
    d_span = 30 if quick else 60
    worst15 = None
    n15 = 0
    for i in range(-s_span, s_span + 1):
        s = F(i, s_den)
        for j in range(-d_span, d_span + 1):
            t = s + F(j, d_den)
            sl = slack_15(s, t)
            n15 += 1
            if worst15 is None or sl < worst15[0]:
                worst15 = (sl, s, t)
    # s exactly an integer is the delicate supporting-slope case
    for i in range(-40, 41):
        s = F(i)
        for j in range(-d_span, d_span + 1):
            t = s + F(j, d_den)
            sl = slack_15(s, t)
            n15 += 1
            if sl < worst15[0]:
                worst15 = (sl, s, t)

    worst16 = None
    worst16_sharp = None
    n16 = 0
    b_values = [F(1), F(3), F(17)] if quick else [F(1), F(3), F(17), F(101)]
    r_values = ([F(1, 2), F(1), F(3, 2), F(7), F(1000)] if quick
                else [F(1, 3), F(1, 2), F(1), F(3, 2), F(7), F(1000), F(10 ** 6)])
    theta_den = 200 if quick else 400
    for k in range(theta_den):
        s = F(k, theta_den)
        for B in b_values:
            for R in r_values:
                A = B * R
                n16 += 1
                sl = slack_16(s, A, B, sharp=False)
                sh = slack_16(s, A, B, sharp=True)
                if worst16 is None or sl < worst16[0]:
                    worst16 = (sl, s, A, B, R)
                if worst16_sharp is None or sh < worst16_sharp[0]:
                    worst16_sharp = (sh, s, A, B, R)
    return {
        "ineq_15_samples": n15,
        "ineq_15_min_slack": str(worst15[0]),
        "ineq_15_holds": worst15[0] >= 0,
        "ineq_15_tight": worst15[0] == 0,
        "ineq_15_argmin": {"s": str(worst15[1]), "t": str(worst15[2])},
        "ineq_16_samples": n16,
        "ineq_16_constant_one_quarter_min_slack": str(worst16[0]),
        "ineq_16_constant_one_quarter_holds": worst16[0] >= 0,
        "ineq_16_sharp_constant_min_slack": str(worst16_sharp[0]),
        "ineq_16_sharp_constant_holds": worst16_sharp[0] >= 0,
        "ineq_16_sharp_constant_tight": worst16_sharp[0] == 0,
        "ineq_16_sharp_argmin": {"s": str(worst16_sharp[1]),
                                 "A": str(worst16_sharp[2]),
                                 "B": str(worst16_sharp[3]),
                                 "R": str(worst16_sharp[4])},
        "sharp_constant_form": "1/2 - 1/(16 R); at R -> 1 this is 7/16",
    }


# ---------------------------------------------------------------------------


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--json", action="store_true",
                    help="print the full report instead of the one-line status")
    args = ap.parse_args()

    N = 100
    T = 4000 if args.quick else 30000
    ident_hi = 400 if args.quick else 2000
    H = harmonic_table(T + 4)

    part_a = envelope_identities(H, 2, ident_hi)
    part_b = floor_orbit(H, N, T, 21, 20)          # y0 = 21/20
    part_c = inequality_sampling(args.quick)

    ok = (part_a["failure_count"] == 0
          and part_b["barrier_engaged"]
          and part_b["linear_barrier_violations"] == 0
          and part_b["increment_bound_violations"] == 0
          and part_b["X_T_le_M_times_T"]
          and part_c["ineq_15_holds"]
          and part_c["ineq_16_constant_one_quarter_holds"]
          and part_c["ineq_16_sharp_constant_holds"])

    report = {
        "check": "erdos243_integer_rounding_barrier",
        "status": "pass" if ok else "fail",
        "evidence_class": "exact_computation",
        "mode": "quick" if args.quick else "full",
        "envelope_identities": part_a,
        "floor_orbit_linear_barrier": part_b,
        "inequalities": part_c,
        "scope": "Finite exact replay of r01 Theorem 2's barrier half and of "
                 "inequalities (15)/(16) on a rational grid.  The divergence "
                 "half of Theorem 2 is an ordinary proof recorded in "
                 "EightReturnRigidityCriteria.md section 1; the onset index of "
                 "the barrier is exp^(m+1)(2 C_N/F_N), so the theorem is "
                 "qualitative and no finite run witnesses it on a small orbit. "
                 "Nothing here settles Erdos #243.",
    }
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(json.dumps({
            "check": report["check"],
            "status": report["status"],
            "evidence_class": report["evidence_class"],
            "mode": report["mode"],
            "envelope_identities_checked": part_a["identities_checked"],
            "envelope_identity_failures": part_a["failure_count"],
            "barrier_index": part_b["barrier"]["index"] if part_b["barrier"] else None,
            "barrier_M": part_b["barrier"]["M"] if part_b["barrier"] else None,
            "X_T_over_T": part_b["X_T_over_T"],
            "linear_barrier_violations": part_b["linear_barrier_violations"],
            "increment_bound_violations": part_b["increment_bound_violations"],
            "max_increment_after_barrier": part_b["max_increment_after_barrier"],
            "ineq_15_min_slack": part_c["ineq_15_min_slack"],
            "ineq_16_sharp_min_slack": part_c["ineq_16_sharp_constant_min_slack"],
            "ineq_16_quarter_min_slack": part_c["ineq_16_constant_one_quarter_min_slack"],
        }, sort_keys=True))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
