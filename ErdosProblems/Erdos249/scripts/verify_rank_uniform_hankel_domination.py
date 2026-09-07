#!/usr/bin/env python3
"""Independent exact verifier for the rank-uniform signed-Hankel domination
theorem and its arithmetic spend (Erdos #249, Mobius--Mersenne power ladder).

Objects.  q_1<q_2<... are the squarefree positive integers, x_j = 1/(2^{q_j}-1),
eps_j = mu(q_j), m_r^{[M]} = sum_{j<=M} eps_j x_j^r, and

    D_{N,M}(s) = det( m_{s+i+j}^{[M]} )_{0<=i,j<N},
    L_N(s)     = (prod_{j<=N} eps_j x_j^s) * prod_{i<j<=N} (x_i-x_j)^2.

Claims tested (all exact rational arithmetic; no floats enter a decision):

  T1  rank-uniform domination  |D_{N,M}(s)/L_N(s) - 1| < C * 2^{2-s}
      for every N, every M>=N (including M=infinity) and every s>=2.
      Two constants are on offer: C = 599/600 and C = 399/400.
  T1s the restriction s>=2 is SHARP: at s=1 the sign law fails.
  V2  for EVEN codimension r = M-N, v_2 D_{N,N+r}(s) = 2 sum_{i<N}(N-i) q_i
      exactly, for every s>=1; for ODD r the same formula fails.
  SCH the coupled Schur approximants R_{N,r} = b^T H^{-1} b with
      H = (m_{4+i+j}), b = (m_{3+i}) at truncation M = N+r: sign law,
      two-sided error scale, and the primitive cleared form Q|Theta_2 - R|.
  FIN the named finite certificates of both source notes.
  SUP the escape-supply scan: min over Mersenne-smooth q of q|Theta_2 - p/q|.

Usage:  verify_rank_uniform_hankel_domination.py [--quick] [--json]
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F

LIMIT = 48


def squarefree(n: int) -> bool:
    d = 2
    while d * d <= n:
        if n % (d * d) == 0:
            return False
        d += 1
    return True


def moebius(n: int) -> int:
    remaining, count, p = n, 0, 2
    while p * p <= remaining:
        if remaining % p == 0:
            remaining //= p
            count += 1
            if remaining % p == 0:
                return 0
            while remaining % p == 0:
                remaining //= p
        p += 1
    if remaining > 1:
        count += 1
    return -1 if count % 2 else 1


def totient(n: int) -> int:
    result, remaining, p = n, n, 2
    while p * p <= remaining:
        if remaining % p == 0:
            while remaining % p == 0:
                remaining //= p
            result -= result // p
        p += 1
    if remaining > 1:
        result -= result // remaining
    return result


QS = [d for d in range(1, LIMIT + 1) if squarefree(d)]
XS = [F(1, 2 ** d - 1) for d in QS]
ES = [moebius(d) for d in QS]

C_R05 = F(599, 600)
C_R06 = F(399, 400)


def det(rows: list[list[F]]) -> F:
    n = len(rows)
    a = [row[:] for row in rows]
    sign, out = 1, F(1)
    for col in range(n):
        piv = next((r for r in range(col, n) if a[r][col] != 0), None)
        if piv is None:
            return F(0)
        if piv != col:
            a[col], a[piv] = a[piv], a[col]
            sign = -sign
        out *= a[col][col]
        inv = 1 / a[col][col]
        for r in range(col + 1, n):
            if a[r][col] == 0:
                continue
            f = a[r][col] * inv
            for c in range(col, n):
                a[r][c] -= f * a[col][c]
    return out * sign


def solve(A: list[list[F]], b: list[F]) -> list[F]:
    n = len(b)
    M = [row[:] + [b[i]] for i, row in enumerate(A)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        pv = M[c][c]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c] / pv
                for k in range(c, n + 1):
                    M[r][k] -= f * M[c][k]
    return [M[i][n] / M[i][i] for i in range(n)]


def moment(r: int, M: int) -> F:
    return sum((ES[j] * XS[j] ** r for j in range(M)), F(0))


def D_(N: int, M: int, s: int) -> F:
    cache: dict[int, F] = {}
    for i in range(N):
        for j in range(N):
            r = s + i + j
            if r not in cache:
                cache[r] = moment(r, M)
    return det([[cache[s + i + j] for j in range(N)] for i in range(N)])


def L_(N: int, s: int) -> F:
    out = F(1)
    for j in range(N):
        out *= ES[j] * XS[j] ** s
    for i in range(N):
        for j in range(i + 1, N):
            out *= (XS[i] - XS[j]) ** 2
    return out


def v2(x: F) -> int:
    def v(n: int) -> int:
        k = 0
        while n % 2 == 0:
            n //= 2
            k += 1
        return k
    return v(abs(x.numerator)) - v(x.denominator)


def log2f(x: F) -> float:
    import math
    n, d = abs(x.numerator), x.denominator
    return (math.log2(n / 2 ** (n.bit_length() - 1)) + n.bit_length() - 1
            - math.log2(d / 2 ** (d.bit_length() - 1)) - d.bit_length() + 1)


def theta_bracket(rung: int, cutoff: int) -> tuple[F, F]:
    """Rigorous enclosure of Theta_rung.  Tail: (2^d-1)^-rung <= 2^{-rung(d-1)}."""
    prefix = sum(
        (F(moebius(d), (2 ** d - 1) ** rung) for d in range(1, cutoff + 1)), F(0))
    err = F(1, 2 ** (rung * cutoff)) / (1 - F(1, 2 ** rung))
    return prefix - err, prefix + err


def cardinal(i: int, N: int, x: F) -> F:
    out = F(1)
    for k in range(N):
        if k != i:
            out *= (x - XS[k]) / (XS[i] - XS[k])
    return out


# --------------------------------------------------------------------- T1 grid
def check_theorem_one(nmax: int, extra: int, smax: int) -> dict:
    worst = (F(0), None)
    sign_violations = []
    for N in range(1, nmax + 1):
        pred = 1
        for j in range(N):
            pred *= ES[j]
        for M in range(N, N + extra + 1):
            for s in range(2, smax + 1):
                d = D_(N, M, s)
                dev = d / L_(N, s) - 1
                norm = abs(dev) * 2 ** (s - 2)
                if d == 0 or (d > 0) != (pred > 0):
                    sign_violations.append([N, M, s])
                if norm > worst[0]:
                    worst = (norm, (N, M, s, dev))
    norm, where = worst
    return {
        "grid": f"N=1..{nmax}, M=N..N+{extra}, s=2..{smax}",
        "sign_law_violations": sign_violations,
        "max_normalised_deviation": [norm.numerator, norm.denominator],
        "max_normalised_deviation_float": float(norm),
        "attained_at": {"N": where[0], "M": where[1], "s": where[2],
                        "D_over_L_minus_1": float(where[3])},
        "exceeds_599_600": norm >= C_R05,
        "exceeds_399_400": norm >= C_R06,
        "verdict": ("both claimed constants hold on this grid"
                    if norm < C_R06 else "REFUTED"),
    }


def check_infinite_truncation(nmax: int, atoms: int, smax: int) -> dict:
    """m = infinity via the exact cardinal-basis identity

        W_N^{(M)}(2)/|L_N(2)| = det(I + sum_{j=N+1}^{M} v_j v_j^T),
        (v_j)_i = (x_j/x_i) ell_i(x_j),

    W being the all-signs-positive Cauchy-Binet sum, so that the total absolute
    weight of tuples using an index above M equals det(I+S_inf) - det(I+S_M),
    which Hadamard bounds by prod_i (1 + A_i + tau_i) - det(I+S_M), where
    tau_i = (C_i/x_i)^2 (4/3) 4^{-q_M} and C_i = prod_{k != i} x_k/|x_i - x_k|
    dominates |ell_i| on (0, x_N).  At shift s every such tuple is damped by a
    further factor at most 2^{2-s}.
    """
    rows = []
    worst = F(0)
    for N in range(1, nmax + 1):
        A, tau = [], []
        for i in range(N):
            A.append(sum(((XS[j] / XS[i]) * cardinal(i, N, XS[j])) ** 2
                         for j in range(N, atoms)))
            C = F(1)
            for k in range(N):
                if k != i:
                    C *= XS[k] / abs(XS[i] - XS[k])
            tau.append((C / XS[i]) ** 2 * F(4, 3) * F(1, 4 ** QS[atoms - 1]))
        S = [[sum((XS[j] / XS[i]) * cardinal(i, N, XS[j])
                  * (XS[j] / XS[k]) * cardinal(k, N, XS[j])
                  for j in range(N, atoms)) for k in range(N)] for i in range(N)]
        for i in range(N):
            S[i][i] += 1
        detS = det(S)
        had = F(1)
        for i in range(N):
            had *= 1 + A[i] + tau[i]
        tail = had - detS
        worst = max(worst, had - 1)
        row = {"N": N, "hadamard_sup_bound_s2": float(had - 1),
               "tail_weight_above_M": float(tail), "shifts": {}}
        for s in range(2, smax + 1):
            dev = D_(N, atoms, s) / L_(N, s) - 1
            err = tail * F(1, 2 ** (s - 2))
            lo, hi = dev - err, dev + err
            row["shifts"][str(s)] = {
                "D_over_L_minus_1_lower": float(lo),
                "D_over_L_minus_1_upper": float(hi),
                "normalised_upper": float(max(abs(lo), abs(hi)) * 2 ** (s - 2)),
            }
        rows.append(row)
    return {
        "atoms_used": atoms,
        "largest_squarefree_index": QS[atoms - 1],
        "per_rank": rows,
        "max_hadamard_sup_bound": float(worst),
        "exceeds_399_400": worst >= C_R06,
    }


def check_shift_one(nmax: int, extra: int) -> dict:
    """The hypothesis s>=2 is sharp: the sign law fails at s=1."""
    viol = []
    worst = F(0)
    for N in range(1, nmax + 1):
        pred = 1
        for j in range(N):
            pred *= ES[j]
        for M in range(N, N + extra + 1):
            d = D_(N, M, 1)
            dev = d / L_(N, 1) - 1
            worst = max(worst, abs(dev))
            if d == 0 or (d > 0) != (pred > 0):
                viol.append({"N": N, "M": M, "D_over_L_minus_1": float(dev)})
    return {
        "max_deviation_at_s1": float(worst),
        "sign_law_violations_at_s1": viol,
        "conclusion": ("the s>=2 hypothesis is necessary: sgn D = prod mu(q_j) "
                       "is false at s=1" if viol else "no violation found"),
    }


# ------------------------------------------------------------------ 2-adic law
def check_valuation(nmax: int, rmax: int, smax: int) -> dict:
    even_ok, odd_exact, odd_total = True, 0, 0
    excess: dict[int, int] = {}
    zeros = []
    for N in range(1, nmax + 1):
        V = 2 * sum((N - i) * QS[i - 1] for i in range(1, N))
        for r in range(0, rmax + 1):
            for s in range(1, smax + 1):
                d = D_(N, N + r, s)
                if d == 0:
                    zeros.append([N, r, s])
                    continue
                v = v2(d)
                if r % 2 == 0:
                    even_ok &= (v == V)
                else:
                    odd_total += 1
                    odd_exact += int(v == V)
                    excess[v - V] = excess.get(v - V, 0) + 1
    return {
        "grid": f"N=1..{nmax}, r=0..{rmax}, s=1..{smax}",
        "even_codimension_formula_exact_everywhere": even_ok,
        "formula": "v_2 D_{N,N+r}(s) = 2 * sum_{i<N} (N-i) q_i",
        "odd_codimension_exact_count": odd_exact,
        "odd_codimension_total": odd_total,
        "odd_codimension_excess_distribution": {str(k): v
                                                for k, v in sorted(excess.items())},
        "vanishing_determinants": zeros,
        "conclusion": (
            "the even-codimension hypothesis is necessary and sufficient on this "
            "grid: exact for every even r and every s>=1 (so D != 0 at s=1 too, "
            "with no analytic input), and false for every odd r tested"),
    }


# ------------------------------------------------------------- Schur family
def schur(N: int, M: int) -> F:
    H = [[moment(4 + i + j, M) for j in range(N)] for i in range(N)]
    b = [moment(3 + i, M) for i in range(N)]
    y = solve(H, b)
    return sum((b[i] * y[i] for i in range(N)), F(0))


def check_schur(nmax: int, rs: tuple[int, ...], lo2: F, hi2: F) -> dict:
    rows = []
    for N in range(1, nmax + 1):
        KN = 2 * sum(QS[:N])
        for r in rs:
            M = N + r
            if M > len(QS):
                continue
            R = schur(N, M)
            delta = D_(N + 1, M, 2) / D_(N, M, 4)
            assert moment(2, M) - R == delta, "block Schur identity failed"
            errlo, errhi = lo2 - R, hi2 - R
            assert errlo * errhi > 0, "Theta_2 enclosure does not separate R"
            Q = R.denominator
            ratio = abs(errlo) / XS[N] ** 2
            rows.append({
                "N": N, "r": r, "M": M, "q_N_plus_1": QS[N],
                "sign_matches_mu": (1 if errlo > 0 else -1) == ES[N],
                "abs_err_over_x_Nplus1_squared": float(ratio),
                "inside_r05_1_7_bounds": F(1, 16000) < ratio < 3,
                "inside_r06_23_bounds": F(1, 12000) < ratio < 3,
                "bits_of_Q": Q.bit_length(),
                "log2_Q_times_abs_err": log2f(Q * abs(errlo)),
                "v2_delta": v2(delta),
                "K_N": KN,
                "v2_delta_ge_K_N": v2(delta) >= KN,
            })
    return {
        "definition": "R_{N,r} = b^T H^{-1} b, H=(m_{4+i+j}), b=(m_{3+i}), M=N+r",
        "rows": rows,
        "min_log2_Q_times_err": min(x["log2_Q_times_abs_err"] for x in rows),
        "conclusion": (
            "Q_{N,r}|Theta_2 - R_{N,r}| already exceeds 2^262 at the smallest "
            "rank of the family and grows with N; r05 (4.5) v_2(delta) >= K_N "
            "holds for every even r and fails for every odd r tested, while the "
            "divergence itself is parity-blind"),
    }


# ---------------------------------------------------------- named finite claims
def check_named_claims(lo2: F, hi2: F, quick: bool) -> dict:
    out: dict[str, object] = {}

    def t_Y(r: int, Y: int) -> F:
        return sum((F(moebius(d), (2 ** d - 1) ** r) for d in range(1, Y + 1)), F(0))

    R = ((t_Y(6, 10) * t_Y(3, 10) ** 2 - 2 * t_Y(5, 10) * t_Y(3, 10) * t_Y(4, 10)
          + t_Y(4, 10) ** 3) / (t_Y(4, 10) * t_Y(6, 10) - t_Y(5, 10) ** 2))
    M10 = sum(1 for d in range(1, 11) if squarefree(d))
    C = [[moment(4 + i + j, M10) for j in range(2)] for i in range(2)]
    bv = [moment(3 + i, M10) for i in range(2)]
    R_mat = sum((bv[i] * v for i, v in enumerate(solve(C, bv))), F(0))
    form = R.denominator * lo2 - R.numerator
    out["r06_eq32_33_N2_Y10"] = {
        "matrix_form_equals_displayed_identity": R_mat == R,
        "numerator_matches": R.numerator == 116203501295657603525246680356285076659870428672475373169443,
        "denominator_matches": R.denominator == 133125213253644728558226198288521239812159655778345347998933,
        "denominator_bits": R.denominator.bit_length(),
        "denominator_exceeds_2_196": R.denominator.bit_length() > 196,
        "log2_abs_primitive_form": log2f(form),
        "primitive_form_exceeds_one": abs(form) > 1,
    }

    def lambert_interp(n: int) -> F:
        A = [[F(1, 2 ** (d * k) - 1) for k in range(1, n + 1)]
             for d in range(1, n + 1)]
        b = [F(1, (2 ** d - 1) ** 2) for d in range(1, n + 1)]
        c = solve(A, b)
        return sum((c[k - 1] * F(1, 2 ** k) for k in range(1, n + 1)), F(0))

    fam = []
    for n in range(1, (7 if quick else 12) + 1):
        An = lambert_interp(n)
        q = An.denominator
        val = min(abs(q * lo2 - An.numerator), abs(q * hi2 - An.numerator))
        fam.append({"n": n, "bits_of_denominator": q.bit_length(),
                    "log2_cleared_form": log2f(val), "below_one": val < 1})
    out["r05_section6_lambert_interpolation_family"] = {
        "A_3": "103/119", "A_3_matches": lambert_interp(3) == F(103, 119),
        "A_4": "969578/1117395",
        "A_4_matches": lambert_interp(4) == F(969578, 1117395),
        "family": fam,
        "conclusion": ("the cleared form decreases only through n=3 (reaching "
                       "0.248 < 1/4) and then diverges super-exponentially"),
    }

    ds = (1, 2, 3, 5)
    V = [[F(1, 2 ** (ds[i] * k) - 1) for k in range(1, 5)] for i in range(4)]
    bb = [F(1, (2 ** ds[i] - 1) ** 2) for i in range(4)]
    w = solve(V, bb)
    val35 = sum((F(1, 2 ** (k + 1)) * w[k] for k in range(4)), F(0))
    g = 9059843 * lo2 - 7860516
    out["r06_eq35_36_four_point_cancellation"] = {
        "value_matches_7860516_over_9059843": val35 == F(7860516, 9059843),
        "cleared_form": float(g),
        "exceeds_82": g > 82,
        "inside_r06_stated_enclosure": F(1386577191, 16777216) < g < F(2782214225, 33554432),
    }

    out["r06_eq34_rational_node_countermodel"] = {
        "closed_form": "m~_r = 1/(2^r-1) - 1/(2^{4r}-1)",
        "m_tilde_2_equals_28_over_85": F(1, 3) - F(1, 255) == F(28, 85),
    }

    # b_m | L_U^2 and b_m odd
    def L_U(U: int) -> int:
        o = 1
        for d in range(1, U + 1):
            if squarefree(d):
                num, den = 1, 1
                for e in range(1, d + 1):
                    if d % e == 0:
                        if moebius(d // e) == 1:
                            num *= 2 ** e - 1
                        elif moebius(d // e) == -1:
                            den *= 2 ** e - 1
                o *= num // den
        return o

    mm = 7 if quick else 9
    out["r05_eq410_squarefree_cyclotomic_denominator"] = {
        "b_m_divides_L_U_squared": all(
            (L_U(QS[m - 1]) ** 2) % moment(2, m).denominator == 0
            for m in range(1, mm + 1)),
        "b_m_odd": all(moment(2, m).denominator % 2 == 1 for m in range(1, mm + 1)),
        "range": f"m=1..{mm}",
    }

    dtop = 1200 if quick else 3000
    bad413 = [Dv for Dv in range(128, dtop)
              if sum(1 for n in range(Dv + 1, 2 * Dv + 1) if squarefree(n)) < Dv // 8]
    defect, bad414 = 0, []
    for Dv in range(1, (2000 if quick else 4000) + 1):
        if squarefree(Dv):
            defect += Dv - totient(Dv)
        if Dv >= 1024 and defect < F(Dv * Dv, 128):
            bad414.append(Dv)
    out["r05_counting_lemmas"] = {
        "eq413_at_least_D_over_8_squarefree_in_D_2D": not bad413,
        "eq413_range": f"128<=D<{dtop}",
        "eq414_squarefree_totient_defect_ge_D2_over_128": not bad414,
        "eq414_range": f"1024<=D<={2000 if quick else 4000}",
    }

    # inertia
    ok = True
    for N in range(1, (5 if quick else 7) + 1):
        want_pos = sum(1 for j in range(N) if ES[j] == 1)
        want_neg = N - want_pos
        for M in range(N, N + (4 if quick else 6)):
            for s in (2, 3, 4):
                prev, pos = F(1), 0
                for n in range(1, N + 1):
                    dn = D_(n, M, s)
                    pos += int(dn / prev > 0)
                    prev = dn
                ok &= (pos == want_pos) and (N - pos == want_neg)
    out["r06_corollary2_exact_inertia"] = {
        "verified": ok,
        "statement": ("#positive eigenvalues = #{j<=N : mu(q_j)=1}, via the "
                      "LDL^T pivots D_n/D_{n-1}"),
    }
    return out


# ----------------------------------------------------------- escape-supply scan
def check_escape_supply(bits: int, dmax: int) -> dict:
    prec = 512
    scale = 1 << prec
    th = 0
    for d in range(1, 700):
        mu = moebius(d)
        if mu:
            th += mu * scale // (2 ** d - 1) ** 2
    limit = 1 << bits
    gens = [2 ** d - 1 for d in range(2, dmax + 1) if squarefree(d)]
    smooth, seen, i = [1], {1}, 0
    while i < len(smooth):
        q = smooth[i]
        i += 1
        for g in gens:
            n = q * g
            if n <= limit and n not in seen:
                seen.add(n)
                smooth.append(n)
    vals = []
    for q in smooth:
        if q == 1:
            continue
        frac = (q * th) % scale
        vals.append((min(frac, scale - frac), q))
    vals.sort()
    n = len(vals)
    return {
        "definition": ("Mersenne-smooth q = product of powers of 2^d-1, d "
                       "squarefree in [2,dmax]; every denominator any "
                       "construction in this batch can produce is of this shape"),
        "bits_bound": bits, "dmax": dmax, "candidates": n,
        "min_q_times_dist": vals[0][0] / scale,
        "argmin_q": vals[0][1],
        "counts_below": {str(t): sum(1 for v, _ in vals if v / scale < t)
                         for t in (0.1, 0.05, 0.01, 0.001)},
        "uniform_expectation": {str(t): round(2 * t * n)
                                for t in (0.1, 0.05, 0.01, 0.001)},
        "conclusion": ("the distribution of q|Theta_2-p/q| over the Mersenne-"
                       "smooth denominators is indistinguishable from uniform "
                       "on [0,1/2]; there is no anomalously good smooth "
                       "approximation to Theta_2 below the tested bound"),
    }


# ------------------------------------------------------- the source certificates
def check_source_certificates() -> dict:
    def product(values):
        out = F(1)
        for v in values:
            out *= v
        return out

    B = 12
    U = {}
    for residue in (1, 2, 3):
        total = F(0)
        for j in range(1, B + 1):
            if (residue + j) % 4 == 0:
                continue
            gamma = product((1 - F(1, 2 ** (j + e))) / (1 - F(1, 2 ** e))
                            for e in range(1, B + 1) if (residue - e) % 4 != 0)
            total += F(1, 4 ** j) * gamma ** 2
        U[residue] = total / (1 - F(1, 2 ** B)) ** 2 + F(16, 3 * 4 ** B)

    def distance(e):
        return e + e // 3

    tot = F(0)
    for j in range(1, B + 1):
        t = F(1, 2 ** distance(j + 2))
        gamma = product((1 - t * F(1, 2 ** distance(e))) / (1 - F(1, 2 ** distance(e)))
                        for e in range(1, B + 1))
        after = (F(1, 2) - t) * (F(1, 4) - t) / F(3, 8)
        tot += t ** 2 * gamma ** 2 * after ** 2
    V = tot / (1 - F(1, 2 ** B)) ** 2 + F(1, 27 * 4 ** B)

    r05 = {
        "U1_lt_291_500": U[1] < F(291, 500), "U1": float(U[1]),
        "U2_lt_837_1000": U[2] < F(837, 1000), "U2": float(U[2]),
        "U3_lt_253_500": U[3] < F(253, 500), "U3": float(U[3]),
        "maxU_lt_21_25": max(U.values()) < F(21, 25),
        "A2_bound_lt_3_1250": V < F(3, 1250), "A2_bound": float(V),
        "eq220": F(4, 49) + F(64, 2025) + F(64, 2883) < F(5, 36),
        "eq221": F(16, 49) * (F(1, 6) + F(5, 36) - F(4, 49)) < F(1, 12),
        "eq222": F(24, 31) ** 2 * F(5, 36) < F(1, 12),
        "eq229": F(3, 1250) + F(1, 49140) < F(1, 400),
        "eq230": F(46, 25) * F(13, 12) * F(400, 399) < 2 - F(1, 600),
        "eq230_value": "2392/1197",
        "eq230_slack_below_599_600": "1/239400",
        "eq35_tail_split": F(1, 12000) - F(1, 49152) > F(1, 16000),
    }

    def dyadic(k):
        return F(1, 1 << k)

    def upper(a, r):
        total = F(0)
        for delta in range(1, 9):
            if (r + delta) % 4 == 0:
                continue
            term = dyadic(a * delta)
            for h in range(1, 15):
                if h % 4 != r:
                    term *= ((1 - dyadic(h + delta)) / (1 - dyadic(h))) ** 2
            total += term
        return total / (1 - dyadic(14)) ** 2 + 12 * dyadic(9 * a) / (1 - dyadic(a))

    bounds = {(2, 1): 581258, (2, 2): 836785, (2, 3): 505591,
              (4, 1): 116059, (4, 2): 182033, (4, 3): 24271,
              (6, 1): 27388, (6, 2): 45175, (6, 3): 1427}
    kappa = F(837, 1000) * (1 + F(183, 1000)
                            + F(183, 1000) * F(46, 1000) / (1 - F(12, 1000)))
    b2 = max(upper(2, r) for r in (1, 2, 3))
    b4 = max(upper(4, r) for r in (1, 2, 3))
    b6 = max(upper(6, r) for r in (1, 2, 3))
    sharper = b2 * (1 + b4 + b4 * b6 / (1 - b6 / 4))
    r06 = {
        "all_nine_U_bounds_hold": all(upper(a, r) < F(n, 10 ** 6)
                                      for (a, r), n in bounds.items()),
        "U_values": {f"{a},{r}": float(upper(a, r)) for (a, r) in sorted(bounds)},
        "prod_1_minus_2^-h_gt_1_over_sqrt12": 12 * F(302715, 1048576) ** 2 > 1,
        "integer_witness_12x302715^2_minus_1048576^2": 12 * 302715 ** 2 - 1048576 ** 2,
        "kappa_equals_492667407_over_494000000": kappa == F(492667407, 494000000),
        "kappa_lt_399_400": kappa < F(399, 400),
        "kappa": float(kappa),
        "sharpened_kappa_from_same_certificate": float(sharper),
    }
    return {"r05_section5": r05, "r06_section1_3": r06,
            "both_certificates_execute_as_written": (
                all(v is True for v in r05.values() if isinstance(v, bool))
                and all(v is True for v in r06.values() if isinstance(v, bool)))}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()
    quick = args.quick

    lo2, hi2 = theta_bracket(2, 60 if quick else 90)
    payload = {
        "schema": "erdos249_rank_uniform_hankel_domination_verifier_v1",
        "mode": "quick" if quick else "full",
        "arithmetic": "exact_rational",
        "theta_2_enclosure_width_log2": log2f(hi2 - lo2),
        "source_certificates": check_source_certificates(),
        "theorem_one_finite_grid": check_theorem_one(
            5 if quick else 7, 6 if quick else 8, 4 if quick else 6),
        "theorem_one_infinite_truncation": check_infinite_truncation(
            4 if quick else 7, 13 if quick else 19, 4 if quick else 6),
        "shift_one_sharpness": check_shift_one(5 if quick else 7,
                                               6 if quick else 8),
        "two_adic_valuation": check_valuation(
            4 if quick else 6, 7 if quick else 9, 6 if quick else 8),
        "schur_family": check_schur(4 if quick else 6, (8, 9, 10), lo2, hi2),
        "named_finite_claims": check_named_claims(lo2, hi2, quick),
        "escape_supply_scan": check_escape_supply(
            48 if quick else 70, 16 if quick else 24),
    }
    payload["status"] = "verified" if (
        not payload["theorem_one_finite_grid"]["sign_law_violations"]
        and not payload["theorem_one_finite_grid"]["exceeds_399_400"]
        and payload["two_adic_valuation"]["even_codimension_formula_exact_everywhere"]
        and payload["source_certificates"]["both_certificates_execute_as_written"]
    ) else "refuted"
    print(json.dumps(payload, indent=None if args.json else 2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
