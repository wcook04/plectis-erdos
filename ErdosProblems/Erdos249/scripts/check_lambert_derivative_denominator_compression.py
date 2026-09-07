#!/usr/bin/env python3
"""Exact lattice probe: can derivative (double-pole) Lambert identities compress the
reduced denominator of a rational approximant to S = sum_{n>=1} phi(n)/2^n?

Objects (all exact, fractions.Fraction / int; no external deps).

  A_k(y)   = sum_{m>=1} m^k y^m = Num_k(y)/(1-y)^{k+1}   (Eulerian numerator)
  Lambert  : sum_{d>=1} mu(d) x^d/(1-x^d) = x
  theta^k  : sum_{d>=1} mu(d) d^k A_k(x^d) = x           for every k >= 0
  at x=2^-j: sum_{d>=1} mu(d) d^k A_k(2^{-jd}) = 2^-j    for every j >= 1, k >= 0
  target   : S = sum_{d>=1} mu(d) A_1(2^-d) = sum_d mu(d) 2^d/(2^d-1)^2 = 1/2 + Theta_2
  prefix   : T_N   = sum_{d<=N} mu(d) A_1(2^-d)
  defect   : I_{j,k,N} = 2^-j - sum_{d<=N} mu(d) d^k A_k(2^{-jd})   ( = the omitted tail)

Approximant family (contains r07's signed-Lambert family as the k=0 slice):

  R = T_N + (1/D) * sum_{j<=J, k<=K} a_{j,k} I_{j,k,N},   D >= 1, a integers.

r07 sec.4 proves that for k=0 only, every squarefree layer m (with primitive prime
ell > N of Phi_m(2), e = v_ell(2^m-1)) keeps its DOUBLE pole: v_ell(T_N) = -2e while
v_ell(I_{j,0,N}) >= -e.  The k=1 identities have pole order exactly 2e, so they CAN
cancel it.  This probe computes the exact leading Laurent coefficient, verifies it
against exact reduced denominators, and measures what the cancellation costs.

Derived leading coefficient at layer m (verified below against exact denominators):
  M_m^2 * ( D*T_N + sum_j a_{j,1} I_{j,1,N} )
      = mu(m) * ( D*sigma2(m) - sum_j a_{j,1}*tau(j,m) )   (mod ell)
  sigma2(m) = sum_{a<=floor(N/m), (a,m)=1} mu(a)/a^2
  tau(j,m)  = -(m'/j'^2) * sum_{a<=floor(N/m')} mu(a*m')/a,  m'=m/gcd(j,m), j'=j/gcd(j,m)

Run:  ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/\
scripts/check_lambert_derivative_denominator_compression.py --quick
"""
from __future__ import annotations

import argparse
import json
import math
import random
import sys
from fractions import Fraction as F


# ---------------------------------------------------------------- sieves ----
def mobius(n: int) -> list[int]:
    mu = [1] * (n + 1)
    primes: list[int] = []
    comp = [False] * (n + 1)
    for i in range(2, n + 1):
        if not comp[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            if i * p > n:
                break
            comp[i * p] = True
            if i % p == 0:
                mu[i * p] = 0
                break
            mu[i * p] = -mu[i]
    mu[0] = 0
    return mu


def totient(n: int) -> list[int]:
    ph = list(range(n + 1))
    for i in range(2, n + 1):
        if ph[i] == i:
            for j in range(i, n + 1, i):
                ph[j] -= ph[j] // i
    return ph


# ----------------------------------------------- Eulerian numerators A_k ----
def eulerian_numerators(K: int) -> list[list[int]]:
    """Num_k with A_k(y) = Num_k(y)/(1-y)^{k+1}; Num_0 = y."""
    nums = [[0, 1]]
    for k in range(K):
        cur = nums[-1]
        der = [i * cur[i] for i in range(1, len(cur))]
        acc = [0] * (len(der) + 1)
        for i, c in enumerate(der):
            acc[i] += c
            acc[i + 1] -= c
        out = [0] * max(len(acc), len(cur))
        for i, c in enumerate(acc):
            out[i] += c
        for i, c in enumerate(cur):
            out[i] += (k + 1) * c
        nums.append([0] + out)
    return nums


def A_at_two_pow(k: int, q: int, nums: list[list[int]]) -> F:
    y = F(1, 1 << q)
    num = F(0)
    for i, c in enumerate(nums[k]):
        if c:
            num += c * y ** i
    return num / (1 - y) ** (k + 1)


# ------------------------------------------------------- enclosure of S -----
def s_enclosure(bits: int) -> tuple[F, F]:
    ph = totient(bits)
    pref = 0
    for n in range(1, bits + 1):
        pref = 2 * pref + ph[n]
    lo = F(pref, 1 << bits)
    return lo, lo + F(bits + 2, 1 << bits)      # 0 < R_bits <= bits + 2


# ------------------------------------------------------------ factoring ----
def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def _rho(n: int, rng: random.Random) -> int:
    if n % 2 == 0:
        return 2
    while True:
        x = rng.randrange(2, n)
        y = x
        c = rng.randrange(1, n)
        d = 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = math.gcd(abs(x - y), n)
        if d != n:
            return d


def factor(n: int, rng: random.Random, acc: dict[int, int] | None = None) -> dict[int, int]:
    if acc is None:
        acc = {}
    if n == 1:
        return acc
    if is_prime(n):
        acc[n] = acc.get(n, 0) + 1
        return acc
    d = _rho(n, rng)
    factor(d, rng, acc)
    factor(n // d, rng, acc)
    return acc


def primitive_part_above(m: int, bound: int, rng: random.Random) -> int:
    """Product of ell^v with ell > bound prime, ell^v || 2^m-1, ord_ell(2) == m."""
    out = 1
    for ell, e in factor((1 << m) - 1, rng).items():
        if ell <= bound:
            continue
        o = ell - 1
        for p in factor(o, rng):
            while o % p == 0 and pow(2, o // p, ell) == 1:
                o //= p
        if o == m:
            out *= ell ** e
    return out


def flog2(x: F) -> float:
    """Exact-ish log2 of a positive Fraction of arbitrary size."""
    n, d = abs(x.numerator), x.denominator
    if n == 0:
        return float("-inf")
    sh = n.bit_length() - d.bit_length()
    if sh >= 0:
        d <<= sh
    else:
        n <<= -sh
    return sh + math.log2(((n << 53) // d) / float(1 << 53))


def v_pow(n: int, base: int) -> int:
    t = 0
    while base > 1 and n % base == 0:
        n //= base
        t += 1
    return t


# ---------------------------------------------------------- the objects ----
def build_objects(N: int, J: int, K: int, mu: list[int], nums: list[list[int]]):
    T = F(0)
    for d in range(1, N + 1):
        if mu[d]:
            T += mu[d] * A_at_two_pow(1, d, nums)
    idf: dict[tuple[int, int], F] = {}
    for j in range(1, J + 1):
        for k in range(K + 1):
            s = F(0)
            for d in range(1, N + 1):
                if mu[d]:
                    s += mu[d] * (d ** k) * A_at_two_pow(k, j * d, nums)
            idf[(j, k)] = F(1, 1 << j) - s
    return T, idf


def layer_forms(N: int, J: int, mu: list[int]):
    """(m, floor(N/m), sigma2, [tau(j,m)]) for squarefree m <= N with sigma2 != 0."""
    rows = []
    for m in range(1, N + 1):
        if mu[m] == 0:
            continue
        k = N // m
        s2 = F(0)
        for a in range(1, k + 1):
            if mu[a] and math.gcd(a, m) == 1:
                s2 += F(mu[a], a * a)
        s2 *= mu[m]
        if s2 == 0:
            continue
        tau = []
        for j in range(1, J + 1):
            g = math.gcd(j, m)
            mp, jp = m // g, j // g
            acc = F(0)
            for a in range(1, N // mp + 1):
                if mu[a * mp]:
                    acc += F(mu[a * mp], a)
            tau.append(-F(mp, jp * jp) * acc)
        rows.append((m, k, s2, tau))
    return rows


def nullspace(rows: list[list[F]], ncols: int) -> list[list[F]]:
    A = [r[:] for r in rows]
    pivots: list[int] = []
    r = 0
    for c in range(ncols):
        pr = None
        for rr in range(r, len(A)):
            if A[rr][c] != 0:
                pr = rr
                break
        if pr is None:
            continue
        A[r], A[pr] = A[pr], A[r]
        inv = A[r][c]
        A[r] = [x / inv for x in A[r]]
        for rr in range(len(A)):
            if rr != r and A[rr][c] != 0:
                f = A[rr][c]
                A[rr] = [A[rr][i] - f * A[r][i] for i in range(ncols)]
        pivots.append(c)
        r += 1
        if r == len(A):
            break
    basis = []
    for fc in [c for c in range(ncols) if c not in pivots]:
        v = [F(0)] * ncols
        v[fc] = F(1)
        for i, pc in enumerate(pivots):
            v[pc] = -A[i][fc]
        basis.append(v)
    return basis


def clear_denoms(vec: list[F]) -> list[int]:
    L = 1
    for x in vec:
        L = L * x.denominator // math.gcd(L, x.denominator)
    ints = [int(x * L) for x in vec]
    g = 0
    for x in ints:
        g = math.gcd(g, abs(x))
    return [x // g for x in ints] if g > 1 else ints


# ------------------------------------------------------------- the probe ----
def run(quick: bool) -> dict:
    K = 3
    J = 4
    rng = random.Random(20260905)
    nums = eulerian_numerators(K)
    mu = mobius(600)
    bits = 2500 if quick else 4000
    s_lo, s_hi = s_enclosure(bits)
    report: dict = {"mode": "quick" if quick else "full", "s_enclosure_bits": bits}

    # 1. exact identity check (truncated defect must sit under the rigorous tail bound)
    dmax = 160 if quick else 240
    ident = []
    for j in range(1, J + 1):
        for k in range(K + 1):
            s = F(0)
            for d in range(1, dmax + 1):
                if mu[d]:
                    s += mu[d] * (d ** k) * A_at_two_pow(k, j * d, nums)
            err = abs(s - F(1, 1 << j))
            bound = F(0)
            for d in range(dmax + 1, dmax + 300):
                bound += F((d ** k) * math.factorial(k) * (1 << (k + 1)), 1 << (j * d))
            ident.append({"j": j, "k": k, "defect_under_tail_bound": bool(err <= bound)})
    report["identity_check"] = {
        "all_pass": all(r["defect_under_tail_bound"] for r in ident),
        "rows": ident,
    }

    # 2. r07 (53)/(54): the derivative rung and its exact 3/2 cancellation at N=2
    u_full = sum(F(mu[d] * d * (1 << d), ((1 << d) - 1) ** 2) for d in range(1, 200) if mu[d])
    t2 = sum(F(mu[d], ((1 << d) - 1) ** 2) for d in range(1, 3))
    u2 = sum(F(mu[d] * d * (1 << d), ((1 << d) - 1) ** 2) for d in range(1, 3))
    report["r07_derivative_rung"] = {
        "identity_53_holds_to_2^-190": bool(abs(u_full - F(1, 2)) < F(1, 1 << 190)),
        "T2": str(t2), "U2": str(u2),
        "T2_minus_half_minus_U2": str(t2 - (F(1, 2) - u2)),
        "equals_three_halves": bool(t2 - (F(1, 2) - u2) == F(3, 2)),
    }

    # 3. main scan
    ns = [10, 14, 18, 22, 26, 30] if quick else [10, 14, 18, 22, 26, 30, 34, 38]
    scan = []
    for N in ns:
        T, idf = build_objects(N, J, 1, mu, nums)
        den_t = T.denominator
        prim = {}
        for m in range(1, N + 1):
            if mu[m]:
                p = primitive_part_above(m, N, rng)
                if p > 1:
                    prim[m] = p
        base_v = {m: v_pow(den_t, prim[m]) for m in prim}
        lay = {r[0]: r for r in layer_forms(N, J, mu)}

        def q_err(R: F):
            q = R.denominator
            lo, hi = s_lo - R, s_hi - R
            if lo <= 0 <= hi:
                return q, None
            return q, min(abs(F(q) * lo), abs(F(q) * hi))

        _, base_qe = q_err(T)
        # 3a. single-layer targeted cancellation, D/a = rho_m = -tau(1,m)/sigma2(m)
        singles = []
        for m in sorted(prim):
            if m not in lay:
                continue
            rho = -lay[m][3][0] / lay[m][2]
            if rho == 0:
                continue
            D, a = rho.numerator, rho.denominator
            if D < 0:
                D, a = -D, -a
            R = T + F(a, D) * idf[(1, 1)]
            q, qe = q_err(R)
            got = {mm: v_pow(q, prim[mm]) for mm in prim}
            singles.append({
                "m": m, "rho": str(rho), "D": D, "a": a,
                "log2_primitive_part": prim[m].bit_length() - 1,
                "v_before": base_v[m], "v_after": got[m],
                "double_pole_removed": got[m] < base_v[m],
                "killed_layers": [mm for mm in prim if got[mm] < base_v[mm]],
                "log2_q": q.bit_length() - 1,
                "log2_q_times_err": (None if qe is None else flog2(qe)),
            })
        # 3b. greedy multi-layer cancellation at width J (largest layers first)
        greedy = []
        for width in range(1, J + 1):
            Tw, idw = build_objects(N, width, 1, mu, nums)
            layw = {r[0]: r for r in layer_forms(N, width, mu)}
            order = sorted([m for m in prim if m in layw],
                           key=lambda m: -prim[m].bit_length())
            chosen: list[int] = []
            sol = None
            for m in order:
                trial = chosen + [m]
                rowset = [[layw[x][2]] + list(layw[x][3]) for x in trial]
                cand = None
                for v in nullspace(rowset, width + 1):
                    if v[0] != 0:
                        cand = v
                        break
                if cand is not None:
                    chosen, sol = trial, cand
            if sol is None:
                greedy.append({"width": width, "cancelled": [], "note": "no D!=0 solution"})
                continue
            iv = clear_denoms(sol)
            D, coef = iv[0], iv[1:]
            if D < 0:
                D, coef = -D, [-x for x in coef]
            R = Tw + sum(F(coef[j - 1], D) * idw[(j, 1)] for j in range(1, width + 1))
            q, qe = q_err(R)
            got = {mm: v_pow(q, prim[mm]) for mm in prim}
            killed = [mm for mm in prim if got[mm] < base_v[mm]]
            greedy.append({
                "width": width, "targets": chosen, "D": D, "a": coef,
                "log2_height": math.log2(max([abs(D)] + [abs(x) for x in coef])),
                "killed_layers": killed,
                "log2_killed_mass": sum(prim[m].bit_length() - 1 for m in killed),
                "log2_q": q.bit_length() - 1,
                "log2_q_times_err": (None if qe is None else flog2(qe)),
            })
        # 3c. do k>=2 identities help?  they carry pole order (k+1)e > 2e
        deeper = []
        for k in (2, 3):
            Tk, idk = build_objects(N, 2, k, mu, nums)
            R = Tk + idk[(1, k)]
            q, qe = q_err(R)
            deeper.append({
                "k": k, "log2_q": q.bit_length() - 1, "log2_q_base": den_t.bit_length() - 1,
                "denominator_grew": q.bit_length() - 1 > den_t.bit_length() - 1,
                "log2_q_times_err": (None if qe is None else flog2(qe)),
            })
        # 3d. small exhaustive box over (D, a_{1,0}, a_{1,1})
        best = (float("inf"), None)  # (log2 of q*|S-R|, coeffs)
        for D in range(1, 7):
            for a0 in range(-6, 7):
                for a1 in range(-6, 7):
                    R = T + (a0 * idf[(1, 0)] + a1 * idf[(1, 1)]) / D
                    q, qe = q_err(R)
                    if qe is None:
                        continue
                    val = flog2(qe)
                    if val < best[0]:
                        best = (val, (D, a0, a1))
        scan.append({
            "N": N,
            "log2_den_T_N": den_t.bit_length() - 1,
            "log2_base_q_times_err": flog2(base_qe),
            "layer_double_pole_profile": {str(m): base_v[m] for m in sorted(base_v)},
            "single_layer_cancellations": singles,
            "greedy_multilayer": greedy,
            "deeper_k_identities": deeper,
            "box_search_best_log2_q_times_err": best[0],
            "box_search_best_coeffs": best[1],
            "box_search_dropped_below_one": best[0] < 0.0,
        })
    report["scan"] = scan
    report["verdict"] = {
        "q_times_err_ever_below_one": any(r["box_search_dropped_below_one"] for r in scan),
        "min_log2_q_times_err_by_N": {
            str(r["N"]): min(
                [r["box_search_best_log2_q_times_err"]]
                + [s["log2_q_times_err"] for s in r["single_layer_cancellations"]
                   if s["log2_q_times_err"] is not None]
                + [g["log2_q_times_err"] for g in r["greedy_multilayer"]
                   if g.get("log2_q_times_err") is not None]
            ) for r in scan
        },
        "max_layers_cancelled_at_any_width": {
            str(r["N"]): max(len(g.get("killed_layers", [])) for g in r["greedy_multilayer"])
            for r in scan
        },
    }
    return report


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--out")
    args = ap.parse_args()
    rep = run(args.quick)
    if args.out:
        with open(args.out, "w") as fh:
            json.dump(rep, fh, indent=1)
    if args.json:
        print(json.dumps(rep, indent=1))
    else:
        print(json.dumps(rep["identity_check"]["all_pass"] and rep["r07_derivative_rung"], indent=1))
        for r in rep["scan"]:
            print(f"N={r['N']:3d} log2 den(T_N)={r['log2_den_T_N']:5d} "
                  f"base log2 q|S-T|={r['log2_base_q_times_err']:8.2f} "
                  f"best log2 q|S-R|={rep['verdict']['min_log2_q_times_err_by_N'][str(r['N'])]:8.2f} "
                  f"max layers killed={rep['verdict']['max_layers_cancelled_at_any_width'][str(r['N'])]}")
        print("q|S-R| ever below 1:", rep["verdict"]["q_times_err_ever_below_one"])
    return 0


if __name__ == "__main__":
    sys.exit(main())
