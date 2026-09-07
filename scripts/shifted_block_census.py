#!/usr/bin/env python3
"""Shifted-block census for tau_A: can the machine-checked engine reach Erdos 257?

WHY THIS EXISTS (the analysis it is bound to)
---------------------------------------------
`Erdos257PeriodNoncollapse/ReciprocalSupportIrrationality.lean` proves

    irrational_binaryCoeffSeries_of_shiftedBlockWitnesses

for ANY `c` with `c n <= n`, hence for `c = tau_A` (`tau_A(n) <= d(n) <= n`).  Its
shift clause is

    forall j in [1, K],  c (N + j) = c j + 1.

`CertificateSocketCollapse.md` section 44 records that the previous, pointwise-bounded
form of this hypothesis was UNSATISFIABLE, and that the repaired tail-bound form is
consistent with unbounded `c`.  Consistency is not satisfiability.  This probe asks the
next question: is the shift clause itself satisfiable at `c = tau_A`, and for how long a
block?

THE ALGEBRA THIS CHECKS (derived first; the run is a check, not the source)
--------------------------------------------------------------------------
Block reduction.  If `a | N` for every `a in A` with `a <= K`, then for `j` in `[1, K]`

    tau_A(N + j) - tau_A(j) = #{a in A : a > K and a | N + j},

because the `a <= K` terms cancel (`a | N` makes `a | N+j` equivalent to `a | j`) and the
`a > K` terms have `a` not dividing `j` (as `1 <= j <= K < a`).  So the shift clause says:
**each of `N+1, ..., N+K` has exactly one divisor in `A` above `K`** -- a covering-type
condition.  At `A` = primes this is `N + j = j * p_j` with `p_j` prime, which is exactly
Pratt's construction; that agreement is the calibration.

K must diverge.  The engine also demands `tail_K <= B`, `2(B+1) < c(N+K+1)`,
`tail_{N+K} <= U` and `U - 1 < eps * 2^K`.  Since `tail_{N+K} >= c(N+K+1)/2 > B + 1`, we
get `U > B + 1` and therefore `B < eps * 2^K`, so `tail_K < eps * 2^K`.  For infinite `A`
the tail is strictly positive, so `eps -> 0` forces `K -> infinity`.  **The witness
hypothesis requires arbitrarily long blocks.**

PREDICTIONS, RECORDED BEFORE THE RUN
------------------------------------
  naturals   `tau_A = d`.  `d(N+1) = 2` forces `N+1` prime; `d(N+2) = 3` forces
             `N+2 = p^2`; `d(N+3) = 3` forces `N+3 = q^2`; consecutive squares are
             impossible.  So max K = 2, attained at N = 2 ONLY (there `N+1 = 3`,
             `N+2 = 4`), and K >= 3 has NO solutions at any N.
  powers2    `tau_A = v_2 + 1`.  `j=1` forces `N+1 = 2 mod 4`, so `N = 1 mod 4` and
             `N+2` is odd, contradicting `v_2(N+2) = 2`.  Max K = 1.
  primes     `tau_A = omega`.  Pratt-type blocks exist; expect max K in the range 3-8
             over this search window, growing slowly.
  CONTROL    a random sequence with the SAME marginal distribution as each `tau_A`.
             If the observed K were mere coincidence-counting, control and real would
             agree.  Predicted control max K: 2-4 over ~10^6 trials.  The control MUST
             fail to reproduce a large real K, or the real K means nothing.

FALSIFIER, stated before the run: if `naturals` exhibits any N with K >= 3, the block
reduction above is wrong and section 45 must not be written.

WHAT A NEGATIVE RESULT WOULD MEAN
---------------------------------
`sum_{a in N} 1/(2^a - 1)` is the Erdos-Borwein constant, proved irrational by Erdos in
1948.  If the engine cannot produce long blocks at `A = N`, it fails on a case the
classical theory settles, and the shifted-block mechanism is eliminated as a route to
Erdos 257 in general -- not merely unproven for it.

Bound directions, per the standing infrastructure rule:
  analysis -> here : CertificateSocketCollapse.md sections 42-44 (the engine, the
                     retraction, the tail-bound repair)
                     ReciprocalSupportIrrationality.lean (the theorem being probed)
  here -> analysis : CertificateSocketCollapse.md section 45, cross-index trap,
                     receipt under state/formal_math/erdos257_period_noncollapse/
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]


def sieve_smallest_prime_factor(M: int):
    spf = list(range(M + 1))
    i = 2
    while i * i <= M:
        if spf[i] == i:
            for m in range(i * i, M + 1, i):
                if spf[m] == m:
                    spf[m] = i
        i += 1
    return spf


def build_tau(kind: str, M: int, spf):
    """tau_A(n) = #{a in A : a | n}, computed exactly for n in [1, M]."""
    tau = [0] * (M + 1)
    if kind == "naturals":                       # A = N   -> tau_A = d
        for a in range(1, M + 1):
            for m in range(a, M + 1, a):
                tau[m] += 1
    elif kind == "primes":                       # A = primes -> tau_A = omega
        for a in range(2, M + 1):
            if spf[a] == a:
                for m in range(a, M + 1, a):
                    tau[m] += 1
    elif kind == "powers2":                      # A = {1,2,4,...} -> tau_A = v_2 + 1
        a = 1
        while a <= M:
            for m in range(a, M + 1, a):
                tau[m] += 1
            a *= 2
    elif kind == "ap3":                          # A = {3,6,9,...}
        for a in range(3, M + 1, 3):
            for m in range(a, M + 1, a):
                tau[m] += 1
    elif kind == "squares":                      # A = {1,4,9,16,...}
        a = 1
        while a * a <= M:
            s = a * a
            for m in range(s, M + 1, s):
                tau[m] += 1
            a += 1
    elif kind == "lacunary":                     # A = {3^i}
        a = 1
        while a <= M:
            for m in range(a, M + 1, a):
                tau[m] += 1
            a *= 3
    else:
        raise ValueError(kind)
    return tau


def max_block(tau, N: int, M: int, cap: int) -> int:
    """Largest K with tau[N+j] == tau[j] + 1 for every j in [1, K]."""
    K = 0
    while K < cap and N + K + 1 <= M:
        j = K + 1
        if tau[N + j] != tau[j] + 1:
            break
        K += 1
    return K


def census(tau, M: int, nmax: int, cap: int):
    best, best_N, hist = 0, None, {}
    for N in range(1, nmax + 1):
        K = max_block(tau, N, M, cap)
        hist[K] = hist.get(K, 0) + 1
        if K > best:
            best, best_N = K, N
    return best, best_N, hist


def control_census(tau, M: int, nmax: int, cap: int, seed: int):
    """Same marginal distribution, independent order: the coincidence null."""
    rng = random.Random(seed)
    pool = tau[1:M + 1]
    shuffled = [0] + rng.sample(pool, len(pool))
    return census(shuffled, M, nmax, cap)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max", type=int, default=1_200_000)
    ap.add_argument("--nmax", type=int, default=600_000)
    ap.add_argument("--cap", type=int, default=64)
    ap.add_argument("--seed", type=int, default=20260823)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    M, nmax, cap = args.max, args.nmax, args.cap
    spf = sieve_smallest_prime_factor(M)
    kinds = ("naturals", "primes", "powers2", "ap3", "squares", "lacunary")

    report = {"max_n": M, "nmax": nmax, "cap": cap, "seed": args.seed, "cohorts": {}}
    for kind in kinds:
        tau = build_tau(kind, M, spf)
        best, best_N, hist = census(tau, M, nmax, cap)
        cbest, cbest_N, _ = control_census(tau, M, nmax, cap, args.seed)
        witness = None
        if best_N is not None:
            witness = [
                {"j": j, "N_plus_j": best_N + j,
                 "tau_N_plus_j": tau[best_N + j], "tau_j": tau[j]}
                for j in range(1, min(best, 12) + 1)
            ]
        report["cohorts"][kind] = {
            "max_K": best,
            "argmax_N": best_N,
            "control_max_K": cbest,
            "control_argmax_N": cbest_N,
            "block_length_histogram": {str(k): v for k, v in sorted(hist.items())},
            "witness_block": witness,
        }
        print(f"{kind:>10}: max_K={best} at N={best_N}   control_max_K={cbest}")

    out = args.out or str(
        REPO / "state/formal_math/erdos257_period_noncollapse/shifted_block_census_receipt.json"
    )
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    blob = json.dumps(report, indent=2, sort_keys=True)
    Path(out).write_text(blob)
    print(f"wrote {out} sha256={hashlib.sha256(blob.encode()).hexdigest()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
