#!/usr/bin/env python3
"""Socket-run census: the parity obstruction to the Erdos 1948 zero-run mechanism.

WHY THIS EXISTS (the analysis it is bound to)
---------------------------------------------
`CertificateSocketCollapse.md` section 26 identifies the corpus's three certificate
sockets with Erdos's own 1948 criterion, `liminf_N frac(2^N y) = 0` -- arbitrarily long
runs of binary zeros in `y = sum_n tau_A(n) 2^-n`.  It reconstructs the engine that
produces those runs (Vandehey, arXiv:1206.0340, following Erdos): by CRT and the
MULTIPLICATIVITY of `d(.)`, force

    2^(k) | tau_A(N + k)     for k = 1, ..., K,

which makes every one of the first `K` terms of `sum_k tau_A(N+k) 2^-k` an integer, so the
fractional part collapses into the tail.  Section 26 closes by stating the open question
in the corpus's own coordinates:

    "Can one force 2^(j+1) | tau_A(n) at k consecutive n, for a general infinite A?"

Section 45 eliminated the OTHER mechanism (shifted blocks) for 257.  The socket lane is
what is left, and this probe attacks its combinatorial core.

THE ALGEBRA THIS CHECKS (derived first; the run is a check, not the source)
--------------------------------------------------------------------------
**Parity obstruction.**  Let `Odd_A := {m >= 1 : tau_A(m) is odd}`.  If some `m` in the
window `[N+1, N+K]` lies in `Odd_A`, then at index `k = m - N >= 1` the run demands
`2^k | tau_A(m)` with `tau_A(m)` odd -- impossible.  So every socket run must fit
strictly between two consecutive elements of `Odd_A`, giving the exact bound

    maxrun  <=  maxgap(Odd_A) - 1,

where `maxgap` is the largest difference between consecutive elements of `Odd_A`.
**Arbitrarily long socket runs REQUIRE `Odd_A` to have unbounded gaps.**  Equivalently:
if `Odd_A` is syndetic, the Erdos 1948 mechanism is unavailable for that support set --
not merely unproven, unavailable.

This is consistent with the two cases whose status is known.  At `A = N`, `tau_A = d` and
`d(m)` is odd exactly when `m` is a perfect square; squares have gaps `~ 2 sqrt(m)`, so
`Odd_A` is NOT syndetic and Erdos's construction is not obstructed -- as it must not be,
since he carried it out.  At `A` = primes, `tau_A = omega` and `Odd_A = {omega odd}` has
density 1/2, so the obstruction bites hard, which is one reason #69 is difficult.

PREDICTIONS, RECORDED BEFORE THE RUN
------------------------------------
  naturals   `Odd_A` = squares.  maxgap grows like `2 sqrt(M)`, so NO cap in principle.
             Observed maxrun is limited here only by the search window: `2^k | d(N+k)`
             needs `d(N+k) >= 2^k`, and `d <= 240` for `N <= 10^6`, so `k <= 7`.
             Predict maxrun in 2-5.  This is the CALIBRATOR: Erdos 1948 proves runs are
             unbounded for this A, so a small observed maxrun here must NOT be read as a
             cap.  Finite search never refutes existence (cross-index T12).
  powers2    `A = {2,4,8,...}`, `tau_A = v_2`.  `v_2(m)` odd includes every `m = 2 mod 4`,
             so maxgap = 4 and **maxrun <= 3**.  Predict exactly 3.
  pow3       `A = {3,9,27,...}`, `tau_A = v_3`.  `v_3(m) = 1` on `m = 3, 6 mod 9`; those
             occur at 3,6,12,15,21,24,... so maxgap = 6 and **maxrun <= 5**.
  primes     `Odd_A = {omega odd}`, density 1/2.  Predict maxgap small (<= 8 over 10^6)
             and maxrun <= maxgap - 1, i.e. a handful.  Additionally `2^k | omega` with
             `omega >= 1` forces `omega(N+k) >= 2^k`, needing `N` past the primorial of
             `2^k` primes -- brutal but not impossible, which is the #69 difficulty.
  ap3        `A = 3N`.  `tau_A(m) = 0` unless `3 | m`, and zero is divisible by
             everything, so those indices are FREE.  `Odd_A = {m = 3s^2}`, gaps unbounded.
             Predict a larger maxrun than the rigid cohorts.
  CONTROL    each `tau_A` reshuffled: same marginal, arithmetic destroyed.  Predicted
             control maxrun 1-3.  The control must ALSO satisfy `maxrun <= maxgap - 1`,
             since that bound is combinatorial and holds for any integer sequence.

FALSIFIER, stated before the run: if ANY cohort -- real or control -- shows
`maxrun > maxgap(Odd_A) - 1`, the parity obstruction is WRONG and no section may be
written on it.  This is checked and reported per cohort as `bound_respected`.

WHAT A POSITIVE RESULT WOULD MEAN
---------------------------------
A complete, elementary obstruction to the only mechanism known to reach the near-covering
regime, stated as a checkable property of `A` alone: `Odd_A` syndetic kills it.  That does
NOT decide Erdos 257, and by T12 the finite maxrun of a non-syndetic cohort is not a cap.

Bound directions, per the standing infrastructure rule:
  analysis -> here : CertificateSocketCollapse.md section 26 (sockets = Erdos 1948, and
                     the `2^(j+1) | tau_A(n)` target), section 45 (the other mechanism,
                     eliminated), cross-index T12 (finite search never refutes existence)
  here -> analysis : CertificateSocketCollapse.md section 46, cross-index trap,
                     receipt under state/formal_math/erdos257_period_noncollapse/
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]


def build_tau(kind: str, M: int):
    """tau_A(n) = #{a in A : a | n}, exact, for n in [1, M]."""
    tau = [0] * (M + 1)

    def add_multiples(a: int) -> None:
        for m in range(a, M + 1, a):
            tau[m] += 1

    if kind == "naturals":
        for a in range(1, M + 1):
            add_multiples(a)
    elif kind == "primes":
        sieve = bytearray([1]) * (M + 1)
        sieve[0:2] = b"\x00\x00"
        i = 2
        while i * i <= M:
            if sieve[i]:
                for m in range(i * i, M + 1, i):
                    sieve[m] = 0
            i += 1
        for a in range(2, M + 1):
            if sieve[a]:
                add_multiples(a)
    elif kind == "powers2":
        a = 2
        while a <= M:
            add_multiples(a)
            a *= 2
    elif kind == "pow3":
        a = 3
        while a <= M:
            add_multiples(a)
            a *= 3
    elif kind == "ap3":
        for a in range(3, M + 1, 3):
            add_multiples(a)
    else:
        raise ValueError(kind)
    return tau


def max_gap_odd(tau, M: int):
    """Largest difference between consecutive m with tau[m] odd (within [1, M])."""
    prev, gap, at = None, 0, None
    for m in range(1, M + 1):
        if tau[m] & 1:
            if prev is not None and m - prev > gap:
                gap, at = m - prev, prev
            prev = m
    return gap, at, prev


def max_socket_run(tau, M: int, nmax: int, cap: int):
    """Largest K with 2^k dividing tau[N+k] for every k in [1, K]."""
    best, best_N = 0, None
    for N in range(1, nmax + 1):
        K = 0
        while K < cap and N + K + 1 <= M:
            k = K + 1
            t = tau[N + k]
            if k < 64 and (t % (1 << k)) != 0:
                break
            K += 1
        if K > best:
            best, best_N = K, N
    return best, best_N


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max", type=int, default=1_000_000)
    ap.add_argument("--nmax", type=int, default=500_000)
    ap.add_argument("--cap", type=int, default=40)
    ap.add_argument("--seed", type=int, default=20260823)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    M, nmax, cap = args.max, args.nmax, args.cap
    rng = random.Random(args.seed)
    kinds = ("naturals", "primes", "powers2", "pow3", "ap3")

    report = {"max_n": M, "nmax": nmax, "cap": cap, "seed": args.seed, "cohorts": {}}
    all_ok = True
    for kind in kinds:
        tau = build_tau(kind, M)
        gap, gap_at, _ = max_gap_odd(tau, M)
        run, run_N = max_socket_run(tau, M, nmax, cap)

        shuffled = [0] + rng.sample(tau[1:M + 1], M)
        cgap, _, _ = max_gap_odd(shuffled, M)
        crun, _ = max_socket_run(shuffled, M, nmax, cap)

        ok = run <= gap - 1
        cok = crun <= cgap - 1
        all_ok = all_ok and ok and cok
        report["cohorts"][kind] = {
            "max_gap_odd": gap, "max_gap_odd_starts_at": gap_at,
            "odd_count": sum(1 for m in range(1, M + 1) if tau[m] & 1),
            "max_socket_run": run, "argmax_N": run_N,
            "control_max_gap_odd": cgap, "control_max_socket_run": crun,
            "bound_respected": ok, "control_bound_respected": cok,
        }
        print(f"{kind:>9}: maxrun={run} (N={run_N})  maxgap(Odd_A)={gap}  "
              f"bound_ok={ok}   control: run={crun} gap={cgap} ok={cok}")

    report["falsifier_survived"] = all_ok
    print(f"FALSIFIER (maxrun <= maxgap-1 everywhere): {'SURVIVED' if all_ok else 'BROKEN'}")

    out = args.out or str(
        REPO / "state/formal_math/erdos257_period_noncollapse/socket_parity_census_receipt.json"
    )
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    blob = json.dumps(report, indent=2, sort_keys=True)
    Path(out).write_text(blob)
    print(f"wrote {out} sha256={hashlib.sha256(blob.encode()).hexdigest()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
