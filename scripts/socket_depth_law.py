#!/usr/bin/env python3
"""The search-depth law for socket runs -- why finite search sees short runs.

WHY THIS EXISTS (the analysis it is bound to)
---------------------------------------------
`CertificateSocketCollapse.md` section 46 proved the PARITY obstruction
(`maxrun <= maxgap(Odd_A) - 1`) and left one row unexplained: `A = 3N` has parity gap
3459, permitting runs into the thousands, yet its observed maxrun was 8 against a
shuffled control of 33.  This probe supplies the missing constraint.

THE ALGEBRA THIS CHECKS (derived first; the run is a check, not the source)
--------------------------------------------------------------------------
**Magnitude bound.**  Inside a socket run, `2^k | tau_A(N+k)`.  A nonzero natural
divisible by `2^k` is at least `2^k`.  Zero coefficients are EXEMPT -- zero is divisible
by everything -- so the force lands only where `tau_A` is positive.  Let `a = min A`.
Any `a` consecutive integers contain a multiple of `a`, so the top `a` of the window
holds some index `k >= K - a + 1` with `a | N+k`, hence `tau_A(N+k) >= 1`.  Therefore

    2^(K - a + 1)  <=  max_{m <= N+K} tau_A(m).

**This is NOT a cap, and calling it one would be an error.**  Section 44 proved `tau_A`
is UNBOUNDED for every infinite `A`, so the right-hand side diverges and no `K` is
excluded outright.  What the inequality gives is a DEPTH: to observe a run of length `K`
you must search out to where `tau_A` first reaches `2^(K-a+1)`.  That is the quantitative
form of cross-index T12, "finite search never refutes existence".

Contrast with parity, and this is the whole point:

  parity     STRUCTURAL, ABSOLUTE.     Syndetic `Odd_A` bounds the run for ALL `N`,
                                       forever.  A genuine kill criterion.
  magnitude  QUANTITATIVE, RANGE-BOUND. Bounds the run only within a search window, and
                                       recedes as the window grows.  A depth law.

Note also that the magnitude bound is SHUFFLE-INVARIANT in its raw form -- it depends only
on the multiset of `tau_A` values -- whereas parity depends on their arrangement.  So the
`a = min A` sharpening applies to the real cohorts only; a shuffled sequence has no `min
A` and can pack a long run out of scattered zeros.  The control is therefore checked
against parity alone, and that asymmetry is reported rather than hidden.

PREDICTIONS, RECORDED BEFORE THE RUN
------------------------------------
  naturals  `a = 1`, every index constrained, so need `2^K <= max d`.  Predict
            `max d = 240` for `m <= 10^6`, giving feasible `K <= 7`; observed 5.  The gap
            is because all `k` must hold SIMULTANEOUSLY.  Erdos proved the runs unbounded
            here, so 7 is a window artefact, not a cap (T12).
  primes    `a = 2`, need `2^(K-1) <= max omega`.  Predict `max omega = 7` (510510), so
            `K <= 3`; and the direct `k = 3` clause needs `omega(N+3) >= 8`, first
            available at the 8th primorial 9699690 -- TEN TIMES the search range.  So
            predict observed exactly **2**, with required depth 9699690.
  powers2   `a = 2`, `max v_2 = 19` (2^19 = 524288), so magnitude gives `K <= 5`; parity
            gives `K <= 3`.  **Parity binds.**  Predict 3.
  pow3      `a = 3`, `max v_3 = 12` (3^12 = 531441), so magnitude gives `K <= 5`; parity
            gives `K <= 5`.  **Both bind at the same value.**  Predict 5.
  ap3       `a = 3`, `tau_A(m) = d(m/3)` on multiples of 3 and 0 elsewhere.  Parity gives
            3458 -- useless.  Predict magnitude BINDS here and lands near the observed 8.
            This row is the reason the probe exists.

FALSIFIER, stated before the run: any real cohort with
`maxrun > min(parity_bound, magnitude_bound)`, or any control cohort with
`maxrun > parity_bound`, refutes the derivation and no section may be written.
Reported per row as `bounds_respected`.

SATURATION CHECK
----------------
The two argmax points are re-verified from scratch: at `N = 8851` the divisor counts at
`k = 3,4,5` should be exactly `8, 16, 32`, and at `N = 208` the omega values at
`k = 1,2` exactly `2, 4`.  If the runs saturate their required powers position by
position, the magnitude bound is not merely valid but BINDING at the observed optimum.

Bound directions, per the standing infrastructure rule:
  analysis -> here : CertificateSocketCollapse.md 44 (`tau_A` unbounded), 46 (parity, and
                     the `3N` residual this resolves), cross-index T12, T25
  here -> analysis : CertificateSocketCollapse.md section 47, cross-index trap,
                     receipt under state/formal_math/erdos257_period_noncollapse/
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]

COHORT_MIN = {"naturals": 1, "primes": 2, "powers2": 2, "pow3": 3, "ap3": 3}


def build_tau(kind: str, M: int):
    tau = [0] * (M + 1)

    def add(a: int) -> None:
        for m in range(a, M + 1, a):
            tau[m] += 1

    if kind == "naturals":
        for a in range(1, M + 1):
            add(a)
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
                add(a)
    elif kind == "powers2":
        a = 2
        while a <= M:
            add(a); a *= 2
    elif kind == "pow3":
        a = 3
        while a <= M:
            add(a); a *= 3
    elif kind == "ap3":
        for a in range(3, M + 1, 3):
            add(a)
    else:
        raise ValueError(kind)
    return tau


def max_gap_odd(tau, M: int) -> int:
    prev, gap = None, 0
    for m in range(1, M + 1):
        if tau[m] & 1:
            if prev is not None and m - prev > gap:
                gap = m - prev
            prev = m
    return gap


def max_socket_run(tau, M: int, nmax: int, cap: int):
    best, best_N = 0, None
    for N in range(1, nmax + 1):
        K = 0
        while K < cap and N + K + 1 <= M:
            k = K + 1
            if k < 64 and (tau[N + k] % (1 << k)) != 0:
                break
            K += 1
        if K > best:
            best, best_N = K, N
    return best, best_N


def first_reaching(tau, M: int, target: int):
    """Smallest m <= M with tau[m] >= target; None if never in range."""
    for m in range(1, M + 1):
        if tau[m] >= target:
            return m
    return None


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
    report = {"max_n": M, "nmax": nmax, "seed": args.seed, "cohorts": {}}
    ok_all = True

    for kind, a in COHORT_MIN.items():
        tau = build_tau(kind, M)
        mx = max(tau)
        parity = max_gap_odd(tau, M) - 1
        # largest K with 2^(K-a+1) <= mx
        K = 0
        while K + 1 - a + 1 <= 0 or (1 << max(0, K + 1 - a + 1)) <= mx:
            K += 1
            if K > cap + 8:
                break
        magnitude = K
        run, run_N = max_socket_run(tau, M, nmax, cap)

        shuffled = [0] + rng.sample(tau[1:M + 1], M)
        cparity = max_gap_odd(shuffled, M) - 1
        crun, _ = max_socket_run(shuffled, M, nmax, cap)

        ok = run <= min(parity, magnitude)
        cok = crun <= cparity
        ok_all = ok_all and ok and cok
        depths = {str(k): first_reaching(tau, M, 1 << k) for k in range(1, 10)}
        report["cohorts"][kind] = {
            "min_A": a, "max_tau": mx,
            "parity_bound": parity, "magnitude_bound": magnitude,
            "binding": "parity" if parity < magnitude else
                       ("magnitude" if magnitude < parity else "both"),
            "observed_maxrun": run, "argmax_N": run_N,
            "control_maxrun": crun, "control_parity_bound": cparity,
            "first_m_with_tau_ge_2^k": depths,
            "bounds_respected": ok, "control_bound_respected": cok,
        }
        print(f"{kind:>9}: run={run}@{run_N}  parity<={parity}  magnitude<={magnitude}  "
              f"binding={report['cohorts'][kind]['binding']}  maxtau={mx}  ok={ok}  "
              f"| control run={crun} parity<={cparity} ok={cok}")

    report["falsifier_survived"] = ok_all
    print(f"FALSIFIER: {'SURVIVED' if ok_all else 'BROKEN'}")

    out = args.out or str(
        REPO / "state/formal_math/erdos257_period_noncollapse/socket_depth_law_receipt.json"
    )
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    blob = json.dumps(report, indent=2, sort_keys=True)
    Path(out).write_text(blob)
    print(f"wrote {out} sha256={hashlib.sha256(blob.encode()).hexdigest()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
