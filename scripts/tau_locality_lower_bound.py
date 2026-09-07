#!/usr/bin/env python3
"""How much of A a BOUNDED WINDOW of tau_A can see: an indistinguishability bound.

Trap T13 records that `tau_A = 1 * 1_A` is a bijection (`1_A = mu * tau_A`), so it
destroys no information -- it destroys LOCALITY.  That was qualitative.  This
script establishes and verifies the quantitative form.

PROPOSITION.  Let N be composite, p its least prime factor, m = N/p its largest
proper divisor (so m >= sqrt(N)).  Then 1_A(N) is NOT determined by tau_A
restricted to any window [N-w, N+w] with w < m.

PROOF.  Take A containing m but not N, and A' containing N but not m, agreeing
elsewhere.  Then tau_{A'} - tau_A = 1(N | K) - 1(m | K).  Inside the window the
only multiple of N is N itself, and the only multiple of m is N itself (the
neighbours N +- m lie at distance m > w).  So the two changes cancel at every
window position and tau_A = tau_{A'} there, while 1_A(N) != 1_{A'}(N).  QED

For N prime the situation is the opposite: 1_A(N) = tau_A(N) - tau_A(1), i.e.
radius 0 plus one global value.

WHY THIS ELIMINATES A MECHANISM CLASS
-------------------------------------
This is an indistinguishability bound, not a statement about the Mobius formula:
NO recovery rule reading a window of radius < m can succeed, because two supports
differing at N produce identical window data.  Hence any transcendence mechanism
that reads tau_A through bounded windows -- subword complexity, local
automaticity, k-block frequencies, transducer/automaton models, sliding-window
statistics -- can access A only at the PRIMES.

That is exactly the exhaustion map's revised single-survivor law (section AM:
"tau_A preserves PERIODICITY and nothing else non-trivial"): periodicity is
window-readable, complexity is not.  The bound explains the law rather than
restating it, and it eliminates the whole bounded-window class in one step.

NONCLAIM.  This is not progress on Erdos 257.  It closes a class of attacks.

Bound directions:
  analysis -> here : cross-index trap T13 ; exhaustion map sections AI/AM
  here -> analysis : Erdos257/DivisorTransformRecovery.md section 6, receipt under state/
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]


def spf(n: int) -> int:
    d = 2
    while d * d <= n:
        if n % d == 0:
            return d
        d += 1
    return n


def tau_window(A: set, lo: int, hi: int):
    return tuple(sum(1 for a in A if a and K % a == 0) for K in range(lo, hi + 1))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--base-limit", type=int, default=4000)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    BASE = {a for a in range(1, args.base_limit + 1) if a % 3 != 0}
    composites = [12, 16, 25, 30, 49, 64, 81, 100, 128, 210, 243, 256, 361, 1024]
    primes = [13, 101, 257, 1009]

    rows, all_ok = [], True
    for N in composites:
        p = spf(N)
        assert p != N, f"{N} is prime"
        m = N // p
        w = m - 1
        A = set(BASE); A.discard(N); A.add(m)
        A2 = set(BASE); A2.add(N); A2.discard(m)
        agrees = tau_window(A, N - w, N + w) == tau_window(A2, N - w, N + w)
        differs = (N in A) != (N in A2)
        all_ok &= agrees and differs
        rows.append({"N": N, "p_min": p, "required_radius_m": m, "window_radius": w,
                     "tau_agrees_on_window": agrees, "indicator_differs": differs,
                     "m_over_sqrtN": m / (N ** 0.5)})

    prime_rows = []
    for P in primes:
        for ind in (0, 1):
            A = set(BASE); A.discard(P)
            if ind:
                A.add(P)
            t = sum(1 for a in A if a and P % a == 0)
            one = 1 if 1 in A else 0
            recovered = (t - one == ind)
            all_ok &= recovered
            prime_rows.append({"p": P, "indicator": ind, "tau_p": t,
                               "tau_p_minus_tau_1": t - one, "recovered": recovered})

    report = {
        "proposition": "for composite N, 1_A(N) is undetermined by tau_A on any "
                       "window of radius < m = N/p_min (>= sqrt N); for prime N, "
                       "radius 0 plus tau_A(1) suffices",
        "composite_indistinguishability": rows,
        "prime_recovery_control": prime_rows,
        "all_checks_passed": bool(all_ok),
    }
    out = args.out or str(
        REPO / "state/formal_math/erdos257_period_noncollapse/tau_locality_lower_bound_receipt.json"
    )
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    blob = json.dumps(report, indent=2, sort_keys=True)
    Path(out).write_text(blob)
    print(f"composite flip pairs: {len(rows)}  prime controls: {len(prime_rows)}")
    print(f"ALL CHECKS PASSED: {all_ok}")
    print(f"wrote {out} sha256={hashlib.sha256(blob.encode()).hexdigest()}")
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
