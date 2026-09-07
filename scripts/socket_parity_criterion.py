#!/usr/bin/env python3
r"""The socket criterion for complement supports: Odd_{N\E} = Sq XOR Odd_E.

WHY THIS EXISTS (the analysis it is bound to)
---------------------------------------------
Cross-index T33b/T33c established socket death for `C = N \ {2^i}` and framed it as a
CONTAINMENT phenomenon: the perturbation `D` must live inside `4N` so that it cannot touch
`m == 2 mod 4`, where `tau_C(m) = d(m) - 1` is odd.  Section 66 asks whether containment
generalises -- does `E` inside a fixed progression `dN` force `Odd_{N\E}` syndetic?

THE ALGEBRA (derived first; this run is a CHECK, not the source)
----------------------------------------------------------------
For `A = N \ E`,  `tau_A = d - tau_E`  pointwise, since a divisor of `m` lies in `A` exactly
when it is not in `E`.  The parity map is `F_2`-LINEAR (cross-index T30), so

    Odd_A  =  Odd_N  XOR  Odd_E  =  Sq  XOR  Odd_E,

because `d(m)` is odd exactly at perfect squares.  **The socket question for the entire
complement family reduces to a question about `E` alone.**

Squares have gaps `~2 sqrt(m) -> infinity`, and a two-line argument gives both directions:
if `Odd_E` is syndetic with gap `g` then `Sq XOR Odd_E` has gap `<= 2g`; and if `Odd_E` has
gaps `L_k -> infinity` at positions `m_k -> infinity`, then inside such a gap
`Sq XOR Odd_E` is just `Sq`, whose local gaps are `~2 sqrt(m_k) -> infinity`.  Hence

    socket kills `N \ E`   <=>   `Odd_E` is SYNDETIC.

PREDICTIONS, RECORDED BEFORE THE RUN
------------------------------------
P1  The identity `Odd_A = Sq XOR Odd_E` holds EXACTLY, every `m`, for every cohort.
P2  `E = {}` (so `A = N`) gives `Odd_A = Sq`, maxgap `~2 sqrt(M)` -- NOT syndetic.  This is
    the T25 check and it alone refutes "E inside dN forces death", since `{}` is inside
    every `dN`.
P3  `E = 4N` is INFINITE and inside `4N`, yet survives: `tau_{4N}(m) = d(m/4)` on `4N`, odd
    exactly at `m = 4k^2 = (2k)^2`, which are squares, so `Odd_A = Sq \ {even squares} =
    {ODD SQUARES}` and the gaps are `~8j -> infinity`.  Predicted maxgap near `M = 60000`:
    about `980`.
P4  Calibration against a landed number: `maxgap(Odd_primes) = 20` (residual (b)).

FALSIFIER, stated before the run: if P1 fails at any `m`, the `F_2` reduction is wrong and
section 66 must not be written.

WHAT THIS CANNOT DO: it says nothing about whether `A` is irrational.  A dead socket removes
one mechanism (T25); a live socket removes nothing.  `N \ 4N` survives the socket and is
still eventually PERIODIC, hence already settled by the Lambert/AP route -- surviving one
mechanism is not surviving the problem.

Bound directions, per the standing infrastructure rule:
  analysis -> here : cross-index T30 (F_2 linearity), T33b/T33c (the containment framing)
  here -> analysis : CertificateSocketCollapse.md section 66, receipt under state/
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]


def divisor_counts(M: int):
    d = [0] * (M + 1)
    for a in range(1, M + 1):
        for m in range(a, M + 1, a):
            d[m] += 1
    return d


def tau_of(S, M: int):
    """tau_S(m) = #{a in S : a | m}."""
    t = [0] * (M + 1)
    for a in S:
        if a < 1 or a > M:
            continue
        for m in range(a, M + 1, a):
            t[m] += 1
    return t


def maxgap(bits, lo: int, hi: int) -> int:
    last, g = None, 0
    for m in range(lo, hi + 1):
        if bits[m]:
            if last is not None:
                g = max(g, m - last)
            last = m
    return g


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--M", type=int, default=200000)
    ap.add_argument("--check-to", type=int, default=60000)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    M, C = args.M, args.check_to

    d = divisor_counts(M)
    sq = [0] * (M + 1)
    k = 1
    while k * k <= M:
        sq[k * k] = 1
        k += 1

    sieve = [True] * (M + 1)
    sieve[0] = sieve[1] = False
    for p in range(2, int(M ** 0.5) + 1):
        if sieve[p]:
            for x in range(p * p, M + 1, p):
                sieve[x] = False
    primes = [p for p in range(2, M + 1) if sieve[p]]
    pow2 = [2 ** i for i in range(1, 20) if 2 ** i <= M]

    cohorts = {
        "empty": [],
        "pow2_ge1": pow2,
        "primes": primes,
        "pow2_xor_primes": sorted(set(pow2) ^ set(primes)),
        "four_N": list(range(4, M + 1, 4)),
    }

    report = {"M": M, "check_to": C, "cohorts": {}}
    identity_ok = True
    for name, E in cohorts.items():
        tE = tau_of(E, M)
        oddE = [tE[m] & 1 for m in range(M + 1)]
        oddA = [(d[m] - tE[m]) & 1 for m in range(M + 1)]
        pred = [(sq[m] ^ oddE[m]) & 1 for m in range(M + 1)]
        ok = all(oddA[m] == pred[m] for m in range(1, C + 1))
        identity_ok = identity_ok and ok
        gE, gA = maxgap(oddE, 2, C), maxgap(oddA, 2, C)
        report["cohorts"][name] = {
            "identity_holds": ok,
            "maxgap_Odd_E": gE,
            "maxgap_Odd_A": gA,
            "socket": "DEAD" if 0 < gA <= 64 else "survives_in_range",
        }

    report["P1_identity"] = identity_ok
    report["P2_naturals_not_syndetic"] = report["cohorts"]["empty"]["maxgap_Odd_A"] > 100
    report["P3_fourN_survives"] = report["cohorts"]["four_N"]["maxgap_Odd_A"] > 100
    # P4 is a PINNED calibration at the DEFAULT box (M=200000, check_to=60000).
    # maxgap is monotone in the window, so asserting 20 at a smaller box is a
    # category error, not drift -- report it as not-applicable instead.
    report["P4_primes_calibration"] = (
        report["cohorts"]["primes"]["maxgap_Odd_E"] == 20
        if (M, C) == (200000, 60000) else "n/a_off_default_box"
    )
    report["falsifier_survived"] = identity_ok

    out = args.out or str(
        REPO / "state/formal_math/erdos257_period_noncollapse/socket_parity_criterion_receipt.json"
    )
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    blob = json.dumps(report, indent=2, sort_keys=True)
    Path(out).write_text(blob)

    print(f"M={M} identity checked to m={C}")
    print(f"{'E':<18} {'identity':>9} {'maxgap Odd_E':>13} {'maxgap Odd_A':>13}  socket")
    for n_, c in report["cohorts"].items():
        print(f"{n_:<18} {str(c['identity_holds']):>9} {c['maxgap_Odd_E']:>13} "
              f"{c['maxgap_Odd_A']:>13}  {c['socket']}")
    for k_ in ("P1_identity", "P2_naturals_not_syndetic", "P3_fourN_survives",
               "P4_primes_calibration"):
        print(f"{k_:<28} = {report[k_]}")
    print(f"wrote {out} sha256={hashlib.sha256(blob.encode()).hexdigest()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
