#!/usr/bin/env python3
"""Scaling of maxgap(Odd_A): bounded (killed) versus growing (escapes).

WHY THIS EXISTS (the analysis it is bound to)
---------------------------------------------
`CertificateSocketCollapse.md` section 46 proved the parity obstruction
`maxrun <= maxgap(Odd_A) - 1`, where `Odd_A = {m : tau_A(m) odd}`, and section 47 priced
the complementary magnitude constraint.  The kill criterion is **`Odd_A` syndetic**, i.e.
`maxgap` BOUNDED.  Every measurement so far reported `maxgap` at a single `M`, and a
single value cannot distinguish "bounded" from "growing slowly" -- the standing rule is
never to read a scalar at one `N` as a limit.  This probe measures the SCALING.

A FORMULA THAT TURNED OUT TO BE CIRCULAR, recorded so it is not re-attempted
--------------------------------------------------------------------------
The involution `d -> m/d` on divisors of `m` has 2-element orbits `{d, m/d}` plus the
fixed point `sqrt(m)` when `m` is square.  The set `{d | m : d in A and m/d in A}` is
invariant, so its size is even except for that fixed point, giving

    tau_A(m)  ==  asym_A(m) + [m square] * 1_A(sqrt m)   (mod 2),
    asym_A(m) := #{d | m : d in A and m/d NOT in A}.

At `A = N` no divisor pair is asymmetric, so `tau_A(m) == [m square]` -- the classical
"`d(m)` odd iff `m` is a square", recovered exactly.  **But off the squares the formula
says `tau_A(m)` is odd exactly when `asym_A(m)` is odd, so any criterion of the form
"`Odd_A` is syndetic iff `asym_A` is odd often" is a restatement of itself.**  It is a
true identity and a USELESS criterion.  It is verified here as an exactness check on the
algebra, and nothing is built on it.

WHAT IS ACTUALLY DECIDED BY SCALING
-----------------------------------
`Odd_A` bounded gaps => the socket mechanism is UNAVAILABLE for `A` (s46, absolute).
`Odd_A` unbounded gaps => the necessary condition is met and the mechanism survives the
parity test.  So the growth law of `maxgap(Odd_A)` in `M` is the verdict, not its value.

At `A = primes`, `Odd_A = {m : omega(m) odd}` and a gap of `g` is a run of `g-1`
consecutive integers with `omega` EVEN.  So:

> **The parity obstruction is vacuous at the primes if and only if there exist
> arbitrarily long runs of consecutive integers with `omega` even.**

That is a Chowla-flavoured statement about sign patterns of `(-1)^omega`.  **I have not
verified its status in the literature and do not claim it is open**; the reduction is what
this probe records, and the measurement below only reports whether the growth is
consistent with the random model `log_2 M`.

PREDICTIONS, RECORDED BEFORE THE RUN
------------------------------------
  involution formula   ZERO failures at every `m`, every cohort.  It is a theorem; a
                       single failure refutes the derivation and voids the section.
  naturals             `Odd_A` = squares, so maxgap = **exactly `2*floor(sqrt M) - 1`**.
                       At `M = 10^6` that is 1999, matching s46's measured 1999.
  powers2              maxgap = **4, CONSTANT in M** (for `M >= 8`).
  pow3                 maxgap = **6, CONSTANT in M** (for `M >= 18`).
  primes               maxgap GROWS like `log_2 M` under the random model: predict roughly
                       14-17 at `10^4`, 17-20 at `10^5`, 20-23 at `10^6`.
  ap3                  `Odd_A = {3 s^2}`, so maxgap ~ `3*(2*floor(sqrt(M/3)) + 1)`, about
                       3465 at `M = 10^6` against s46's measured 3459.

FALSIFIER, stated before the run: (i) any `m` where the involution formula fails; or
(ii) a geometric cohort (`powers2`, `pow3`) whose maxgap GROWS with `M` -- that would
refute the syndetic kill of section 46 and force a retraction.  Reported as
`falsifier_survived`.

Bound directions, per the standing infrastructure rule:
  analysis -> here : CertificateSocketCollapse.md 46 (parity obstruction), 47 (depth law),
                     cross-index T25, T26
  here -> analysis : CertificateSocketCollapse.md section 48, cross-index trap,
                     receipt under state/formal_math/erdos257_period_noncollapse/
"""

from __future__ import annotations

import argparse
import hashlib
import json
from math import isqrt
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]


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


def in_A(kind: str, d: int) -> bool:
    if d < 1:
        return False
    if kind == "naturals":
        return True
    if kind == "primes":
        if d < 2:
            return False
        i = 2
        while i * i <= d:
            if d % i == 0:
                return False
            i += 1
        return True
    if kind == "powers2":
        return d >= 2 and (d & (d - 1)) == 0
    if kind == "pow3":
        if d < 3:
            return False
        while d % 3 == 0:
            d //= 3
        return d == 1
    if kind == "ap3":
        return d % 3 == 0
    raise ValueError(kind)


def check_involution(kind: str, tau, upto: int) -> int:
    """Return the number of m <= upto where the parity identity FAILS."""
    fails = 0
    for m in range(1, upto + 1):
        asym = 0
        i = 1
        while i * i <= m:
            if m % i == 0:
                for d in ({i, m // i} if i * i != m else {i}):
                    if in_A(kind, d) and not in_A(kind, m // d):
                        asym += 1
            i += 1
        r = isqrt(m)
        sq = 1 if (r * r == m and in_A(kind, r)) else 0
        if (asym + sq) % 2 != tau[m] % 2:
            fails += 1
    return fails


def max_gap_odd(tau, M: int) -> int:
    prev, gap = None, 0
    for m in range(1, M + 1):
        if tau[m] & 1:
            if prev is not None and m - prev > gap:
                gap = m - prev
            prev = m
    return gap


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max", type=int, default=1_000_000)
    ap.add_argument("--involution-upto", type=int, default=20000)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    M = args.max
    scales = [s for s in (10**3, 10**4, 10**5, 10**6, 10**7) if s <= M]
    kinds = ("naturals", "primes", "powers2", "pow3", "ap3")
    report = {"max_n": M, "scales": scales, "cohorts": {}}
    ok = True

    for kind in kinds:
        tau = build_tau(kind, M)
        fails = check_involution(kind, tau, min(args.involution_upto, M))
        gaps = {str(s): max_gap_odd(tau, s) for s in scales}
        grows = len(scales) > 1 and gaps[str(scales[-1])] > gaps[str(scales[0])]
        geometric = kind in ("powers2", "pow3")
        row_ok = (fails == 0) and not (geometric and grows)
        ok = ok and row_ok
        report["cohorts"][kind] = {
            "involution_failures": fails,
            "involution_checked_upto": min(args.involution_upto, M),
            "max_gap_by_scale": gaps,
            "grows_with_M": grows,
            "verdict": "BOUNDED -> killed" if not grows else "GROWS -> escapes parity",
            "row_ok": row_ok,
        }
        print(f"{kind:>9}: involution_fails={fails}  gaps={gaps}  "
              f"{'GROWS' if grows else 'BOUNDED'}")

    report["falsifier_survived"] = ok
    print(f"FALSIFIER: {'SURVIVED' if ok else 'BROKEN'}")
    out = args.out or str(
        REPO / "state/formal_math/erdos257_period_noncollapse/odd_gap_scaling_receipt.json"
    )
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    blob = json.dumps(report, indent=2, sort_keys=True)
    Path(out).write_text(blob)
    print(f"wrote {out} sha256={hashlib.sha256(blob.encode()).hexdigest()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
