#!/usr/bin/env python3
"""Do the two mechanisms converge on one tuples hypothesis at the primes?  They do NOT.

WHY THIS EXISTS (the analysis it is bound to)
---------------------------------------------
`CertificateSocketCollapse.md` section 48 (cross-index T27b) reduced the last undecided
cohort to a single statement:

    the parity obstruction is vacuous at A = primes
      <=>  there exist arbitrarily long runs of consecutive integers with omega EVEN.

Section 27 recorded the transplant lane and the socket lane as INCOMPARABLE.  The
hypothesis under test here was that at the PRIMES they nevertheless bottom out in the same
Dickson / Hardy-Littlewood k-tuples conjecture that Pratt's Proposition 2.1 needs -- which
would explain why #69 resists two structurally different attacks for one reason.

THE PROPOSED CONSTRUCTION, AND WHY IT IS FALSE
----------------------------------------------
Proposed: pick distinct primes `p_1..p_K` all `> K`; by CRT choose `m` with
`m == -j + p_j (mod p_j^2)`, so `p_j || m+j` exactly; then require each `(m+j)/p_j` to be
prime, giving `omega(m+j) = 2` throughout.  The `K` cofactors are linear forms in the CRT
parameter, so simultaneous primality is a Dickson instance.

**It fails for `K >= 4`, elementarily.**  The construction forces every `m+j` to be a
product of exactly two primes, each to the FIRST power.  If `4 | m+j` then, since `p_j` is
odd, `4 | (m+j)/p_j`, so that cofactor is not prime.  One of any four consecutive integers
is `== 0 (mod 4)`.  Hence `K <= 3`, and `33 = 3*11`, `34 = 2*17`, `35 = 5*7` realises the
maximum.

THE OBVIOUS REPAIR ALSO FAILS
-----------------------------
`omega` ignores multiplicity, so the run can continue past a multiple of 4:
`36 = 2^2 * 3^2` has `omega = 2`, making `33..36` a run of FOUR consecutive `omega = 2`
integers.  So one may drop squarefreeness and ask for `omega = 2` throughout.  That is
capped too:

  * any 30 consecutive integers contain a multiple of `30 = 2*3*5`, which has
    `omega >= 3`.  **So `omega = 2` runs have length `<= 29`, unconditionally.**
  * any 6 consecutive integers contain a multiple of 6, and `omega = 2` there forces
    `2, 3 | n` with no third prime, i.e. `n = 2^a 3^b` -- a 3-SMOOTH number.  Those number
    `O(log^2 x)` up to `x`, so `omega = 2` runs of length `>= 6` are confined to windows
    straddling one of a very sparse set.

**Conclusion, stated before the run: arbitrarily long `omega`-even runs cannot come from a
fixed `omega` value.  They require `omega` to VARY over the window (2, 4, 6, ...), which is
not a clean `k`-tuples statement.  The hypothesised convergence does not go through by this
route.**  This probe measures the three routes separately so the claim is checkable and so
the weaker route is never confused with the stronger one.

PREDICTIONS, RECORDED BEFORE THE RUN
------------------------------------
  squarefree semiprimes  max run **exactly 3** -- a theorem (the mod-4 argument above),
                         first realised at 33.
  omega = 2              max run at least 4 (`33..36`), and `<= 29` unconditionally.
                         Predict the observed maximum is small, 4-7, and that every run of
                         length `>= 6` contains a 3-smooth multiple of 6.
  omega even             max run about 19 at `10^6`, matching section 48's
                         `maxgap(Odd_primes) = 20` (a gap of `g` is a run of `g-1`).
  CALIBRATOR `A = N`     `d(m)` is even iff `m` is NOT a square, so runs of `d`-even are the
                         gaps between consecutive squares: about `2 sqrt(M)`, i.e. ~1998 at
                         `10^6`.  Erdos 1948 lives in this row; it is enormous and must be,
                         and it is reported to keep the primes row in proportion.

FALSIFIER, stated before the run: (i) any run of 4 consecutive squarefree semiprimes, or
(ii) any run of 30 consecutive `omega = 2` integers.  Either refutes the elementary
arguments above and voids the section.

Bound directions, per the standing infrastructure rule:
  analysis -> here : CertificateSocketCollapse.md 27 (incomparability), 48 + T27b (the
                     reduction), T27c (a stalled max-statistic is not a bound)
  here -> analysis : CertificateSocketCollapse.md section 49, cross-index trap,
                     receipt under state/formal_math/erdos257_period_noncollapse/
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]


def factor_tables(M: int):
    """omega[n], squarefree-semiprime flag, and 3-smooth flag, for n <= M."""
    omega = [0] * (M + 1)
    maxexp = [0] * (M + 1)          # largest exponent in the factorisation
    for p in range(2, M + 1):
        if omega[p] == 0:            # p is prime
            for m in range(p, M + 1, p):
                omega[m] += 1
                e, t = 0, m
                while t % p == 0:
                    t //= p
                    e += 1
                if e > maxexp[m]:
                    maxexp[m] = e
    return omega, maxexp


def max_run(pred, M: int):
    best, best_at, cur, start = 0, None, 0, None
    for n in range(2, M + 1):
        if pred(n):
            if cur == 0:
                start = n
            cur += 1
            if cur > best:
                best, best_at = cur, start
        else:
            cur = 0
    return best, best_at


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max", type=int, default=1_000_000)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    M = args.max

    omega, maxexp = factor_tables(M)

    def is_sqfree_semiprime(n: int) -> bool:
        return omega[n] == 2 and maxexp[n] == 1

    def is_omega2(n: int) -> bool:
        return omega[n] == 2

    def is_omega_even(n: int) -> bool:
        return omega[n] % 2 == 0 and omega[n] > 0

    def is_three_smooth(n: int) -> bool:
        while n % 2 == 0:
            n //= 2
        while n % 3 == 0:
            n //= 3
        return n == 1

    rows = {}
    for name, pred in (("squarefree_semiprime", is_sqfree_semiprime),
                       ("omega_eq_2", is_omega2),
                       ("omega_even", is_omega_even)):
        run, at = max_run(pred, M)
        rows[name] = {"max_run": run, "starts_at": at}
        print(f"{name:>22}: max_run={run} starting at {at}")

    # every omega=2 run of length >= 6 must straddle a 3-smooth multiple of 6
    long_o2 = []
    cur, start = 0, None
    for n in range(2, M + 1):
        if is_omega2(n):
            if cur == 0:
                start = n
            cur += 1
        else:
            if cur >= 6:
                long_o2.append({"start": start, "length": cur,
                                "three_smooth_multiple_of_6": [
                                    x for x in range(start, start + cur)
                                    if x % 6 == 0 and is_three_smooth(x)]})
            cur = 0
    rows["omega_eq_2"]["runs_ge_6"] = long_o2

    # calibrator: A = N, d(m) even iff m is not a square
    import math
    r = math.isqrt(M)
    cal = (r * r) - ((r - 1) * (r - 1)) - 1
    rows["calibrator_naturals_d_even"] = {
        "max_run_between_consecutive_squares": cal,
        "note": "d(m) even iff m is not a square; Erdos 1948 lives in this row",
    }
    print(f"{'calibrator A=N':>22}: d-even run between last two squares = {cal}")

    ok = (rows["squarefree_semiprime"]["max_run"] <= 3
          and rows["omega_eq_2"]["max_run"] <= 29)
    report = {"max_n": M, "rows": rows, "falsifier_survived": ok}
    print(f"FALSIFIER (sqfree-semiprime <= 3 and omega=2 <= 29): "
          f"{'SURVIVED' if ok else 'BROKEN'}")

    out = args.out or str(
        REPO / "state/formal_math/erdos257_period_noncollapse/omega_even_run_routes_receipt.json"
    )
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    blob = json.dumps(report, indent=2, sort_keys=True)
    Path(out).write_text(blob)
    print(f"wrote {out} sha256={hashlib.sha256(blob.encode()).hexdigest()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
