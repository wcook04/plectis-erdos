#!/usr/bin/env python3
"""Outcome-screened control for the socket census: does the shuffle measure arithmetic?

WHY THIS EXISTS (the analysis it is bound to)
---------------------------------------------
`erdos257_hole_geometry/notes/ResonanceOverlap.md` section 7 item 6 states a
general methodological rule that this lane never applied:

    "Band-matching by expected count is necessary but not sufficient.
     A control needs an OUTCOME screen as well as an EXPECTATION screen."

Every census in `CertificateSocketCollapse.md` sections 45/46/55 uses a
MARGINAL-PRESERVING SHUFFLE as its null.  That is an expectation screen: the
shuffled sequence has the same multiset of `tau_A` values, hence the same mean,
same variance, same everything about the marginal.  It was never outcome
screened -- I never asked WHY the control fires.

The socket clause is `2^k | tau_A(N+k)`.  ZERO IS DIVISIBLE BY EVERYTHING, so
every zero passes the clause FOR FREE at every k.  A shuffle preserves the
multiset, hence preserves the zero COUNT exactly.  So for a support whose
`tau_A` vanishes often, the control's socket run is a run of ZEROS -- a
deterministic consequence of the support's divisibility skeleton, carrying no
information about the arithmetic of the nonzero values.

Section 46 read the gap between observed and control as the real sequence being
"worse than chance".  If the zero-run account is right, that reading is wrong:
the control is high because the support has many zeros, not because the
arithmetic is anomalous.

PREDICTIONS, written before the run
-----------------------------------
Zero fractions follow from `tau_A = 1_A * 1` (the corpus's own definition):

    naturals A = N        tau = d(m) >= 1            z = 0
    primes   A = P        tau = omega(m), 0 at m=1   z ~ 1e-6
    powers2  A = {2^i}    tau = v_2(m), 0 on odds    z = 1/2
    pow3     A = {3^i}    tau = v_3(m)               z = 2/3
    ap3      A = 3N       tau = d(m/3) or 0          z = 2/3

P1. A PURE BERNOULLI(z) zero-indicator process -- carrying NO tau values at all,
    no arithmetic whatsoever -- reproduces the section-46 controls
    (powers2 17, pow3 31, ap3 33) to within +-4.
P2. It does NOT reproduce naturals 6 and primes 2, where z = 0 and the control
    genuinely measures divisibility of nonzero values.
P3. The ZERO-PINNED shuffle (control B: zeros held at their true positions,
    only the NONZERO values permuted among the nonzero positions) collapses the
    high controls toward the observed values, because it screens the free pass
    out of the null.

FALSIFIER, stated before the run: if P1 fails -- if Bernoulli(z) alone lands far
from the recorded controls -- then zero density is NOT the driver, the section-46
framing survives, and this correction is withdrawn.

WHAT THIS CANNOT DO: it cannot touch section 46's VERDICT.  The parity
obstruction `maxrun <= maxgap(Odd_A) - 1` is a proved theorem with a
machine-checked constructive core (`no_socketRun_of_odd_in_window`, axioms
[propext, Quot.sound]).  The control was decoration around a theorem.  What is
at stake is only the FRAMING -- the claim that these supports are "worse than
chance".

Bound directions, per the standing infrastructure rule:
  analysis -> here : ResonanceOverlap.md section 7 item 6 (the general rule)
                     CertificateSocketCollapse.md section 46 (what is corrected)
  here -> analysis : CertificateSocketCollapse.md section 60, receipt under state/
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]


def tau_tables(M: int):
    """tau_A(m) = #{a in A : a | m} for the five census cohorts, m in [1, M]."""
    out = {}

    d = [0] * (M + 1)
    for a in range(1, M + 1):
        for m in range(a, M + 1, a):
            d[m] += 1
    out["naturals"] = d[:]

    # primes: tau = omega (number of DISTINCT prime divisors)
    om = [0] * (M + 1)
    sieve = [True] * (M + 1)
    for p in range(2, M + 1):
        if sieve[p]:
            for m in range(p, M + 1, p):
                om[m] += 1
                if m > p:
                    sieve[m] = False
    out["primes"] = om

    # powers2 = {2^i : i >= 1}: tau = v_2.  (Fixed by the receipt: odd_count
    # 333333 = M/3 is exactly the density of v_2 odd, which forces i >= 1.)
    for name, b in (("powers2", 2), ("pow3", 3)):
        v = [0] * (M + 1)
        q = b
        while q <= M:
            for m in range(q, M + 1, q):
                v[m] += 1
            q *= b
        out[name] = v

    # ap3 = 3N: tau_A(m) = #{k>=1 : 3k | m} = d(m/3) if 3|m else 0
    a3 = [0] * (M + 1)
    for m in range(3, M + 1, 3):
        a3[m] = d[m // 3]
    out["ap3"] = a3

    return out


def max_socket_run(tau, nmax: int, cap: int) -> int:
    """Longest K with 2^k | tau(N+k) for k = 0..K-1, over N <= nmax."""
    best = 0
    for N in range(1, nmax + 1):
        k = 0
        while k < cap and N + k < len(tau):
            t = tau[N + k]
            if t & ((1 << k) - 1):  # 2^k does not divide t
                break
            k += 1
        if k > best:
            best = k
    return best


def bernoulli_zero_run(z: float, nmax: int, cap: int, rng: random.Random) -> int:
    """P1's null: NO arithmetic at all.  Position is 'zero' with prob z; a zero
    passes every socket clause for free, a nonzero fails immediately."""
    if z <= 0.0:
        return 0
    zero = [rng.random() < z for _ in range(nmax + cap + 2)]
    best = run = 0
    for i in range(1, nmax + cap + 1):
        run = run + 1 if zero[i] else 0
        if run > best:
            best = min(run, cap)
    return best


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--M", type=int, default=1000000)
    ap.add_argument("--nmax", type=int, default=500000)
    ap.add_argument("--cap", type=int, default=40)
    ap.add_argument("--seed", type=int, default=20260823)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    M, nmax, cap = args.M, args.nmax, args.cap
    rng = random.Random(args.seed)
    taus = tau_tables(M)

    # the section-46 controls, quoted from the landed receipt
    s46_control = {"naturals": 6, "primes": 2, "powers2": 17, "pow3": 31, "ap3": 33}
    s46_observed = {"naturals": 5, "primes": 2, "powers2": 3, "pow3": 5, "ap3": 8}

    report = {"M": M, "nmax": nmax, "cap": cap, "seed": args.seed, "cohorts": {}}
    for name, tau in taus.items():
        z = sum(1 for m in range(1, M + 1) if tau[m] == 0) / M

        # P1: pure Bernoulli(z), no arithmetic whatsoever
        bern = bernoulli_zero_run(z, nmax, cap, rng)

        # control B: ZERO-PINNED shuffle -- zeros stay put, nonzeros permuted
        pinned = tau[:]
        nz_pos = [m for m in range(1, M + 1) if tau[m] != 0]
        nz_val = [tau[m] for m in nz_pos]
        rng.shuffle(nz_val)
        for m, v in zip(nz_pos, nz_val):
            pinned[m] = v
        run_B = max_socket_run(pinned, nmax, cap)

        report["cohorts"][name] = {
            "zero_fraction": z,
            "s46_observed": s46_observed[name],
            "s46_control_full_shuffle": s46_control[name],
            "bernoulli_zero_only": bern,
            "control_B_zero_pinned": run_B,
            "P1_gap": abs(bern - s46_control[name]),
        }

    zc = [c for c in report["cohorts"].values() if c["zero_fraction"] > 0.1]
    zf = [c for c in report["cohorts"].values() if c["zero_fraction"] <= 0.1]
    report["P1_holds"] = all(c["P1_gap"] <= 4 for c in zc)
    report["P2_holds"] = all(c["bernoulli_zero_only"] < c["s46_control_full_shuffle"] for c in zf)
    report["P3_holds"] = all(
        c["control_B_zero_pinned"] < c["s46_control_full_shuffle"] for c in zc
    )
    report["falsifier_survived"] = report["P1_holds"]

    out = args.out or str(
        REPO / "state/formal_math/erdos257_period_noncollapse/zero_screened_control_receipt.json"
    )
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    blob = json.dumps(report, indent=2, sort_keys=True)
    Path(out).write_text(blob)

    print(f"M={M} nmax={nmax} cap={cap}")
    print(f"{'cohort':>9} {'z':>7} {'obs':>5} {'ctrlA':>6} {'bern':>6} {'ctrlB':>6} {'|A-bern|':>9}")
    for name, c in report["cohorts"].items():
        print(
            f"{name:>9} {c['zero_fraction']:>7.4f} {c['s46_observed']:>5} "
            f"{c['s46_control_full_shuffle']:>6} {c['bernoulli_zero_only']:>6} "
            f"{c['control_B_zero_pinned']:>6} {c['P1_gap']:>9}"
        )
    print(f"P1 (bernoulli reproduces ctrlA on zero-heavy) = {report['P1_holds']}")
    print(f"P2 (fails on zero-free cohorts)              = {report['P2_holds']}")
    print(f"P3 (zero-pinned control collapses)           = {report['P3_holds']}")
    print(f"wrote {out} sha256={hashlib.sha256(blob.encode()).hexdigest()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
