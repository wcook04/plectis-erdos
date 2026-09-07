#!/usr/bin/env python3
"""The parity map A -> Odd_A is a BIJECTION over F_2 -- so what does a syndetic Odd_A cost?

WHY THIS EXISTS (the analysis it is bound to)
---------------------------------------------
`CertificateSocketCollapse.md` section 46 proved the parity obstruction
`maxrun <= maxgap(Odd_A) - 1` with `Odd_A = {m : tau_A(m) odd}`, and section 50 / T29c
called it a FOURTH orthogonal coordinate on the exhaustion map.  Section 50 also recorded
that the map's OPEN class is "aperiodic and not base-adapted", and that reciprocal-summable
sets are already SOLVED (class iii, machine-checked at
`ReciprocalSupportIrrationality.lean:1013`), so a counterexample needs
`sum_{a in A} 1/a = infinity`.

The decisive question for my own claim: **on the open class, is the parity coordinate
non-vacuous?**  If `sum 1/a = infinity` forced `Odd_A` to have unbounded gaps, the
obstruction would never bite where the problem is open and T29c would be worth much less
than claimed.

THE ALGEBRA (derived first; the run is a check, not the source)
--------------------------------------------------------------
`tau_A = 1_A * 1` in Dirichlet convolution.  Over `F_2` convolution by the constant-one
function is INVERTIBLE, with inverse convolution by the Moebius function, and
`mu(n) = 1 (mod 2)` exactly when `n` is squarefree.  Hence

    1_A(n)  ==  sum_{d | n, n/d squarefree} tau_A(d)   (mod 2).

**So for ANY target set `S` there is exactly one `A` with `Odd_A = S`.**  The parity map is
a bijection on subsets of `N`; it constrains nothing about `A` by itself.  A syndetic
`Odd_A` is therefore always achievable, and the only question is WHICH CLASS the realising
`A` falls into -- periodic (solved i), base-adapted (solved ii), reciprocal-summable
(solved iii), or the open region.

PREDICTIONS, RECORDED BEFORE THE RUN
------------------------------------
  CALIBRATOR 1  feeding `S = {perfect squares}` must return **`A = N`** exactly, because
                `d(m)` is odd iff `m` is a square.  Any deviation refutes the transform.
  CALIBRATOR 2  feeding `S = {m : v_2(m) odd}` must return **`A = {2,4,8,16,...}`**
                exactly, because `tau_{2^i} = v_2`.  Two independent exact checks.
  ROUND TRIP    for every target `S`, recomputing `tau_A` from the derived `A` must
                reproduce `S` exactly on `[1, M]`.  This is the falsifier.
  S = 2N        (syndetic, gap 2).  Predict the realising `A` has POSITIVE DENSITY, hence
                `sum 1/a = infinity` -- which would put a syndetic `Odd_A` inside the
                divergent class and make the parity coordinate non-vacuous there.
  S = 3N        (syndetic, gap 3).  Same prediction.
  PERIODICITY   the realising `A` for a periodic `S` is the live risk: if `A` comes out
                EVENTUALLY PERIODIC it is solved class (i), and the example never reaches
                the OPEN class -- in which case the parity coordinate is still unproven
                there and I must say so.  Tested by checking `1_A` against every period
                `r <= 64` on a tail window.

FALSIFIER, stated before the run: (i) either calibrator returning anything but `N` and
`{2^i}`; or (ii) any round-trip mismatch.  Either voids the section.

Bound directions, per the standing infrastructure rule:
  analysis -> here : CertificateSocketCollapse.md 46 (parity), 50 + T29a/T29c (the map,
                     the frame correction), exhaustion map section AO
  here -> analysis : CertificateSocketCollapse.md section 51, cross-index trap,
                     receipt under state/formal_math/erdos257_period_noncollapse/
"""

from __future__ import annotations

import argparse
import hashlib
import json
from math import isqrt
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]


def squarefree_flags(M: int):
    sf = bytearray([1]) * (M + 1)
    d = 2
    while d * d <= M:
        sq = d * d
        for m in range(sq, M + 1, sq):
            sf[m] = 0
        d += 1
    return sf


def invert_parity(target, M: int, sf):
    """1_A(n) = sum_{d|n, n/d squarefree} 1_S(d)  (mod 2)."""
    ind = bytearray(M + 1)
    for n in range(1, M + 1):
        acc = 0
        d = 1
        while d * d <= n:
            if n % d == 0:
                for dd in ({d, n // d} if d * d != n else {d}):
                    if sf[n // dd] and target[dd]:
                        acc ^= 1
            d += 1
        ind[n] = acc
    return ind


def tau_parity(ind, M: int):
    """Odd_A from A: tau_A(m) mod 2."""
    out = bytearray(M + 1)
    for a in range(1, M + 1):
        if ind[a]:
            for m in range(a, M + 1, a):
                out[m] ^= 1
    return out


def eventually_periodic(ind, M: int, max_r: int = 64):
    """Smallest r <= max_r such that 1_A is r-periodic on the top half; None if none."""
    lo = M // 2
    for r in range(1, max_r + 1):
        if all(ind[n] == ind[n + r] for n in range(lo, M - r)):
            return r
    return None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max", type=int, default=20000)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    M = args.max
    sf = squarefree_flags(M)

    def mk(pred):
        t = bytearray(M + 1)
        for m in range(1, M + 1):
            if pred(m):
                t[m] = 1
        return t

    def v2odd(m):
        v = 0
        while m % 2 == 0:
            m //= 2
            v += 1
        return v % 2 == 1

    targets = {
        "CALIB_squares": mk(lambda m: isqrt(m) ** 2 == m),
        "CALIB_v2_odd": mk(v2odd),
        "S_2N": mk(lambda m: m % 2 == 0),
        "S_3N": mk(lambda m: m % 3 == 0),
        "S_all": mk(lambda m: True),
    }

    report = {"max_n": M, "targets": {}}
    ok = True
    for name, tgt in targets.items():
        ind = invert_parity(tgt, M, sf)
        back = tau_parity(ind, M)
        round_trip = all(back[m] == tgt[m] for m in range(1, M + 1))
        members = [n for n in range(1, M + 1) if ind[n]]
        dens = len(members) / M
        recip = sum(1.0 / n for n in members)
        per = eventually_periodic(ind, M)
        row = {
            "round_trip_exact": round_trip,
            "A_first_20": members[:20],
            "A_count": len(members),
            "A_density": dens,
            "reciprocal_partial_sum": recip,
            "eventually_periodic_period": per,
        }
        report["targets"][name] = row
        ok = ok and round_trip
        print(f"{name:>14}: round_trip={round_trip}  |A|={len(members)} dens={dens:.4f}  "
              f"sum1/a={recip:.4f}  period={per}  first={members[:8]}")

    c1 = report["targets"]["CALIB_squares"]["A_first_20"] == list(range(1, 21))
    powers2 = [2 ** i for i in range(1, 15) if 2 ** i <= M]
    c2 = report["targets"]["CALIB_v2_odd"]["A_first_20"][:len(powers2)] == powers2
    report["calibrator_squares_gives_N"] = c1
    report["calibrator_v2odd_gives_powers_of_2"] = c2
    ok = ok and c1 and c2
    report["falsifier_survived"] = ok
    print(f"CALIB squares -> A = N: {c1}")
    print(f"CALIB v2-odd  -> A = powers of 2: {c2}")
    print(f"FALSIFIER: {'SURVIVED' if ok else 'BROKEN'}")

    out = args.out or str(
        REPO / "state/formal_math/erdos257_period_noncollapse/parity_inverse_transform_receipt.json"
    )
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    blob = json.dumps(report, indent=2, sort_keys=True)
    Path(out).write_text(blob)
    print(f"wrote {out} sha256={hashlib.sha256(blob.encode()).hexdigest()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
