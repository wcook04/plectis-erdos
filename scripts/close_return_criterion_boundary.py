#!/usr/bin/env python3
"""The machine-checked close-return criterion cannot reach the open regime.

WHAT IS BEING TESTED
--------------------
`Erdos257PeriodNoncollapse/ReciprocalSupportIrrationality.lean:938` proves, with
`sorry = 0` and `axiom = 0` in its whole declaring chain:

    theorem irrational_erdosSupportSeries_two_of_infinite_of_shiftedAtom_closeReturn
        (A : Set N) (hA : A.Infinite)
        (hclose : forall eps > 0, exists N > 0,
           (sum_d shiftedSupportAtom A N d) < (sum_d shiftedSupportAtom A 0 d) + eps) :
        Irrational (erdosSupportSeries 2 A)

and its docstring is explicit: "no summability-to-return theorem is assumed here".
Summability is only one PRODUCER of `hclose` (line 957).  With

    shiftedMersenneAtom N d = 2^(N mod d) / (2^d - 1)          (line 21)
    Phi_A(N) = sum_{d in A} 2^(N mod d) / (2^d - 1),  Phi_A(0) = y

Erdos 257 therefore follows, for EVERY infinite A, from the cofinal return

    inf_{N >= 1} Phi_A(N) = Phi_A(0).

So the obvious next move is to hunt a producer of `hclose` for harmonically
divergent A.  THIS SCRIPT SHOWS THAT MOVE IS DEAD.

THE OBSTRUCTION (proved, then measured)
---------------------------------------
Let a+(N) = min{a in A : a > N}.  For d = a+(N) we have N mod d = N, so that one
term contributes 2^(N mod d)/(2^d - 1) = (2^N - 1 + 1)/(2^d - 1) against
1/(2^d - 1) at N = 0, an excess of

    (2^N - 1) / (2^(a+(N)) - 1)  ~  2^(-(a+(N) - N)).

Hence if the gaps of A above N are bounded by G, then Phi_A(N) - Phi_A(0) is
bounded below by roughly 2^-G for EVERY N, and `hclose` FAILS.  Equivalently:

    hclose  ==>  a+(N) - N -> infinity  ==>  A has density zero.

For A = N the bound is exact at N = 1: every d >= 2 has 1 mod d = 1, so
Phi(1) - Phi(0) = sum_{d>=2} 1/(2^d - 1) = E - 1 = T_1 = 0.6066951...

CONSEQUENCE
-----------
`hclose` is sufficient but NOT necessary: A = N has E irrational (Erdos 1948)
while `hclose` fails there outright.  The criterion is structurally confined to
sparse supports, so **strengthening the producer cannot extend the Lean route**.
Reaching the open positive-density regime needs a different CRITERION, not a
better producer.

Bound directions:
  analysis -> here : ReciprocalSupportIrrationality.lean lines 21, 26, 938, 957
  here -> analysis : Erdos257/DivisorTransformRecovery.md section 8, receipt under state/
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]


def Phi(A, N: int, cap: int) -> F:
    return sum((F(2 ** (N % d), 2 ** d - 1) for d in A if 1 <= d <= cap), F(0))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--cap", type=int, default=220)
    ap.add_argument("--nmax", type=int, default=120)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    cap, nmax = args.cap, args.nmax

    families = {
        "all_naturals":        (set(range(1, cap + 1)), "divergent"),
        "evens":               ({d for d in range(2, cap + 1, 2)}, "divergent"),
        "odds":                ({d for d in range(1, cap + 1, 2)}, "divergent"),
        "one_mod_three":       ({d for d in range(1, cap + 1) if d % 3 == 1}, "divergent"),
        "zero_mod_seven":      ({d for d in range(7, cap + 1, 7)}, "divergent"),
        "powers_of_two":       ({2 ** k for k in range(1, 8)}, "summable"),
        "squares":             ({k * k for k in range(1, 15)}, "summable"),
    }

    rows = []
    for name, (A, kind) in families.items():
        p0 = Phi(A, 0, cap)
        vals = [(float(Phi(A, N, cap) - p0), N) for N in range(1, nmax + 1)]
        gap, argmin = min(vals)
        tail_min = min(v for v, N in vals if N >= nmax // 2)   # large-N regime
        srt = sorted(d for d in A if d <= cap)
        max_gap = max((b - a for a, b in zip(srt, srt[1:])), default=1)
        rows.append({"family": name, "reciprocal_sum": kind,
                     "min_excess": float(gap), "argmin_N": argmin,
                     "tail_min": tail_min, "max_gap": max_gap,
                     "close_return_possible": float(gap) < 1e-3})
        print(f"{name:>18} [{kind:>9}]  min={float(gap):.6f} (N={argmin:>3})  "
              f"large-N min={tail_min:.6f}  gap G={max_gap}  2^-G={2.0**-max_gap:.6f}")

    # The prediction is ASYMPTOTIC, not about the global min: with gaps bounded by
    # G, the single term at d = a+(N) forces excess >= (2^N - 1)/(2^(N+G) - 1),
    # which tends to 2^-G.  Small N can dip below that (2^N - 1 is small there),
    # so the right check is the tail of the N range against 2^-G.
    ok = True
    for r in rows:
        if r["reciprocal_sum"] != "divergent":
            continue
        floor = 2.0 ** (-r["max_gap"])
        r["predicted_floor_2^-G"] = floor
        r["tail_min_excess"] = r["tail_min"]
        r["matches_prediction"] = r["tail_min"] >= 0.9 * floor
        ok &= r["matches_prediction"]
    sum_max = max(r["min_excess"] for r in rows if r["reciprocal_sum"] == "summable")
    verdict = ("criterion separates: every bounded-gap (divergent) family is pinned at "
               "its 2^-G floor for large N, every summable family reaches ~0"
               if ok and sum_max < 1e-3 else "PREDICTION NOT MATCHED")
    report = {"cap": cap, "nmax": nmax, "families": rows,
              "max_excess_over_summable_families": sum_max,
              "every_bounded_gap_family_pinned_at_2^-G": all(
                  r.get("matches_prediction", True) for r in rows),
              "verdict": verdict}
    out = args.out or str(
        REPO / "state/formal_math/erdos257_period_noncollapse/close_return_boundary_receipt.json"
    )
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    blob = json.dumps(report, indent=2, sort_keys=True)
    Path(out).write_text(blob)
    print(f"\n{verdict}")
    print(f"wrote {out} sha256={hashlib.sha256(blob.encode()).hexdigest()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
