#!/usr/bin/env python3
"""Explicit members of the exhaustion map's OPEN class -- and a correction to section 52.

WHY THIS EXISTS (the analysis it is bound to)
---------------------------------------------
The exhaustion map (`docs/formal_math/erdos257_computational_exhaustion_map_2026_08_22.md`
section AO) splits supports into SOLVED (i) eventually periodic, (ii) base-adapted with
`Y_A` Mahler, (iii) reciprocal-summable (machine-checked at
`ReciprocalSupportIrrationality.lean:1013`), and OPEN = aperiodic and not base-adapted.
Section 51 built `A = N \\ {2^i}` as a candidate; section 52 killed it -- base-adapted at
`k = 2` -- and recorded T31a: XOR from ADAPTED pieces can never escape class (ii).

TWO ALGEBRAIC POINTS, DERIVED BEFORE THIS RUN
---------------------------------------------
**The dual of T31a, which says the construction CAN work.**  Mahler-adapted functions at a
fixed `k` form a MODULE: relations for `Y_1` and `Y_2` combine into one for `Y_1 +- Y_2`
at higher order.  So if `B` is adapted at `k` and `P xor B` were adapted at `k`, then
`P = (P xor B) xor B` would be adapted too.  Contrapositive:

    P NOT adapted at k   =>   P xor B NOT adapted at k, for every adapted B.

So a non-adapted ingredient SURVIVES xor-ing with adapted material.  (Caveat T31c: the
instrument certifies non-adaptation only inside its box, and this argument needs genuine
non-adaptation at all orders.)

**A correction section 53 owes section 52.**  Section 52 closed with "I currently have no
explicit member of the open class".  That is WRONG.  The primes are aperiodic, have
`sum 1/p = infinity` (so not class iii), and read nullity `0,0,0` (so not base-adapted in
the box) -- they satisfy every coordinate.  **The primes ARE an explicit named member**,
and the corpus has always known it; they are exactly Erdos #69.  What I lack is a member
OTHER than the primes, which is what this probe hunts.

PREDICTIONS, RECORDED BEFORE THE RUN
------------------------------------
  CALIBRATORS   `N` must FIRE (`14, 9, 8` per section AN / T31b); `primes` must read
                `0,0,0`.  Either failing voids the run.
  primes xor {2^i}    = odd primes together with the powers of two.  `{2^i}` is adapted,
                so by the dual argument predict nullity **0,0,0**; `sum 1/a` diverges;
                aperiodic.  A member OTHER than the primes if it holds.
  primes xor 3N       `3N` is periodic hence adapted; predict **0,0,0**, divergent.
  primes xor {n^2}    squares' adaptation status is NOT known to me -- tested here as an
                ingredient in its own right before the xor is interpreted.
  primes xor {2^(2^k)}  BOTH ingredients are non-adapted, so NO theorem applies and the
                verdict is genuinely uncertain.  This is the interesting row.
  primes minus {p = 1 mod 4}  still divergent by Dirichlet; predict `0,0,0`.
  Odd_A maxgap  predict GROWING (unbounded) for every candidate, so the section-46 parity
                obstruction does NOT bite on any of them -- i.e. the socket route stays
                available and coordinate (4) fails throughout.  Measured over DECADES
                (T27a), never at one `M`.

FALSIFIER, stated before the run: `N` failing to fire, or `primes` reading anything but
`0,0,0`.  Either means the instrument is misread and no conclusion may be drawn.

Bound directions, per the standing infrastructure rule:
  analysis -> here : exhaustion map section AO; CertificateSocketCollapse.md 7, 46, 51, 52;
                     cross-index T31a/T31b/T31c
  here -> analysis : CertificateSocketCollapse.md section 53, cross-index trap,
                     receipt under state/formal_math/erdos257_period_noncollapse/
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from math import isqrt
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]

_spec = importlib.util.spec_from_file_location(
    "mni", str(Path(__file__).with_name("mahler_nullity_independent.py")))
_mni = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mni)


def sieve(M):
    s = bytearray([1]) * (M + 1)
    s[0:2] = b"\x00\x00"
    i = 2
    while i * i <= M:
        if s[i]:
            for m in range(i * i, M + 1, i):
                s[m] = 0
        i += 1
    return s


def build_sets(M, pr):
    P = {n for n in range(2, M + 1) if pr[n]}
    pow2 = {2 ** i for i in range(1, 40) if 2 ** i <= M}
    sq = {n * n for n in range(1, isqrt(M) + 1)}
    ap3 = {n for n in range(3, M + 1, 3)}
    dd = {2 ** (2 ** k) for k in range(0, 7) if 2 ** (2 ** k) <= M}
    p1mod4 = {p for p in P if p % 4 == 1}
    return {
        "CALIB N (must fire)": set(range(1, M + 1)),
        "CALIB primes (must be 0,0,0)": P,
        "ingredient {n^2}": sq,
        "ingredient 3N": ap3,
        "primes xor {2^i}": P ^ pow2,
        "primes xor 3N": P ^ ap3,
        "primes xor {n^2}": P ^ sq,
        "primes xor {2^(2^k)}": P ^ dd,
        "primes minus {p=1 mod 4}": P - p1mod4,
    }


def tau_parity_gaps(S, M, scales):
    """maxgap of Odd_A over each scale."""
    odd = bytearray(M + 1)
    for a in S:
        if a >= 1:
            for m in range(a, M + 1, a):
                odd[m] ^= 1
    out = {}
    for sc in scales:
        prev, gap = None, 0
        for m in range(1, sc + 1):
            if odd[m]:
                if prev is not None and m - prev > gap:
                    gap = m - prev
                prev = m
        out[str(sc)] = gap
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max", type=int, default=100000)
    ap.add_argument("--bits", type=int, default=200)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    M, B = args.max, args.bits
    pr = sieve(M)
    sets = build_sets(M, pr)
    scales = [s for s in (10**3, 10**4, 10**5) if s <= M]

    report = {"max_n": M, "nullity_box": "d=2, D=5", "bits": B, "rows": {}}
    for name, S in sets.items():
        bits = [1 if n in S else 0 for n in range(B + 1)]
        nul = [_mni.nullity(bits, k, d=2, D=5) for k in (2, 3, 4)]
        recip = sum(1.0 / a for a in S if a >= 1)
        gaps = tau_parity_gaps(S, M, scales)
        grows = gaps[str(scales[-1])] > gaps[str(scales[0])]
        report["rows"][name] = {
            "nullity_k234": nul, "reciprocal_partial_sum": recip,
            "odd_maxgap_by_scale": gaps, "odd_gap_grows": grows,
            "size": len(S),
        }
        print(f"{name:<30} nullity={str(nul):<12} sum1/a={recip:7.3f} "
              f"Odd_gaps={list(gaps.values())} {'GROWS' if grows else 'BOUNDED'}")

    calN = report["rows"]["CALIB N (must fire)"]["nullity_k234"]
    calP = report["rows"]["CALIB primes (must be 0,0,0)"]["nullity_k234"]
    ok = all(v > 0 for v in calN) and calP == [0, 0, 0]
    report["falsifier_survived"] = ok
    print(f"\nCALIB N fires: {calN}   CALIB primes: {calP}")
    print(f"FALSIFIER: {'SURVIVED' if ok else 'BROKEN'}")
    print("box: d=2, D=5 -- nullity 0 rules out THAT BOX only (T31c)")

    out = args.out or str(
        REPO / "state/formal_math/erdos257_period_noncollapse/open_class_member_search_receipt.json")
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    blob = json.dumps(report, indent=2, sort_keys=True)
    Path(out).write_text(blob)
    print(f"wrote {out} sha256={hashlib.sha256(blob.encode()).hexdigest()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
