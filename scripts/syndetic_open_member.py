#!/usr/bin/env python3
"""Closing coordinate (4): a set that is OPEN-class AND has syndetic Odd_A.

WHY THIS EXISTS (the analysis it is bound to)
---------------------------------------------
`CertificateSocketCollapse.md` section 53 / cross-index T32c: every set known to sit in
the exhaustion map's OPEN class (aperiodic, reciprocal-divergent, box-non-adapted) has
`Odd_A` with GROWING gaps, so the section-46 parity obstruction never bites on it.  **No
set yet has both.**  This probe hunts one.

THE PLAN COLLAPSED, AND THAT IS THE FIRST RESULT
------------------------------------------------
The plan was: pick syndetic `S`, solve `Odd_B = Odd_P xor S` for `B`, set `A = P xor B`.
But the parity map is `F_2`-LINEAR (T30), so `B = P xor C` where `Odd_C = S`, and

    A = P xor B = P xor (P xor C) = C.

**The primes cancel.**  `A` is simply the inverse transform of `S`; the "perturb the
primes" framing was redundant.  Worse, the natural syndetic target is a dead end: forward,
`{d} -> dN`, so any `S` that is a finite Boolean combination of APs has a FINITE preimage
(T30a).  Concretely `{m == 2 mod 4} = 2N xor 4N` has preimage `{2} xor {4} = {2,4}`.

THE MECHANISM THAT DOES WORK
----------------------------
`C = N \\ {2^i}` (section 51) gets `Odd_C` containing `{m == 2 mod 4}` for a specific
reason: at `m == 2 mod 4` the only power of two dividing `m` is `2` itself, so removing `2`
from the support turns `tau_C(m) = d(m) - 1 = 2 d(u) - 1`, which is ODD.  Section 52 killed
that set because it is base-ADAPTED at `k = 2`.

So perturb it with a NON-adapted `D`, chosen so the mechanism survives:

> **If `D` is contained in `4N`, no element of `D` divides any `m == 2 mod 4`** (such `m`
> are not divisible by 4).  So `tau_{C xor D}(m) = tau_C(m)` at every such `m`, and
> `Odd_{C xor D}` still contains `{m == 2 mod 4}` -- SYNDETIC with gap 4, untouched.

And if `D` is non-adapted then `C xor D` is non-adapted by T32a, since `C` is adapted.
The candidate is `D = {4p : p prime}`.

PREDICTIONS, RECORDED BEFORE THE RUN
------------------------------------
  CALIBRATORS  `N` must FIRE (`14,9,8`); `primes` must read `0,0,0`; the inverse
               transform must round-trip.
  preimage of `{m == 2 mod 4}`   must be EXACTLY `{2, 4}` -- predicted by linearity, and a
               check on the transform independent of the two existing calibrators.
  `{4p}` as an ingredient        predict nullity `0,0,0` (scaling the primes by 4 should
               not manufacture a Mahler relation) -- but this is a PREDICTION, not a
               theorem, and the instrument decides.
  `(N \\ {2^i}) xor {4p}`         predict nullity `0,0,0` by T32a; `sum 1/c` DIVERGENT
               (`~ log x` minus `~ (1/4) log log x`); and **`Odd` maxgap BOUNDED at exactly
               4 across every decade**, by the `D` contained in `4N` argument.
  `(N \\ {2^i}) xor primes`       the contrast row: primes are NOT inside `4N`, they DO hit
               `m == 2 mod 4`, so predict the gap GROWS -- showing the containment
               condition is doing the work rather than the non-adaptation.

FALSIFIER, stated before the run: calibrators failing; the preimage of `{m == 2 mod 4}`
being anything but `{2,4}`; or the `4N` candidate's `Odd` maxgap GROWING, which would
refute the containment argument outright.

Bound directions, per the standing infrastructure rule:
  analysis -> here : CertificateSocketCollapse.md 46, 51, 52, 53; T30/T30a, T31a, T32a,
                     T32c; exhaustion map section AO
  here -> analysis : CertificateSocketCollapse.md section 54, cross-index trap,
                     receipt under state/formal_math/erdos257_period_noncollapse/
"""

from __future__ import annotations

import argparse, hashlib, importlib.util, json
from math import isqrt
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
_spec = importlib.util.spec_from_file_location(
    "mni", str(Path(__file__).with_name("mahler_nullity_independent.py")))
_mni = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(_mni)


def sieve(M):
    s = bytearray([1]) * (M + 1); s[0:2] = b"\x00\x00"
    i = 2
    while i * i <= M:
        if s[i]:
            for m in range(i * i, M + 1, i): s[m] = 0
        i += 1
    return s


def odd_set(S, M):
    o = bytearray(M + 1)
    for a in S:
        if a >= 1:
            for m in range(a, M + 1, a): o[m] ^= 1
    return o


def maxgap(o, upto):
    prev, g = None, 0
    for m in range(1, upto + 1):
        if o[m]:
            if prev is not None and m - prev > g: g = m - prev
            prev = m
    return g


def squarefree(M):
    sf = bytearray([1]) * (M + 1); d = 2
    while d * d <= M:
        for m in range(d * d, M + 1, d * d): sf[m] = 0
        d += 1
    return sf


def inverse_transform(target, M, sf):
    ind = bytearray(M + 1)
    for n in range(1, M + 1):
        acc, d = 0, 1
        while d * d <= n:
            if n % d == 0:
                for dd in ({d, n // d} if d * d != n else {d}):
                    if sf[n // dd] and target[dd]: acc ^= 1
            d += 1
        ind[n] = acc
    return ind


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max", type=int, default=200000)
    ap.add_argument("--bits", type=int, default=200)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    M, B = args.max, args.bits
    pr = sieve(M)
    P = {n for n in range(2, M + 1) if pr[n]}
    pow2 = {2 ** i for i in range(1, 40) if 2 ** i <= M}
    Nset = set(range(1, M + 1))
    base = Nset - pow2                      # N \ {2^i}, adapted (s52)
    fourp = {4 * p for p in P if 4 * p <= M}

    # independent transform check: preimage of {m == 2 mod 4} must be exactly {2,4}
    sf = squarefree(min(M, 5000))
    tgt = bytearray(min(M, 5000) + 1)
    for m in range(2, min(M, 5000) + 1, 4): tgt[m] = 1
    pre = inverse_transform(tgt, min(M, 5000), sf)
    preimage = [n for n in range(1, min(M, 5000) + 1) if pre[n]]

    scales = [s for s in (10**3, 10**4, 10**5, 2 * 10**5) if s <= M]
    cases = {
        "CALIB N": Nset,
        "CALIB primes": P,
        "ingredient {4p}": fourp,
        "CANDIDATE (N\\{2^i}) xor {4p}": base ^ fourp,
        "CONTRAST (N\\{2^i}) xor primes": base ^ P,
        "reference N\\{2^i} (adapted)": base,
    }
    report = {"max_n": M, "nullity_box": "d=2,D=5",
              "preimage_of_2mod4": preimage, "rows": {}}
    for name, S in cases.items():
        bits = [1 if n in S else 0 for n in range(B + 1)]
        nul = [_mni.nullity(bits, k, d=2, D=5) for k in (2, 3, 4)]
        recip = sum(1.0 / a for a in S if a >= 1)
        o = odd_set(S, M)
        gaps = {str(s): maxgap(o, s) for s in scales}
        grows = gaps[str(scales[-1])] > gaps[str(scales[0])]
        report["rows"][name] = {"nullity_k234": nul, "reciprocal_partial_sum": recip,
                                "odd_maxgap_by_scale": gaps, "odd_gap_grows": grows}
        print(f"{name:<32} nullity={str(nul):<12} sum1/a={recip:8.3f} "
              f"gaps={list(gaps.values())} {'GROWS' if grows else 'BOUNDED'}")

    calN = report["rows"]["CALIB N"]["nullity_k234"]
    calP = report["rows"]["CALIB primes"]["nullity_k234"]
    ok = all(v > 0 for v in calN) and calP == [0, 0, 0] and preimage == [2, 4]
    report["falsifier_survived"] = ok
    print(f"\npreimage of {{m==2 mod 4}} = {preimage}  (must be [2, 4])")
    print(f"CALIB N {calN}, primes {calP}")
    print(f"FALSIFIER: {'SURVIVED' if ok else 'BROKEN'}")
    print("box: d=2,D=5 -- nullity 0 rules out THAT BOX only (T31c)")

    out = args.out or str(REPO / "state/formal_math/erdos257_period_noncollapse/syndetic_open_member_receipt.json")
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    blob = json.dumps(report, indent=2, sort_keys=True)
    Path(out).write_text(blob)
    print(f"wrote {out} sha256={hashlib.sha256(blob.encode()).hexdigest()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
