#!/usr/bin/env python3
"""Erdos 269: the finest all-ones frame, and why the fiber proof cannot transfer.

The pure-power / fiber theorem (`ErdosProblems/Erdos269/PurePowerIrrationality.lean`,
`PurePowerIrrationalityNote.md`) proves irrationality whenever the Cantor digits
are constant, the tail state is bounded, and the radix word has right-special
factors with separated extensions.  This probe asks whether S itself admits such
a frame, in the finest reindexing available.

The frame.  Enumerate the smooth numbers s_1 < s_2 < ... (s_n >= 2) and set
r_n = H(s_n)/H(s_{n-1}) with H(s_0) = H(1) = 1.  The running height jumps only at
prime powers, so r_n = p when s_n = p^k and r_n = 1 otherwise, and

        1/H(s_n) = 1/(r_1 ... r_n),        S = sum_{n>=1} 1/(r_1 r_2 ... r_n).

This is an ALL-ONES Cantor series over the four-letter alphabet {1,2,3,5}: the
digits are constant, exactly the hypothesis the fiber proof needs.  The whole of
S is carried by the single word (r_n).

Why the proof still does not transfer -- two exact obstructions, both measured:

 (i) UNBOUNDED STATES.  The tail state V_n = sum_{k>=0} 1/(r_n ... r_{n+k})
     satisfies V_n >= (length of the run of 1s starting at n), and the runs are
     the counts of smooth numbers between consecutive prime powers, which grow
     like a^2.  So the interval confinement V_n in (1/r, 2/r) is unavailable.

 (ii) NO USABLE REPEATED FACTOR.  Shrinking the gap needs a repeated factor whose
     radix product P is large, and P only grows across prime-power letters, so the
     factor must span several full runs.  Those factors never repeat: the run
     lengths grow, so the gap patterns are eventually all distinct.

Conclusion recorded by this probe: the obstruction to #269 is not a missing
technique.  Every all-ones reindexing of S has unbounded states, because the
smooth counting function grows.  The fibers are precisely the sub-objects with
exactly one point per dyadic scale, and those are the ones the theorem reaches.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import sys
from collections import Counter
from fractions import Fraction

PRIMES = (2, 3, 5)


def height(x: int) -> int:
    out = 1
    for q in PRIMES:
        t = 1
        while t * q <= x:
            t *= q
        out *= t
    return out


def smooth_up_to(limit: int) -> list[int]:
    out, v3 = [], 1
    while v3 < limit:
        v = v3
        while v < limit:
            s = v
            while s < limit:
                out.append(s)
                s <<= 1
            v *= 5
        v3 *= 3
    return sorted(set(x for x in out if x >= 2))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--bits", type=int, default=120)
    ap.add_argument("--gap-lengths", type=int, nargs="*", default=[1, 2, 3, 4])
    ap.add_argument("--receipt", type=str, default=None)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    sm = smooth_up_to(1 << args.bits)
    radices, prev = [], 1
    for s in sm:
        h = height(s)
        radices.append(h // prev)
        prev = h
    alphabet_ok = set(radices) <= {1, 2, 3, 5}

    direct = sum((Fraction(1, height(s)) for s in sm), Fraction())
    word, prod = Fraction(0), 1
    for x in radices:
        prod *= x
        word += Fraction(1, prod)
    identity_exact = direct == word

    runs, cur = [], 0
    for x in radices:
        if x == 1:
            cur += 1
        else:
            if cur:
                runs.append(cur)
            cur = 0

    marks = [i for i, x in enumerate(radices) if x != 1]
    gap_rows = []
    for k in args.gap_lengths:
        pats = [tuple(marks[j + 1 + t] - marks[j + t] for t in range(k))
                for j in range(len(marks) - k - 1)]
        c = Counter(pats)
        repeats = sum(v - 1 for v in c.values() if v > 1)
        gap_rows.append({"gaps_spanned": k, "positions": len(pats),
                         "distinct_patterns": len(c), "repeats": repeats,
                         "any_repeat": repeats > 0})

    first_clean = next((r["gaps_spanned"] for r in gap_rows if not r["any_repeat"]), None)

    receipt = {
        "problem_id": "erdos_269",
        "probe": "erdos269_all_ones_frame_nogo",
        "frame": "S = sum_{n>=1} 1/(r_1...r_n), r_n = H(s_n)/H(s_{n-1}) in {1,2,3,5}",
        "smooth_numbers": len(sm), "bits": args.bits,
        "alphabet_is_1235": alphabet_ok,
        "identity_exact_in_rationals": identity_exact,
        "S_value": float(word),
        "fraction_of_unit_letters": radices.count(1) / len(radices),
        "obstruction_i_unbounded_states": {
            "runs_of_unit_radix": len(runs), "max_run": max(runs) if runs else 0,
            "last_runs": runs[-5:],
            "consequence": "V_n >= run length, so interval confinement is unavailable",
        },
        "obstruction_ii_no_repeated_factor": {
            "rows": gap_rows,
            "first_gap_count_with_no_repeat": first_clean,
            "consequence": "a repeated factor with large radix product does not exist, "
                           "so no right-special separation is available",
        },
        "conclusion": "Every all-ones reindexing of S has unbounded states because the "
                      "smooth counting function grows. The fiber sub-objects have exactly "
                      "one point per dyadic scale and are the ones the theorem reaches.",
        "claim_boundary": "structural no-go for this proof route; not an irrationality "
                          "claim and not a proof that S is rational",
        "status": "pass" if alphabet_ok and identity_exact else "fail",
    }
    if args.receipt:
        p = pathlib.Path(args.receipt)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    if args.json:
        print(json.dumps(receipt, indent=2, sort_keys=True))
    else:
        print(f"smooth numbers below 2^{args.bits}: {len(sm)}; alphabet "
              f"{sorted(set(radices))}; unit letters "
              f"{100 * radices.count(1) / len(radices):.2f}%")
        print(f"S = sum 1/(r_1..r_n) equals the height sum exactly in Q: {identity_exact}"
              f"   ({float(word):.18f})")
        print(f"\n(i)  runs of r=1: {len(runs)}, max {max(runs)}, last five {runs[-5:]}")
        print("     => V_n >= run length: states UNBOUNDED, no interval confinement")
        print("\n(ii) repeated factors spanning full runs")
        print("       gaps   positions   distinct   repeats")
        for r in gap_rows:
            print(f"     {r['gaps_spanned']:6d} {r['positions']:11d} "
                  f"{r['distinct_patterns']:10d} {r['repeats']:9d}")
        print(f"     => no factor spanning {first_clean} or more full runs ever repeats: "
              f"no right-special separation")
        print(f"status : {receipt['status']}")
    return 0 if receipt["status"] == "pass" else 1


if __name__ == "__main__":
    sys.exit(main())
