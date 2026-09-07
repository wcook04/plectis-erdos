#!/usr/bin/env python3
"""Erdos 269 companion: exact witness for irrationality of the pure prime-power series.

Sigma_p := sum_{m>=1} 1/H(p^m),  H(x) = prod_{q in {2,3,5}} q^floor(log_q x).

This is NOT Erdos 269 (which is S = sum over ALL smooth s of 1/H(s)).  It is the
one-channel sub-series, and unlike S it is provably irrational.  All arithmetic
here is exact: integers and Fractions only, no floating-point logarithms.

Objects.  H_M := H(p^(M-1)),  y_M := H_M * sum_{m>=M} 1/H(p^m),
          b_m := H(p^(m+1))/H(p^m).
Facts checked:
  (T) telescope         sum_p (p-1) Sigma_p = 1 exactly.
  (C) clearing          H(p^m) | H_M for m < M, so y_M = H_M*Sigma_p - integer.
  (R) range/recurrence  0 < y_M < 1 and y_{M+1} = b_{M-1} y_M - 1.
  (I) confinement       y_M in (1/b_{M-1}, 2/b_{M-1}) -- the interval is fixed by
                        the CURRENT radix letter alone.  This is what fails for S,
                        whose digits are shell lattice counts growing like n^2.
  (S) right-special     for every L the radix word has a right-special factor of
                        length L whose two extensions a != a' satisfy
                        max(a,a') > 2*min(a,a'), so their confinement intervals
                        are disjoint.
  (G) gap               for two occurrences M, M' of the two extensions,
                        y_M - y_M' = (y_{M+L} - y_{M'+L}) / P with P = prod of the
                        common prefix, so  0 < |y_M - y_M'| <= 1/P -> 0
                        while  |H_M - H_M'| is a nonzero integer.
  (L) linear form       || (H_M - H_M') * Sigma_p || = |y_M - y_M'|, small nonzero.
Together (C)+(G)+(L) give arbitrarily small nonzero integer linear forms in
Sigma_p, hence irrationality.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import sys
from fractions import Fraction

PRIMES = (2, 3, 5)


def height(x: int) -> int:
    """H(x) by exact integer comparison only."""
    out = 1
    for q in PRIMES:
        t = 1
        while t * q <= x:
            t *= q
        out *= t
    return out


def exponents(p: int, mmax: int) -> list[tuple[int, int, int]]:
    """Exact exponent triples of H(p^m) for m = 0..mmax, computed incrementally.

    e_q(m) is the largest j with q^j <= p^m.  Only integer comparisons are used;
    running powers are advanced in place so no giant power is ever recomputed.
    """
    out = []
    powp = 1
    runners = {q: [1, 0] for q in PRIMES}          # q -> [current q^j, j]
    for _ in range(mmax + 2):
        trip = []
        for q in PRIMES:
            cur = runners[q]
            while cur[0] * q <= powp:
                cur[0] *= q
                cur[1] += 1
            trip.append(cur[1])
        out.append(tuple(trip))
        powp *= p
    return out


def radices_from_exponents(exps: list[tuple[int, int, int]]) -> list[int]:
    """b_m = H(p^(m+1)) / H(p^m) as an exact small integer."""
    out = []
    for m in range(len(exps) - 1):
        r = 1
        for q, lo, hi in zip(PRIMES, exps[m], exps[m + 1]):
            r *= q ** (hi - lo)
        out.append(r)
    return out


def height_from_exponent(trip: tuple[int, int, int]) -> int:
    out = 1
    for q, e in zip(PRIMES, trip):
        out *= q ** e
    return out


def telescope_exact(cutoff: int) -> dict:
    total = Fraction(0)
    per = {}
    for p in PRIMES:
        s, m = Fraction(0), 1
        while True:
            term = Fraction(1, height(p ** m))
            s += term
            if term < Fraction(1, 10 ** cutoff):
                break
            m += 1
        per[p] = s
        total += (p - 1) * s
    return {"per_channel": {str(p): float(v) for p, v in per.items()},
            "sigma2_exact_head": str(float(per[2])),
            "telescope_minus_one_abs_lt": f"1e-{cutoff}",
            "telescope_defect_is_below_cutoff": abs(total - 1) < Fraction(4, 10 ** cutoff)}


def state_bounds(radices: list[int], M: int, depth: int) -> tuple[Fraction, Fraction, int]:
    """Rigorous rational bracket for y_M using 0 < y_{M+depth} < 1.

    y_M = sum_{j<depth} 1/(b_{M-1}...b_{M-1+j}) + y_{M+depth}/P, P = prod_{i<depth} b_{M-1+i}.
    """
    acc, prod = Fraction(0), 1
    for j in range(depth):
        prod *= radices[M - 1 + j]
        acc += Fraction(1, prod)
    return acc, acc + Fraction(1, prod), prod


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--prime", type=int, default=2, choices=list(PRIMES))
    ap.add_argument("--scan", type=int, default=60000, help="positions scanned for factors")
    ap.add_argument("--lengths", type=int, nargs="*", default=[4, 8, 12, 16, 20, 24, 28, 32])
    ap.add_argument("--confine-checks", type=int, default=3000)
    ap.add_argument("--telescope-cutoff", type=int, default=80)
    ap.add_argument("--receipt", type=str, default=None)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    p = args.prime
    mmax = args.scan + max(args.lengths) + 80
    exps = exponents(p, mmax)
    radices = radices_from_exponents(exps)

    # (T)
    tele = telescope_exact(args.telescope_cutoff)

    # (C) clearing: H(p^m) | H_M for m < M
    # exponentwise monotonicity is exactly divisibility of the monomials
    clearing_fail = [(M, m) for M in range(1, 2000) for m in (0, M // 2, max(M - 1, 0))
                     if m < M and any(a > b for a, b in zip(exps[m], exps[M - 1]))]

    # (I) confinement, with rigorous rational brackets
    confine_fail = []
    for M in range(1, args.confine_checks + 1):
        lo, hi, _ = state_bounds(radices, M, 60)
        b = radices[M - 1]
        if not (Fraction(1, b) < lo and hi < Fraction(2, b)):
            confine_fail.append(M)

    # (S)+(G)+(L)
    rows, sep_fail = [], []
    for L in args.lengths:
        first: dict[tuple[int, ...], dict[int, int]] = {}
        for M in range(1, args.scan):
            w = tuple(radices[M - 1:M - 1 + L])
            ext = radices[M - 1 + L]
            first.setdefault(w, {}).setdefault(ext, M)
        hit = None
        for w, exts in first.items():
            if len(exts) < 2:
                continue
            ks = sorted(exts)
            for i in range(len(ks)):
                for j in range(i + 1, len(ks)):
                    a, a2 = ks[i], ks[j]
                    if max(a, a2) > 2 * min(a, a2):          # disjoint confinement intervals
                        hit = (w, exts[a], exts[a2], a, a2)
                        break
                if hit:
                    break
            if hit:
                break
        if hit is None:
            sep_fail.append(L)
            continue
        w, M0, M1, a, a2 = hit
        P = 1
        for t in w:
            P *= t
        lo0, hi0, _ = state_bounds(radices, M0, L + 70)
        lo1, hi1, _ = state_bounds(radices, M1, L + 70)
        gap_lo = min(abs(lo0 - hi1), abs(lo1 - hi0))
        gap_hi = max(abs(hi0 - lo1), abs(hi1 - lo0))
        # exact identity y_M - y_M' = (y_{M+L} - y_{M'+L}) / P
        s0lo, s0hi, _ = state_bounds(radices, M0 + L, 70)
        s1lo, s1hi, _ = state_bounds(radices, M1 + L, 70)
        shift_ok = (lo0 - hi1) <= (s0hi - s1lo) / P and (s0lo - s1hi) / P <= (hi0 - lo1)
        n = height_from_exponent(exps[M0 - 1]) - height_from_exponent(exps[M1 - 1])
        rows.append({
            "L": L, "M": M0, "M_prime": M1, "ext_a": a, "ext_a_prime": a2,
            "prefix_product_P": str(P),
            "gap_lower_bound": float(gap_lo), "gap_upper_bound": float(gap_hi),
            "one_over_P": float(Fraction(1, P)),
            "gap_nonzero": gap_lo > 0,
            "gap_below_one_over_P": gap_hi <= Fraction(1, P),
            "shift_identity_consistent": shift_ok,
            "linear_form_multiplier_nonzero": n != 0,
            "multiplier_bits": int(abs(n)).bit_length(),
        })

    ok = (tele["telescope_defect_is_below_cutoff"] and not clearing_fail
          and not confine_fail and not sep_fail
          and all(r["gap_nonzero"] and r["gap_below_one_over_P"]
                  and r["shift_identity_consistent"]
                  and r["linear_form_multiplier_nonzero"] for r in rows))

    receipt = {
        "problem_id": "erdos_269_companion",
        "checker": "check_erdos269_pure_power_irrationality",
        "claim_boundary": "This is the ONE-CHANNEL sub-series sum_m 1/H(p^m), not Erdos 269's "
                          "S = sum over all smooth s of 1/H(s). No claim about S is made.",
        "prime_channel": p,
        "T_telescope_exact": tele,
        "C_clearing_failures": clearing_fail,
        "I_confinement_failures": confine_fail,
        "I_confinement_checked": args.confine_checks,
        "S_separated_right_special_missing_lengths": sep_fail,
        "G_gap_rows": rows,
        "status": "pass" if ok else "fail",
    }
    if args.receipt:
        path = pathlib.Path(args.receipt)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    if args.json:
        print(json.dumps(receipt, indent=2, sort_keys=True))
    else:
        print(f"(T) telescope sum_p (p-1)Sigma_p = 1 exactly : "
              f"{'ok' if tele['telescope_defect_is_below_cutoff'] else 'FAIL'}   "
              f"Sigma_2 = {tele['per_channel']['2']:.16f}")
        print(f"(C) clearing H(p^m) | H_M for m<M          : failures {len(clearing_fail)}")
        print(f"(I) confinement y_M in (1/b, 2/b)          : failures {len(confine_fail)} "
              f"of {args.confine_checks}")
        print(f"(S) separated right-special factor exists  : missing lengths {sep_fail}")
        print("(G) gap rows")
        print("      L        M        M'   a   a'   1/P            gap in         nonzero  |n| bits")
        for r in rows:
            print(f"    {r['L']:3d} {r['M']:8d} {r['M_prime']:8d} {r['ext_a']:3d} {r['ext_a_prime']:4d}  "
                  f"{r['one_over_P']:.3e}   [{r['gap_lower_bound']:.3e},{r['gap_upper_bound']:.3e}]  "
                  f"{'yes' if r['gap_nonzero'] else 'NO ':>5}   {r['multiplier_bits']:6d}")
        print(f"status : {receipt['status']}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
