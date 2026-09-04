#!/usr/bin/env python3
"""Exact-arithmetic probe for the Erdos #269 width bound and the rationality bridge.

Self-contained: enumerates the {2,3,5}-smooth numbers below 2^(A_max+2) with
exact integers and Fractions, never a float in any decision.  It checks the
statements the Lean modules ``NormalizedStateWidth`` and
``RationalityCarryBridge`` land, plus one packet correction.

1. WIDTH.  The half-height normalized tail state (the Lean convention)
       X_a = (H(2^a)/2) * sum_{h >= 2^a} 1/H(h)
   satisfies the Lean bound  X_a <= 90 (a+1)^2  (the Lean proof uses the crude
   digit majorant d_a <= 15 (a+1)^2 and sum_n (n+1)^2 / 2^(n+1) = 6) and the
   cubic target 40 (a+4)^3 named in the longitudinal record.  The measured sup
   of X_a / (a+1)^2 is reported with its slack.

2. DIGIT.  The paper's checker digit (9.1)
       m_a = A_2(a+1) + sum_{(p,e) in I_a} (p-1) sigma_a(p,e) (C_p(e) - C_2(a)),
   A_p(e) = #{(i,j) : q^i r^j < p^e},  C_p(e) = sum_{u<=e} A_p(u) = #{smooth x < p^e},
   equals the Lean threshold-count digit
       N + 10 C3 + 4 C5   (3-jump before 5-jump)   or   N + 2 C3 + 12 C5,
   and both equal (H(2^(a+1))/2) * sum_{shell a} 1/H(h).

3. E5.  Abel form of the value:
       sum_{h < R} 1/H(h) = sum_{t < R} (p_t - 1) N(t)/H(t) + p_R N(R)/H(R)
   at every prime power R, with N(x) = #{smooth h : 1 <= h < x}; the packet row
   written with A(x) = #{2 <= h < x} is short by exactly the telescope, i.e. by 1.

4. TELESCOPE.  sum_{p^e < L} (p-1)/H(p^e) = 1 - 1/H(last prime power below L).

Receipt: state/formal_math/probes/erdos269_width_and_bridge_receipt.json
"""

from __future__ import annotations

import bisect
import json
import sys
from fractions import Fraction
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
RECEIPT = REPO / "state/formal_math/probes/erdos269_width_and_bridge_receipt.json"

PRIMES = (2, 3, 5)


def ilog(p: int, x: int) -> int:
    e = 0
    q = p
    while q <= x:
        q *= p
        e += 1
    return e


def height(x: int) -> int:
    return 2 ** ilog(2, x) * 3 ** ilog(3, x) * 5 ** ilog(5, x)


def smooth_below(limit: int) -> list[int]:
    out = []
    i = 1
    while i < limit:
        j = i
        while j < limit:
            k = j
            while k < limit:
                out.append(k)
                k *= 5
            j *= 3
        i *= 2
    out.sort()
    return out


def prime_powers_below(limit: int) -> list[tuple[int, int, int]]:
    out = []
    for p in PRIMES:
        v, e = p, 1
        while v < limit:
            out.append((v, p, e))
            v *= p
            e += 1
    out.sort()
    return out


def main(A_max: int = 300) -> int:
    limit = 2 ** (A_max + 2)
    smooth = smooth_below(limit)
    shells: dict[int, list[int]] = {a: [] for a in range(A_max + 2)}
    for h in smooth:
        shells[h.bit_length() - 1].append(h)
    mass = {a: sum(Fraction(1, height(h)) for h in shells[a]) for a in shells}

    def H2(a: int) -> int:
        return height(2 ** a)

    # ---- digits ---------------------------------------------------------------
    digit_mismatch = []
    for a in range(0, A_max + 1):
        sh = shells[a]
        N = len(sh)
        cleared = Fraction(H2(a + 1), 2) * mass[a]
        assert cleared.denominator == 1, a
        cleared = int(cleared)
        t3 = 3 ** ilog(3, 2 ** (a + 1))
        t5 = 5 ** ilog(5, 2 ** (a + 1))
        C3 = sum(1 for h in sh if h < t3)
        C5 = sum(1 for h in sh if h < t5)
        lean_digit = N + 10 * C3 + 4 * C5 if t3 <= t5 else N + 2 * C3 + 12 * C5
        jumps = [(v, p, e) for (v, p, e) in prime_powers_below(2 ** (a + 1))
                 if p != 2 and 2 ** a < v]
        paper_digit = N
        for (v, p, _e) in jumps:
            sigma = 1
            for (w, q, _f) in jumps:
                if w > v:
                    sigma *= q
            paper_digit += (p - 1) * sigma * sum(1 for x in sh if x < v)
        if not (lean_digit == paper_digit == cleared):
            digit_mismatch.append((a, lean_digit, paper_digit, cleared))

    # ---- width -----------------------------------------------------------------
    # suffix sums of shell masses; the shells beyond A_max+1 are bounded by the
    # Lean majorant 30 (n+1)^2 / 2^(n+1), summed crudely from M = A_max + 2.
    # Relative tail: (H(2^a)/2) * mass_n = d_n / (b_a ... b_n) <= 15 (n+1)^2 / 2^(n+1-a)
    # for n >= a, so the shells n >= M contribute at most
    # 15 (M+1)^2 * 4 / 2^(M-a) (crude geometric tail, valid for M - a >= 4).
    M = A_max + 2
    suffix = {M: Fraction(0)}
    for a in range(A_max + 1, -1, -1):
        suffix[a] = mass[a] + suffix[a + 1]
    A_report = A_max - 60
    worst_ratio, worst_a = Fraction(0), None
    width_fail, cubic_fail = [], []
    for a in range(0, A_report + 1):
        Xa_hi = Fraction(H2(a), 2) * suffix[a] + Fraction(15 * (M + 1) ** 2 * 4, 2 ** (M - a))
        ratio = Xa_hi / (a + 1) ** 2
        if ratio > worst_ratio:
            worst_ratio, worst_a = ratio, a
        if Xa_hi > 90 * (a + 1) ** 2:
            width_fail.append(a)
        if Xa_hi > 40 * (a + 4) ** 3:
            cubic_fail.append(a)

    # ---- telescope and Abel form -------------------------------------------------
    pps = prime_powers_below(limit)
    tele = sum(Fraction(p - 1, height(v)) for (v, p, _e) in pps)
    last_pp = pps[-1][0]
    tele_ok = tele == 1 - Fraction(1, height(last_pp))

    def N(x: int) -> int:
        return bisect.bisect_left(smooth, x)

    abel_fail = []
    for (R, pR, _e) in pps[-40:]:
        S_R = sum(mass[a] for a in range(0, R.bit_length()))  # over shells below 2^(bitlen)
        S_R = sum(Fraction(1, height(h)) for h in smooth[:N(R)])
        abel_below = sum(Fraction((p - 1) * N(v), height(v)) for (v, p, _f) in pps if v < R)
        if S_R != abel_below + Fraction(pR * N(R), height(R)):
            abel_fail.append(str(R))
    abel_N = sum(Fraction((p - 1) * N(v), height(v)) for (v, p, _e) in pps)
    abel_A = sum(Fraction((p - 1) * (N(v) - 1), height(v)) for (v, p, _e) in pps)
    e5_gap_ok = (abel_N - abel_A) == tele

    receipt = {
        "schema": "erdos269_width_and_bridge_probe_v1",
        "A_max": A_max,
        "smooth_count_below_2_pow_A_max_plus_2": len(smooth),
        "digit": {
            "range_checked": [0, A_max],
            "mismatches": digit_mismatch,
            "identity": "paper (9.1) == Lean threshold digit == (H(2^(a+1))/2) * shell mass",
        },
        "width": {
            "convention": "half height, X_a = (H(2^a)/2) * sum_{h>=2^a} 1/H(h) = Lean trueNormalizedState a",
            "range_reported": [0, A_report],
            "lean_bound": "X_a <= 90 (a+1)^2",
            "cubic_target": "X_a <= 40 (a+4)^3",
            "sup_ratio_Xa_over_sq": float(worst_ratio),
            "sup_ratio_at": worst_a,
            "quadratic_failures": width_fail,
            "cubic_failures": cubic_fail,
            "tail_bound_used_above_2_pow": str(M),
        },
        "telescope": {
            "prime_powers_below_2_pow": A_max + 2,
            "sum_equals_one_minus_last": tele_ok,
        },
        "abel_E5": {
            "abel_form_failures_last_40_prime_powers": abel_fail,
            "N_minus_A_gap_equals_telescope": e5_gap_ok,
            "statement": ("S = sum_p (p-1) sum_n N(p^n)/H(p^n) with N(x) = #{1 <= h < x}; "
                          "the A(x) = #{2 <= h < x} form sums to S - 1"),
        },
    }
    RECEIPT.parent.mkdir(parents=True, exist_ok=True)
    RECEIPT.write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + "\n")
    ok = (not digit_mismatch and not width_fail and not cubic_fail and tele_ok
          and e5_gap_ok and not abel_fail)
    print(json.dumps(receipt, indent=2, ensure_ascii=False))
    print("OK" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(int(sys.argv[1]) if len(sys.argv) > 1 else 300))
