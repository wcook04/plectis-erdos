#!/usr/bin/env python3
"""Exact replay of the primitive record two-unit barrier and its boundary.

Source note: ErdosProblems/Erdos243/EightReturnRigidityCriteria.md section 3
(returns r03, r07, r08).  Lean authority for the two structural halves is
ErdosProblems/Erdos243/PrimitiveRecordBarrier.lean, declarations
primitive_valuation_no_drop, protectedPrimePower_persists and odd_record_cut.
This checker is the finite falsifier beside those declarations.

Primitive one step, nearest-integer selector (Koizumi Lemma 15 in primitive
coordinates; note that the floor selector a = floor(v/u) + 1 forces e >= 0 and
deletes the negative branch entirely):

    a = floor(v/u + 1/2) + 1 = (2 v + 3 u) // (2 u),
    e = v - (a - 1) u  in [-u/2, u/2),   w = a u - v = u - e  in (u/2, 3u/2],
    h = gcd(w, a v) = gcd(w, a^2),   u' = w/h,   v' = a v / h.

Part A -- valuation no drop.  For every primitive state and every prime p | v,
with l = nu_p(v):

    nu_p(v') = nu_p(a) + l - min(nu_p(w), nu_p(a) + l)          (exact identity)
    nu_p(v') < l   ==>   nu_p(a) = l  and  p^(l+1) | w          (r07 Lemma 1)
    nu_p(v') = 0   ==>   p^(2 l) | w                            (full erasure)
    p | v and p does not divide v'  ==>  p^2 | h and p^2 | w    (r03 Lemma 1)

together with the selector receipts -u <= 2 e < u, u < 2 w <= 3 u,
gcd(u', v') = 1, gcd(u, u') = 1 and h = gcd(w, a^2).

Part B -- the odd cut.  For every primitive state, every odd prime p with
p^l exactly dividing v, and every odd multiple H of p with u < H and
3 H < 2 p^(l+1):  a jump of size at most two cannot reach H, that is

    NOT ( u' >= H  and  u' - u <= 2 ).

This is the one-step content of odd_record_cut: the landing u' = H is killed by
p | v' and gcd(u', v') = 1, and the only remaining jump-2 crossing is
(H-1, H+1), both even because H is odd, against gcd(u, u') = 1.

Part C -- the three-rise crossing fixtures.  The three exact families from
r03 section 8, r07 section 8 and r08 section 6, with their two stated concrete
instances.  These are the obstructions to extending the barrier from 2 to 3.
FAMILY-LIMIT WORDING: each family member is a one-step (r03) or two-step
(r07, r08) fixture, not an orbit segment obeying the rate hypothesis.  For a
FIXED p and a -> infinity the ratio a'/a^2 tends to u/u' = 1 - 3/(u+3), which is
bounded away from 1; only the joint limit p -> infinity recovers a'/a^2 -> 1.
The checker reports both a'/a^2 and u/u' so the two limits are never conflated.

Run:
    ./repo-python .../scripts/check_erdos243_record_two_unit_barrier.py --quick
    ./repo-python .../scripts/check_erdos243_record_two_unit_barrier.py
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from math import gcd


def vp(n: int, p: int) -> int:
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


def prime_factors(n: int) -> list:
    fs, d = [], 2
    while d * d <= n:
        if n % d == 0:
            fs.append(d)
            while n % d == 0:
                n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        fs.append(n)
    return fs


def step(u: int, v: int):
    """Nearest-integer primitive step.  Returns (a, e, w, h, u', v')."""
    a = (2 * v + 3 * u) // (2 * u)
    e = v - (a - 1) * u
    w = a * u - v
    h = gcd(w, a * v)
    return a, e, w, h, w // h, a * v // h


def crt2(r1: int, m1: int, r2: int, m2: int) -> int:
    t = ((r2 - r1) * pow(m1, -1, m2)) % m2
    return (r1 + m1 * t) % (m1 * m2)


# ---------------------------------------------------------------------------
# Part A
# ---------------------------------------------------------------------------


def valuation_no_drop(umax: int, vmax: int) -> dict:
    states = combos = drops = erasures = 0
    failures = []
    for u in range(1, umax):
        for v in range(1, vmax):
            if gcd(u, v) != 1:
                continue
            a, e, w, h, u2, v2 = step(u, v)
            if w <= 0:
                failures.append(("nonpositive_w", u, v))
                continue
            states += 1
            if not (-u <= 2 * e < u):
                failures.append(("centring", u, v, e))
            if not (u < 2 * w <= 3 * u):
                failures.append(("w_range", u, v, w))
            if gcd(u2, v2) != 1:
                failures.append(("successor_not_primitive", u, v))
            if gcd(u, u2) != 1:
                failures.append(("adjacent_not_coprime", u, v))
            if h != gcd(w, a * a):
                failures.append(("h_ne_gcd_w_a_squared", u, v))
            for p in prime_factors(v):
                combos += 1
                l, l2, al, bl = vp(v, p), vp(v2, p), vp(a, p), vp(w, p)
                if l2 != al + l - min(bl, al + l):
                    failures.append(("exact_valuation_identity", u, v, p))
                if l2 < l:
                    drops += 1
                    if al != l:
                        failures.append(("drop_needs_nu_p_a_eq_l", u, v, p))
                    if w % p ** (l + 1) != 0:
                        failures.append(("drop_needs_p_pow_l_plus_1_dvd_w", u, v, p))
                if l2 == 0:
                    erasures += 1
                    if w % p ** (2 * l) != 0:
                        failures.append(("erasure_needs_p_pow_2l_dvd_w", u, v, p))
                    if h % (p * p) or w % (p * p):
                        failures.append(("r03_lemma1_p_squared", u, v, p))
    return {"u_max": umax, "v_max": vmax, "primitive_states": states,
            "state_prime_combinations": combos,
            "valuation_drops": drops, "full_erasures": erasures,
            "failure_count": len(failures), "failure_sample": failures[:6]}


# ---------------------------------------------------------------------------
# Part B
# ---------------------------------------------------------------------------


def odd_cut(umax: int, vmax: int) -> dict:
    states = triples = 0
    failures = []
    for u in range(1, umax):
        for v in range(1, vmax):
            if gcd(u, v) != 1:
                continue
            a, e, w, h, u2, v2 = step(u, v)
            if w <= 0:
                continue
            states += 1
            for p in prime_factors(v):
                if p == 2:
                    continue
                l = vp(v, p)
                bound = 2 * p ** (l + 1)
                k = 1
                while 3 * k * p < bound:
                    H = k * p
                    if H > u:
                        triples += 1
                        if u2 >= H and u2 - u <= 2:
                            failures.append({"u": u, "v": v, "p": p, "l": l,
                                             "H": H, "u_next": u2, "a": a,
                                             "e": e, "h": h})
                    k += 2
    return {"u_max": umax, "v_max": vmax, "primitive_states": states,
            "state_prime_height_triples": triples,
            "failure_count": len(failures), "failure_sample": failures[:6]}


# ---------------------------------------------------------------------------
# Part C
# ---------------------------------------------------------------------------


def fixture_row(tag: str, u: int, v: int, p: int, k: int) -> dict:
    a, e, w, h, u2, v2 = step(u, v)
    a2, e2 = step(u2, v2)[0], step(u2, v2)[1]
    checks = {
        "primitive": gcd(u, v) == 1,
        "e_eq_minus_three": e == -3,
        "w_eq_u_plus_three": w == u + 3,
        "h_eq_one": h == 1,
        "u_next_eq_u_plus_three": u2 == u + 3,
        "p_power_divides_v": v % p ** k == 0,
        "p_divides_v_next": v2 % p == 0,
        "u_lt_p_lt_u_next": u < p < u2,
    }
    return {"family": tag, "p": p, "u": u, "u_next": u2, "a": a, "e": e,
            "h": h, "a_next": a2, "e_next": e2,
            "a_next_over_a_squared": float(Fraction(a2, a * a)),
            "u_over_u_next": float(Fraction(u, u2)),
            "checks_all_true": all(checks.values()),
            "failed_checks": [k2 for k2, v3 in checks.items() if not v3]}


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def three_rise_fixtures(quick: bool) -> dict:
    rows = []
    failures = []

    # F1 (r03 section 8): u = p-1, v = p(p-4), a = p-2, p = 2 mod 3, p >= 11.
    # One-step crossing only; the successor error is NOT -3, which is why F1 is
    # strictly weaker than F2/F3 as an obstruction.
    f1_members = 0
    f1_pmax = 60 if quick else 200
    for p in range(11, f1_pmax):
        if not is_prime(p) or p % 3 != 2:
            continue
        u, v = p - 1, p * (p - 4)
        a, e, w, h, u2, v2 = step(u, v)
        f1_members += 1
        ok = (gcd(u, v) == 1 and a == p - 2 and e == -3 and w == p + 2
              and h == 1 and u2 == p + 2 and v % p == 0 and v2 % p == 0
              and u < p < u2)
        if not ok:
            failures.append({"family": "F1_r03", "p": p})

    # F2 (r07 section 8): p^2 | v.
    f2_primes = (11, 13, 17, 19, 23) if quick else (11, 13, 17, 19, 23, 29, 31, 37, 101, 1009)
    for p in f2_primes:
        u = p - 1
        if u % 3 == 0:
            u = p - 2
        w = u + 3
        if gcd(p * p, w) != 1:
            continue
        a = crt2((1 + 3 * pow(u, -1, p * p)) % (p * p), p * p, 1, w)
        while a <= 2 * u:
            a += p * p * w
        v = (a - 1) * u - 3
        row = fixture_row("F2_r07", u, v, p, 2)
        rows.append(row)
        if not row["checks_all_true"]:
            failures.append(row)

    # F3 (r08 section 6): p^3 | v.
    f3_primes = (11, 13, 17, 19, 23) if quick else (11, 13, 17, 19, 23, 29, 31, 37, 101)
    for p in f3_primes:
        r = 1 if p % 3 == 2 else 2
        u = p - r
        u2t = u + 3
        a = crt2((u2t * pow(u, -1, p ** 3)) % p ** 3, p ** 3, 1, u2t)
        while a <= 2 * u:
            a += p ** 3 * u2t
        v = a * u - u2t
        row = fixture_row("F3_r08", u, v, p, 3)
        rows.append(row)
        if not row["checks_all_true"]:
            failures.append(row)

    # The two stated concrete instances, reproduced exactly.
    a, e, w, h, u2, v2 = step(10, 10527)
    a2, e2 = step(u2, v2)[0], step(u2, v2)[1]
    r07_instance = {"stated": [10, 10527, 1054], "u_next": u2, "a": a, "e": e,
                    "h": h, "a_next": a2, "e_next": e2,
                    "p_squared_divides_v": 10527 % 121 == 0,
                    "p_squared_divides_v_next": v2 % 121 == 0,
                    "reproduces": (u2, a, e, h, a2, e2) == (13, 1054, -3, 1, 853498, -3)}
    a, e, w, h, u2, v2 = step(10, 89177)
    a2, e2 = step(u2, v2)[0], step(u2, v2)[1]
    r08_instance = {"stated": [10, 89177, 8919, -3, 1], "u_next": u2, "a": a,
                    "e": e, "h": h, "v_next": v2, "a_next": a2, "e_next": e2,
                    "v_factorisation_11_cubed_times_67": 11 ** 3 * 67 == 89177,
                    "reproduces": (a, e, h, u2, v2, a2, e2)
                                  == (8919, -3, 1, 13, 795369663, 61182283, -3)}
    if not r07_instance["reproduces"]:
        failures.append(r07_instance)
    if not r08_instance["reproduces"]:
        failures.append(r08_instance)

    return {
        "F1_r03_members_checked": f1_members,
        "F2_F3_rows": rows,
        "r07_concrete_instance": r07_instance,
        "r08_concrete_instance": r08_instance,
        "failure_count": len(failures),
        "failure_sample": failures[:4],
        "family_limit_wording": "a'/a^2 -> 1 is a limit ACROSS the family as "
                                "p -> infinity, not along any orbit: for fixed p "
                                "and a -> infinity, a'/a^2 -> u/u' = 1 - 3/(u+3). "
                                "The rows report both quantities.",
    }


# ---------------------------------------------------------------------------


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    umax, vmax = (45, 160) if args.quick else (60, 400)
    part_a = valuation_no_drop(umax, vmax)
    part_b = odd_cut(umax, vmax)
    part_c = three_rise_fixtures(args.quick)

    ok = (part_a["failure_count"] == 0 and part_b["failure_count"] == 0
          and part_c["failure_count"] == 0)

    report = {
        "check": "erdos243_record_two_unit_barrier",
        "status": "pass" if ok else "fail",
        "evidence_class": "exact_computation",
        "mode": "quick" if args.quick else "full",
        "selector": "nearest integer a = (2v+3u)//(2u)",
        "valuation_no_drop": part_a,
        "odd_cut": part_b,
        "three_rise_fixtures": part_c,
        "lean_authority": ["ErdosProblems.Erdos243.primitive_valuation_no_drop",
                           "ErdosProblems.Erdos243.protectedPrimePower_persists",
                           "ErdosProblems.Erdos243.odd_record_cut"],
        "scope": "Finite exhaustive falsifier for the two structural lemmas and "
                 "the exact obstruction fixtures.  The prime-power supply lemma "
                 "is asymptotic and has no finite witness; the composed theorem "
                 "is vacuous on every computable finite orbit, because small "
                 "seeds reach e_n = 0 long before the numerator reaches the "
                 "protected height.  Nothing here settles Erdos #243.",
    }
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(json.dumps({
            "check": report["check"], "status": report["status"],
            "evidence_class": report["evidence_class"], "mode": report["mode"],
            "primitive_states": part_a["primitive_states"],
            "state_prime_combinations": part_a["state_prime_combinations"],
            "valuation_drops": part_a["valuation_drops"],
            "full_erasures": part_a["full_erasures"],
            "valuation_failures": part_a["failure_count"],
            "odd_cut_triples": part_b["state_prime_height_triples"],
            "odd_cut_failures": part_b["failure_count"],
            "three_rise_F1_members": part_c["F1_r03_members_checked"],
            "three_rise_F2_F3_rows": len(part_c["F2_F3_rows"]),
            "three_rise_failures": part_c["failure_count"],
            "r07_instance_reproduces": part_c["r07_concrete_instance"]["reproduces"],
            "r08_instance_reproduces": part_c["r08_concrete_instance"]["reproduces"],
        }, sort_keys=True))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
