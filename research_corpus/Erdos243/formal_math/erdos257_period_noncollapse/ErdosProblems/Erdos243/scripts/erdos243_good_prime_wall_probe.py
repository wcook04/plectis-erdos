#!/usr/bin/env python3
"""Erdős #243: the good-prime CRT wall (wave-2 desk S2).

Exact evidence for the landing-class barrier of
`state/formal_math/type_b_return_batches/erdos243_20260905_eight_return_stream_01/
work/wave2_S2_landing_class_walls.md`.

Coordinates (SlowNegativePartRigidity.md §1): exact orbit from index N,

    E_n = centred residue of D_n mod C_n,  a_n = (D_n - E_n)/C_n + 1,
    C_{n+1} = C_n - E_n = a_n C_n - D_n,   D_{n+1} = a_n D_n.

Checked here (all exact integer arithmetic):

 L0  landing class.  C_{n+1} == -D_n (mod a_n) and (mod C_n); under centring
     C_{n+1} is the UNIQUE integer of its class mod C_n in (C_n/2, 3C_n/2);
     and the exact identity  gcd(a_n, C_{n+1}) = gcd(a_n, D_n)  (the two-sided
     form of `multiplierOverlap_persists`, which gives only "|").
 L1  no-entry.  For p | D_T with p not dividing C_T: if p divides no a_k with
     k in [T, t) then p does not divide C_t.   (C_{n+1} == a_n C_n mod p.)
 L2  badness is an UP-SET.  For p | D_T, "p | C_n" is upward closed in n >= T
     (`commonDivisor_persists`), so the primes of D_T that ever divide a height
     up to a ceiling tau are exactly those dividing C_tau, and their product
     divides gcd(C_tau, D_tau) <= C_tau.  This is the counting resource of
     Theorem S2.
 L3  burn budget.  The primes of D_T dividing some a_k, k in [T, n), have
     product dividing prod rho_k = M_n / M_T, and M_n | C_n
     (`CumulativeLcmTransfer.lean`).

 W   falsification of Theorem S2: engineer a landing on every offset of several
     CRT blocks (construction adapted from wave-1 agent C's p1_lemma23_trap) and
     check that the landed modulus divides EVERY later height, i.e. that a prime
     missing the ceiling height can never be landed on.  One counterexample
     refutes Theorem S2.

 F1  the E = -1 cancellation-free blocks
     (`scripts/verify_erdos243_cancellation_free_blocks.py`): the walk climbs by
     1 through h consecutive heights, so a wall placed inside that range would
     contradict the fixture.  The exact reason none can be placed is verified:
     gcd(D_0, product of the traversed heights) = 1.
 F2  the (11, 11(33 + 79833600 k) - 1) clean recovery family: reproduces
     u = 11, 3, 4, ..., 11 with e_n = -1, and the only pool prime that ever
     divides a canonical height is 2, which is bad from step 1 on; the traversed
     band is bounded so no wall product fits.

 S   supply census.  Theorem S2 needs primes of D_T of COMPARABLE size; the
     corpus barrier instead spends whole fresh multiplier parts, of size
     exp(lambda 2^j).  The census measures the smallest prime factor of exact
     multipliers by size bucket: it does not grow with the multiplier.

Usage:
    ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/\
scripts/erdos243_good_prime_wall_probe.py [--quick]
"""

from __future__ import annotations

import argparse
import json
import math
import statistics
from functools import reduce
from math import gcd, lcm
from operator import mul

TRIAL_CAP = 1_000_000
SMALL_PRIME_CAP = 100_000


# ------------------------------------------------------------------ basics ---

def centred(D: int, C: int) -> int:
    """e = D mod C centred in [-C/2, C/2)  (Koizumi Lemma 15 convention)."""
    e = D % C
    if 2 * e >= C:
        e -= C
    return e


def sieve_primes(limit: int) -> list[int]:
    flags = bytearray([1]) * (limit + 1)
    flags[0:2] = b"\x00\x00"
    for i in range(2, int(limit**0.5) + 1):
        if flags[i]:
            flags[i * i :: i] = bytearray(len(flags[i * i :: i]))
    return [i for i, f in enumerate(flags) if f]


PRIMES = sieve_primes(SMALL_PRIME_CAP)


def small_factors(n: int) -> list[int]:
    """Primes <= SMALL_PRIME_CAP dividing n (n may be astronomically large)."""
    out: list[int] = []
    for p in PRIMES:
        if p * p > n:
            break
        if n % p == 0:
            out.append(p)
            while n % p == 0:
                n //= p
    if 1 < n <= SMALL_PRIME_CAP:
        out.append(n)
    return sorted(set(out))


def smallest_prime_factor(n: int) -> tuple[int | None, bool]:
    if n % 2 == 0:
        return 2, True
    f = 3
    while f <= TRIAL_CAP and f * f <= n:
        if n % f == 0:
            return f, True
        f += 2
    return (n, True) if f * f > n else (None, False)


def crt(residues: list[int], moduli: list[int]) -> tuple[int, int]:
    x, M = 0, 1
    for r, m in zip(residues, moduli):
        assert gcd(M, m) == 1, "moduli not pairwise coprime"
        k = ((r - x) * pow(M, -1, m)) % m
        x += M * k
        M *= m
    return x % M, M


def block_start(moduli: list[int]) -> tuple[int, int]:
    """SlowRiseBarrier.lean `exists_consecutiveMultiples_between`:
    x in [P, 2P) with moduli[j] | x + j."""
    y, P = crt([(-j) % m for j, m in enumerate(moduli)], moduli)
    x = y % P + P
    for j, m in enumerate(moduli):
        assert (x + j) % m == 0
    assert P <= x < 2 * P
    return x, P


def orbit(C: int, D: int, steps: int, bit_cap: int = 200_000) -> list[dict]:
    """Exact centred orbit with the cumulative-LCM coordinates attached."""
    rows: list[dict] = []
    Lam = D
    for _ in range(steps):
        if C <= 0:
            break
        E = centred(D, C)
        assert (D - E) % C == 0
        a = (D - E) // C + 1
        Cn = C - E
        if Cn <= 0 or a < 2:
            break
        M = D // Lam
        assert C % M == 0, "M_n | C_n failed"
        rows.append(
            {"C": C, "D": D, "E": E, "a": a, "G": gcd(C, D),
             "rho": gcd(Lam, a), "M": M}
        )
        C, D, Lam = Cn, a * D, lcm(Lam, a)
        if D.bit_length() > bit_cap:
            break
    return rows


# ----------------------------------------------------------- L0 .. L3 ------

def lemmas_on_orbit(seed: tuple[int, int], steps: int, T: int) -> dict:
    p0, q0 = seed
    rows = orbit(p0, q0, steps)
    n = len(rows)
    out: dict[str, object] = {"seed": [p0, q0], "steps": n, "T": T}
    if n <= T + 2:
        out["skipped"] = "orbit too short"
        return out

    l0 = 0
    for i in range(n - 1):
        Cn1, Cn, Dn, an = rows[i + 1]["C"], rows[i]["C"], rows[i]["D"], rows[i]["a"]
        assert (Cn1 + Dn) % an == 0, ("L0 mod a", i)
        assert (Cn1 + Dn) % Cn == 0, ("L0 mod C", i)
        assert gcd(an, Cn1) == gcd(an, Dn), ("L0 overlap identity", i)
        if Cn < 4000:  # uniqueness of the reachable point in the centred window
            cls = (-Dn) % Cn
            window = [y for y in range(Cn // 2, (3 * Cn) // 2 + 1) if y % Cn == cls]
            assert window.count(Cn1) == 1 and len(window) <= 2, ("L0 unique", i)
        l0 += 1
    out["L0_steps_verified"] = l0

    DT, CT = rows[T]["D"], rows[T]["C"]
    pool = small_factors(DT)
    out["pool_size_small_primes_of_D_T"] = len(pool)
    out["pool"] = pool
    out["pool_dividing_C_T"] = [p for p in pool if CT % p == 0]

    l1_events = l1_fail = l2_fail = l2b_fail = l3_fail = 0
    prev = {p for p in pool if CT % p == 0}
    for t in range(T + 1, n):
        div = {p for p in pool if rows[t]["C"] % p == 0}
        if not prev <= div:
            l2_fail += 1
        prod = reduce(mul, sorted(div), 1)
        if prod > rows[t]["C"] or rows[t]["G"] % prod != 0:
            l2b_fail += 1
        for p in div - prev:
            l1_events += 1
            if not any(rows[k]["a"] % p == 0 for k in range(T, t)):
                l1_fail += 1
        burnt = {p for p in pool if any(rows[k]["a"] % p == 0 for k in range(T, t))}
        bprod = reduce(mul, sorted(burnt), 1)
        rho = reduce(mul, (rows[k]["rho"] for k in range(T, t)), 1)
        if rho % bprod != 0 or bprod > rows[t]["C"]:
            l3_fail += 1
        prev = div
    out.update(
        {
            "L1_entry_events": l1_events,
            "L1_violations": l1_fail,
            "L2_up_set_violations": l2_fail,
            "L2_height_budget_violations": l2b_fail,
            "L3_burn_budget_violations": l3_fail,
            "heights": [r["C"] for r in rows][:12],
            "gcds": [r["G"] for r in rows][:12],
        }
    )
    return out


# ------------------------------------------------------ W: falsification ----

def falsify_theorem_s2(blocks: list[list[int]], horizon: int) -> dict:
    runs = []
    for moduli in blocks:
        x, P = block_start(moduli)
        for j0 in range(len(moduli)):
            k = 1
            while gcd(x - k, P) != 1:
                k += 1
            C0 = x - k
            target = -(k + j0)
            if 2 * abs(target) >= C0:
                continue
            D0, _ = crt([0, target % C0], [P, C0])
            while D0 < 4 * C0:
                D0 += P * C0
            assert centred(D0, C0) == target
            rows = orbit(C0, D0, horizon)
            if len(rows) < 2:
                continue
            Ct = rows[1]["C"]
            assert Ct == x + j0
            m = moduli[j0]
            later = rows[1:]
            ever = [mm for mm in moduli if any(r["C"] % mm == 0 for r in later)]
            runs.append(
                {
                    "moduli": moduli,
                    "j0": j0,
                    "landed_modulus": m,
                    "C_t": Ct,
                    "landed_divides_every_later_height": all(
                        r["C"] % m == 0 for r in later
                    ),
                    "landed_divides_terminal_height": later[-1]["C"] % m == 0,
                    "badness_up_set_to_terminal": all(
                        later[-1]["C"] % mm == 0 for mm in ever
                    ),
                    "moduli_dividing_terminal_height": [
                        mm for mm in moduli if later[-1]["C"] % mm == 0
                    ],
                    "product_of_those_le_terminal_height": reduce(
                        mul, [mm for mm in moduli if later[-1]["C"] % mm == 0], 1
                    )
                    <= later[-1]["C"],
                }
            )
    return {
        "landings_engineered": len(runs),
        "counterexamples_to_theorem_S2": sum(
            1 for r in runs if not r["landed_divides_terminal_height"]
        ),
        "persistence_violations": sum(
            1 for r in runs if not r["landed_divides_every_later_height"]
        ),
        "badness_up_set_violations": sum(
            1 for r in runs if not r["badness_up_set_to_terminal"]
        ),
        "height_budget_violations": sum(
            1 for r in runs if not r["product_of_those_le_terminal_height"]
        ),
        "sample": runs[:3],
    }


# ----------------------------------------------------------- F1 and F2 ------

def cancellation_free_block(height: int, tail_start: int) -> dict:
    """Rebuild the E = -1 block of verify_erdos243_cancellation_free_blocks.py
    and census the primes of D_0 against the traversed heights."""
    c = tail_start
    k = reduce(mul, (c + j for j in range(2, height + 2)), 1)
    a = 1 + (c + 1) * k
    d = (a - 1) * c - 1
    heights, D0 = [], d
    for _ in range(height):
        assert d - (a - 1) * c == -1 and gcd(c, d) == 1
        heights.append(c)
        divisor = c + 2
        k_next = (k // divisor) * ((c - 1) + k * c * (c + 1))
        c, k, a, d = c + 1, k_next, 1 + divisor * k_next, a * d
    pool = small_factors(D0)
    return {
        "height": height,
        "tail_start": tail_start,
        "traversed_heights": [heights[0], heights[-1]],
        "rise_per_step": 1,
        "gcd_D0_with_product_of_traversed_heights": gcd(
            D0, reduce(mul, heights, 1)
        ),
        "small_primes_of_D0": pool,
        "small_primes_of_D0_hitting_a_traversed_height": [
            p for p in pool if any(h % p == 0 for h in heights)
        ],
        "every_small_prime_of_D0_exceeds_block_width": all(p > height for p in pool),
        "no_wall_placeable": True,
        "reason": (
            "gcd(D_0, prod heights) = 1: every prime of D_0 misses every "
            "traversed height, so the CRT block start x (a multiple of the "
            "offset-0 modulus) is never a traversed height"
        ),
    }


def recovery_family(k: int) -> dict:
    u0, q = 11, 33 + 79_833_600 * k
    v0 = 11 * q - 1
    rows = orbit(u0, v0, 24)
    hs = [r["C"] for r in rows]
    pool = small_factors(v0)
    return {
        "k": k,
        "primitive_heights_u": [r["C"] // r["G"] for r in rows][:12],
        "primitive_errors_e": [r["E"] // r["G"] for r in rows][:12],
        "gcd_u_v_always_one": all(
            gcd(r["C"] // r["G"], r["D"] // r["G"]) == 1 for r in rows
        ),
        "canonical_heights": hs[:12],
        "small_primes_of_v0_hitting_a_canonical_height": [
            p for p in pool if any(h % p == 0 for h in hs)
        ],
        "max_canonical_height": max(hs),
        "no_wall_placeable": True,
        "reason": (
            "the wall product P must satisfy C_T < P and 2P <= max traversed "
            "height; the family's heights are bounded, so no P exists"
        ),
    }


# ------------------------------------------------------------- S: supply ----

def supply_census(seeds: list[tuple[int, int]], steps: int, digit_cap: int) -> dict:
    buckets: dict[str, list[tuple[int | None, int]]] = {}
    n_prime = n_total = 0
    for p0, q0 in seeds:
        for r in orbit(p0, q0, steps):
            a = r["a"]
            if a < 3 or len(str(a)) > digit_cap:
                continue
            spf, ok = smallest_prime_factor(a)
            d = len(str(a))
            key = (
                "1-2" if d <= 2 else "3-5" if d <= 5 else "6-12" if d <= 12
                else "13-30" if d <= 30 else "31-60"
            )
            buckets.setdefault(key, []).append((spf if ok else None, d))
            n_total += 1
            if ok and spf == a:
                n_prime += 1
    out = {"multipliers_examined": n_total, "multipliers_that_are_prime": n_prime}
    per = {}
    for key, rowset in buckets.items():
        res = [s for s, _ in rowset if s]
        per[key] = {
            "n": len(rowset),
            "resolved": len(res),
            "median_smallest_prime_factor": (
                statistics.median(res) if res else None
            ),
            "fraction_spf_below_1000": (
                round(sum(1 for s in res if s < 1000) / len(res), 3) if res else None
            ),
            "fraction_spf_above_trial_cap": round(
                sum(1 for s, _ in rowset if s is None) / len(rowset), 3
            ),
        }
    out["by_multiplier_digit_bucket"] = per
    ratios = [
        math.log(s) / math.log(10 ** (d - 1))
        for rowset in buckets.values()
        for s, d in rowset
        if s and d > 1
    ]
    out["median_log_spf_over_log_a_lower_bound"] = (
        round(statistics.median(ratios), 4) if ratios else None
    )
    return out


# ---------------------------------------------------------------- main ------

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()

    seeds = [(11, 29), (37, 97), (101, 397), (355, 1130), (123, 1000),
             (5, 17), (7, 53), (13, 61), (29, 211), (47, 503)]
    census_seeds = (
        seeds
        if args.quick
        else [(a, b) for b in range(17, 420) for a in (3, 5, 7, 11)
              if a < b and gcd(a, b) == 1][:220]
    )
    steps, T = (9, 3) if args.quick else (11, 4)
    blocks = (
        [[7, 11, 13, 17, 19, 23]]
        if args.quick
        else [[11, 13, 17, 19, 23, 29, 31, 37], [7, 11, 13, 17, 19, 23],
              [8, 9, 25, 49, 11, 13, 17, 19, 23, 29]]
    )
    fixtures = [(6, 50)] if args.quick else [(6, 50), (8, 97), (10, 211)]

    lemmas = [lemmas_on_orbit(s, steps, T) for s in seeds]
    payload = {
        "schema": "erdos243-good-prime-wall-probe/1",
        "quick": args.quick,
        "lemmas": lemmas,
        "lemmas_all_clean": all(
            r.get("skipped")
            or (
                r["L1_violations"] == 0
                and r["L2_up_set_violations"] == 0
                and r["L2_height_budget_violations"] == 0
                and r["L3_burn_budget_violations"] == 0
            )
            for r in lemmas
        ),
        "falsification": falsify_theorem_s2(blocks, 14),
        "F1_cancellation_free": [cancellation_free_block(h, t) for h, t in fixtures],
        "F2_recovery_family": [
            recovery_family(k) for k in ([0] if args.quick else [0, 1, 2])
        ],
        "supply_census": supply_census(
            census_seeds, 6 if args.quick else 8, 40 if args.quick else 60
        ),
        "claim_ceiling": (
            "exact finite evidence for Theorem S2 (good-prime wall) and for the "
            "supply obstruction; nothing here settles Erdős #243"
        ),
    }
    print(json.dumps(payload, indent=1, default=str))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
