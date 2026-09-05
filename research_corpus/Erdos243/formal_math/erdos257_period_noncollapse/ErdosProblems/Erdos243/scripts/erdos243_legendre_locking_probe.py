#!/usr/bin/env python3
"""Erdos #243: the primitive square-transport / Legendre invariant (wave-2 desk S1).

Central object
--------------
Unconditionally, for every divisor d of C_{n+1},

    E_n * E_{n+1} = (a_n E_n)^2   (mod d).                       (raw transport)

r04's parent-attack hint proposed LANDING a prime p = 3 (mod 4) (p | C_t and
p | D_t, which by common-divisor persistence makes p | C_m, p | D_m, p | E_m for
every m >= t) and then reading the corollary "|E_n E_{n+1}| is a non-residue mod
p" at every later sign change.  That plan is SELF-DEFEATING: after the landing
p | E_m for every m >= t, so p | E_n E_{n+1} and the corollary's own hypothesis
p !| E_n E_{n+1} fails at every later index.  Part 1 measures this exactly.

The repair is to leave the raw coordinates.  In primitive coordinates
(G_n = gcd(C_n,D_n), u_n = C_n/G_n, v_n = D_n/G_n, e_n = E_n/G_n,
h_n = G_{n+1}/G_n), let d_n be the largest divisor of u_{n+1} coprime to
G_{n+1}.  Then (Lemma S1 of the note)

    h_n * e_n * e_{n+1} = v_n^2   (mod d_n),   gcd(v_n, d_n) = 1,

with NO cleanliness hypothesis, and the non-vacuity p !| e_n e_{n+1} h_n is
AUTOMATIC.  Parts 2-4 verify this exactly, including at paid steps (h_n > 1)
where the corpus's R2 form ("-u_n u_{n+2} is a unit square mod u_{n+1}", which
needs h_n = h_{n+1} = 1) does not apply.

Part 5 measures non-vacuity frequency (does u_{n+1} carry a prime = 3 mod 4?),
sign-change frequency, and the longest all-negative run, and part 6 replays the
corpus's exact fixtures (the E = -1 cancellation-free seeds and the
(11, 11*(33+79833600k)-1) recovery family) to confirm the lemma does not
falsely exclude them.

Usage
-----
    ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/scripts/erdos243_legendre_locking_probe.py --quick
    ./repo-python .../erdos243_legendre_locking_probe.py --qmax 400 --step-cap 200 --out receipt.json
"""

from __future__ import annotations

import argparse
import json
import sys
from math import gcd
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from erdos243_orbit_engine import run_orbit  # noqa: E402


# --------------------------------------------------------------------------
# small helpers
# --------------------------------------------------------------------------

def prime_factors(n: int) -> list[int]:
    """Distinct prime factors by trial division (n stays small in these runs)."""
    n = abs(n)
    out: list[int] = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        out.append(n)
    return out


def coprime_part(m: int, g: int) -> int:
    """Largest divisor of m coprime to g."""
    m = abs(m)
    while True:
        c = gcd(m, g)
        if c == 1:
            return m
        m //= c


def legendre(a: int, p: int) -> int:
    """Legendre symbol (a|p) for odd prime p."""
    a %= p
    if a == 0:
        return 0
    r = pow(a, (p - 1) // 2, p)
    return 1 if r == 1 else -1


def jacobi(a: int, m: int) -> int:
    """Jacobi symbol (a|m), m odd positive."""
    assert m > 0 and m % 2 == 1
    a %= m
    result = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if m % 8 in (3, 5):
                result = -result
        a, m = m, a
        if a % 4 == 3 and m % 4 == 3:
            result = -result
        a %= m
    return result if m == 1 else 0


def primitive_frames(orb: dict) -> list[dict]:
    """Turn a lean=False orbit into per-step primitive frames.

    A frame at index n needs G_n, G_{n+1}, E_n, E_{n+1}, C_{n+1}, r_n.
    """
    C, E, G, R = orb["C"], orb["E"], orb["G"], orb["R"]
    frames = []
    for n in range(len(E) - 1):
        if n + 1 >= len(G) or E[n] == 0:
            break
        Gn, Gn1 = G[n], G[n + 1]
        if Gn1 % Gn:
            continue  # should not happen; G is non-decreasing multiplicatively
        h = Gn1 // Gn
        u_n = C[n] // Gn
        u_n1 = C[n + 1] // Gn1
        e_n = E[n] // Gn
        e_n1 = E[n + 1] // Gn1
        frames.append(
            {
                "n": n,
                "C": C[n], "C1": C[n + 1],
                "G": Gn, "G1": Gn1, "h": h,
                "u": u_n, "u1": u_n1,
                "e": e_n, "e1": e_n1,
                "E": E[n], "E1": E[n + 1],
                "r": R[n],
            }
        )
    return frames


# --------------------------------------------------------------------------
# parts
# --------------------------------------------------------------------------

def part1_raw_vacuity(all_frames: list[list[dict]]) -> dict:
    """Every prime dividing G_{n+1} (a LANDED prime: p | C_{n+1} and p | D_{n+1})
    divides E_{n+1}, hence divides E_n E_{n+1}: the raw-coordinate Legendre
    corollary is vacuous at exactly the primes the landing plan produces."""
    landed_p3 = 0            # landed primes = 3 mod 4 seen at a step
    landed_p3_vacuous = 0    # ... whose non-vacuity hypothesis fails
    unlanded_p3 = 0          # primes = 3 mod 4 dividing C_{n+1} but not D_{n+1}
    unlanded_p3_nonvacuous = 0
    for frames in all_frames:
        for f in frames:
            for p in prime_factors(f["C1"]):
                if p % 4 != 3:
                    continue
                if f["G1"] % p == 0:          # p | C_{n+1} and p | D_{n+1}
                    landed_p3 += 1
                    if (f["E"] * f["E1"]) % p == 0:
                        landed_p3_vacuous += 1
                else:                          # p | C_{n+1}, p !| D_{n+1}
                    unlanded_p3 += 1
                    if (f["E"] * f["E1"]) % p:
                        unlanded_p3_nonvacuous += 1
    return {
        "landed_3mod4_prime_slots": landed_p3,
        "landed_slots_where_hypothesis_p_nmid_EE_FAILS": landed_p3_vacuous,
        "landed_vacuity_rate": (landed_p3_vacuous / landed_p3) if landed_p3 else None,
        "unlanded_3mod4_prime_slots": unlanded_p3,
        "unlanded_slots_nonvacuous": unlanded_p3_nonvacuous,
        "unlanded_nonvacuity_rate": (unlanded_p3_nonvacuous / unlanded_p3) if unlanded_p3 else None,
        "reading": "a landed prime never gives a usable Legendre condition; "
                   "an unlanded prime always does",
    }


def part2_primitive_transport(all_frames: list[list[dict]]) -> dict:
    """h_n e_n e_{n+1} = v_n^2 (mod d_n) with d_n the G-coprime part of u_{n+1},
    and gcd(v_n, d_n) = 1 (so the Legendre reading is never vacuous)."""
    checked = 0
    failures = []
    unit_failures = 0
    paid_steps = 0            # h_n > 1: outside the corpus R2 unit-square form
    outside_R2 = 0            # h_n > 1 (R2 also needs h_{n+1} = 1, so this is a floor)
    d_trivial = 0             # d_n = 1: no content at this step
    for frames in all_frames:
        for f in frames:
            d = coprime_part(f["u1"], f["G1"])
            if d <= 1:
                d_trivial += 1
                continue
            if gcd(f["G"], d) != 1:
                failures.append({"kind": "gcd(G_n,d)!=1", **{k: f[k] for k in ("n", "G", "u1")}})
                continue
            v_mod = (f["r"] % d) * pow(f["G"] % d, -1, d) % d
            X = f["h"] * f["e"] * f["e1"]
            checked += 1
            if (X - v_mod * v_mod) % d:
                failures.append({"kind": "transport", "n": f["n"], "d": d, "X": X, "v": v_mod})
            if gcd(v_mod, d) != 1:
                unit_failures += 1
            if f["h"] > 1:
                paid_steps += 1
                outside_R2 += 1
    return {
        "steps_checked": checked,
        "transport_failures": failures[:10],
        "transport_failure_count": len(failures),
        "unit_failures_gcd_v_d_ne_1": unit_failures,
        "paid_steps_h_gt_1_covered": paid_steps,
        "steps_outside_corpus_R2_form": outside_R2,
        "steps_with_trivial_d": d_trivial,
    }


def part3_legendre(all_frames: list[list[dict]]) -> dict:
    """Legendre reading of the transport at every step, split by sign pattern."""
    stats = {
        "sign_change_steps": 0,
        "same_sign_steps": 0,
        "zero_or_skipped": 0,
        "sign_change_p3_conditions": 0,
        "sign_change_p3_nonresidue_confirmed": 0,
        "same_sign_p3_conditions": 0,
        "same_sign_p3_residue_confirmed": 0,
        "jacobi_checks": 0,
        "jacobi_plus_one": 0,
        "violations": [],
    }
    for frames in all_frames:
        for f in frames:
            d = coprime_part(f["u1"], f["G1"])
            if d <= 1 or f["e"] == 0 or f["e1"] == 0:
                stats["zero_or_skipped"] += 1
                continue
            X = f["h"] * f["e"] * f["e1"]
            sign_change = (f["e"] < 0) != (f["e1"] < 0)
            if sign_change:
                stats["sign_change_steps"] += 1
            else:
                stats["same_sign_steps"] += 1
            dodd = d
            while dodd % 2 == 0:
                dodd //= 2
            if dodd > 1:
                stats["jacobi_checks"] += 1
                j = jacobi(X % dodd, dodd)
                if j == 1:
                    stats["jacobi_plus_one"] += 1
                else:
                    stats["violations"].append({"kind": "jacobi", "n": f["n"], "d": dodd, "X": X, "j": j})
            for p in prime_factors(d):
                if p % 4 != 3:
                    continue
                ls = legendre(X, p)
                if sign_change:
                    stats["sign_change_p3_conditions"] += 1
                    # X < 0 and (X|p) = 1 with (-1|p) = -1 forces (|X| | p) = -1
                    if ls == 1 and legendre(abs(X), p) == -1:
                        stats["sign_change_p3_nonresidue_confirmed"] += 1
                    else:
                        stats["violations"].append({"kind": "signchange", "n": f["n"], "p": p, "X": X})
                else:
                    stats["same_sign_p3_conditions"] += 1
                    if ls == 1 and legendre(abs(X), p) == 1:
                        stats["same_sign_p3_residue_confirmed"] += 1
                    else:
                        stats["violations"].append({"kind": "samesign", "n": f["n"], "p": p, "X": X})
    stats["violations"] = stats["violations"][:10]
    return stats


def is_square(n: int) -> bool:
    if n < 0:
        return False
    r = int(n ** 0.5)
    while r * r > n:
        r -= 1
    while (r + 1) * (r + 1) <= n:
        r += 1
    return r * r == n


def part4_square_defect(all_frames: list[list[dict]]) -> dict:
    """Sharp corollary: if |h_n e_n e_{n+1}| is a perfect square then the sign of
    e_n e_{n+1} decides the shape of d_n.  Same sign: no condition (a square is a
    residue everywhere).  Sign change: -1 must be a QR mod d_n, so every prime
    factor of d_n is = 1 (mod 4) and 4 !| d_n."""
    same_sign_square = 0
    sign_change_square = 0
    sign_change_square_all_1mod4 = 0
    witnesses = []
    for frames in all_frames:
        for f in frames:
            d = coprime_part(f["u1"], f["G1"])
            if d <= 1 or f["e"] == 0 or f["e1"] == 0:
                continue
            X = f["h"] * f["e"] * f["e1"]
            if not is_square(abs(X)):
                continue
            if X > 0:
                same_sign_square += 1
                continue
            sign_change_square += 1
            ps = prime_factors(d)
            ok = all(p % 4 == 1 for p in ps if p != 2) and d % 4 != 0
            if ok:
                sign_change_square_all_1mod4 += 1
            witnesses.append({"n": f["n"], "e": f["e"], "e1": f["e1"], "h": f["h"],
                              "d": d, "primes": ps, "all_1mod4": ok})
    return {
        "same_sign_perfect_square_steps_no_condition": same_sign_square,
        "sign_change_perfect_square_steps": sign_change_square,
        "of_which_d_has_every_prime_1mod4_and_4_nmid_d": sign_change_square_all_1mod4,
        "witnesses": witnesses[:12],
        "reading": "at a sign change with |h e_n e_{n+1}| a perfect square the "
                   "next primitive numerator is forced into the density-zero set "
                   "of integers all of whose odd prime factors are 1 mod 4",
    }


def part7_legendre_only_no_go(u0: int, steps: int, trials: int) -> dict:
    """Prop-7 analogue for the NEW mechanism.

    The data the Legendre invariant sees at step n is (u_n, e_n, h_n) with
    u_{n+1} = (u_n - e_n)/h_n, |e_n| < u_n/2, gcd(e_n, u_n) = 1, and the
    requirement that h_n e_n e_{n+1} be a quadratic residue modulo u_{n+1}.
    Track a greedy walk that takes the DEEPEST admissible negative error at
    every step.  If deep excursions stay admissible, the invariant alone cannot
    push the barrier past log log, exactly as Prop. 7 caps the coprimality route.
    """
    walks = []
    for t in range(trials):
        u = u0 + 2 * t
        e = -1
        heights = [u]
        errs = []
        ratios = []
        ok = True
        for _ in range(steps):
            u1 = u - e                       # h_n = 1 (clean) throughout
            if u1 > 4 * 10 ** 7:
                break
            ps = [p for p in prime_factors(u1)]
            best = None
            # deepest admissible negative error at the next step
            lo = -((u1 - 1) // 2)
            for cand in range(lo, 0):
                if gcd(cand, u1) != 1:
                    continue
                x = e * cand
                if all(legendre(x, p) == 1 for p in ps if p != 2):
                    best = cand
                    break
            if best is None:
                ok = False
                break
            errs.append(best)
            ratios.append(abs(best) / u1)
            e = best
            u = u1
            heights.append(u)
        walks.append({
            "u0": u0 + 2 * t,
            "steps_taken": len(errs),
            "max_height": max(heights),
            "min_depth_ratio_|e|/u": min(ratios) if ratios else None,
            "mean_depth_ratio": (sum(ratios) / len(ratios)) if ratios else None,
            "admissible_throughout": ok,
            "errs_head": errs[:10],
        })
    depth_ok = [w for w in walks if w["min_depth_ratio_|e|/u"] is not None
                and w["min_depth_ratio_|e|/u"] > 0.4]
    return {
        "walks": walks,
        "walks_with_every_error_deeper_than_0.4*u": len(depth_ok),
        "walks_total": len(walks),
        "reading": "the Legendre invariant admits walks whose every rise is a "
                   "constant fraction of the height, so it cannot by itself "
                   "exclude negative parts of order log C_n, let alone log log C_n; "
                   "this is the exact no-go for the mechanism",
    }


def part8_defect_charge(all_frames: list[list[dict]]) -> dict:
    """Corollary S3: a Legendre DEFECT is charged to h_n alone.

    If (e_n e_{n+1} | p) = -1 for some prime p | d_n then, since
    h_n e_n e_{n+1} = v_n^2 is a nonzero square mod p, (h_n | p) = -1; so h_n is
    a quadratic non-residue mod p and in particular h_n > 1.  The corpus's R2
    form only concludes "h_n > 1 or h_{n+1} > 1".  Since G_{n+1} = h_n G_n and
    G_N <= C_N, the number of defect indices below N is at most log2 C_N.
    """
    defects = 0
    defects_with_h_gt_1 = 0
    defects_with_h_nonresidue = 0
    r2_would_need_h_next = 0
    paid = 0
    witnesses = []
    for frames in all_frames:
        for f in frames:
            d = coprime_part(f["u1"], f["G1"])
            if f["h"] > 1:
                paid += 1
            if d <= 1 or f["e"] == 0 or f["e1"] == 0:
                continue
            bad_p = [p for p in prime_factors(d)
                     if p != 2 and legendre(f["e"] * f["e1"], p) == -1]
            if not bad_p:
                continue
            defects += 1
            if f["h"] > 1:
                defects_with_h_gt_1 += 1
            if all(legendre(f["h"], p) == -1 for p in bad_p):
                defects_with_h_nonresidue += 1
            else:
                witnesses.append({"n": f["n"], "h": f["h"], "d": d, "bad_p": bad_p,
                                  "e": f["e"], "e1": f["e1"]})
            r2_would_need_h_next += 1
    return {
        "defect_steps": defects,
        "defect_steps_with_h_gt_1": defects_with_h_gt_1,
        "defect_steps_where_h_is_nonresidue_mod_every_bad_p": defects_with_h_nonresidue,
        "paid_steps_total": paid,
        "counterexamples_to_charge": witnesses[:8],
        "reading": "every Legendre defect is a paid step and h_n is a non-residue "
                   "mod each offending prime; the defect count below N is at most "
                   "log2 C_N because G_{n+1} = h_n G_n and G_N <= C_N",
    }


def part5_supply(all_frames: list[list[dict]], orbits: list[dict]) -> dict:
    """How often is the mechanism non-vacuous, and are sign changes forced?"""
    steps = 0
    with_p3 = 0
    all_p1mod4 = 0
    for frames in all_frames:
        for f in frames:
            d = coprime_part(f["u1"], f["G1"])
            if d <= 1:
                continue
            steps += 1
            ps = prime_factors(d)
            if any(p % 4 == 3 for p in ps):
                with_p3 += 1
            elif all(p % 4 == 1 for p in ps if p != 2):
                all_p1mod4 += 1
    longest_neg = 0
    longest_neg_seed = None
    sign_changes = 0
    neg_steps = 0
    total_E = 0
    for orb in orbits:
        cur = 0
        E = orb["E"]
        for i, e in enumerate(E):
            total_E += 1
            if e < 0:
                neg_steps += 1
                cur += 1
                if cur > longest_neg:
                    longest_neg, longest_neg_seed = cur, orb.get("seed")
            else:
                cur = 0
            if i + 1 < len(E) and e != 0 and E[i + 1] != 0 and (e < 0) != (E[i + 1] < 0):
                sign_changes += 1
    return {
        "steps_with_nontrivial_d": steps,
        "steps_where_d_has_a_3mod4_prime": with_p3,
        "nonvacuity_rate": (with_p3 / steps) if steps else None,
        "steps_where_d_is_a_sum_of_two_squares_shape": all_p1mod4,
        "total_error_steps": total_E,
        "negative_error_steps": neg_steps,
        "sign_changes": sign_changes,
        "longest_all_negative_run": longest_neg,
        "longest_all_negative_run_seed": longest_neg_seed,
    }


def part6_fixtures(step_cap: int, height_cap: int) -> dict:
    """The corpus's exact fixtures must NOT be excluded by the lemma."""
    out = []
    seeds = []
    # E = -1 cancellation-free seeds (C_0 = c, D_0 = c*m - 1 gives E_0 = -1)
    for c in (5, 11, 40, 101, 1000):
        for m in (3, 7, 33, 1001):
            seeds.append(("E_minus_one", c, c * m - 1))
    # the (11, 11*(33 + 79833600 k) - 1) recovery family
    for k in (0, 1, 2, 3, 5, 8, 13, 21, 100):
        seeds.append(("normalized_return_11", 11, 11 * (33 + 79833600 * k) - 1))
    total_checked = 0
    total_fail = 0
    for name, C0, D0 in seeds:
        orb = run_orbit(C0, D0, height_cap=height_cap, step_cap=step_cap,
                        exact_bits=200000, lean=False)
        orb["seed"] = [C0, D0]
        frames = primitive_frames(orb)
        checked = fails = 0
        flat_runs = 0     # e_n = e_{n+1} = -1: X = +1, a square, condition free
        for f in frames:
            d = coprime_part(f["u1"], f["G1"])
            if d <= 1:
                continue
            v_mod = (f["r"] % d) * pow(f["G"] % d, -1, d) % d
            X = f["h"] * f["e"] * f["e1"]
            checked += 1
            if (X - v_mod * v_mod) % d:
                fails += 1
            if f["e"] == -1 and f["e1"] == -1 and f["h"] == 1:
                flat_runs += 1
        total_checked += checked
        total_fail += fails
        out.append({"family": name, "seed": [C0, D0], "status": orb["status"],
                    "steps": orb["steps"], "frames_checked": checked,
                    "transport_failures": fails,
                    "flat_minus_one_steps_with_square_1": flat_runs,
                    "E_head": orb["E"][:12]})
    return {
        "fixtures": out,
        "total_frames_checked": total_checked,
        "total_transport_failures": total_fail,
        "reading": "flat E = -1 runs give X = +1, a square modulo every modulus, "
                   "so the Legendre invariant imposes no condition there: the "
                   "mechanism does not falsely exclude the corpus fixtures",
    }


# --------------------------------------------------------------------------
# driver
# --------------------------------------------------------------------------

def collect_orbits(qmax: int, step_cap: int, height_cap: int, top: int) -> list[dict]:
    scored = []
    for q in range(3, qmax + 1):
        for p in range(1, q):
            if gcd(p, q) != 1:
                continue
            orb = run_orbit(p, q, height_cap=height_cap, step_cap=step_cap,
                            exact_bits=4000, lean=True)
            scored.append((orb["steps"], max(orb["C"]), p, q))
    scored.sort(reverse=True)
    orbits = []
    for _, _, p, q in scored[:top]:
        orb = run_orbit(p, q, height_cap=height_cap, step_cap=step_cap,
                        exact_bits=200000, lean=False)
        orb["seed"] = [p, q]
        orbits.append(orb)
    return orbits


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true",
                    help="small, fast configuration (qmax 120, 24 orbits)")
    ap.add_argument("--qmax", type=int, default=300)
    ap.add_argument("--top", type=int, default=60)
    ap.add_argument("--step-cap", type=int, default=120)
    ap.add_argument("--height-cap", type=int, default=10 ** 9)
    ap.add_argument("--nogo-u0", type=int, default=1009)
    ap.add_argument("--nogo-steps", type=int, default=30)
    ap.add_argument("--nogo-trials", type=int, default=6)
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()
    if args.quick:
        args.qmax, args.top, args.step_cap = 120, 24, 80
        args.nogo_u0, args.nogo_steps, args.nogo_trials = 1009, 18, 3

    orbits = collect_orbits(args.qmax, args.step_cap, args.height_cap, args.top)
    all_frames = [primitive_frames(o) for o in orbits]

    report = {
        "probe": "erdos243_legendre_locking_probe",
        "config": {"qmax": args.qmax, "top": args.top, "step_cap": args.step_cap,
                   "height_cap": args.height_cap, "quick": args.quick},
        "orbits": [{"seed": o["seed"], "status": o["status"], "steps": o["steps"],
                    "max_C": max(o["C"])} for o in orbits],
        "total_primitive_frames": sum(len(f) for f in all_frames),
        "part1_raw_landing_is_vacuous": part1_raw_vacuity(all_frames),
        "part2_primitive_transport": part2_primitive_transport(all_frames),
        "part3_legendre_reading": part3_legendre(all_frames),
        "part4_square_defect": part4_square_defect(all_frames),
        "part8_defect_charge": part8_defect_charge(all_frames),
        "part5_supply_and_sign_changes": part5_supply(all_frames, orbits),
        "part6_corpus_fixtures": part6_fixtures(args.step_cap, args.height_cap),
        "part7_legendre_only_no_go": part7_legendre_only_no_go(
            args.nogo_u0, args.nogo_steps, args.nogo_trials),
    }
    p2 = report["part2_primitive_transport"]
    p3 = report["part3_legendre_reading"]
    report["verdict"] = {
        "transport_identity_holds_everywhere": p2["transport_failure_count"] == 0,
        "legendre_reading_holds_everywhere": len(p3["violations"]) == 0,
        "non_vacuity_automatic": p2["unit_failures_gcd_v_d_ne_1"] == 0,
        "fixtures_survive": report["part6_corpus_fixtures"]["total_transport_failures"] == 0,
    }
    text = json.dumps(report, indent=2, sort_keys=False)
    if args.out:
        Path(args.out).write_text(text + "\n", encoding="utf-8")
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
