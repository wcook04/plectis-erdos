#!/usr/bin/env python3
"""Erdos 243, wave-2 desk S4: the cost of a large clean rise.

By r08 Corollary 6 (wave-1 B verified) the parent theorem is equivalent to

    #{n : h_n = 1 and e_n <= -3} < infinity.

A clean rise (h_n = 1, e_n = -m, m >= 3) carries no gcd charge itself, so any
closure must charge it to a LATER payment.  This probe measures that charge on
exact orbits and on the corpus's exact three-rise fixtures.

Parts
-----
1. fixture_continuation : the three exact three-rise crossing families
   (r03 sec.8, r07 sec.8, r08 sec.6) run FORWARD with the forced multiplier;
   the word (u, e, h) after the rise, the first payment and its size.
2. generic_clean_rises  : every clean rise with m >= 3 on a survey of exact
   orbits; gap to the first later payment, its size, and whether the payment
   size is bounded in m (candidate charge laws, falsified or not).
3. free_continuation    : the longest observed all-clean continuation after a
   clean rise m >= 3, together with the explicit free parameter
   v -> v + k * prod_{j<=L} u_j reproducing the same word (no local forced
   payment).
4. budget_identity      : the exact integer identity
   prod_n (u_n - e_n) = (prod_n h_n) * prod_{n>=1} u_n, i.e. the height
   telescoping, plus the normalised rise/fall/payment masses per orbit.
5. legendre_disjointness: Legendre defects (desk S1, Theorem S2) never occur at
   clean steps, so the S1 charge is identically zero on the r08 Cor 6 set.
6. s4r_rise_blocks     : FIXTURE S4-R, the corpus E = -1 cancellation-free
   family generalised to E = -m: arbitrarily long blocks of CLEAN RISES of any
   fixed size m >= 3, with normalised error m/c as small as desired and no
   payment anywhere in the block.

Usage
-----
    ./repo-python .../erdos243_clean_rise_cost_probe.py --quick
    ./repo-python .../erdos243_clean_rise_cost_probe.py --qmax 200 --out full.json
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from math import gcd
from pathlib import Path

_HERE = Path(__file__).resolve().parent
if str(_HERE) not in sys.path:
    sys.path.insert(0, str(_HERE))

from erdos243_orbit_engine import run_orbit  # noqa: E402

TERMINATED = "terminated"


# --------------------------------------------------------------------------
# primitive frames
# --------------------------------------------------------------------------
def frames(C0: int, D0: int, *, step_cap: int = 260, height_cap: int = 10 ** 9):
    """Primitive frames (n, u_n, e_n, h_n, u_{n+1}) plus orbit status."""
    orb = run_orbit(C0, D0, step_cap=step_cap, height_cap=height_cap, lean=False)
    C, E, G = orb["C"], orb["E"], orb["G"]
    out = []
    for n in range(len(E) - 1):
        g = G[n]
        gn1 = G[n + 1]
        u = C[n] // g
        e = E[n] // g
        h = gn1 // g
        un1 = C[n + 1] // gn1
        # exact consistency of the primitive cocycle
        assert h * un1 == u - e, (C0, D0, n, u, e, h, un1)
        out.append((n, u, e, h, un1))
    return out, orb


def is_qr(a: int, p: int) -> bool:
    a %= p
    if a == 0:
        return True
    return pow(a, (p - 1) // 2, p) == 1


def odd_prime_factors(n: int, bound: int = 10 ** 7):
    n = abs(n)
    ps = []
    d = 3
    while d * d <= n and d <= bound:
        if n % d == 0:
            ps.append(d)
            while n % d == 0:
                n //= d
        d += 2
    if n > 1 and n % 2 == 1:
        ps.append(n)
    return ps


# --------------------------------------------------------------------------
# part 1: the three exact three-rise crossing families, run forward
# --------------------------------------------------------------------------
def _digit(u, v):
    return (2 * v + 3 * u) // (2 * u)


def _crt(r1, m1, r2, m2):
    g = pow(m1, -1, m2)
    t = ((r2 - r1) * g) % m2
    return (r1 + m1 * t) % (m1 * m2)


def fixture_states(pmax: int = 60):
    """(tag, u, v) for the three families.  Reproduced, not retyped, from the
    wave-1 B probe p3_three_rise_families.py (same constructions)."""
    out = []
    primes = [p for p in range(11, pmax) if all(p % d for d in range(2, int(p ** .5) + 1))]
    for p in primes:
        if p % 3 == 2:
            out.append((f"F1_r03_p{p}", p - 1, p * (p - 4), p, 1))
    for p in primes:
        for t in (1, 2):
            u = p - t
            if u % 3 == 0:
                continue
            w = u + 3
            if gcd(p * p, w) != 1:
                continue
            inv = pow(u, -1, p * p)
            a = _crt((1 + 3 * inv) % (p * p), p * p, 1, w)
            while a <= 2 * u:
                a += p * p * w
            out.append((f"F2_r07_p{p}_t{t}", u, (a - 1) * u - 3, p, 2))
            break
    for p in primes:
        r = 1 if p % 3 == 2 else 2
        u = p - r
        u2 = u + 3
        inv = pow(u, -1, p ** 3)
        a = _crt((u2 * inv) % p ** 3, p ** 3, 1, u2)
        while a <= 2 * u:
            a += p ** 3 * u2
        out.append((f"F3_r08_p{p}", u, a * u - u2, p, 3))
    return out


def part1_fixture_continuation(pmax: int, step_cap: int):
    rows = []
    for tag, u, v, p, k in fixture_states(pmax):
        if gcd(u, v) != 1:
            continue
        fr, orb = frames(u, v, step_cap=step_cap)
        if not fr:
            continue
        n0, u0, e0, h0, u1 = fr[0]
        # first payment strictly after the rise
        first_pay, pay_size = None, None
        for (n, uu, ee, hh, _) in fr[1:]:
            if hh > 1:
                first_pay, pay_size = n, hh
                break
        clean_run = 0
        for (n, uu, ee, hh, _) in fr[1:]:
            if hh > 1:
                break
            clean_run += 1
        rows.append({
            "tag": tag, "p": p, "pk": k, "u": u, "rise_e": e0, "rise_h": h0,
            "u_next": u1, "steps": len(fr), "status": orb["status"],
            "clean_steps_after_rise": clean_run,
            "first_payment_gap": None if first_pay is None else first_pay - n0,
            "first_payment_size": pay_size,
            "word_after_rise": [(uu, ee, hh) for (_, uu, ee, hh, _) in fr[1:9]],
        })
    sizes = [r["first_payment_size"] for r in rows if r["first_payment_size"]]
    return {
        "n_fixtures": len(rows),
        "all_rises_are_clean_size_3": all(r["rise_e"] == -3 and r["rise_h"] == 1 for r in rows),
        "max_first_payment_size": max(sizes) if sizes else None,
        "min_first_payment_size": min(sizes) if sizes else None,
        "n_no_payment_before_stop": sum(1 for r in rows if r["first_payment_size"] is None),
        "max_clean_steps_after_rise": max((r["clean_steps_after_rise"] for r in rows), default=0),
        "rows": rows,
    }


# --------------------------------------------------------------------------
# part 2 / 4 / 5: survey of exact orbits
# --------------------------------------------------------------------------
def survey(qmax: int, step_cap: int, height_cap: int):
    rises = []          # clean rises with m >= 3
    orbit_rows = []
    defects = {"total": 0, "at_clean_steps": 0, "checked_frames": 0}
    ident_fail = 0
    for q in range(3, qmax + 1):
        for p in range(1, q):
            if gcd(p, q) != 1:
                continue
            fr, orb = frames(p, q, step_cap=step_cap, height_cap=height_cap)
            if len(fr) < 3:
                continue
            H = [f[3] for f in fr]
            # ---- part 4: exact height telescoping identity
            lhs = 1
            for (_, u, e, _, _) in fr:
                lhs *= (u - e)
            rhs = 1
            for h in H:
                rhs *= h
            for (_, _, _, _, un1) in fr:
                rhs *= un1
            rhs //= 1
            prod_u_tail = 1
            for (_, _, _, _, un1) in fr:
                prod_u_tail *= un1
            if lhs != (rhs // prod_u_tail) * prod_u_tail or lhs != _prod(H) * prod_u_tail:
                ident_fail += 1
            rise_mass = sum(math.log1p((-e) / u) for (_, u, e, _, _) in fr if e < 0)
            fall_mass = sum(-math.log1p(-e / u) for (_, u, e, _, _) in fr if e > 0)
            pay_mass = sum(math.log(h) for h in H)
            u_first = fr[0][1]
            u_last = fr[-1][4]
            orbit_rows.append({
                "seed": [p, q], "steps": len(fr), "status": orb["status"],
                "rise_mass": rise_mass, "fall_mass": fall_mass,
                "pay_mass": pay_mass,
                "log_height_growth": math.log(u_last / u_first),
                "residual": rise_mass - fall_mass - pay_mass - math.log(u_last / u_first),
            })
            # ---- part 5: Legendre defects vs clean steps
            for (n, u, e, h, un1) in fr:
                if n + 1 >= len(fr):
                    break
                e_next = fr[n + 1][2] if fr[n + 1][0] == n + 1 else None
                if e_next is None:
                    continue
                d = un1
                # largest divisor of u_{n+1} coprime to G_{n+1} is un1 itself in
                # primitive coordinates whenever gcd(u_{n+1}, G_{n+1}) = 1; use
                # the odd prime factors of u_{n+1} that do not divide e_n e_{n+1}
                x = e * e_next
                for pr in odd_prime_factors(d):
                    if pr < 3 or x % pr == 0:
                        continue
                    defects["checked_frames"] += 1
                    if not is_qr(x, pr):
                        defects["total"] += 1
                        if h == 1:
                            defects["at_clean_steps"] += 1
            # ---- part 2: clean rises m >= 3
            for i, (n, u, e, h, un1) in enumerate(fr):
                if h != 1 or e > -3:
                    continue
                gap, size, cum = None, None, 0.0
                clean_after = 0
                for j in range(i + 1, len(fr)):
                    hh = fr[j][3]
                    if hh > 1:
                        gap, size = j - i, hh
                        cum = math.log(hh)
                        break
                    clean_after += 1
                rises.append({
                    "seed": [p, q], "n": n, "m": -e, "u": u, "u_next": un1,
                    "gap": gap, "payment": size, "clean_after": clean_after,
                    "terminated_clean": gap is None and orb["status"] == TERMINATED,
                    "status": orb["status"],
                })
    return rises, orbit_rows, defects, ident_fail


def _prod(xs):
    out = 1
    for x in xs:
        out *= x
    return out


# --------------------------------------------------------------------------
# part 3: free continuation after a clean rise (the fixture that kills the
# local charge family)
# --------------------------------------------------------------------------
def part3_free_continuation(rises, qmax_seed_cap: int = 4):
    """Take the observed clean rise with the longest all-clean continuation and
    exhibit the free parameter v -> v + k * prod_{j<=L} C_j."""
    best = max(rises, key=lambda r: r["clean_after"], default=None)
    if best is None:
        return {"found": False}
    p, q = best["seed"]
    orb = run_orbit(p, q, step_cap=260, height_cap=10 ** 9, lean=False)
    L = best["n"] + best["clean_after"] + 2
    L = min(L, len(orb["C"]))
    M = _prod(orb["C"][:L])
    ref_E = orb["E"][:L]
    agree = []
    for k in range(1, qmax_seed_cap + 1):
        o2 = run_orbit(p, q + k * M, step_cap=L + 4, height_cap=10 ** 12, lean=True)
        same = o2["E"][: len(ref_E)] == ref_E
        agree.append({"k": k, "same_word_to_L": same, "L": L})
    return {
        "found": True, "seed": [p, q], "rise_index": best["n"], "m": best["m"],
        "u_at_rise": best["u"], "clean_steps_after_rise": best["clean_after"],
        "payment_after": best["payment"], "gap": best["gap"],
        "free_modulus_bits": M.bit_length(), "L": L,
        "family": f"(C0,D0) = ({p}, {q} + k*M), M = prod_(j<{L}) C_j",
        "agreement": agree,
        "all_agree": all(a["same_word_to_L"] for a in agree),
    }


# --------------------------------------------------------------------------
# part 6: FIXTURE S4-R -- the corpus E = -1 cancellation-free block
# generalised to E = -m, i.e. arbitrarily long blocks of CLEAN RISES of any
# fixed size m >= 3.  This is the fixture that kills every local charge on a
# clean rise.
#
#   heights      c_n = c + n m
#   invariant    D_n = (a_n - 1) c_n - m ,   a_n = 1 + c_{n+1} k_n
#   recursion    a_{n+1} - 1 = k_n (a_n c_n - m) ,
#                k_{n+1} = (k_n / c_{n+2}) (a_n c_n - m)
#   seed         k_0 = lam * prod_{j=2}^{H+1} c_j          (lam >= 1 free)
# --------------------------------------------------------------------------
def s4r_seed(c: int, m: int, H: int, lam: int = 1):
    """Seed (C_0, D_0) of fixture S4-R.  Requires gcd(c, m) = 1 and 2m < c."""
    cs = [c + n * m for n in range(H + 3)]
    k = lam
    for j in range(2, H + 2):
        k *= cs[j]
    a = 1 + cs[1] * k
    D = (a - 1) * cs[0] - m
    return cs, k, a, D


def s4r_internal_chain(c: int, m: int, H: int, lam: int = 1, exact_cap: int = 7):
    """Check every invariant of the closed-form recursion (exact big ints).

    Capped at `exact_cap` steps because a_n is doubly exponential."""
    cs, k, a, D = s4r_seed(c, m, H, lam)
    checked = 0
    for n in range(min(H, exact_cap)):
        assert D == (a - 1) * cs[n] - m, ("invariant", n)
        assert a == 1 + cs[n + 1] * k, ("a-form", n)
        assert gcd(cs[n], D) == 1, ("primitive", n)
        assert gcd(a, D) == 1, ("clean: gcd(a_n, D_n) = 1", n)
        assert 2 * m < cs[n], ("centring", n)
        e = D % cs[n]
        if 2 * e > cs[n]:
            e -= cs[n]
        assert e == -m, ("error", n, e)
        assert (D - e) // cs[n] + 1 == a, ("pseudo-greedy digit", n)
        assert k % cs[n + 2] == 0, ("divisibility chain", n)
        k_next = (k // cs[n + 2]) * (a * cs[n] - m)
        a_next = 1 + cs[n + 2] * k_next
        D_next = a * D
        assert a_next - 1 == k * (a * cs[n] - m), ("recursion", n)
        assert D_next == (a_next - 1) * cs[n + 1] - m, ("next invariant", n)
        assert a_next > a, ("increasing multipliers", n)
        # Sylvester defect: a^2 - a + 1 - a' = m (a^2 - 1) / c_{n+1}
        assert a * a - a + 1 - a_next == m * (a * a - 1) // cs[n + 1], ("defect", n)
        assert 0 < a * a - a_next < 2 * m * a * a // cs[n + 1] + a, ("defect size", n)
        a, D, k = a_next, D_next, k_next
        checked += 1
    return checked


def part6_s4r_rise_blocks(cases, exact_cap: int = 7):
    rows = []
    for (c, m, H, lam) in cases:
        if gcd(c, m) != 1 or 2 * m >= c:
            rows.append({"c": c, "m": m, "H": H, "lam": lam, "admissible": False})
            continue
        checked = s4r_internal_chain(c, m, H, lam, exact_cap)
        cs, k, a, D = s4r_seed(c, m, H, lam)
        orb = run_orbit(cs[0], D, step_cap=H + 8, height_cap=10 ** 300, lean=False)
        E, C, G = orb["E"], orb["C"], orb["G"]
        word_ok = len(E) >= H and all(E[n] == -m for n in range(H))
        clean_ok = len(G) >= H and all(G[n] == 1 for n in range(H))
        first_pay = next((n for n in range(1, len(G)) if G[n] != G[n - 1]), None)
        rows.append({
            "c": c, "m": m, "H": H, "lam": lam, "admissible": True,
            "internal_steps_checked": checked,
            "engine_word_all_minus_m": word_ok,
            "engine_clean_through_block": clean_ok,
            "first_payment_index": first_pay,
            "payment_inside_block": first_pay is not None and first_pay < H,
            "normalised_error_at_start": m / c,
            "D0_bits": D.bit_length(), "orbit_status": orb["status"],
        })
    ok = [r for r in rows if r.get("engine_word_all_minus_m") and r.get("engine_clean_through_block")]
    return {
        "n_cases": len(rows), "n_verified": len(ok),
        "max_verified_block_length": max((r["H"] for r in ok), default=0),
        "max_verified_rise_size": max((r["m"] for r in ok), default=0),
        "any_payment_inside_block": any(r.get("payment_inside_block") for r in rows),
        "min_normalised_error": min((r["normalised_error_at_start"] for r in ok), default=None),
        "rows": rows,
    }


# --------------------------------------------------------------------------
def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--qmax", type=int, default=120)
    ap.add_argument("--pmax", type=int, default=60)
    ap.add_argument("--step-cap", type=int, default=260)
    ap.add_argument("--height-cap", type=int, default=10 ** 9)
    ap.add_argument("--block-H", type=int, default=16)
    ap.add_argument("--out", type=str, default=None)
    args = ap.parse_args()
    if args.quick:
        args.qmax, args.pmax, args.step_cap = 40, 24, 120
        args.block_H = 10

    H = args.block_H
    cases = [(10, 3, min(H, 6), 1), (13, 3, H, 1), (13, 4, H, 1), (17, 5, H, 1),
             (31, 9, H, 1), (49, 16, H, 1), (1009, 7, H, 1), (100003, 3, H, 1),
             (13, 4, H, 2), (13, 4, H, 1000003), (100003, 3, min(H, 12), 7)]
    part6 = part6_s4r_rise_blocks(cases)

    part1 = part1_fixture_continuation(args.pmax, args.step_cap)
    rises, orbit_rows, defects, ident_fail = survey(args.qmax, args.step_cap, args.height_cap)
    part3 = part3_free_continuation(rises)

    pays = [r["payment"] for r in rises if r["payment"]]
    by_m = {}
    for r in rises:
        by_m.setdefault(r["m"], {"n": 0, "max_payment": 0, "max_clean_after": 0,
                                 "n_terminated_clean": 0})
        d = by_m[r["m"]]
        d["n"] += 1
        d["max_payment"] = max(d["max_payment"], r["payment"] or 0)
        d["max_clean_after"] = max(d["max_clean_after"], r["clean_after"])
        d["n_terminated_clean"] += int(bool(r["terminated_clean"]))

    report = {
        "part1_fixture_continuation": part1,
        "part2_generic_clean_rises": {
            "n_rises_m_ge_3": len(rises),
            "max_m": max((r["m"] for r in rises), default=0),
            "n_with_no_later_payment": sum(1 for r in rises if r["payment"] is None),
            "n_terminated_clean": sum(1 for r in rises if r["terminated_clean"]),
            "payment_sizes_seen": sorted(set(pays)),
            "max_payment": max(pays) if pays else None,
            "max_clean_steps_after_rise": max((r["clean_after"] for r in rises), default=0),
            "by_rise_size": {str(k): v for k, v in sorted(by_m.items())},
            "charge_law_falsifiers": {
                "payment_ge_m": sum(1 for r in rises if r["payment"] and r["payment"] < r["m"]),
                "payment_ge_2": sum(1 for r in rises if r["payment"] and r["payment"] < 2),
                "payment_ge_two_pow_clean_after": sum(
                    1 for r in rises
                    if r["payment"] and r["payment"] < 2 ** min(r["clean_after"], 20)),
                "n_rises_with_payment": len(pays),
            },
        },
        "part3_free_continuation": part3,
        "part4_budget_identity": {
            "orbits": len(orbit_rows),
            "exact_identity_failures": ident_fail,
            "max_abs_residual": max((abs(o["residual"]) for o in orbit_rows), default=0.0),
            "max_pay_mass": max((o["pay_mass"] for o in orbit_rows), default=0.0),
            "max_rise_mass": max((o["rise_mass"] for o in orbit_rows), default=0.0),
            "mean_pay_over_rise": (
                sum(o["pay_mass"] for o in orbit_rows)
                / max(sum(o["rise_mass"] for o in orbit_rows), 1e-12)),
        },
        "part5_legendre_disjointness": defects,
        "part6_s4r_rise_blocks": part6,
        "params": vars(args),
    }
    slim = {k: v for k, v in report.items()
            if k not in ("part1_fixture_continuation", "part6_s4r_rise_blocks")}
    slim["part1_fixture_continuation"] = {k: v for k, v in part1.items() if k != "rows"}
    slim["part6_s4r_rise_blocks"] = {k: v for k, v in part6.items() if k != "rows"}
    print(json.dumps(slim, indent=1, default=str))
    if args.out:
        Path(args.out).write_text(json.dumps(report, indent=1, default=str))
        print(f"# full report -> {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
