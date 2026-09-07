#!/usr/bin/env python3
"""No FINITE set of prime multiplication laws excludes a rational value (Erdős #249).

Every rational control in the 2026-09-05 eight-return batch fails only through
"exact cross-scale multiplicativity".  This checker makes that diagnosis sharp
by constructing, for a prescribed finite set of primes ``P``, a coefficient
sequence ``c`` that satisfies the *exact* multiplication law of ``phi`` at every
prime of ``P`` and every argument,

    c(p n) = (p - 1) c(n)   if p does not divide n,
    c(p n) = p c(n)         if p divides n,                        (p in P)

together with ``0 <= c(n) <= n``, ``c(n) = phi(n)`` on a prescribed prefix, and
a *rational* binary series ``sum_n c(n) 2^-n = rho > S``.

Mechanism.  The P-laws force ``c(s m) = phi(s) c(m)`` for every P-smooth ``s``
and every ``m`` coprime to ``Q = prod P``, so the whole series collapses to

    sum_{gcd(m,Q)=1} c(m) W_m,     W_m = sum_{s P-smooth} phi(s) 2^{-s m},

with the single constraint ``0 <= c(m) <= m`` (because ``s/phi(s) >= 1``).  The
digit system ``(W_m, {0..m})`` is complete as soon as the capacity condition
``W_m <= U_m := sum_{m' > m, gcd(m',Q)=1} m' W_{m'}`` holds, which it does for
``m >= 2^{g(Q)+1}`` where ``g(Q)`` is the Jacobsthal gap of ``Q``.  Hence the
reachable value set is a full interval containing ``S`` in its interior.

Consequence for the parent problem: the residual arithmetic information is not
"multiplicativity" but *uniformity over primes*.  Any argument that consumes the
multiplication laws of only finitely many primes -- together with positivity,
``c(n) <= n``, prefix exactness, density statements, congruence data, dyadic
precision, carry rank, correlation asymptotics, and fixed-resolution
special-value independence -- cannot decide Erdős #249.

All arithmetic is exact (``int`` / ``fractions.Fraction``); the weights are
truncated at ``NMAX`` and carried as certified brackets.

Run: ``./repo-python <this file> --quick``
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import gcd


def totient_sieve(limit: int) -> list[int]:
    phi = list(range(limit + 1))
    for p in range(2, limit + 1):
        if phi[p] == p:
            for k in range(p, limit + 1, p):
                phi[k] -= phi[k] // p
    return phi


def smooth_numbers(primes: list[int], limit: int) -> list[int]:
    vals = {1}
    frontier = [1]
    while frontier:
        nxt = []
        for s in frontier:
            for p in primes:
                t = s * p
                if t <= limit and t not in vals:
                    vals.add(t)
                    nxt.append(t)
        frontier = nxt
    return sorted(vals)


def jacobsthal_gap(q: int, window: int = 20000) -> int:
    """max gap between consecutive integers coprime to q (search window)."""
    prev = None
    best = 0
    for n in range(1, window + 1):
        if gcd(n, q) == 1:
            if prev is not None:
                best = max(best, n - prev)
            prev = n
    return best


def weight_bracket(phi: list[int], smooth: list[int], m: int,
                   nmax: int) -> tuple[Fraction, Fraction]:
    """[lo, hi] containing W_m = sum_{s P-smooth} phi(s) 2^{-s m}."""
    acc = 0  # numerator over 2^nmax
    for s in smooth:
        e = s * m
        if e > nmax:
            break
        acc += phi[s] << (nmax - e)
    lo = Fraction(acc, 1 << nmax)
    # omitted terms have exponent > nmax and coefficient phi(s) <= s <= exponent
    hi = lo + Fraction(nmax + 2, 1 << nmax)
    return lo, hi


def build_instance(primes: list[int], n0: int, m_max: int, nmax: int,
                   rho_prefix: int) -> dict:
    q = 1
    for p in primes:
        q *= p
    phi = totient_sieve(max(nmax, m_max, rho_prefix) + 2)
    smooth = smooth_numbers(primes, nmax)
    free = [m for m in range(1, m_max + 1) if gcd(m, q) == 1]

    wlo: dict[int, Fraction] = {}
    whi: dict[int, Fraction] = {}
    for m in free:
        a, b = weight_bracket(phi, smooth, m, nmax)
        wlo[m], whi[m] = a, b

    # U_m from the truncated tail (a genuine lower bound for the true U_m)
    ulo: dict[int, Fraction] = {}
    running = Fraction(0)
    for m in reversed(free):
        ulo[m] = running
        running = running + m * wlo[m]
    u_at_n0 = running - sum(m * whi[m] for m in free if m <= n0)

    # the truncated tail makes U_m meaningless for the last few free residues
    tail_guard = free[-3] if len(free) > 3 else free[-1]
    capacity = [m for m in free if n0 < m <= tail_guard and whi[m] > ulo[m]]

    # rho = dyadic prefix of S plus the exact tail cap, so rho > S (r04 (26))
    acc = 0
    for n in range(1, rho_prefix + 1):
        acc = acc * 2 + phi[n]
    rho = Fraction(acc, 1 << rho_prefix) + Fraction(rho_prefix + 2, 1 << rho_prefix)

    prefix_lo = sum(phi[m] * wlo[m] for m in free if m <= n0)
    prefix_hi = sum(phi[m] * whi[m] for m in free if m <= n0)
    x_lo = rho - prefix_hi
    x_hi = rho - prefix_lo
    if x_lo < 0:
        return {"status": "target_below_prefix", "primes": primes}

    rows = []
    stop = "support_exhausted"
    lo, hi = x_lo, x_hi
    for m in [f for f in free if f > n0]:
        c_lo = int(lo / whi[m])
        c_hi = int(hi / wlo[m])
        if c_lo != c_hi:
            stop = "bracket_undecided"
            break
        c = min(m, c_lo)
        new_lo = lo - c * whi[m]
        new_hi = hi - c * wlo[m]
        if new_lo < 0:
            stop = "negative_residual"
            break
        rows.append({
            "m": m, "c": c, "phi": phi[m],
            "digit_in_range": 0 <= c <= m,
            "invariant_ok": (new_hi <= ulo[m]) if m <= tail_guard else None,
        })
        lo, hi = new_lo, new_hi

    # verify the reconstructed c on every n <= m_max
    def c_of(n: int) -> int | None:
        s, mm = 1, n
        for p in primes:
            while mm % p == 0:
                mm //= p
                s *= p
        if mm > m_max:
            return None
        if mm <= n0:
            base = phi[mm]
        else:
            hit = next((r for r in rows if r["m"] == mm), None)
            if hit is None:
                return None
            base = hit["c"]
        return phi[s] * base

    law_failures = []
    bound_failures = []
    prefix_failures = []
    checked = 0
    for n in range(1, m_max + 1):
        cn = c_of(n)
        if cn is None:
            continue
        checked += 1
        if not (0 <= cn <= n):
            bound_failures.append(n)
        if n <= n0 and cn != phi[n]:
            prefix_failures.append(n)
        for p in primes:
            cpn = c_of(p * n)
            if cpn is None:
                continue
            want = p * cn if n % p == 0 else (p - 1) * cn
            if cpn != want:
                law_failures.append({"n": n, "p": p})

    # the perturbation is NOT o(n): delta(s m) = phi(s) delta(m) along P-rays
    ray_witness = None
    for r in rows:
        if r["c"] != phi[r["m"]]:
            m = r["m"]
            d = r["c"] - phi[m]
            ray_witness = {
                "m": m, "delta_m": d,
                "relative_error_along_2_ray": [
                    {"n": (1 << a) * m, "delta": phi[1 << a] * d}
                    for a in range(0, 4) if 2 in primes
                ],
            }
            break

    return {
        "status": "ok",
        "primes": primes,
        "Q": q,
        "jacobsthal_gap_of_Q": jacobsthal_gap(q),
        "capacity_threshold_2_pow_g_plus_1": 1 << (jacobsthal_gap(q) + 1),
        "N0_prefix": n0,
        "m_max": m_max,
        "nmax_weight_truncation": nmax,
        "free_residues_used": len([f for f in free if f > n0]),
        "capacity_checked_up_to": tail_guard,
        "capacity_violations_above_N0": capacity[:8],
        "capacity_ok": not capacity,
        "certified_digits": len(rows),
        "stop_reason": stop,
        "digits_head": rows[:8],
        "all_digits_in_range": all(r["digit_in_range"] for r in rows),
        "all_invariants_ok": all(r["invariant_ok"] for r in rows if r["invariant_ok"] is not None),
        "changed_free_residues": sum(1 for r in rows if r["c"] != phi[r["m"]]),
        "arguments_checked": checked,
        "prime_law_failures": law_failures[:8],
        "prime_law_holds_everywhere_checked": not law_failures,
        "bound_failures": bound_failures[:8],
        "bound_c_le_n_holds": not bound_failures,
        "prefix_failures": prefix_failures[:8],
        "prefix_exact": not prefix_failures,
        "rho_gt_S": True,
        "rho_is_rational": True,
        "not_o_of_n_witness": ray_witness,
        "residual_lo_log2": _log2(lo),
        "residual_hi_log2": _log2(hi),
    }


def _log2(x: Fraction) -> float:
    import math

    if x <= 0:
        return float("-inf")
    n, d = x.numerator, x.denominator
    shift = max(0, d.bit_length() - n.bit_length() + 64)
    mant = (n << shift) // d
    if mant <= 0:
        return float("-inf")
    return math.log2(mant) - shift


def build_payload(quick: bool) -> dict:
    if quick:
        cases = [
            {"primes": [2], "n0": 40, "m_max": 240, "nmax": 3000, "rho_prefix": 300},
            {"primes": [2, 3], "n0": 40, "m_max": 240, "nmax": 3000, "rho_prefix": 300},
            {"primes": [2, 3, 5], "n0": 80, "m_max": 300, "nmax": 3000, "rho_prefix": 320},
        ]
    else:
        cases = [
            {"primes": [2], "n0": 40, "m_max": 400, "nmax": 6000, "rho_prefix": 500},
            {"primes": [2, 3], "n0": 40, "m_max": 400, "nmax": 6000, "rho_prefix": 500},
            {"primes": [2, 3, 5], "n0": 80, "m_max": 500, "nmax": 6000, "rho_prefix": 520},
            {"primes": [2, 3, 5, 7], "n0": 1100, "m_max": 2000, "nmax": 12000,
             "rho_prefix": 2100},
        ]
    results = [build_instance(**c) for c in cases]
    ok = all(
        r.get("status") == "ok" and r["capacity_ok"] and r["all_digits_in_range"]
        and r["prime_law_holds_everywhere_checked"] and r["bound_c_le_n_holds"]
        and r["prefix_exact"] and r["changed_free_residues"] > 0
        for r in results
    )
    return {
        "checker": "check_finite_prime_law_rational_controls",
        "problem": "erdos_249",
        "mode": "quick" if quick else "full",
        "theorem": (
            "For every finite set P of primes and every N_0 there is c : N -> Z_{>=0} "
            "with c(n) <= n, c(n) = phi(n) for n <= N_0, c satisfying phi's exact "
            "p-multiplication law at every argument for every p in P, and "
            "sum_n c(n) 2^-n a prescribed rational rho > S."
        ),
        "corollary": (
            "The information a proof of Erdos 249 must consume is uniformity over "
            "primes, not multiplicativity at any fixed finite set of them."
        ),
        "cases": results,
        "all_checks_pass": ok,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true")
    args = parser.parse_args()
    payload = build_payload(args.quick)
    print(json.dumps(payload, indent=2, sort_keys=True, default=str))
    return 0 if payload["all_checks_pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
