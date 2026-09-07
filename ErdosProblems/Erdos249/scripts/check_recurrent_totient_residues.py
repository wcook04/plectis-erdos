#!/usr/bin/env python3
"""Finite checks for the all-modulus totient-observable classification.

Implements the Carmichael-semigroup formula for the recurrent totient classes
R_m (Type B annex Proposition B, independently re-coded).  Exact integer
arithmetic; SymPy is used only for factorisation and Carmichael's lambda.

Checks (``--quick`` is the default bounded run):

1. m = 12: R_12 is all six even residues.
2. m = 1092: R_1092 is all even residues except {302, 790}; |R| = 544.
   (Ford–Konyagin–Pomerance totient-free classes.)
3. Every totient with index n <= N and n not dividing rad(m) lands in the
   computed set, for a short list of moduli.
4. Proposition C exhaustive: no unit-centre representation of 2 mod 12.
5. Lemma A4 exhaustive: for 2 <= m <= M, every prime p dividing m, and
   2 <= nu <= Nu, a unit s exists with s^{nu-1}(s-1) ≡ p^{nu-1}(p-1) (mod m).
6. Optional small-L search for isolated p^2 pulses at residue 2 mod 12.

Boundary: these checks support implementation correctness of the finite
formula and the two negative witnesses.  They do not prove Theorem A, and
they do not decide irrationality of sum phi(n)/2^n.

Run: ``./repo-python <this file> --quick``
"""

from __future__ import annotations

import argparse
from math import gcd

from sympy import factorint, reduced_totient


def rad(m: int) -> int:
    r = 1
    for p in factorint(m):
        r *= int(p)
    return r


def totient_sieve(limit: int) -> list[int]:
    phi = list(range(limit + 1))
    for p in range(2, limit + 1):
        if phi[p] == p:
            for k in range(p, limit + 1, p):
                phi[k] -= phi[k] // p
    return phi


def recurrent_totient_residues(m: int) -> set[int]:
    """Finite formula (B): R_m = H_m * prod_{p|m} E_p."""
    if not isinstance(m, int) or m < 2:
        raise ValueError("m must be an integer at least 2")
    lam = int(reduced_totient(m))
    units = [s for s in range(m) if gcd(s, m) == 1]
    generators = {
        pow(s, e - 1, m) * (s - 1) % m
        for s in units
        for e in range(1, lam + 1)
    }
    semigroup = set(generators)
    pending = list(generators)
    while pending:
        x = pending.pop()
        for y in generators:
            z = x * y % m
            if z not in semigroup:
                semigroup.add(z)
                pending.append(z)
    residues = semigroup
    for p, alpha in factorint(m).items():
        p, alpha = int(p), int(alpha)
        coprime_part = m // p**alpha
        period = int(reduced_totient(coprime_part)) if coprime_part > 1 else 1
        factors = {1} | {
            pow(p, e - 1, m) * (p - 1) % m
            for e in range(1, alpha + period + 1)
        }
        residues = {x * y % m for x in residues for y in factors}
    return residues


def even_residues(m: int) -> set[int]:
    return set(range(0, m, 2)) if m % 2 == 0 else set()


def check_m12() -> dict:
    R = recurrent_totient_residues(12)
    expected = even_residues(12)
    return {
        "m": 12,
        "R": sorted(R),
        "expected_even": sorted(expected),
        "ok": R == expected,
    }


def check_m1092() -> dict:
    R = recurrent_totient_residues(1092)
    even = even_residues(1092)
    missing = even - R
    extra_odd = {r for r in R if r % 2 == 1}
    return {
        "m": 1092,
        "card_R": len(R),
        "card_even": len(even),
        "missing_even": sorted(missing),
        "extra_odd": sorted(extra_odd),
        "ok": missing == {302, 790} and not extra_odd and len(R) == 544,
    }


def check_brute_support(moduli: list[int], n_limit: int, phi: list[int]) -> list[dict]:
    rows = []
    for m in moduli:
        R = recurrent_totient_residues(m)
        Rrad = rad(m)
        bad = []
        for n in range(1, min(n_limit, len(phi) - 1) + 1):
            if Rrad % n == 0:
                continue  # n | rad(m)
            r = phi[n] % m
            if r not in R:
                bad.append((n, r))
                if len(bad) >= 8:
                    break
        rows.append({"m": m, "bad_count": len(bad), "bad_sample": bad, "ok": not bad})
    return rows


def check_prop_c(a_limit: int) -> dict:
    """No a <= a_limit and unit s mod 12 with phi(a)*(s-1) ≡ 2 (mod 12)."""
    phi = totient_sieve(a_limit)
    units = [s for s in range(12) if gcd(s, 12) == 1]
    hits = []
    for a in range(0, a_limit + 1):
        for s in units:
            if (phi[a] * (s - 1)) % 12 == 2:
                hits.append((a, s, phi[a]))
    return {
        "a_limit": a_limit,
        "hits": hits,
        "ok": not hits,
        "witness_phi_121": phi[121] if a_limit >= 121 else None,
        "witness_ok": a_limit >= 121 and phi[121] == 110 and 110 % 12 == 2,
    }


def check_lemma_a4(m_max: int, nu_max: int) -> dict:
    failures = []
    checked = 0
    for m in range(2, m_max + 1):
        units = [s for s in range(m) if gcd(s, m) == 1]
        for p in factorint(m):
            p = int(p)
            for nu in range(2, nu_max + 1):
                target = pow(p, nu - 1, m) * (p - 1) % m
                found = any(pow(s, nu - 1, m) * (s - 1) % m == target for s in units)
                checked += 1
                if not found:
                    failures.append({"m": m, "p": p, "nu": nu, "target": target})
                    if len(failures) >= 8:
                        return {"checked": checked, "failures": failures, "ok": False}
    return {"checked": checked, "failures": failures, "ok": not failures}


def find_isolated_prime_square_pulses(phi: list[int], L: int, search_limit: int) -> dict:
    """Search primes p ≡ 11 (mod 12) with n0 = p^2 isolated at residue 2 mod 12."""
    found = []
    for p in range(11, search_limit + 1):
        if p % 12 != 11:
            continue
        if p >= len(phi) or phi[p] != p - 1:
            continue  # not prime (sieve: phi[p] = p-1 iff p prime for p>1)
        n0 = p * p
        if n0 + L >= len(phi):
            break
        if phi[n0] % 12 != 2:
            continue
        isolated = True
        for j in range(1, L + 1):
            if phi[n0 - j] % 12 != 0 or phi[n0 + j] % 12 != 0:
                isolated = False
                break
        if isolated:
            found.append(n0)
            if len(found) >= 3:
                break
    return {"L": L, "centres": found, "ok": bool(found)}


def build_payload(quick: bool) -> dict:
    n_limit = 8000 if quick else 20000
    m_max = 40 if quick else 100
    nu_max = 6 if quick else 9
    a_limit = 200 if quick else 2000
    moduli = [2, 3, 4, 6, 8, 10, 12, 15, 18, 24, 30, 36, 60] if quick else [
        2, 3, 4, 6, 8, 10, 12, 15, 18, 24, 30, 36, 60, 1092
    ]
    phi = totient_sieve(max(n_limit, 121 * 121 + 8, 20000 if not quick else 8000))

    m12 = check_m12()
    m1092 = check_m1092()
    brute = check_brute_support(moduli, n_limit, phi)
    prop_c = check_prop_c(a_limit)
    lemma_a4 = check_lemma_a4(m_max, nu_max)
    pulses = [
        find_isolated_prime_square_pulses(phi, L, min(200 if quick else 800, int(len(phi) ** 0.5) - 2))
        for L in (1, 2)
    ]
    all_ok = (
        m12["ok"]
        and m1092["ok"]
        and all(r["ok"] for r in brute)
        and prop_c["ok"]
        and prop_c["witness_ok"]
        and lemma_a4["ok"]
    )
    return {
        "checker": "check_recurrent_totient_residues",
        "problem": "erdos_249",
        "mode": "quick" if quick else "full",
        "m12": m12,
        "m1092": m1092,
        "brute_support": brute,
        "prop_c": prop_c,
        "lemma_a4": lemma_a4,
        "prime_square_pulses": pulses,
        "all_checks_pass": all_ok,
        "claim_boundary": (
            "Finite formula and two negative witnesses only. "
            "Does not prove the all-modulus theorem and does not decide S."
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true", help="small deterministic run")
    args = parser.parse_args()
    payload = build_payload(args.quick)
    import json

    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if payload["all_checks_pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
