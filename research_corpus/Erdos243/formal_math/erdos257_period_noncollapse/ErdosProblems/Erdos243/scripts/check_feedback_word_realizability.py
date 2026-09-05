#!/usr/bin/env python3
"""Exact finite-state realizability of numerator words for the Erdos 243 transport.

Setting.  Integers (C_n, D_n, a_n) with the product-cleared transport

    C_{n+1} = a_n C_n - D_n,     D_{n+1} = a_n D_n.                        (T)

Any integer orbit reduces modulo every positive integer m to a (T)-orbit over
Z/mZ.  Hence: if a prescribed numerator word (c_0, ..., c_{L}) in (Z/mZ)^{L+1}
admits NO choice of denominators d_i and multipliers a_i in Z/mZ satisfying (T),
then no integer orbit can carry that residue word, at any index.  This module is
the exact decision procedure for that question, plus the enumerations and
certificate checks used by wave-1 verification of returns r02 and r06.

Two independent implementations of the decision procedure are provided and
cross-checked against each other:

  * ``reachable_denominators`` -- brute force over all a in Z/mZ (valid for every
    modulus m, prime or composite).  This is the ``possible_final_denominators``
    routine of r06 section 7.
  * ``reachable_denominators_field`` -- the closed-form state-set transport of
    r02 section 2, equations (5)-(6), valid only for prime m.

Nonemptiness of the final state set is NOT a claim that an integer lift exists;
only emptiness is used, and only as an obstruction.

Run:
    ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/scripts/check_feedback_word_realizability.py --quick
    ./repo-python .../check_feedback_word_realizability.py --json
"""

from __future__ import annotations

import argparse
import json
import sys
from itertools import product
from math import gcd


# --------------------------------------------------------------------------
# 1. The exact decision procedure
# --------------------------------------------------------------------------


def reachable_denominators(modulus: int, word) -> set:
    """All d_L in Z/mZ reachable through an exact (T)-segment with numerators `word`.

    Brute force over every multiplier residue; valid for any modulus >= 1.
    Empty result  <=>  the word is unrealizable over Z/mZ  <=>  no integer orbit
    can carry it.
    """
    live = set(range(modulus))
    for current, following in zip(word, word[1:]):
        c = current % modulus
        g = gcd(c, modulus)
        step = modulus // g
        nxt = set()
        for d in live:
            r = (d + following) % modulus
            if r % g:
                continue                       # a*c = d + c' has no solution
            a0 = _solve_linear_congruence(c, r, modulus, g)
            for j in range(g):                 # the g solutions a0 + j*step
                nxt.add(((a0 + j * step) * d) % modulus)
        live = nxt
        if not live:
            return live
    return live


def _solve_linear_congruence(c: int, r: int, modulus: int, g: int) -> int:
    """One solution a of a*c = r (mod modulus), given g = gcd(c, modulus) | r."""
    if c == 0:
        return 0                                # then g = modulus and r = 0
    cc, rr, mm = c // g, r // g, modulus // g
    return (rr * pow(cc, -1, mm)) % mm


def reachable_denominators_field(prime: int, word) -> set:
    """r02 section 2 state-set transport (5)-(6).  Prime modulus only."""
    live = set(range(prime))
    for i in range(len(word) - 1):
        c_i, c_next = word[i] % prime, word[i + 1] % prime
        if c_i != 0:
            inv = pow(c_i, prime - 2, prime)
            live = {(x * (x + c_next) % prime) * inv % prime for x in live}
        else:
            forced = (-c_next) % prime
            if forced not in live:
                live = set()
            elif c_next % prime == 0:
                live = {0}
            else:
                live = set(range(prime))
        if not live:
            return live
    return live


def is_forbidden(modulus: int, word) -> bool:
    return not reachable_denominators(modulus, word)


# --------------------------------------------------------------------------
# 2. Certificates claimed by r02 and r06
# --------------------------------------------------------------------------

R02_CERTIFICATES = [
    (3, (1, 0, 1), "r02 (11)"),
    (3, (2, 0, 2), "r02 (11)"),
    (5, (1, 0, 3), "r02 (11)"),
    (7, (3, 3, 0, 1), "r02 (12) Lemma 3"),
    (11, (7, 8, 0, 5), "r02 (13) Lemma 4"),
]

R06_CERTIFICATES = [
    (3, (1, 0, 1), "r06 (15)"),
    (4, (0, 0, 2), "r06 (26)/(27) via Lemma 4"),
    (7, (3, 0, 6), "r06 (16)"),
    (11, (7, 8, 0, 5), "r06 (20) Prop 7"),
]


def check_certificates() -> dict:
    out = []
    for tag, certs in (("r02", R02_CERTIFICATES), ("r06", R06_CERTIFICATES)):
        for modulus, word, cite in certs:
            brute = reachable_denominators(modulus, word)
            row = {
                "return": tag,
                "citation": cite,
                "modulus": modulus,
                "word": list(word),
                "reachable_denominators": sorted(brute),
                "forbidden": not brute,
            }
            if _is_prime(modulus):
                field = reachable_denominators_field(modulus, word)
                row["field_transport_agrees"] = field == brute
            out.append(row)
    return {"certificates": out,
            "all_forbidden": all(r["forbidden"] for r in out),
            "field_agreement": all(r.get("field_transport_agrees", True) for r in out)}


# --------------------------------------------------------------------------
# 3. Exhaustive enumeration of forbidden words
# --------------------------------------------------------------------------


def _is_prime(n: int) -> bool:
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def enumerate_forbidden(modulus: int, length: int, exclude_absorbing: bool = False):
    """All forbidden words of the given length over Z/mZ.

    ``exclude_absorbing`` drops words containing the trivial pattern (0,0,z), z!=0,
    which is forbidden over every ring (r06 Lemma 4) and therefore uninformative.
    """
    found = []
    for word in product(range(modulus), repeat=length):
        if exclude_absorbing and _has_absorbing_pattern(modulus, word):
            continue
        if is_forbidden(modulus, word):
            found.append(word)
    return found


def _has_absorbing_pattern(modulus: int, word) -> bool:
    for i in range(len(word) - 2):
        if word[i] % modulus == 0 and word[i + 1] % modulus == 0 and word[i + 2] % modulus:
            return True
    return False


def forbidden_census(primes, lengths=(3, 4), extra_moduli=(4, 8, 9)) -> dict:
    census = []
    for m in list(primes) + list(extra_moduli):
        for L in lengths:
            all_words = enumerate_forbidden(m, L)
            nontrivial = [w for w in all_words if not _has_absorbing_pattern(m, w)]
            census.append({
                "modulus": m,
                "prime": _is_prime(m),
                "length": L,
                "total_words": m ** L,
                "forbidden": len(all_words),
                "forbidden_fraction": len(all_words) / m ** L,
                "forbidden_nonabsorbing": len(nontrivial),
                "sample_nonabsorbing": [list(w) for w in nontrivial[:12]],
            })
    return {"census": census}


# --------------------------------------------------------------------------
# 4. Polynomial profiles -> minimal certificates
# --------------------------------------------------------------------------


def poly_words(coeffs, modulus: int, length: int):
    """All (start residue t, word) pairs for P(t..t+length-1) mod m, t = 0..m-1."""
    def ev(x):
        acc = 0
        for c in coeffs:            # coeffs high -> low
            acc = acc * x + c
        return acc % modulus
    return [(t, tuple(ev(t + j) for j in range(length))) for t in range(modulus)]


def minimal_certificate(coeffs, max_modulus: int = 40, lengths=(3, 4)):
    """Smallest (modulus, length, start) whose block from P is forbidden."""
    for m in range(2, max_modulus + 1):
        for L in lengths:
            if L > m:
                continue
            for t, word in poly_words(coeffs, m, L):
                if is_forbidden(m, word):
                    return {"modulus": m, "length": L, "start_residue": t,
                            "word": list(word)}
    return None


R02_TABLE = [
    # (u(k) coefficients high->low, prime, start residue, word)  -- r02 section 7
    ((1, 0, 0), 3, 2, (1, 0, 1)),
    ((1, 1, 1), 3, 0, (1, 0, 1)),
    ((1, 1, -1), 11, 5, (7, 8, 0, 5)),
    ((2, 0, -1), 7, 3, (3, 3, 0, 1)),
    ((2, 2, 1), 5, 0, (1, 0, 3)),
    ((2, 2, -1), 3, 0, (2, 0, 2)),
]


def check_r02_table() -> dict:
    rows = []
    for coeffs, p, start, claimed in R02_TABLE:
        def ev(x):
            acc = 0
            for c in coeffs:
                acc = acc * x + c
            return acc
        actual = tuple(ev(start + j) % p for j in range(len(claimed)))
        rows.append({
            "polynomial": list(coeffs),
            "prime": p,
            "start_residue": start,
            "claimed_word": list(claimed),
            "actual_word": list(actual),
            "word_matches": actual == claimed,
            "word_forbidden": is_forbidden(p, actual),
            "raw_values": [ev(start + j) for j in range(len(claimed))],
            "minimal_certificate": minimal_certificate(coeffs),
        })
    return {"table": rows,
            "all_ok": all(r["word_matches"] and r["word_forbidden"] for r in rows)}


# --------------------------------------------------------------------------
# 5. r06 Theorem 8: exhaustive construction over monic integer quadratics
# --------------------------------------------------------------------------


def theorem8_certificate(b: int, c: int):
    """Reproduce the r06 Theorem 8 case split for Q(n) = n^2 + b n + c.

    Returns the construction (modulus, block, start residue in the translated
    variable x) selected by sections 4.1-4.5.
    """
    if b % 2 == 0:
        s = b // 2
        k = c - s * s
        # Q(n) = x^2 + k, x = n + s
        if k == 0:
            return {"branch": "4.1 k=0", "modulus": 3, "x_start": -1,
                    "block": [1, 0, 1], "shift": s}
        p = _odd_prime_factor(4 * k + 1)
        r = (-1 * pow(2, -1, p)) % p
        return {"branch": "4.1 k!=0", "modulus": p, "x_start": r,
                "block": [0, 0, 2], "shift": s}
    s = (b - 1) // 2
    k = c - s * (s + 1)
    # Q(n) = x^2 + x + k, x = n + s
    if k % 2 == 0:
        r = 3 if k % 4 == 0 else 1
        return {"branch": "4.2 k even", "modulus": 4, "x_start": r,
                "block": [0, 0, 2], "shift": s}
    if abs(k) > 1:
        p = _odd_prime_factor(k)
        return {"branch": "4.3 k odd |k|>1", "modulus": p, "x_start": -1,
                "block": [0, 0, 2], "shift": s}
    if k == 1:
        return {"branch": "4.4 x^2+x+1", "modulus": 7, "x_start": 1,
                "block": [3, 0, 6], "shift": s}
    return {"branch": "4.5 x^2+x-1", "modulus": 11, "x_start": 5,
            "block": [7, 8, 0, 5], "shift": s}


def _odd_prime_factor(n: int) -> int:
    n = abs(n)
    d = 3
    while d * d <= n:
        if n % d == 0:
            return d
        d += 2
    if n > 1 and n % 2:
        return n
    raise ValueError(f"no odd prime factor of {n}")


def check_theorem8(b_range=range(-20, 21), c_range=range(-100, 101)) -> dict:
    bad = []
    lengths = {}
    pairs = 0
    for b in b_range:
        for c in c_range:
            pairs += 1
            cert = theorem8_certificate(b, c)
            m, block, x0, shift = (cert["modulus"], cert["block"],
                                   cert["x_start"], cert["shift"])
            # the block is asserted for the TRANSLATED variable x = n + shift
            if b % 2 == 0:
                k = c - shift * shift
                vals = [((x0 + j) ** 2 + k) % m for j in range(len(block))]
            else:
                k = c - shift * (shift + 1)
                vals = [((x0 + j) ** 2 + (x0 + j) + k) % m for j in range(len(block))]
            n0 = x0 - shift
            vals_n = [((n0 + j) ** 2 + b * (n0 + j) + c) % m for j in range(len(block))]
            ok = (vals == [v % m for v in block]
                  and vals_n == [v % m for v in block]
                  and is_forbidden(m, tuple(block))
                  and len(block) <= m)
            lengths.setdefault(len(block), 0)
            lengths[len(block)] += 1
            if not ok:
                bad.append({"b": b, "c": c, "cert": cert,
                            "block_from_x": vals, "block_from_n": vals_n})
    return {"pairs_checked": pairs, "failures": bad[:20],
            "failure_count": len(bad), "block_length_histogram": lengths}


# --------------------------------------------------------------------------
# 6. r06 Lemma 4/5/6 identities: exhaustive small-modulus verification
# --------------------------------------------------------------------------


def check_ring_identities(moduli=(2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13)) -> dict:
    lemma4 = lemma5 = lemma6 = True
    l4_bad = l5_bad = l6_bad = []
    for m in moduli:
        R = range(m)
        for a0, a1, a2, d0, c0 in product(R, R, R, R, R):
            c1 = (a0 * c0 - d0) % m
            d1 = (a0 * d0) % m
            c2 = (a1 * c1 - d1) % m
            d2 = (a1 * d1) % m
            c3 = (a2 * c2 - d2) % m
            # Lemma 4: (c0,c1,c2) = (0,0,z) forces z = 0
            if c0 == 0 and c1 == 0 and c2 != 0:
                lemma4 = False
                l4_bad = [{"m": m, "state": [a0, a1, d0, c0]}]
            # Lemma 5: c1 = 0  =>  -c0 c2 = (a0 c0)^2
            if c1 == 0 and (-c0 * c2 - (a0 * c0) ** 2) % m != 0:
                lemma5 = False
                l5_bad = [{"m": m, "state": [a0, a1, d0, c0]}]
            # Lemma 6: c2 = 0  =>  d0^2 (d0 + c1)^2 + c0^2 c1 c3 = 0
            if c2 == 0 and (d0 ** 2 * (d0 + c1) ** 2 + c0 ** 2 * c1 * c3) % m != 0:
                lemma6 = False
                l6_bad = [{"m": m, "state": [a0, a1, a2, d0, c0]}]
    return {"moduli": list(moduli),
            "lemma4_absorbing_zeros": lemma4, "lemma4_counterexample": l4_bad,
            "lemma5_square_condition": lemma5, "lemma5_counterexample": l5_bad,
            "lemma6_quartic_identity": lemma6, "lemma6_counterexample": l6_bad}


# --------------------------------------------------------------------------
# 7. r02 Proposition 5 / (20): fixed divisor and adjacent coprimality
# --------------------------------------------------------------------------


def fixed_divisor(coeffs, span: int = 400) -> int:
    """d(P) = gcd{P(k) : k in Z}.

    Exact: writing P in the binomial basis P = sum alpha_i C(X,i), one has
    d(P) = gcd(alpha_0..alpha_n) = gcd(P(0), ..., P(n)) for n = deg P, because the
    two tuples are Z-linear transforms of one another.  ``span`` is retained only
    as a redundancy check.
    """
    n = len(coeffs) - 1
    g = 0
    for k in range(n + 1):
        g = gcd(g, _ev(coeffs, k))
    return g


def adjacent_coprime_everywhere(coeffs, span: int = 3000) -> bool:
    """Exact (not sampled) test of gcd(u(k), u(k+1)) = 1 for every k in Z.

    For u(X) = l X^2 + b X + c the two quadratics u(X), u(X+1) differ by the
    linear h(X) = l(2X+1) + b, so a prime p divides two adjacent values for some
    integer k only if p divides the resultant

        Res(h, u) = l * (l^2 + 4 l c - b^2)                                 (*)

    or p | 2l (where h drops degree mod p).  The candidate set is therefore
    finite and each candidate is settled by a scan over one period mod p.
    A vanishing (*) means a common rational root, hence failure.
    """
    if len(coeffs) != 3:
        return _adjacent_coprime_sampled(coeffs, span)
    lead, b, c = coeffs
    if lead == 0:
        return _adjacent_coprime_sampled(coeffs, span)
    disc = lead * lead + 4 * lead * c - b * b
    if disc == 0:
        return False
    candidates = _prime_factors(abs(2 * lead * disc))
    for p in candidates:
        for k in range(p):
            if _ev(coeffs, k) % p == 0 and _ev(coeffs, k + 1) % p == 0:
                return False
    return True


def _adjacent_coprime_sampled(coeffs, span: int) -> bool:
    prev = _ev(coeffs, -span)
    for k in range(-span + 1, span + 1):
        cur = _ev(coeffs, k)
        if gcd(prev, cur) != 1:
            return False
        prev = cur
    return True


def _prime_factors(n: int) -> list:
    out, d = [], 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def quadratic_normal_form_search(lead_max: int = 4, b_max: int = 60,
                                 c_max: int = 60, span: int = 400) -> dict:
    """Enumerate primitive integer quadratics whose adjacent values are always
    coprime, testing r02 section 6's classification (leading coefficient 1 and 2)
    and probing beyond it."""
    survivors = {}
    for lead in range(1, lead_max + 1):
        found = []
        for b in range(-b_max, b_max + 1):
            for c in range(-c_max, c_max + 1):
                if gcd(gcd(lead, b), c) != 1:
                    continue
                if fixed_divisor((lead, b, c)) != 1:
                    continue
                if adjacent_coprime_everywhere((lead, b, c), span=span):
                    found.append((lead, b, c))
        # translation classes: u(k+j) has (lead, b+2*lead*j, c=u(j))
        classes = {}
        for (l, b, c) in found:
            reps = []
            for j in range(-3, 4):
                bb = b + 2 * l * j
                cc = l * j * j + b * j + c
                reps.append((l, bb, cc))
            key = min(reps, key=lambda t: (abs(t[1]), t[1], abs(t[2]), t[2]))
            classes.setdefault(key, []).append((l, b, c))
        survivors[lead] = {
            "count": len(found),
            "translation_class_representatives": sorted(
                [list(k) for k in classes], key=lambda t: (abs(t[1]), abs(t[2]))),
        }
    return survivors


def check_theorem7_examples() -> dict:
    """Rational-root consequence (23) and the degree-6 intersective example."""
    # (X^2-13)(X^2-17)(X^2-221): a root modulo every prime outside {2,13,17}
    def has_root(mod, poly):
        return any(_ev(poly, x) % mod == 0 for x in range(mod))
    deg6 = _poly_mul(_poly_mul((1, 0, -13), (1, 0, -17)), (1, 0, -221))
    primes = [p for p in range(3, 400) if _is_prime(p)]
    missing = [p for p in primes if p not in (13, 17) and not has_root(p, deg6)]
    # rational-root polynomials: check the criterion holds
    rr = [(1, -3), (2, -5), (1, 0, -4), (3, 1, -2, -8)]
    rr_rows = []
    for poly in rr:
        bad = [p for p in primes if not has_root(p, poly)]
        rr_rows.append({"poly": list(poly), "primes_without_root": bad[:10],
                        "count_without_root": len(bad)})
    return {"degree6_poly": list(deg6),
            "primes_3_to_400_without_root_excluding_13_17": missing,
            "degree6_intersective_outside_2_13_17": missing == [],
            "rational_root_examples": rr_rows}


def _ev(coeffs, x):
    acc = 0
    for c in coeffs:
        acc = acc * x + c
    return acc


def _poly_mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return tuple(out)


# --------------------------------------------------------------------------
# 8. Entry point
# --------------------------------------------------------------------------


def run(quick: bool) -> dict:
    report = {}
    report["certificates"] = check_certificates()
    report["ring_identities"] = check_ring_identities(
        moduli=(2, 3, 4, 5, 7) if quick else (2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13))
    report["r02_section7_table"] = check_r02_table()
    report["theorem8"] = check_theorem8(
        b_range=range(-4, 5), c_range=range(-8, 9)) if quick else check_theorem8()
    report["forbidden_census"] = forbidden_census(
        primes=[2, 3, 5, 7] if quick else [2, 3, 5, 7, 11, 13],
        lengths=(3,) if quick else (3, 4),
        extra_moduli=(4,) if quick else (4, 8, 9))
    report["theorem7_examples"] = check_theorem7_examples()
    if not quick:
        report["quadratic_normal_forms"] = quadratic_normal_form_search()
    return report


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--quick", action="store_true",
                    help="small ranges; seconds rather than minutes")
    ap.add_argument("--json", action="store_true", help="emit the full report as JSON")
    args = ap.parse_args()
    report = run(args.quick)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
        return 0
    c = report["certificates"]
    print(f"certificates: all_forbidden={c['all_forbidden']} "
          f"field_transport_agrees={c['field_agreement']}")
    for row in c["certificates"]:
        print(f"  {row['return']:>3} mod {row['modulus']:>2} {row['word']!s:<16} "
              f"forbidden={row['forbidden']}")
    ri = report["ring_identities"]
    print(f"ring identities: L4={ri['lemma4_absorbing_zeros']} "
          f"L5={ri['lemma5_square_condition']} L6={ri['lemma6_quartic_identity']}")
    t = report["r02_section7_table"]
    print(f"r02 section 7 table: all_ok={t['all_ok']}")
    for row in t["table"]:
        print(f"  u={row['polynomial']} p={row['prime']} start={row['start_residue']} "
              f"word={row['actual_word']} matches={row['word_matches']} "
              f"forbidden={row['word_forbidden']} minimal={row['minimal_certificate']}")
    t8 = report["theorem8"]
    print(f"theorem 8: pairs={t8['pairs_checked']} failures={t8['failure_count']} "
          f"lengths={t8['block_length_histogram']}")
    print("forbidden census (modulus, length, forbidden/total, nonabsorbing):")
    for row in report["forbidden_census"]["census"]:
        print(f"  m={row['modulus']:>2} L={row['length']} "
              f"{row['forbidden']}/{row['total_words']} "
              f"(frac {row['forbidden_fraction']:.4f}) nonabsorbing={row['forbidden_nonabsorbing']}")
    t7 = report["theorem7_examples"]
    print(f"theorem 7 degree-6 intersective outside {{2,13,17}}: "
          f"{t7['degree6_intersective_outside_2_13_17']}")
    if "quadratic_normal_forms" in report:
        print("primitive adjacent-coprime quadratics (translation classes):")
        for lead, info in report["quadratic_normal_forms"].items():
            print(f"  lead={lead}: {info['count']} found, classes="
                  f"{info['translation_class_representatives']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
