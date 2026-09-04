#!/usr/bin/env python3
"""Erdos #1049: the q-Apery block law, DERIVED from a telescoping Casoratian.

What changed
------------
`HarmonicZeroBlockLawLab.md` recorded the block law as an *exact empirical
identification*, explicitly not proved, with the harmonic numbers appearing
through a leading-order expansion of `sum_{m<=n} 1/(1-q^m)` that was described
as "a leading-order computation, not a proof".

This probe supplies the missing structure.  The two solutions `L_j`, `R_j` of the
source recurrence have a Casoratian that telescopes in closed form:

    W_j := L_{j+1} R_j - L_j R_{j+1}
         = - 3^{j+1} (3^{j+1} + 2^{j+2}) / ( 2^{j+1} (3^{j+1} - 2^{j+1}) ).

Everything follows from that one identity.  Writing rho_j = L_j / R_j,

    rho_{j+1} - rho_j = W_j / (R_j R_{j+1}),                                (*)

so rho_j is an explicit telescoping sum, not the output of a dynamical system.
For p >= 5,

    v_p(W_j) = v_p(3^{j+1} + 2^{j+2}) - v_p(3^{j+1} - 2^{j+1}),

and v_p(3^{j+1} - 2^{j+1}) > 0 exactly when d | j+1, where d = ord_p(3/2).
Hence the increments in (*) are p-integral EXCEPT at j = dK - 1, which is why
the loss structure is organised into blocks [dK, dK+d-1]: the block boundaries
are the poles of a telescoping product, not an emergent feature.

Summing the polar increments, with 3^{dK} - 2^{dK} = 2^{dK}((1+pi)^K - 1) where
pi = q^d - 1 has v_p(pi) = eps = v_p(3^d - 2^d), gives (1+pi)^K - 1 = K*pi*u_K
with u_K = 1 (mod p^eps).  The K-dependence of every other factor is through
q^{dK} = (1+pi)^K = 1 (mod p^eps) and through R_{dK-1}, R_{dK} mod p, which are
d-periodic in the index and therefore constant in K.  So each polar increment is
-(c/pi)(1/K) times a unit congruent to 1 mod p^eps, and

    rho_j  =  rho_{j0}  -  (c / pi) * H_{floor(j/d)}  +  (p-integral),

with c a fixed p-adic unit.  The harmonic numbers are DERIVED here, not observed.
Therefore, on the generic class,

    v_p(L_j / R_j) = v_p(H_{floor(j/d)}) - eps     when v_p(H_{floor(j/d)}) < eps,
    v_p(L_j / R_j) >= 0                            otherwise,

and since (A_j, B_j) is the primitive integer vector proportional to (L_j, R_j),

    p | B_j   <=>   v_p(L_j) < v_p(R_j)   <=>   v_p(H_{floor(j/d)}) < eps.

Two corrections to the recorded law
-----------------------------------
1. THE CRITERION IS eps, NOT J_p.  The lab's law used the Eswarathasan-Levine
   set J_p = { K : p | numerator(H_K) }, i.e. v_p(H_K) >= 1.  The derivation
   gives v_p(H_K) >= eps.  These agree exactly when eps = 1 and differ when
   p^2 | 3^d - 2^d.  p = 23 (d = 11, 3^11 - 2^11 = 23^2 * 331, eps = 2) is a
   live case inside the checked range.

2. THE BLOCKS ARE NOT WHOLLY LOST.  The derivation is generic in the standing
   assumption that R_j is a p-adic unit.  R_j mod p is d-periodic, and for 24 of
   the 75 primes below 400 it vanishes on a nonempty set of residues mod d.  At
   such an index inside a loss block, (*) picks up an extra pole and p | B_j
   after all.  p = 11, j = 31 is an exact-rational counterexample to the law as
   stated: 3 is in J_11 (H_3 = 11/6), so [30,39] is recorded as a whole loss
   block, yet 11 | B_31.

Both corrections are CONSERVATIVE for the downstream window-divisor certificate,
and falsifier 6 below is the load-bearing check: the certificate only needs each
loss block to retain at least one index with p not dividing B_j, and the R-zero
set -- being a proper subset of the residues mod d -- can never cover a block.

Predeclared falsifiers
----------------------
1. Casoratian closed form fails at any j (exact rational arithmetic).
2. lim L_j / R_j disagrees with sum_{n>=1} 2^n/(3^n - 2^n) (the Erdos #1049
   target constant at base 3/2).
3. Divisibility law  p | B_j  <=>  v_p(H_{floor(j/d)}) < eps  fails at any
   (p, j) with p in the generic class (R_j a unit at every index tested).
4. Strict valuation law  v_p(L_j/R_j) = v_p(H_{floor(j/d)}) - eps  fails on the
   pole side for a generic prime.
5. Regression: the recorded exceptional pair (p, j) = (11, 31) stops being
   exceptional -- guards against silently absorbing the anomaly.
6. Some loss block is covered entirely, i.e. every index in [dK, dK+d-1] with
   v_p(H_K) >= eps has p | B_j.  This is the assumption the window-divisor
   criterion rests on; it must not fail.

Exit code 0 iff every falsifier passes.

Replay
------
    ./repo-python formal_math/probes/erdos1049_casoratian_block_law.py
    ./repo-python formal_math/probes/erdos1049_casoratian_block_law.py \
        --max-index 300 --max-prime 400 --json
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from math import gcd

sys.path.insert(0, str(__import__("pathlib").Path(__file__).resolve().parent))

from erdos1049_padic_window_divisor_law import (  # noqa: E402
    order_of_three_halves,
    valuations,
)

sys.set_int_max_str_digits(0)

Q = Fraction(3, 2)


# ---------------------------------------------------------------- arithmetic


def vp_int(n: int, p: int):
    if n == 0:
        return None
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def vp_frac(fr: Fraction, p: int):
    a = vp_int(fr.numerator, p)
    if a is None:
        return None
    return a - (vp_int(fr.denominator, p) or 0)


def sieve(n: int) -> list[int]:
    s = [True] * (n + 1)
    s[0] = s[1] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            for k in range(i * i, n + 1, i):
                s[k] = False
    return [i for i in range(n + 1) if s[i]]


def exact_rows(jmax: int) -> tuple[list[Fraction], list[Fraction]]:
    """L_j, R_j over Q, seeds and indexing identical to the sibling probe."""
    L = [Fraction(0), Fraction(-21, 2)]
    R = [Fraction(1), Fraction(-11, 4)]
    alpha = Q
    for _ in range(jmax):
        a, qa, qq = alpha, Q * alpha, Q * Q
        y0 = Q * (a - 1) * (qa + 2)
        y2 = (qa - 1) * (a + 2)
        y1 = (qq * Q * a ** 5 + 2 * qq * (Q + 1) * a ** 4 + qq * a ** 3
              - 4 * Q * (Q + 1) * a ** 2 + (qq - 4 * Q + 1) * a + 2 * (Q + 1))
        L.append(-(y1 * L[-1] + y0 * L[-2]) / y2)
        R.append(-(y1 * R[-1] + y0 * R[-2]) / y2)
        alpha *= Q
    return L, R


def casoratian_closed_form(j: int) -> Fraction:
    return -Fraction(3 ** (j + 1) * (3 ** (j + 1) + 2 ** (j + 2)),
                     2 ** (j + 1) * (3 ** (j + 1) - 2 ** (j + 1)))


def primitive(l: Fraction, r: Fraction) -> tuple[int, int]:
    den = l.denominator * r.denominator // gcd(l.denominator, r.denominator)
    a = l.numerator * (den // l.denominator)
    b = r.numerator * (den // r.denominator)
    g = gcd(abs(a), abs(b))
    return (a // g, b // g) if g else (a, b)


def harmonic_valuations(p: int, kmax: int) -> list:
    out = [None]
    h = Fraction(0)
    for k in range(1, kmax + 1):
        h += Fraction(1, k)
        out.append(vp_frac(h, p))
    return out


# ---------------------------------------------------------------- falsifiers


def check_casoratian(exact_jmax: int) -> dict:
    L, R = exact_rows(exact_jmax + 2)
    bad = []
    for j in range(0, exact_jmax):
        w = L[j + 1] * R[j] - L[j] * R[j + 1]
        if w != casoratian_closed_form(j):
            bad.append(j)
    return {"name": "casoratian_closed_form", "indices_checked": exact_jmax,
            "failures": bad, "passed": not bad}


def check_limit(exact_jmax: int, terms: int = 700) -> dict:
    L, R = exact_rows(exact_jmax + 2)
    rho = L[-1] / R[-1]
    target = sum(Fraction(2 ** n, 3 ** n - 2 ** n) for n in range(1, terms + 1))
    diff = abs(rho - target)
    # agreement measured in decimal digits
    digits = 0
    if diff != 0:
        d = diff
        while d < 1 and digits < 4000:
            d *= 10
            digits += 1
    else:
        digits = 4000
    return {"name": "limit_is_the_erdos1049_constant",
            "agreement_decimal_digits": digits,
            "target": "sum_{n>=1} 2^n/(3^n - 2^n)",
            "passed": digits >= 100}


def analyse_prime(p: int, jmax: int) -> dict:
    d = order_of_three_halves(p)
    eps = vp_int(3 ** d - 2 ** d, p)
    vL, vR = valuations(p, jmax + 2, N=70)
    hv = harmonic_valuations(p, jmax // d + 3)
    rzero = [j for j in range(2, min(jmax, len(vR))) if vR[j] not in (0, None)]
    generic = not rzero
    div_fail, val_fail, covered_blocks = [], [], []
    seen_blocks: dict[int, list[bool]] = {}
    for j in range(d, min(jmax, len(vL))):
        k = j // d
        if not (0 < k < len(hv)) or hv[k] is None:
            continue
        lv, rv = vL[j], vR[j]
        if lv is None or rv is None:
            continue
        rho_v = lv - rv
        divides = rho_v < 0
        want = hv[k] < eps
        if want:
            seen_blocks.setdefault(k, [])
        else:
            seen_blocks.setdefault(k, []).append(divides)
        if generic:
            if divides != want:
                div_fail.append({"j": j, "K": k, "v_rho": rho_v, "vH": hv[k]})
            if want and rho_v != hv[k] - eps:
                val_fail.append({"j": j, "K": k, "got": rho_v,
                                 "predicted": hv[k] - eps, "vH": hv[k]})
    # falsifier 6: a loss block must retain at least one non-dividing index
    for k, flags in seen_blocks.items():
        if flags and all(flags) and len(flags) == d:
            covered_blocks.append(k)
    return {"p": p, "d": d, "eps": eps, "generic": generic,
            "r_zero_residues": sorted({j % d for j in rzero}),
            "div_failures": div_fail, "val_failures": val_fail,
            "covered_loss_blocks": covered_blocks}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-index", type=int, default=300)
    ap.add_argument("--max-prime", type=int, default=400)
    ap.add_argument("--exact-index", type=int, default=40,
                    help="how far to run the exact-rational Casoratian check")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    results = [check_casoratian(args.exact_index), check_limit(args.exact_index)]

    per_prime = []
    for p in sieve(args.max_prime):
        if p < 5 or p == 7:      # 7 divides the Casoratian seed W_0 = -21/2
            continue
        per_prime.append(analyse_prime(p, args.max_index))

    generic = [r for r in per_prime if r["generic"]]
    exceptional = [r for r in per_prime if not r["generic"]]
    div_fail = [(r["p"], f) for r in generic for f in r["div_failures"]]
    val_fail = [(r["p"], f) for r in generic for f in r["val_failures"]]
    covered = [(r["p"], r["covered_loss_blocks"]) for r in per_prime
               if r["covered_loss_blocks"]]

    results.append({"name": "divisibility_law_generic_class",
                    "generic_primes": len(generic),
                    "exceptional_primes": len(exceptional),
                    "failures": div_fail, "passed": not div_fail})
    results.append({"name": "strict_valuation_law_generic_class",
                    "failures": val_fail, "passed": not val_fail})

    # falsifier 5: the recorded exceptional pair must stay exceptional
    r11 = next((r for r in per_prime if r["p"] == 11), None)
    reg_ok = False
    if r11 is not None and not r11["generic"]:
        vL, vR = valuations(11, 40, N=70)
        reg_ok = (vL[31] - vR[31]) < 0 and vp_frac(
            sum(Fraction(1, i) for i in range(1, 4)), 11) >= r11["eps"]
    results.append({"name": "regression_p11_j31_still_exceptional",
                    "detail": "3 in J_11 (H_3 = 11/6) yet 11 | B_31",
                    "passed": bool(reg_ok)})

    results.append({"name": "no_loss_block_is_wholly_covered",
                    "covered": covered, "passed": not covered})

    eps_ge2 = [(r["p"], r["d"], r["eps"]) for r in per_prime if r["eps"] >= 2]
    payload = {
        "probe": "erdos1049_casoratian_block_law",
        "max_index": args.max_index, "max_prime": args.max_prime,
        "primes_analysed": len(per_prime),
        "generic_primes": len(generic), "exceptional_primes": len(exceptional),
        "primes_with_eps_ge_2": eps_ge2,
        "r_zero_primes": [{"p": r["p"], "d": r["d"],
                           "residues": r["r_zero_residues"]}
                          for r in exceptional],
        "falsifiers": results,
        "all_passed": all(r["passed"] for r in results),
    }

    if args.json:
        print(json.dumps(payload, indent=2))
    else:
        print(f"Erdos 1049 -- Casoratian block law, "
              f"j < {args.max_index}, p < {args.max_prime}")
        print(f"  primes analysed        : {len(per_prime)} "
              f"({len(generic)} generic, {len(exceptional)} with an R-zero)")
        print(f"  primes with eps >= 2   : {eps_ge2}  "
              f"(here 'v_p(H_K) < eps' differs from 'K not in J_p')")
        print()
        for r in results:
            mark = "PASS" if r["passed"] else "FAIL"
            extra = ""
            if r["name"] == "casoratian_closed_form":
                extra = f"  ({r['indices_checked']} indices, exact rationals)"
            if r["name"] == "limit_is_the_erdos1049_constant":
                extra = f"  ({r['agreement_decimal_digits']} decimal digits)"
            if r["name"] == "divisibility_law_generic_class":
                extra = f"  ({r['generic_primes']} generic primes)"
            print(f"  [{mark}] {r['name']}{extra}")
            for f in r.get("failures", [])[:6]:
                print(f"          {f}")
        print()
        print("  all falsifiers passed" if payload["all_passed"]
              else "  FALSIFIER FIRED")
    return 0 if payload["all_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
