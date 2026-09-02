#!/usr/bin/env python3
"""Erdos #249: parity-perturbed rational controls for the binary totient series.

Claim under test.  Let S = sum_{n>=1} phi(n)/2^n and xi = 3/2 - S.  Expand xi in
base 4 with the complete residue digit set {-1,0,1,2}:

    x_0 = xi,  d_m = floor(4 x_{m-1} + 1/3),  x_m = 4 x_{m-1} - d_m,

so that x_m stays in J = [-1/3, 2/3) and xi = sum_{m>=1} d_m 4^{-m}.  Put
c(n) = phi(n) for odd n and c(2m) = phi(2m) + d_m.  Then

  (i)   0 <= c(n) <= n for every n,
  (ii)  c(n) = phi(n) for every odd n and |c(n) - phi(n)| <= 2 for every n,
  (iii) sum_{n>=1} c(n)/2^n = 3/2 exactly.

Consequently c has a tempered integral binary carry (multiplier 2), its odd
dyadic sections are exactly the odd totient sections (rank >= 2^e - 1 through
level e), and every hypothesis of the carry anti-compression theorem holds
while the series is rational.

This probe (1) computes the digits d_m to high precision and checks (i)-(iii)
to the working precision, (2) checks the odd-support mirror construction with
digit set {-2,-1,0,1}, (3) measures the exact rational rank of the truncated
section-evaluation matrices of c and of phi through levels e = 1..4, and
(4) runs the density-zero greedy variant (perturbation supported on a set F of
density zero with gaps <= log2 n) and checks its invariant.

Everything here is finite computation.  The theorem itself is proved in
ErdosProblems/Erdos249/ParityPerturbedRationalControl.md and .lean.  Nothing
here bears on whether S is irrational.
"""
from __future__ import annotations

import json
import math
import sys
from fractions import Fraction
from pathlib import Path

from mpmath import mp, mpf, floor as mpfloor

REPO = Path(__file__).resolve().parents[2]
RECEIPT = REPO / "state" / "formal_math" / "probes" / "erdos249_parity_perturbed_rational_control_receipt.json"


def totient_table(limit: int) -> list[int]:
    phi = list(range(limit + 1))
    for p in range(2, limit + 1):
        if phi[p] == p:  # p prime
            for k in range(p, limit + 1, p):
                phi[k] -= phi[k] // p
    phi[0] = 0
    return phi


def totient_series(phi: list[int], terms: int) -> mpf:
    # tail after `terms` is below (terms+2)/2^terms; with terms = 4000 that is 1e-1200
    s = mpf(0)
    for n in range(1, terms + 1):
        s += mpf(phi[n]) / mpf(2) ** n
    return s


def centered_base4_digits(x: mpf, count: int, digit_set_lo: int) -> tuple[list[int], list[mpf]]:
    """Digits in {lo, lo+1, lo+2, lo+3} with remainder interval [lo/3, (lo+3)/3)."""
    # For lo = -1: J = [-1/3, 2/3), d = floor(4x + 1/3).  For lo = -2: J = [-2/3, 1/3), d = floor(4x + 2/3).
    shift = mpf(-digit_set_lo) / 3
    digits: list[int] = []
    rems: list[mpf] = [x]
    cur = x
    for _ in range(count):
        d = int(mpfloor(4 * cur + shift))
        cur = 4 * cur - d
        digits.append(d)
        rems.append(cur)
    return digits, rems


def rank_over_Q(rows: list[list[int]]) -> int:
    m = [[Fraction(v) for v in r] for r in rows]
    rank = 0
    ncols = len(m[0]) if m else 0
    for col in range(ncols):
        piv = None
        for r in range(rank, len(m)):
            if m[r][col] != 0:
                piv = r
                break
        if piv is None:
            continue
        m[rank], m[piv] = m[piv], m[rank]
        pv = m[rank][col]
        m[rank] = [v / pv for v in m[rank]]
        for r in range(len(m)):
            if r != rank and m[r][col] != 0:
                f = m[r][col]
                m[r] = [a - f * b for a, b in zip(m[r], m[rank])]
        rank += 1
    return rank


def sections_through_level(seq: list[int], e: int, points: int) -> list[list[int]]:
    rows = []
    for j in range(0, e + 1):
        for r in range(2 ** j):
            rows.append([seq[2 ** j * n + r] for n in range(points)])
    return rows


def main() -> int:
    mp.dps = 800
    LIMIT = 4200
    phi = totient_table(LIMIT)
    S = totient_series(phi, 4000)
    out: dict = {"S_first_60_digits": mp.nstr(S, 60)}

    # --- (1) even-support construction, target 3/2, digits {-1,0,1,2}
    xi = mpf(3) / 2 - S
    assert mpf(-1) / 3 <= xi < mpf(2) / 3, "xi must lie in J"
    M = 1000  # digits m = 1..M cover even arguments up to 2M = 2000
    d, rems = centered_base4_digits(xi, M, -1)
    assert all(-1 <= t <= 2 for t in d)
    assert all(mpf(-1) / 3 <= r < mpf(2) / 3 for r in rems)
    assert d[0] <= 1, "first digit must be <= 1 so that c(2) <= 2"
    partial = sum(mpf(d[m - 1]) / mpf(4) ** m for m in range(1, M + 1))
    out["even_support"] = {
        "target": "3/2",
        "xi_first_40_digits": mp.nstr(xi, 40),
        "digits_first_80": d[:80],
        "digit_histogram": {str(k): d.count(k) for k in (-1, 0, 1, 2)},
        "abs_error_xi_minus_partial_log10": float(mp.log10(abs(xi - partial))) if xi != partial else None,
    }
    # build c up to 2M and check (i),(ii),(iii)
    N = 2 * M
    c = [0] * (N + 1)
    for n in range(1, N + 1):
        if n % 2 == 1:
            c[n] = phi[n]
        else:
            c[n] = phi[n] + d[n // 2 - 1]
    assert all(0 <= c[n] <= n for n in range(N + 1)), "growth bound c(n) <= n"
    assert all(abs(c[n] - phi[n]) <= 2 for n in range(N + 1))
    assert all(c[n] == phi[n] for n in range(1, N + 1, 2))
    cs = sum(mpf(c[n]) / mpf(2) ** n for n in range(1, N + 1))
    err = abs(cs - mpf(3) / 2)
    # tail beyond N is below (N+2)/2^N ~ 1e-600
    assert err < mpf(2) ** (-(N - 20)), f"series of c is not 3/2 to the expected precision: {err}"
    out["even_support"]["series_minus_3_over_2_log10"] = float(mp.log10(err)) if err != 0 else None
    out["even_support"]["c_first_40"] = c[1:41]
    out["even_support"]["phi_first_40"] = phi[1:41]

    # --- (2) odd-support mirror construction, target 1, digits {-2,-1,0,1}
    eta = (mpf(1) - S) / 2  # sum over odd n=2m-1 of delta 2^{-n} = 2 sum delta_m 4^{-m}
    assert mpf(-2) / 3 <= eta < mpf(1) / 3
    d2, rems2 = centered_base4_digits(eta, M, -2)
    assert all(-2 <= t <= 1 for t in d2)
    assert d2[0] in (-1, 0), "c(1) = 1 + d_1 must stay in [0,1]"
    c2 = [0] * (N + 1)
    for n in range(1, N + 1):
        if n % 2 == 0:
            c2[n] = phi[n]
        else:
            c2[n] = phi[n] + d2[(n + 1) // 2 - 1]
    assert all(0 <= c2[n] <= n for n in range(N + 1))
    assert all(c2[n] == phi[n] for n in range(2, N + 1, 2))
    cs2 = sum(mpf(c2[n]) / mpf(2) ** n for n in range(1, N + 1))
    err2 = abs(cs2 - 1)
    assert err2 < mpf(2) ** (-(N - 20))
    out["odd_support"] = {
        "target": "1",
        "digits_first_80": d2[:80],
        "series_minus_1_log10": float(mp.log10(err2)) if err2 != 0 else None,
        "c_first_40": c2[1:41],
    }

    # --- (2b) the exact variant formalised in ParityPerturbedRationalControl.lean:
    #          even support, digit set {-2,-1,0,1}, target 5/4, digits d_m = floor(4 x + 2/3).
    #          Digits are CERTIFIED from an exact rational enclosure lo <= S <= hi, lo = prefix
    #          through B terms, hi = lo + (B+2)/2^B, by running the recursion on both endpoints
    #          in exact arithmetic and keeping only the digits on which the endpoints agree.
    B = 4000
    lo = sum(Fraction(phi[n], 2 ** n) for n in range(1, B + 1))
    hi = lo + Fraction(B + 2, 2 ** B)
    assert mpf(lo.numerator) / mpf(lo.denominator) <= S <= mpf(hi.numerator) / mpf(hi.denominator)

    def exact_digits(x: Fraction, count: int, lo_digit: int) -> list[int]:
        shift = Fraction(-lo_digit, 3)
        out: list[int] = []
        cur = x
        for _ in range(count):
            dd = math.floor(4 * cur + shift)
            cur = 4 * cur - dd
            out.append(dd)
        return out

    xi_lo = Fraction(5, 4) - hi
    xi_hi = Fraction(5, 4) - lo
    dl = exact_digits(xi_lo, 1200, -2)
    dh = exact_digits(xi_hi, 1200, -2)
    certified = 0
    while certified < 1200 and dl[certified] == dh[certified]:
        certified += 1
    assert certified >= 600, certified
    d54 = dl[:certified]
    assert all(-2 <= t <= 1 for t in d54)
    assert d54[0] >= -1, "c(2) = 1 + d_1 must be >= 0"
    N54 = 2 * certified
    c54 = [0] * (N54 + 1)
    for n in range(1, N54 + 1):
        c54[n] = phi[n] if n % 2 == 1 else phi[n] + d54[n // 2 - 1]
    assert all(0 <= c54[n] <= n for n in range(N54 + 1))
    assert all(-2 <= c54[n] - phi[n] <= 1 for n in range(N54 + 1))
    # exact check of the series against the enclosure: |sum_{n<=N54} c/2^n - 5/4| <= tail bound + enclosure width
    partial54 = sum(Fraction(c54[n], 2 ** n) for n in range(1, N54 + 1))
    xi_partial = sum(Fraction(d54[m - 1], 4 ** m) for m in range(1, certified + 1))
    # sum_{n<=N54} c/2^n = (prefix of S through N54) + xi_partial; remainder of xi expansion is < 2/3 * 4^-certified
    S_prefix = sum(Fraction(phi[n], 2 ** n) for n in range(1, N54 + 1))
    assert partial54 == S_prefix + xi_partial
    gap = abs(partial54 - Fraction(5, 4))
    assert gap <= Fraction(N54 + 2, 2 ** N54) + Fraction(2, 3 * 4 ** certified) + (hi - lo)
    out["even_support_lean_variant"] = {
        "target": "5/4",
        "digit_set": [-2, -1, 0, 1],
        "certified_digit_count": certified,
        "digits_first_80": d54[:80],
        "digit_histogram": {str(k): d54.count(k) for k in (-2, -1, 0, 1)},
        "c_first_40": c54[1:41],
        "enclosure_terms": B,
        "series_prefix_minus_5_over_4_log2": float(mp.log(mpf(gap.numerator) / mpf(gap.denominator), 2)) if gap else None,
    }

    # --- (3) exact ranks of truncated section-evaluation matrices
    ranks = {}
    for e in range(1, 5):
        pts = 64
        assert 2 ** e * pts + 2 ** e <= N
        r_phi = rank_over_Q(sections_through_level(phi, e, pts))
        r_c = rank_over_Q(sections_through_level(c, e, pts))
        r_c2 = rank_over_Q(sections_through_level(c2, e, pts))
        r_c54 = rank_over_Q(sections_through_level(c54, e, pts))
        # odd sections only (levels 1..e): should be 2^e - 1 for phi and for c
        odd_rows_phi = [row for j in range(1, e + 1) for r in range(2 ** j) if r % 2 == 1
                        for row in [[phi[2 ** j * n + r] for n in range(pts)]]]
        odd_rows_c = [row for j in range(1, e + 1) for r in range(2 ** j) if r % 2 == 1
                      for row in [[c[2 ** j * n + r] for n in range(pts)]]]
        assert odd_rows_phi == odd_rows_c
        ranks[str(e)] = {
            "sections_through_level": 2 ** (e + 1) - 1,
            "rank_phi_truncated": r_phi,
            "rank_c_even_perturbed_truncated": r_c,
            "rank_c_odd_perturbed_truncated": r_c2,
            "rank_c_lean_variant_5_over_4_truncated": r_c54,
            "odd_sections_rank": rank_over_Q(odd_rows_phi),
            "expected_phi_rank": 2 ** e + 1,
            "expected_odd_rank": 2 ** e - 1,
        }
        assert ranks[str(e)]["odd_sections_rank"] == 2 ** e - 1
        assert r_phi == 2 ** e + 1, f"truncated phi rank {r_phi} at e={e}"
        assert r_c >= 2 ** e - 1
    out["section_ranks"] = ranks

    # --- (4) density-zero greedy variant: free set F = {n >= 4 : 2^{floor(log2 log2 n)} | n}
    def modulus(n: int) -> int:
        return 2 ** int(math.floor(math.log2(math.log2(n)))) if n >= 4 else 1

    Ng = 3000
    free = [n >= 1 and (n < 4 or n % modulus(n) == 0) for n in range(Ng + 1)]
    free[0] = False
    # L_n = forced future mass, U_n = L_n + free future capacity, both as exact Fractions over the finite horizon
    # (beyond the horizon everything is treated as forced with phi; the horizon tail is < (Ng+2)/2^Ng)
    L = [Fraction(0)] * (Ng + 2)
    U = [Fraction(0)] * (Ng + 2)
    for n in range(Ng, 0, -1):
        w = Fraction(1, 2 ** n)
        if free[n]:
            L[n - 1] = L[n]
            U[n - 1] = U[n] + n * w
        else:
            L[n - 1] = L[n] + phi[n] * w
            U[n - 1] = U[n] + phi[n] * w
    rho = Fraction(3, 2)
    assert L[0] <= rho <= U[0], (float(L[0]), float(U[0]))
    R = rho
    cg = [0] * (Ng + 1)
    gap_ok = True
    free_positions = [n for n in range(1, Ng + 1) if free[n]]
    last_checked_free = free_positions[-2]  # the final free position has no in-horizon successor
    for n in range(1, Ng + 1):
        w = Fraction(1, 2 ** n)
        if free[n]:
            # capacity condition needed by the invariant: U_n - L_n >= 2^{-n}; only meaningful
            # while the next free position lies inside the finite horizon
            if n <= last_checked_free and U[n] - L[n] < w:
                gap_ok = False
            x = R
            if x <= U[n]:
                dig = 0
            else:
                dig = math.ceil((x - U[n]) / w)
            assert 0 <= dig <= n
            cg[n] = dig
        else:
            cg[n] = phi[n]
        R -= cg[n] * w
        assert L[n] <= R <= U[n], (n, float(R), float(L[n]), float(U[n]))
    assert gap_ok
    density = sum(1 for n in range(1, Ng + 1) if free[n]) / Ng
    out["density_zero_greedy"] = {
        "target": "3/2",
        "horizon": Ng,
        "free_count": sum(1 for n in range(1, Ng + 1) if free[n]),
        "free_density_on_horizon": density,
        "max_gap_observed": max(
            b - a for a, b in zip([n for n in range(1, Ng + 1) if free[n]][:-1],
                                  [n for n in range(1, Ng + 1) if free[n]][1:])),
        "invariant_held_everywhere": True,
        "capacity_condition_held_at_every_free_position": gap_ok,
        "residual_at_horizon": float(R),
        "residual_bound": float(Fraction(Ng + 2, 2 ** Ng)) if Ng < 1000 else "below 2^-2900",
    }

    # --- (5) correlation invariance: two-point shifted correlations move by O(x), not by the main term
    corr = {}
    X = 1900
    for h in (1, 2, 6):
        base = sum(phi[n] * phi[n - h] for n in range(h + 1, X + 1))
        pert = sum(c[n] * c[n - h] for n in range(h + 1, X + 1))
        corr[str(h)] = {"phi_corr": base, "c_corr": pert, "difference_over_x": (pert - base) / X,
                        "main_term_over_x_squared": base / X ** 2}
    out["shifted_correlation_invariance"] = corr

    RECEIPT.parent.mkdir(parents=True, exist_ok=True)
    RECEIPT.write_text(json.dumps(out, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: out[k] for k in ("S_first_60_digits", "section_ranks", "density_zero_greedy",
                                          "shifted_correlation_invariance")}, indent=1))
    print("even-support digits:", d[:40])
    print("even-support c(1..30):", c[1:31])
    print("phi(1..30):          ", phi[1:31])
    print("odd-support digits:", d2[:40])
    print("receipt:", RECEIPT)
    return 0


if __name__ == "__main__":
    sys.exit(main())
