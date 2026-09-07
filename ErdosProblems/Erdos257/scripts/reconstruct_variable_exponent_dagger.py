#!/usr/bin/env python3
"""Reconstruct A^dagger / A* identities far enough to check cost bounds.

The full 4^j prime-harmonic blocks are not enumerable (j=1 already needs
prime mass about 4). This checker therefore:

* verifies the exact frame identities (A5)--(A8) and Lemma A.1 on concrete
  squarefree frames, importing existing divisor helpers;
* checks Bertrand intervals for reserved primes q_j at small j, both the
  r2 windows (2^{6j}, 2^{6j+1}) and the r3 A* windows (2^{3j}, 2^{3j+1});
* checks the elementary inequalities that turn those identities into the
  old and new variable-exponent cost bounds;
* reconstructs a miniature dagger (small harmonic targets);
* independently checks the S2 witness x=17/256 against the exact branch map;
* checks r3 A.1 modular estimates, the flagship (Q+2)/d dominator, the
  logarithmic-square obstruction, D_2(6)={21,63}, the prime-lcm formula,
  the sharp base comparison, and the elementary zero-window / unbounded-tail
  statements.

Finite checks do not prove the infinite constructions.
"""
from __future__ import annotations

import argparse
import importlib.util
import math
import sys
from fractions import Fraction
from pathlib import Path

_HELPERS = Path(__file__).resolve().parent


def _load_helper(mod_name: str, filename: str):
    spec = importlib.util.spec_from_file_location(mod_name, _HELPERS / filename)
    if spec is None or spec.loader is None:
        raise ImportError(filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


_weighted = _load_helper(
    "erdos257_weighted_gcd_frame_moving_clique_audit",
    "weighted_gcd_frame_moving_clique_audit.py",
)
_eight = _load_helper("erdos257_eight_return_exact_audit", "eight_return_exact_audit.py")
divisors = _weighted.divisors
greedy = _eight.greedy


def is_prime(n: int) -> bool:
    """Trial division; only used on the small Bertrand windows below 2^25."""
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def first_prime_in_open_interval(lo: int, hi: int) -> int | None:
    """Existence check for Bertrand windows; do not enumerate the interval."""
    n = lo + 1
    if n < 3:
        n = 3
    elif n % 2 == 0:
        n += 1
    while n < hi:
        if is_prime(n):
            return n
        n += 2
    return None


def odd_primes_upto(limit: int) -> list[int]:
    if limit < 3:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    p = 3
    while p * p <= limit:
        if sieve[p]:
            step = p * 2
            for m in range(p * p, limit + 1, step):
                sieve[m] = 0
        p += 2
    return [n for n in range(3, limit + 1, 2) if sieve[n]]


def incidence(frame: set[int], n: int) -> int:
    return sum(1 for a in frame if n % a == 0)


def periodic_mean_power(frame: set[int], alpha: float) -> float:
    if not frame:
        return 0.0
    period = math.lcm(*frame)
    total = sum(incidence(frame, n) ** alpha for n in range(1, period + 1))
    return total / period


def squarefree_divisors(primes: list[int]) -> list[int]:
    """Divisors of a squarefree integer from its prime list; 2^k, not O(n)."""
    out = [1]
    for p in primes:
        out.extend(d * p for d in list(out))
    return out


def squarefree_frame(g: int, primes: list[int]) -> tuple[set[int], int]:
    m = 1
    for p in primes:
        m *= p
    frame = {g * d for d in squarefree_divisors(primes)}
    return frame, m


def exact_expansion_cost(g: int, primes: list[int], alpha: float) -> tuple[float, float]:
    """Return (C_alpha, exact periodic mean) for F={g d : d | M}."""
    t = 2.0**alpha - 1.0
    cost = 1.0 / g
    mean = 1.0 / g
    for p in primes:
        cost *= 1.0 + t / p
        mean *= 1.0 + t / p
    return cost, mean


def lemma_a1_bound(frame: set[int], alpha: float, covers: list[tuple[set[int], dict[int, float]]]) -> tuple[float, float]:
    """Cesaro of f^alpha versus the sum of cover costs on one period of F."""
    period = math.lcm(*frame) if frame else 1
    left = sum(incidence(frame, n) ** alpha for n in range(1, period + 1)) / period
    total_cost = 0.0
    for _G, coeffs in covers:
        total_cost += sum(c / d for d, c in coeffs.items())
    return left, total_cost


def check_identities(quick: bool) -> dict:
    samples = [
        (3, [5, 7], 0.5),
        (5, [11], 1.0),
        (7, [3, 5, 11], 0.25),
        (11, [13, 17], 0.125),
    ]
    if not quick:
        samples.append((13, [19, 23, 29], 0.5))
    rows = []
    for g, primes, alpha in samples:
        frame, _m = squarefree_frame(g, primes)
        cost, mean_formula = exact_expansion_cost(g, primes, alpha)
        mean_direct = periodic_mean_power(frame, alpha)
        assert abs(mean_formula - mean_direct) < 1e-9, (g, primes, alpha, mean_formula, mean_direct)
        t = 2.0**alpha - 1.0
        mprod = math.prod(primes)

        def omega(e: int) -> int:
            return sum(1 for p in primes if e % p == 0)

        for n in range(1, min(g * mprod * 2, 400) + 1):
            f = incidence(frame, n)
            if n % g != 0:
                assert f == 0
                continue
            w = sum(1 for p in primes if (n // g) % p == 0)
            assert f == 2**w
            prod = 1.0
            ng = n // g
            for p in primes:
                prod *= 1.0 + t * (1.0 if ng % p == 0 else 0.0)
            assert abs(f**alpha - prod) < 1e-9
        coeffs = {g * e: t ** omega(e) for e in squarefree_divisors(primes)}
        left, right = lemma_a1_bound(frame, alpha, [(frame, coeffs)])
        assert left <= right + 1e-9, (left, right)
        rows.append(
            {
                "g": g,
                "primes": primes,
                "alpha": alpha,
                "cost": cost,
                "mean": mean_direct,
                "a1_left": left,
                "a1_right": right,
            }
        )
    return {"frames_checked": len(rows), "rows": rows}


def check_elementary_inequalities() -> dict:
    """The analytic comparisons used to bound C_j without listing P_j."""
    failures = []
    for k in range(0, 21):
        alpha = k / 20
        # Convexity of 2^x on [0,1]: 2^alpha - 1 <= alpha.
        if 2.0**alpha - 1.0 > alpha + 1e-12:
            failures.append(("two_pow_minus_one", alpha))
        if alpha > 0:
            b = 2.0**alpha
            if b - 1.0 < alpha * math.log(2) - 1e-12:
                failures.append(("log_lower", alpha))
    # A.3: alpha_j = 4^{-j}, S_j <= 4^j + 1, so alpha_j S_j <= 1 + 4^{-j} <= 5/4.
    for j in range(1, 12):
        alpha_j = 4.0 ** (-j)
        s_upper = 4.0**j + 1.0
        if alpha_j * s_upper > 1.25 + 1e-12:
            failures.append(("alpha_S", j))
        q_lower = 2 ** (6 * j)
        cost_upper = math.exp(1.25) / q_lower
        # B_j = 2^{alpha_j} <= 2, 2^{j alpha_j} <= 2 for j>=1.
        b_j = 2.0**alpha_j
        term = cost_upper * (2.0 ** (j * alpha_j)) * b_j / (b_j - 1.0) ** 2
        closed = (4 * math.exp(1.25) / (math.log(2) ** 2)) * (2.0 ** (-2 * j))
        # The closed form in (A7) uses 2^{j alpha_j}<=2 and B<=2, B-1 >= alpha log 2.
        if term > closed * 1.01:
            failures.append(("a7_term", j, term, closed))
    assert not failures, failures
    return {"inequality_points": 21, "layers": 11}


def check_bertrand_windows(quick: bool) -> dict:
    js = range(1, 4 if quick else 6)
    rows = []
    for j in js:
        lo = 2 ** (6 * j)
        hi = 2 ** (6 * j + 1)
        q = first_prime_in_open_interval(lo, hi)
        assert q is not None, (j, lo, hi)
        assert lo < q < hi
        rows.append({"j": j, "lo": lo, "hi": hi, "q": q})
    return {"windows": rows}


def reconstruct_miniature_dagger(prime_limit: int, layers: int) -> dict:
    """Small-target analogue: reserve Bertrand q_j, fill leftover primes."""
    reserved = []
    leftover = odd_primes_upto(prime_limit)
    for j in range(1, layers + 1):
        lo = 2 ** (6 * j)
        hi = 2 ** (6 * j + 1)
        if hi > prime_limit:
            break
        window = [p for p in leftover if lo < p < hi]
        if not window:
            break
        q = window[0]
        reserved.append(q)
        leftover = [p for p in leftover if p != q]
    frames = []
    used = set(reserved)
    leftover = [p for p in leftover if p not in used]
    idx = 0
    for j, q in enumerate(reserved, start=1):
        target = min(0.35 * j, 1.2)
        block = []
        mass = 0.0
        while idx < len(leftover) and mass < target and len(block) < 8:
            p = leftover[idx]
            idx += 1
            block.append(p)
            mass += 1.0 / p
        if not block:
            break
        frame, _m = squarefree_frame(q, block)
        alpha_j = 4.0 ** (-j)
        cost, mean = exact_expansion_cost(q, block, alpha_j)
        rec_mass = (1.0 / q) * math.prod(1.0 + 1.0 / p for p in block)
        frames.append(
            {
                "j": j,
                "q": q,
                "block": block,
                "alpha": alpha_j,
                "cost": cost,
                "mean_alpha": mean,
                "reciprocal_mass": rec_mass,
                "W2_emptyP": rec_mass,  # h_P=1 when P misses the frame primes
            }
        )
    # Finite P={2}: later frames are odd, so h_{2}=1 and W equals reciprocal mass.
    w_tail = [f["reciprocal_mass"] for f in frames]
    return {
        "reserved": reserved,
        "frames": frames,
        "reciprocal_masses": w_tail,
        "max_frame_reciprocal": max(w_tail) if w_tail else 0.0,
    }


def check_s2_witness() -> dict:
    """Type B's x=17/256: skip through n=2, Phi_2=-15/8, skip image 1/2."""
    x = Fraction(17, 256)
    selected, _defects, width = greedy(x.numerator, x.denominator, 8)
    assert 1 not in selected and 2 not in selected
    r2 = x  # both first ranks skipped
    phi2 = (4 ** 2) * (2 * r2 - Fraction(1, 4))
    assert phi2 == Fraction(-15, 8)
    tau2 = Fraction(4, 7)
    assert phi2 < tau2
    image = 4 * phi2 + (2 ** 3)
    assert image == Fraction(1, 2)
    return {
        "x": str(x),
        "selected_prefix": sorted(a for a in selected if a <= 8),
        "phi2": str(phi2),
        "phi3": str(image),
        "enclosure_width": width,
        "unit_interval_not_invariant": True,
    }


def check_b1_numeric() -> dict:
    """C_i >= 1 - exp(-H_i) for a coprime finite E covered by one G."""
    E = [3, 5, 7, 11]
    G = set(E)
    H = sum(Fraction(1, a) for a in E)
    L = math.lcm(*E)
    event = sum(1 for n in range(1, L + 1) if any(n % a == 0 for a in E)) / L
    prod = 1.0
    for a in E:
        prod *= 1 - 1 / a
    exact = 1 - prod
    assert abs(event - exact) < 1e-12
    lower = 1 - math.exp(-float(H))
    assert exact + 1e-12 >= lower
    # Majorant c_a = 1 on E: cost = sum 1/a = H, which is >= exact.
    cost = float(H)
    assert cost + 1e-12 >= exact
    return {
        "E": E,
        "H": str(H),
        "union_density": event,
        "one_minus_prod": exact,
        "one_minus_exp": lower,
        "majorant_cost": cost,
    }


def _atom_mod(B: float, L: int, d: int, m: int) -> float:
    return (B ** ((L * m) % d)) / (B**d - 1.0)


def check_a1_modular_estimate(quick: bool) -> dict:
    """Finite check of r3 (A1): mean B^{Lm mod d}/(B^d-1) <= B^L/(d log B)."""
    samples = [
        (2.0, 1, 6, 120),
        (2.0, 2, 9, 180),
        (3.0, 1, 4, 80),
        (2.0, 6, 15, 90),
    ]
    if not quick:
        samples.append((2.0, 4, 21, 210))
    rows = []
    for B, L, d, X in samples:
        mean = sum(_atom_mod(B, L, d, m) for m in range(1, X + 1)) / X
        bound = (B**L) / (d * math.log(B))
        assert mean <= bound + 1e-12, (B, L, d, X, mean, bound)
        g = math.gcd(L, d)
        limit = g / (d * (B**g - 1.0))
        # Period d/g residues; large X should sit near the limit, below the bound.
        assert limit <= bound + 1e-9
        rows.append(
            {
                "B": B,
                "L": L,
                "d": d,
                "X": X,
                "mean": mean,
                "bound": bound,
                "gcd_limit": limit,
            }
        )
    return {"rows": rows}


def check_flagship_q_plus_two_dominator() -> dict:
    """Atom Cesàro via geometric incidences is <= (Q+2)/d."""
    rows = []
    for Q, d, X in ((1, 6, 80), (2, 9, 90), (6, 15, 60)):
        # ω_{2,d}(N) = sum_{k>=0} 2^{-(kd + r)} with r = N mod d, equivalently
        # sum_t 2^{-t} 1_{d | N+t} wait: incidence of d at N+r is 1 iff d | N+r.
        left = 0.0
        for m in range(1, X + 1):
            n = Q * m
            s = 0.0
            # Truncate the geometric tail far enough for the comparison.
            for r in range(1, 80):
                if (n + r) % d == 0:
                    s += 2.0 ** (-r)
            left += s
        left /= X
        closed = (Q + 2.0) / d
        assert left <= closed + 1e-9, (Q, d, X, left, closed)
        rows.append({"Q": Q, "d": d, "X": X, "mean": left, "bound": closed})
    return {"rows": rows}


def check_b1_log_square_obstruction() -> dict:
    """Old cover cost K >= (1/2) E[(log^+ f_F)^2] on one displayed squarefree frame."""
    g, primes, alpha = 3, [5, 7], 0.25
    frame, _m = squarefree_frame(g, primes)
    t = 2.0**alpha - 1.0
    coeffs = {g * e: t ** sum(1 for p in primes if e % p == 0) for e in squarefree_divisors(primes)}
    k_alpha = (2.0**alpha) / ((2.0**alpha - 1.0) ** 2)
    # Displayed cover: one set, j=1 so 2^{j α}=2^α; the r3 old cost uses 2^{jα} k(α) C.
    C = sum(c / d for d, c in coeffs.items())
    old_cost = C * (2.0**alpha) * k_alpha
    period = math.lcm(*frame)
    mean_sq = 0.0
    for n in range(1, period + 1):
        f = incidence(frame, n)
        if f > 1:
            mean_sq += (math.log(f) ** 2)
    mean_sq /= period
    lower = 0.5 * mean_sq
    assert old_cost + 1e-12 >= lower, (old_cost, lower)
    return {
        "g": g,
        "primes": primes,
        "alpha": alpha,
        "old_cost": old_cost,
        "half_log_square_mean": lower,
        "gap": old_cost - lower,
    }


def check_a_star_scale_collision(quick: bool) -> dict:
    """Analytic discriminator: 2^{3j} (A*) vs 2^{6j} (A^dagger) at α_j=4^{-j}."""
    js = range(1, 6 if quick else 9)
    rows = []
    new_sum = 0.0
    old_star_sum = 0.0
    old_dagger_sum = 0.0
    for j in js:
        alpha = 4.0 ** (-j)
        b = 2.0**alpha
        two_j_alpha = 2.0 ** (j * alpha)
        # C_j <= e^{5/4}/q_j, q_j > 2^{3j} (A*) or 2^{6j} (A^dagger).
        c_star = math.exp(1.25) * (2.0 ** (-3 * j))
        c_dag = math.exp(1.25) * (2.0 ** (-6 * j))
        new_term = c_star * two_j_alpha / (b - 1.0)
        old_star = c_star * two_j_alpha * b / ((b - 1.0) ** 2)
        old_dag = c_dag * two_j_alpha * b / ((b - 1.0) ** 2)
        new_sum += new_term
        old_star_sum += old_star
        old_dagger_sum += old_dag
        rows.append(
            {
                "j": j,
                "new_term": new_term,
                "old_star_term": old_star,
                "old_dagger_term": old_dag,
            }
        )
    # A* new cost remains O(∑ 2^{-j}); A* old cost grows; A^dagger old cost decays.
    assert new_sum < 8.0, new_sum
    assert old_star_sum > old_dagger_sum
    assert rows[-1]["old_star_term"] > rows[0]["old_star_term"]
    assert rows[-1]["old_dagger_term"] < rows[0]["old_dagger_term"]
    bertrand_star = []
    for j in range(1, 4 if quick else 5):
        lo = 2 ** (3 * j)
        hi = 2 ** (3 * j + 1)
        q = first_prime_in_open_interval(lo, hi)
        assert q is not None, (j, lo, hi)
        bertrand_star.append({"j": j, "lo": lo, "hi": hi, "q": q})
    return {
        "new_partial_sum": new_sum,
        "old_star_partial_sum": old_star_sum,
        "old_dagger_partial_sum": old_dagger_sum,
        "rows": rows,
        "bertrand_star": bertrand_star,
        "collision": (
            "A* uses q_j in (2^{3j}, 2^{3j+1}) and is outside the old "
            "variable-exponent class; A^dagger used (2^{6j}, 2^{6j+1}) and "
            "satisfied the old class. Neither is inside reciprocal summability "
            "or a finite-P weighted class. Pairwise-coprime obstruction still "
            "defeats the new positive-cover method."
        ),
    }


def _finite_sum_value(F: set[int], b: int) -> Fraction:
    return sum((Fraction(1, b**n - 1) for n in F), start=Fraction(0))


def check_d1_denominator_realisation() -> dict:
    """D_2(6) = {21, 63}; 9 has ord_9(2)=6 but is not realised."""
    universe = (1, 2, 3, 6)
    realised = {}
    for mask in range(1, 1 << len(universe)):
        F = {universe[i] for i in range(len(universe)) if mask & (1 << i)}
        if math.lcm(*F) != 6:
            continue
        val = _finite_sum_value(F, 2)
        realised[frozenset(F)] = {"value": str(val), "D": val.denominator}
    dens = sorted({row["D"] for row in realised.values()})
    assert dens == [21, 63], dens
    # Order 6 modulo 9: 2^3 ≡ -1, 2^6 ≡ 1, no smaller positive exponent.
    assert pow(2, 6, 9) == 1
    assert all(pow(2, k, 9) != 1 for k in (1, 2, 3))
    assert 9 not in dens
    return {"D_2_6": dens, "supports": {str(sorted(F)): row for F, row in realised.items()}}


def check_d2_prime_lcm_formula() -> dict:
    """D_b(p) = {M, M/gcd(b-1, p+1)} for prime p."""
    rows = []
    for b, p in ((2, 3), (2, 5), (2, 7), (3, 2), (3, 5), (4, 3)):
        M = b**p - 1
        g = math.gcd(b - 1, p + 1)
        expected = sorted({M, M // g})
        dens = []
        for F in ({p}, {1, p}):
            dens.append(_finite_sum_value(F, b).denominator)
        dens = sorted(set(dens))
        assert dens == expected, (b, p, dens, expected)
        rows.append({"b": b, "p": p, "D": dens, "M": M, "gcd": g})
    return {"rows": rows}


def check_c1_base_comparison() -> dict:
    """(b^r-1)/(b^d-1) <= (2^r-1)/(2^d-1) for integers 0<=r<d and b>=2."""
    failures = []
    for b in range(2, 8):
        for d in range(1, 10):
            for r in range(d):
                left = Fraction(b**r - 1, b**d - 1)
                right = Fraction(2**r - 1, 2**d - 1)
                if left > right:
                    failures.append((b, r, d, str(left), str(right)))
    assert not failures, failures[:5]
    return {"checked_bases": list(range(2, 8)), "d_max": 9, "failures": 0}


def check_c2_c3_elementary() -> dict:
    """Zero windows <= min(A)-1; infinite supports have unbounded shifted tails."""
    A = {4, 6, 15}
    a0 = min(A)
    # Scan a stretch of incidences.
    longest = 0
    run = 0
    for n in range(1, 241):
        inc = sum(1 for a in A if n % a == 0)
        if inc == 0:
            run += 1
            longest = max(longest, run)
        else:
            run = 0
    assert longest <= a0 - 1
    # Unbounded tails: k distinct elements, L a common multiple, T_{L-1} >= k/2.
    k = 3
    L = math.lcm(*sorted(A)[:k])
    tail = sum(
        (sum(1 for a in A if (L - 1 + r) % a == 0) * (2.0 ** (-r)))
        for r in range(1, 40)
    )
    assert tail + 1e-12 >= k / 2.0
    return {"min_A": a0, "longest_zero_window": longest, "tail_at_L": tail, "k_over_2": k / 2.0}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--prime-limit", type=int, default=200000)
    parser.add_argument("--layers", type=int, default=4)
    args = parser.parse_args()
    if args.quick:
        args.prime_limit = min(args.prime_limit, 20000)
        args.layers = min(args.layers, 3)
    print("reconstruct: identities", file=sys.stderr, flush=True)
    identities = check_identities(args.quick)
    print("reconstruct: inequalities", file=sys.stderr, flush=True)
    inequalities = check_elementary_inequalities()
    print("reconstruct: bertrand", file=sys.stderr, flush=True)
    bertrand = check_bertrand_windows(args.quick)
    print("reconstruct: miniature", file=sys.stderr, flush=True)
    dagger = reconstruct_miniature_dagger(args.prime_limit, args.layers)
    print("reconstruct: s2", file=sys.stderr, flush=True)
    s2 = check_s2_witness()
    print("reconstruct: b1", file=sys.stderr, flush=True)
    b1 = check_b1_numeric()
    print("reconstruct: a1", file=sys.stderr, flush=True)
    a1 = check_a1_modular_estimate(args.quick)
    print("reconstruct: q_plus_two", file=sys.stderr, flush=True)
    q2 = check_flagship_q_plus_two_dominator()
    print("reconstruct: b1_log_square", file=sys.stderr, flush=True)
    b1_log = check_b1_log_square_obstruction()
    print("reconstruct: a_star", file=sys.stderr, flush=True)
    a_star = check_a_star_scale_collision(args.quick)
    print("reconstruct: d1", file=sys.stderr, flush=True)
    d1 = check_d1_denominator_realisation()
    print("reconstruct: d2", file=sys.stderr, flush=True)
    d2 = check_d2_prime_lcm_formula()
    print("reconstruct: c1", file=sys.stderr, flush=True)
    c1 = check_c1_base_comparison()
    print("reconstruct: c2c3", file=sys.stderr, flush=True)
    c2c3 = check_c2_c3_elementary()
    print("reconstruct: done", file=sys.stderr, flush=True)
    receipt = {
        "schema": "erdos257_variable_exponent_dagger_reconstruction_v1",
        "identities": identities,
        "inequalities": inequalities,
        "bertrand": bertrand,
        "miniature_dagger": {
            "reserved": dagger["reserved"],
            "frame_count": len(dagger["frames"]),
            "max_frame_reciprocal": dagger["max_frame_reciprocal"],
            "frames": [
                {
                    "j": f["j"],
                    "q": f["q"],
                    "block": f["block"],
                    "cost": f["cost"],
                    "reciprocal_mass": f["reciprocal_mass"],
                }
                for f in dagger["frames"]
            ],
        },
        "s2_witness": s2,
        "b1_numeric": b1,
        "a1_modular_estimate": a1,
        "flagship_q_plus_two": q2,
        "b1_log_square": b1_log,
        "a_star_scale": a_star,
        "d1_denominator_realisation": d1,
        "d2_prime_lcm": d2,
        "c1_base_comparison": c1,
        "c2_c3_elementary": c2c3,
        "claim_boundary": (
            "Exact identities, small-j Bertrand windows, and finite arithmetic "
            "for r3 A.1/B.1/B.2/D.1/D.2/C. Finite reconstruction does not prove "
            "the infinite A* construction or hereditary irrationality. A* is "
            "outside the old variable-exponent class; A^dagger is not."
        ),
    }
    import json

    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
