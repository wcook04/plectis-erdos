#!/usr/bin/env python3
"""Exact certificate for LowCriticalPotentialClosure.md.

Three rigorous outputs, all in rational arithmetic with directed rounding.

1. The scalar-potential certificate of the returned mu <= 1/8 theorem
   (Lemma 6.1 of the eighth 2026-09-05 return): the forcing integral at
   X0 = 2079/1000 exceeds 7/40, which exceeds V(1) = int_0^1 delta.

2. The sharpened all-degree threshold.  Under the failure hypothesis the
   normalised area a(x) = Area(K_{mu e^x})/pi of a counterexample satisfies
   a' >= G(x, a) almost everywhere, with

       G(x, a) = (1/(2 pi^2)) [ 2 sqrt(k(x,a)) - sqrt(2 a (x+2)) ]_+^2,
       k(x, a) = max(2, 2x/delta(a)),   delta(a) = -log(1 - exp(-1/a)),

   and a <= 1 while mu e^x < 1.  G decreases in a; its k-term increases in x
   and its subtracted term increases in x, so on a cell [x_i, x_{i+1}] the
   bound G_cell(a) = G with k at x_i and the root term at x_{i+1} is a valid
   lower bound, decreasing in a.  A monotone implicit-Euler lower step then
   propagates a rigorous lower bound for a.  The initial area is covered by a
   geometric grid: on [0, x_s] every trajectory grows at least c x_s with an
   explicit c, so a(x_s) lies in [alpha_0, 1], and comparison from the grid
   point below it bounds the hitting time.  The certified X_cert is the largest
   grid hitting time; the theorem then holds for mu <= mu_star whenever
   mu_star * exp(X_cert) <= 1.

3. Per-degree thresholds for n = 4..7 using the two extra facts available at
   fixed degree: the Polya cap a(x) <= (mu e^x)^(2/n) and the COVER-wins
   floor a(x) >= delta^{-1}(2x/n).

Every exp is bounded by a truncated Taylor series (lower) or a Taylor series
with a geometric tail (upper); every sqrt by integer square roots; every
rational is floored or ceiled onto a fixed grid so denominators stay small.
"""
from __future__ import annotations

import json
import sys
from fractions import Fraction as Q
from math import isqrt

D = 10**12
INV_TWO_PI_SQ_LOWER = Q(49, 968)          # 1/(2 pi^2) > 49/968 because pi < 22/7
K_CAP = 10**8                             # a lower bound on k may be truncated


def floor_q(q: Q) -> Q:
    return Q((q.numerator * D) // q.denominator, D)


def ceil_q(q: Q) -> Q:
    return Q(-((-q.numerator * D) // q.denominator), D)


def sqrt_lower(q: Q) -> Q:
    if q <= 0:
        return Q(0)
    return Q(isqrt((q.numerator * D * D) // q.denominator), D)


def sqrt_upper(q: Q) -> Q:
    if q <= 0:
        return Q(0)
    v = -((-q.numerator * D * D) // q.denominator)
    r = isqrt(v)
    if r * r < v:
        r += 1
    return Q(r, D)


def exp_lower_small(y: Q, terms: int = 80) -> Q:
    """Truncated Taylor series: a lower bound for exp(y), y >= 0."""
    total, term = Q(1), Q(1)
    for j in range(1, terms):
        term = term * y / j
        total += term
    return floor_q(total)


def exp_lower(y: Q) -> Q:
    """exp(y) >= exp(min(y, 64)); square a small-argument lower bound."""
    y = min(y, Q(64))
    j = 0
    while y > 4:
        y /= 2
        j += 1
    value = exp_lower_small(y)
    for _ in range(j):
        value = floor_q(value * value)
    return value


def exp_upper(y: Q, terms: int = 60) -> Q:
    """Taylor series plus geometric tail: an upper bound for exp(y), 0 <= y < terms."""
    assert 0 <= y < terms
    total, term = Q(1), Q(1)
    for j in range(1, terms):
        term = term * y / j
        total += term
    tail = term * y / terms / (1 - y / terms)
    return ceil_q(total + tail)


_DELTA_CACHE: dict[Q, Q] = {}
A_GRID = 10**7


def delta_upper(a: Q) -> Q:
    """delta(a) = -log(1-exp(-1/a)) = sum_j exp(-j/a)/j <= 1/(exp(1/a)-1).

    delta is increasing, so evaluating at a rounded UP onto the grid 1/A_GRID
    keeps the result an upper bound and makes it cacheable.
    """
    a_up = Q(-((-a.numerator * A_GRID) // a.denominator), A_GRID)
    hit = _DELTA_CACHE.get(a_up)
    if hit is None:
        e = exp_lower(1 / a_up)
        u = ceil_q(1 / e)                       # upper bound for exp(-1/a)
        if u >= 1:
            hit = Q(10**6)
        else:
            # delta = sum_{j>=1} u^j/j <= partial sum + geometric tail
            J = 40
            total, power = Q(0), Q(1)
            for j in range(1, J + 1):
                power = floor_q(power * u) if power * u > 0 else power * u
                power = ceil_q(power) if j == 1 else power
                total += power / j
            tail = power * u / ((J + 1) * (1 - u))
            hit = ceil_q(total + tail)
        _DELTA_CACHE[a_up] = hit
    return hit


def k_lower(x: Q, a: Q) -> Q:
    if x <= 0:
        return Q(2)
    d = delta_upper(a)
    k = 2 * x / d
    return min(max(Q(2), floor_q(k)), Q(K_CAP))


def g_cell_lower(x_left: Q, x_right: Q, a: Q) -> Q:
    """Lower bound for G(x, a) on x in [x_left, x_right]; decreasing in a."""
    b = 2 * sqrt_lower(k_lower(x_left, a)) - sqrt_upper(2 * a * (x_right + 2))
    if b <= 0:
        return Q(0)
    return floor_q(INV_TWO_PI_SQ_LOWER * b * b)


def a_floor_from_cover(x: Q, n: int) -> Q:
    """Rigorous lower bound for the area forced by k(x, a) <= n.

    Any a_m with delta_upper(a_m) < 2x/n has k(x, a) > n for every a <= a_m,
    which contradicts failure; hence the true area exceeds a_m.
    """
    target = 2 * x / n
    if delta_upper(Q(1)) < target:
        return Q(1)
    lo, hi = Q(1, 10**6), Q(1)
    if not delta_upper(lo) < target:
        return Q(0)
    for _ in range(40):
        mid = (lo + hi) / 2
        if delta_upper(mid) < target:
            lo = mid
        else:
            hi = mid
    return floor_q(lo)


def lower_step(x_left: Q, x_right: Q, a_i: Q) -> Q:
    """Monotone implicit-Euler lower bound.

    With phi(a) = a - a_i - h G_cell(a) increasing in a, the true a(x_right)
    satisfies phi >= 0, hence a(x_right) >= a_star, the unique zero of phi.
    Any a with phi(a) < 0 lies below a_star, so the bisection bracket's low end
    is a rigorous lower bound.  The bracket [a_corr, a_pred] contains a_star.
    """
    h = x_right - x_left
    g_i = g_cell_lower(x_left, x_right, a_i)
    a_pred = a_i + h * g_i
    if a_pred > 1:
        # if even phi(1) < 0 the lower bound already exceeds the cap
        if 1 - a_i - h * g_cell_lower(x_left, x_right, Q(1)) < 0:
            return Q(1) + Q(1, D)
        a_pred = Q(1)
    a_corr = a_i + h * g_cell_lower(x_left, x_right, a_pred)
    lo, hi = a_corr, a_pred
    for _ in range(40):
        if hi - lo < Q(1, 10**6):
            break
        mid = (lo + hi) / 2
        if mid - a_i - h * g_cell_lower(x_left, x_right, mid) < 0:
            lo = mid
        else:
            hi = mid
    return floor_q(max(lo, a_i))


GEOMETRIC_RATIO = Q(1, 16)


def next_x(x: Q, h: Q) -> Q:
    """Geometric cells while x is small (k grows like x there), uniform cells after."""
    return x + min(h, max(x * GEOMETRIC_RATIO, Q(1, 10**7)))


def hitting_time(alpha: Q, x_s: Q, h: Q, cap_test, floor_fn=None, x_max: Q = Q(4)) -> Q | None:
    x, a = x_s, alpha
    if floor_fn is not None:
        a = max(a, floor_fn(x))
    if cap_test(x, a):
        return x
    while x < x_max:
        x_next = next_x(x, h)
        a = lower_step(x, x_next, a)
        if floor_fn is not None:
            a = max(a, floor_fn(x_next))
        x = x_next
        if cap_test(x, a):
            return x
    return None


def start_shift(x_s: Q) -> Q:
    """Certified minimum growth on [0, x_s]: a' >= c with c from k >= 2 and a <= 1."""
    b = 2 * sqrt_lower(Q(2)) - sqrt_upper(2 * (x_s + 2))
    assert b > 0
    return floor_q(INV_TWO_PI_SQ_LOWER * b * b)


def geometric_grid(alpha_0: Q, count: int) -> list[Q]:
    grid = []
    for i in range(count + 1):
        # alpha_0^(1 - i/count) via repeated rational powers is awkward; use a
        # decimal geometric ladder and floor each entry.
        t = Q(i, count)
        # alpha_0 = 10^-6 -> 10^(-6(1-t)); floor(10^(-6+6t)) computed from float then rationalised downward
        value = Q(10) ** 0
        exponent = -6 * (1 - t)
        f = 10.0 ** float(exponent)
        value = floor_q(Q(f).limit_denominator(D))
        grid.append(max(value, alpha_0))
    grid[-1] = Q(1)
    return sorted(set(grid))


def certify_all_degree(h: Q, grid_count: int) -> dict:
    x_s = Q(3, 10**5)
    c = start_shift(x_s)
    alpha_0 = Q(1, 10**6)
    assert c * x_s >= alpha_0, "start shift too small for the grid floor"
    grid = geometric_grid(alpha_0, grid_count)
    cap = lambda x, a: a > 1
    worst = Q(0)
    worst_alpha = None
    for alpha in grid:
        t = hitting_time(alpha, x_s, h, cap)
        assert t is not None, f"no hit from alpha={alpha}"
        if t > worst:
            worst, worst_alpha = t, alpha
    return {"X_cert": worst, "worst_alpha": worst_alpha, "grid_points": len(grid), "x_s": x_s, "start_slope": c}


def certify_degree(n: int, mu_star: Q, h: Q, grid_count: int) -> bool:
    """Contradiction for every counterexample of degree n with mu <= mu_star."""
    x_s = Q(3, 10**5)
    c = start_shift(x_s)
    alpha_0 = Q(1, 10**6)
    assert c * x_s >= alpha_0
    grid = geometric_grid(alpha_0, grid_count)

    def cap(x, a):
        # a > (mu e^x)^(2/n)  <=>  a^n > mu^2 e^(2x)
        return a ** n > mu_star ** 2 * exp_upper(2 * x)

    floor_fn = lambda x: a_floor_from_cover(x, n)
    x_max = Q(6)
    for alpha in grid:
        t = hitting_time(alpha, x_s, h, cap, floor_fn, x_max)
        if t is None:
            return False
        # levels used must stay below one: t < log(1/mu_star)  <=>  mu_star e^t < 1
        if not mu_star * exp_upper(t) < 1:
            return False
    return True


def returned_scalar_certificate() -> dict:
    """The eighth return's Lemma 6.1, replayed exactly."""
    def ceilq(x):
        return (x.numerator + x.denominator - 1) // x.denominator

    def delta_upper_at(a, DD=10**9):
        q = 1 / a
        S = term = Q(1)
        for j in range(1, 31):
            term *= q / j
            S += term
        y = 1 / S
        sm, yp = Q(0), Q(1)
        for j in range(1, 25):
            yp *= y
            sm += yp / j
        sm += yp * y / (25 * (1 - y))
        return Q(ceilq(sm * DD), DD)

    N = 100
    ds = [delta_upper_at(Q(i, N)) for i in range(1, N + 1)]
    F_up = sum(ds, Q(0)) / N
    assert F_up == Q(4354523513, 25000000000)
    assert ds[-1] < Q(459, 1000)
    assert F_up < Q(7, 40)
    L0, C, DD, N2 = Q(2079, 1000), Q(459, 1000), 10**8, 128

    def sqrt_floor_scaled(q):
        return isqrt(q.numerator * DD * DD // q.denominator)

    S = 0
    for i in range(N2):
        x = L0 * i / N2
        lo1 = sqrt_floor_scaled(x)
        hi2 = sqrt_floor_scaled(C * (x + 2)) + 1
        g = max(0, 2 * lo1 - hi2)
        S += g * g
    J_low = L0 / N2 * Q(49, 484) * Q(S, DD * DD)
    assert J_low == Q(5032220493131721796221, 28160000000000000000000)
    assert J_low > Q(7, 40)
    assert Q(842, 405) > L0
    return {"V1_upper": str(F_up), "forcing_lower": str(J_low), "X0": str(L0), "log8_lower": "842/405"}


def main() -> int:
    quick = "--quick" in sys.argv
    h = Q(1, 100) if quick else Q(1, 800)
    grid_count = 8 if quick else 12
    report = {"status": "pass", "evidence_class": "exact_rational_certificate", "mode": "quick" if quick else "full"}
    report["returned_one_eighth_certificate"] = returned_scalar_certificate()

    all_deg = certify_all_degree(h, grid_count)
    X = all_deg["X_cert"]
    candidates = [Q(1, 5), Q(199, 1000), Q(198, 1000), Q(197, 1000), Q(49, 250), Q(39, 200), Q(19, 100), Q(1, 6), Q(1, 8)]
    certified = None
    for mu in candidates:
        if mu * exp_upper(X) <= 1:
            certified = mu
            break
    assert certified is not None
    assert certified > Q(1, 8), "the sharpening must beat the returned 1/8"
    report["all_degree"] = {
        "X_cert": str(X), "X_cert_float": float(X), "mu_threshold": str(certified),
        "worst_initial_area": float(all_deg["worst_alpha"]), "grid_points": all_deg["grid_points"], "step": str(h),
    }

    degree_candidates = {
        4: [Q(57, 100), Q(11, 20), Q(1, 2), Q(9, 20), Q(2, 5), Q(1, 3)],
        5: [Q(9, 20), Q(11, 25), Q(2, 5), Q(7, 20), Q(3, 10), Q(1, 4)],
        6: [Q(3, 10), Q(7, 25), Q(1, 4), Q(11, 50), Q(1, 5)],
        7: [Q(199, 1000), Q(19, 100), Q(9, 50), Q(1, 6)],
    }
    degree_rows = {}
    for n, cands in degree_candidates.items():
        chosen = None
        for mu_n in cands:
            if certify_degree(n, mu_n, h, grid_count):
                chosen = mu_n
                break
        assert chosen is not None, f"degree {n}: no candidate certified"
        assert chosen >= certified, f"degree {n} threshold {chosen} below the all-degree threshold {certified}"
        degree_rows[n] = str(chosen)
    report["per_degree_thresholds"] = degree_rows
    report["universal_authority"] = "LowCriticalPotentialClosure.md"
    print(json.dumps(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
