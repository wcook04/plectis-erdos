#!/usr/bin/env python3
"""Exact rational certificate for the fixed-degree cluster-separation closure.

Sharpens the fixed-degree arm of ClusterSeparationLowCriticalClosure.md.  The
new ingredient is the ANGULAR separation bound: the corpus used only the
triangle inequality d_i + d_j >= d_min between the COVER point h and two roots
of the ancestor component, which is the phi = pi case of the hyperbolic law of
cosines.  Keeping the angle and summing sin^2(phi_ij/2) over all pairs (an exact
identity bounded by k^2/4) gives a second, strictly better arity bound.

Failure forces, at every regular level t in (mu, 1) with x = log(t/mu),
    x  <=  min( Lambda(k, a), Theta(k, a) ),   a = Area(C_t)/pi <= t^(2/n) <= 1,
with k <= n the arity of the ancestor component.  Lambda is the ordered profile
bound (2') of ClusterSeparationLowCriticalClosure.md; Theta is the new angular
bound.  Letting t -> 1 gives mu >= exp(-min(Lambda(n,1), Theta(n,1))), so any
mu strictly below that constant is contradictory.

Prints one JSON line.
"""
from __future__ import annotations
import json, sys
from fractions import Fraction as Q
from math import isqrt

D = 10**24


def floor_q(q: Q) -> Q:
    return Q((q.numerator * D) // q.denominator, D)


def ceil_q(q: Q) -> Q:
    return Q(-((-q.numerator * D) // q.denominator), D)


def sqrt_upper(q: Q) -> Q:
    if q <= 0:
        return Q(0)
    v = -((-q.numerator * D * D) // q.denominator)
    r = isqrt(v)
    if r * r < v:
        r += 1
    return Q(r, D)


def sqrt_lower(q: Q) -> Q:
    if q <= 0:
        return Q(0)
    return Q(isqrt((q.numerator * D * D) // q.denominator), D)


# ---------------------------------------------------------------- exponentials
def exp_upper(y: Q, terms: int = 90) -> Q:
    """Upper bound for exp(y), y >= 0, by halving, series + geometric tail, squaring."""
    assert y >= 0
    j = 0
    while y > 1:
        y /= 2
        j += 1
    tot = term = Q(1)
    for i in range(1, terms):
        term = term * y / i
        tot += term
    tot = ceil_q(tot + term * y / terms / (1 - y / terms))
    for _ in range(j):
        tot = ceil_q(tot * tot)
    return tot


def exp_lower(y: Q, terms: int = 90) -> Q:
    """Lower bound for exp(y), y >= 0."""
    assert y >= 0
    j = 0
    while y > 1:
        y /= 2
        j += 1
    tot = term = Q(1)
    for i in range(1, terms):
        term = term * y / i
        tot += term
    tot = floor_q(tot)
    for _ in range(j):
        tot = floor_q(tot * tot)
    return tot


def em_upper(y: Q) -> Q:
    """Upper bound for exp(-y), y >= 0."""
    return ceil_q(1 / exp_lower(y))


def em_lower(y: Q) -> Q:
    """Lower bound for exp(-y), y >= 0."""
    return floor_q(1 / exp_upper(y))


# ------------------------------------------------------------- delta, tau, lam
def delta_bounds(a: Q):
    """delta(a) = -log(1 - e^(-1/a)) = sum_{j>=1} u^j / j,  u = e^(-1/a)."""
    J = 60
    out = []
    for direction in ("lower", "upper"):
        u = em_lower(1 / a) if direction == "lower" else em_upper(1 / a)
        if u >= 1:
            out.append(Q(10) ** 9)
            continue
        tot = Q(0)
        pw = Q(1)
        for j in range(1, J + 1):
            pw = floor_q(pw * u) if direction == "lower" else ceil_q(pw * u)
            tot += pw / j
        if direction == "lower":
            out.append(floor_q(tot))
        else:
            out.append(ceil_q(tot + pw * u / ((J + 1) * (1 - u))))
    return out[0], out[1]


def tau_bounds(a: Q):
    """tau(a) = -log tanh(1/a) = 2 sum_{j>=0} v^(2j+1)/(2j+1),  v = e^(-2/a)."""
    J = 60
    out = []
    for direction in ("lower", "upper"):
        v = em_lower(2 / a) if direction == "lower" else em_upper(2 / a)
        if v >= 1:
            out.append(Q(10) ** 9)
            continue
        v2 = floor_q(v * v) if direction == "lower" else ceil_q(v * v)
        tot = Q(0)
        pw = v
        for j in range(0, J + 1):
            tot += pw / (2 * j + 1)
            pw = floor_q(pw * v2) if direction == "lower" else ceil_q(pw * v2)
        if direction == "lower":
            out.append(floor_q(2 * tot))
        else:
            out.append(ceil_q(2 * (tot + pw / ((2 * J + 3) * (1 - v2)))))
    return out[0], out[1]


def lam_upper(d: Q) -> Q:
    """lam(d) = 2 artanh(e^-d); upper bound needs e^-d from above."""
    if d <= 0:
        return Q(10) ** 9
    v = em_upper(d)
    if v >= 1:
        return Q(10) ** 9
    J = 40
    tot = Q(0)
    pw = v
    v2 = ceil_q(v * v)
    for j in range(J + 1):
        tot += pw / (2 * j + 1)
        pw = ceil_q(pw * v2)
    return ceil_q(2 * (tot + pw / ((2 * J + 3) * (1 - v2))))


def lam_lower(d: Q) -> Q:
    if d <= 0:
        return Q(10) ** 9
    v = em_lower(d)
    if v <= 0:
        return Q(0)
    J = 40
    tot = Q(0)
    pw = v
    v2 = floor_q(v * v)
    for j in range(J + 1):
        tot += pw / (2 * j + 1)
        pw = floor_q(pw * v2)
    return floor_q(2 * tot)


def tanh_bounds(y_lo: Q, y_up: Q):
    """tanh(y) = (1 - e^-2y)/(1 + e^-2y), increasing in y."""
    e_hi = em_upper(2 * y_lo)          # e^-2y at the small end, from above
    e_lo = em_lower(2 * y_up)
    lo = floor_q((1 - e_hi) / (1 + e_hi))
    up = ceil_q((1 - e_lo) / (1 + e_lo))
    return max(Q(0), lo), up


# -------------------------------------------------------- the two arity bounds
_PRIM: dict = {}


def primitives(a: Q):
    """(delta_lo, delta_up, tau_lo, tau_up, W_lo, W_up, r_lo, r_up, M_lo, M_up)."""
    if a in _PRIM:
        return _PRIM[a]
    dl, du = delta_bounds(a)
    tl, tu = tau_bounds(a)
    W_lo, W_up = tanh_bounds(dl / 4, du / 4)
    r_lo, r_up = tanh_bounds(tl / 4, tu / 4)
    # M = (r^2 + r^-2)/2 is DECREASING in r on (0,1)
    if r_lo <= 0:
        M_lo, M_up = Q(1), Q(10) ** 12
    else:
        M_up = ceil_q((r_lo * r_lo + 1 / (r_lo * r_lo)) / 2)
        M_lo = floor_q((r_up * r_up + 1 / (r_up * r_up)) / 2)
    out = (dl, du, tl, tu, W_lo, W_up, r_lo, r_up, M_lo, M_up)
    _PRIM[a] = out
    return out


def lambda_upper(k: int, a: Q) -> Q:
    """Ordered-profile bound (2') of ClusterSeparationLowCriticalClosure.md, from above."""
    dl, du, tl, tu, *_ = primitives(a)
    # g = d_min - d_low = 2 lam(tau/2) - lam(delta/2); lam(g) <= lam(d_min/2) = tau/2 always
    lg = tu / 2
    if tl > 0 and dl > 0:
        g_lo = 2 * lam_lower(tu / 2) - lam_upper(dl / 2)
        if g_lo > 0:
            lg = min(lg, lam_upper(g_lo))
    return max(du / 2 + (k - 1) * lg, Q(k) * tu / 2)


def theta_upper(k: int, a: Q) -> Q:
    """Angular second-moment bound, from above.

    M S^2 <= k^2/4 + (M + k - 1)(r S + W(W - r)),  S = sum_j w_j,  and the
    objective sum_j 2 artanh(w_j) <= 2 S / (1 - W^2).
    """
    dl, du, tl, tu, W_lo, W_up, r_lo, r_up, M_lo, M_up = primitives(a)
    if M_lo <= 0 or W_up >= 1:
        return Q(10) ** 9
    B = ceil_q((M_up + k - 1) * r_up)
    ww = W_up * W_up - W_lo * r_lo          # upper bound for W(W - r); >= 0 since W > r
    if ww < 0:
        ww = Q(0)
    C = Q(k * k, 4) + ceil_q((M_up + k - 1) * ww)
    S = ceil_q((B + sqrt_upper(B * B + 4 * M_lo * C)) / (2 * M_lo))
    return ceil_q(2 * S / (1 - W_up * W_up))


def bound_upper(k: int, a: Q) -> Q:
    return min(lambda_upper(k, a), theta_upper(k, a))


# ------------------------------------------------------------------- main pass
CANDIDATES = [Q(p, 1000) for p in range(700, 199, -1)]


def certify_closed_form(n: int):
    """Largest listed rational mu with mu * exp(bound_upper(n,1)) < 1."""
    b = bound_upper(n, Q(1))
    e = exp_upper(b)
    for mu in CANDIDATES:
        if mu * e < 1:
            return mu, b
    return None, b


def main() -> int:
    rep = {
        "status": "pass",
        "evidence_class": "exact_rational_certificate",
        "mechanism": "COVER one-root Bergman + pairwise cluster separation + hyperbolic angular"
                     " second-moment packing + Polya cap; arity cap k <= n",
    }
    rows = {}
    for n in range(3, 13):
        mu, b = certify_closed_form(n)
        assert mu is not None, f"degree {n}: no candidate certified"
        lam_u = lambda_upper(n, Q(1))
        th_u = theta_upper(n, Q(1))
        rows[n] = {
            "mu_threshold": str(mu),
            "mu_threshold_float": float(mu),
            "bound_upper": float(b),
            "lambda_upper": float(lam_u),
            "theta_upper": float(th_u),
            "binding": "theta" if th_u <= lam_u else "lambda",
        }
    rep["per_degree"] = rows
    # regression guards against the landed constants
    assert rows[4]["mu_threshold_float"] > 0.5, "must beat the landed n=4 value 1/2"
    assert rows[5]["mu_threshold_float"] > 0.45, "must beat the landed n=5 value 9/20"
    assert rows[6]["mu_threshold_float"] > 0.4, "must beat the landed n=6 value 2/5"
    assert rows[7]["mu_threshold_float"] > 0.35, "must beat the landed n=7 value 7/20"
    assert rows[9]["mu_threshold_float"] > 0.36, "must beat the all-degree 9/25 at n = 9"
    rep["all_degree_baseline"] = "9/25 (ClusterSeparationLowCriticalClosure.md)"
    rep["degrees_beating_all_degree_baseline"] = [
        n for n in rows if rows[n]["mu_threshold_float"] > 9 / 25
    ]
    print(json.dumps(rep))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
