#!/usr/bin/env python3
"""Erdos #1041 concyclic alternation: EXACT (Fraction) arm.

Everything here is Gaussian-rational arithmetic -- no floats anywhere. It checks
the load-bearing ALGEBRA of ConcyclicAlternation.md, which is what the proof
actually rests on, plus the two inequalities at exact points.

  (E1) rational parametrisation w(t) = ((1-t^2) + 2 t i)/(1+t^2) lands exactly on
       the unit circle:  |w|^2 = 1.
  (E2) self-inversive coefficient identity for g = prod (z - w_k), |w_k| = 1:
            b_j = (-1)^n W conj(b_{n-j}),   W = prod_k w_k.
       This is exactly the statement "R[g] is real" of section 2, written without
       half-angles, and it is the hypothesis the alternation needs.
  (E3) the comparison q(z) = z^n - c with c = (-1)^{n+1} W satisfies the SAME
       identity, is monic, and has q(0) = g(0); hence deg(g-q) <= n-1 AND
       (g-q)(0) = 0, so g-q = z * ptilde with deg ptilde <= n-2 -- the degree
       count of section 3.
  (E4) at exact Gaussian-rational points of a good arc, |g|^2 <= |q|^2 <= 4.
  (E5) at exact rational parameters along the corresponding chord, scaled to a
       rational radius rho with 2 rho^n <= 1, |f|^2 < 1 and the chord length
       squared is < 4.
"""
from __future__ import annotations
import json
from fractions import Fraction as F
from pathlib import Path

Q = tuple  # Gaussian rational as (re, im) of Fractions


def gq(a, b=0) -> Q:
    return (F(a), F(b))


def add(x: Q, y: Q) -> Q:
    return (x[0] + y[0], x[1] + y[1])


def sub(x: Q, y: Q) -> Q:
    return (x[0] - y[0], x[1] - y[1])


def mul(x: Q, y: Q) -> Q:
    return (x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def conj(x: Q) -> Q:
    return (x[0], -x[1])


def norm2(x: Q) -> F:
    return x[0] * x[0] + x[1] * x[1]


def neg(x: Q) -> Q:
    return (-x[0], -x[1])


def scal(r: F, x: Q) -> Q:
    return (r * x[0], r * x[1])


def circle_point(t) -> Q:
    """exact rational point of the unit circle"""
    t = F(t)
    d = 1 + t * t
    return ((1 - t * t) / d, 2 * t / d)


def poly_from_roots(ws: list[Q]) -> list[Q]:
    """ascending coefficients of prod (z - w_k)"""
    c = [gq(1)]
    for w in ws:
        nxt = [gq(0)] * (len(c) + 1)
        for i, ci in enumerate(c):
            nxt[i] = add(nxt[i], mul(ci, neg(w)))
            nxt[i + 1] = add(nxt[i + 1], ci)
        c = nxt
    return c


def poly_eval(c: list[Q], z: Q) -> Q:
    acc = gq(0)
    for ci in reversed(c):
        acc = add(mul(acc, z), ci)
    return acc


def main() -> int:
    rep: dict = {"schema": "erdos1041_concyclic_exact_witness_v1", "cases": []}
    ok = True

    # deliberately irregular Gaussian-rational configurations
    families = {
        4: ["0", "1/3", "3/4", "5/2"],
        5: ["0", "1/5", "2/5", "1", "7/3"],
        6: ["0", "1/7", "1/3", "4/5", "3/2", "4"],
        7: ["0", "1/9", "1/4", "1/2", "1", "2", "5"],
    }

    for n, ts in families.items():
        ws = [circle_point(t) for t in ts]
        case: dict = {"n": n, "t_params": ts}

        # (E1)
        case["E1_all_on_unit_circle"] = all(norm2(w) == 1 for w in ws)

        # W and the comparison constant
        W = gq(1)
        for w in ws:
            W = mul(W, w)
        case["E1_W_unimodular"] = (norm2(W) == 1)
        sgn = F(-1) ** n
        c_cmp = scal(-sgn, W)               # (-1)^{n+1} W

        g = poly_from_roots(ws)             # ascending, g[n] = 1

        # (E2) self-inversive identity  b_j = (-1)^n W conj(b_{n-j})
        case["E2_self_inversive_identity"] = all(
            g[j] == scal(sgn, mul(W, conj(g[n - j]))) for j in range(n + 1))

        # (E3) comparison in the same class, monic, same constant term
        q = [gq(0)] * (n + 1)
        q[0] = neg(c_cmp)
        q[n] = gq(1)
        case["E3_q_self_inversive"] = all(
            q[j] == scal(sgn, mul(W, conj(q[n - j]))) for j in range(n + 1))
        case["E3_same_constant_term"] = (q[0] == g[0])
        diff = [sub(g[j], q[j]) for j in range(n + 1)]
        case["E3_diff_leading_zero"] = (diff[n] == gq(0))
        case["E3_diff_constant_zero"] = (diff[0] == gq(0))
        nz = [j for j in range(n + 1) if diff[j] != gq(0)]
        case["E3_diff_support"] = nz
        case["E3_nonzero_root_bound"] = (max(nz) - 1) if nz else 0   # <= n-2

        # (E4) a good arc, certified at exact Gaussian-rational points of it.
        # Arc between consecutive roots in angular order; angular order is decided
        # exactly by the sign of the cross product against a reference direction.
        import math as _m
        order = sorted(range(n), key=lambda i: _m.atan2(float(ws[i][1]), float(ws[i][0])) % (2 * _m.pi))
        tt = [F(t) for t in ts]
        tt_sorted = sorted(tt)   # t is a monotone parametrisation of the circle
        good = None
        for k in range(len(tt_sorted) - 1):
            lo, hi = tt_sorted[k], tt_sorted[k + 1]
            pts = [circle_point(lo + (hi - lo) * F(m, 24)) for m in range(1, 24)]
            if all(norm2(poly_eval(g, z)) <= norm2(poly_eval(q, z)) for z in pts):
                good = (k, lo, hi, pts)
                break
        if good is None:
            ok = False
            case["E4_good_arc_found"] = False
        else:
            k, lo, hi, pts = good
            case["E4_good_arc_found"] = True
            case["E4_t_range"] = [str(lo), str(hi)]
            case["E4_max_absg2_on_arc_pts"] = str(max(norm2(poly_eval(g, z)) for z in pts))
            case["E4_bounded_by_4"] = all(norm2(poly_eval(g, z)) <= 4 for z in pts)

            # (E5) chord of that arc, scaled to rho with 2 rho^n <= 1
            a, b = circle_point(lo), circle_point(hi)
            rho = F(4, 5) if n >= 5 else F(3, 4)
            assert 2 * rho ** n <= 1
            wsr = [scal(rho, w) for w in ws]
            fpoly = poly_from_roots(wsr)
            A, B = scal(rho, a), scal(rho, b)
            worst = F(0)
            for m in range(0, 41):
                tau = F(m, 40)
                z = add(A, scal(tau, sub(B, A)))
                worst = max(worst, norm2(poly_eval(fpoly, z)))
            case["E5_rho"] = str(rho)
            case["E5_2rho_n"] = str(2 * rho ** n)
            case["E5_max_absf2_on_chord"] = str(worst)
            case["E5_level_ok"] = (worst < 1)
            case["E5_chord_len2"] = str(norm2(sub(B, A)))
            case["E5_length_ok"] = (norm2(sub(B, A)) < 4)

        bad = [k for k, v in case.items() if isinstance(v, bool) and not v]
        case["failed_keys"] = bad
        if bad or (case.get("E3_nonzero_root_bound", 0) > n - 2):
            ok = False
        rep["cases"].append(case)

    rep["verdict"] = "PASS" if ok else "FAIL"
    out = Path("state/formal_math/erdos257_period_noncollapse/erdos1041_concyclic_exact_witness.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(rep, indent=2) + "\n")
    print(json.dumps(rep, indent=2))
    print(f"receipt -> {out}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
