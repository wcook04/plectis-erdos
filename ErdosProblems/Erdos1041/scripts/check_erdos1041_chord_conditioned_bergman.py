#!/usr/bin/env python3
"""Replay for ChordConditionedBergman.md.

Four arms.  RATIONAL1720 and CUBIC are exact rational certificates and carry
proof authority for the two rational statements they certify.  SPECTRUM and
RANDOM are finite floating-point falsification arms with no universal
authority: the analytic proofs in the note supply the quantifiers.
"""
import argparse
import cmath
import json
import math
import random
from fractions import Fraction as F
from math import isqrt


# ---------------------------------------------------------------- exact tools

def iroot(n, k):
    """Floor of the k-th root of a nonnegative integer."""
    lo, hi = 0, 1
    while hi ** k <= n:
        hi *= 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid ** k <= n:
            lo = mid
        else:
            hi = mid
    return lo


def sqrt_enclosure(fr, digits=45):
    """Rational lo <= sqrt(fr) < hi, certified by squaring."""
    scale = 10 ** digits
    m = isqrt(fr.numerator * scale * scale * fr.denominator)
    lo = F(m, scale * fr.denominator)
    hi = F(m + 1, scale * fr.denominator)
    assert lo * lo <= fr < hi * hi
    return lo, hi


def two_thirds_power_enclosure(fr, digits=45):
    """Rational lo <= fr**(2/3) < hi, certified by cubing against fr**2."""
    target = fr * fr
    scale = 10 ** digits
    m = iroot(target.numerator * (scale ** 3) * (target.denominator ** 2), 3)
    lo = F(m, scale * target.denominator)
    hi = F(m + 1, scale * target.denominator)
    assert lo ** 3 <= target < hi ** 3
    return lo, hi


def log_enclosure(x_lo, x_hi, terms=60):
    """Rational enclosure of log on 1 <= x <= 2 from the artanh series."""
    assert 1 <= x_lo <= x_hi <= 2

    def series(x):
        s = (x - 1) / (x + 1)
        total = F(0)
        for j in range(terms):
            total += s ** (2 * j + 1) / (2 * j + 1)
        total *= 2
        remainder = 2 * s ** (2 * terms + 1) / ((2 * terms + 1) * (1 - s * s))
        return total, total + remainder

    lo, _ = series(x_lo)
    _, hi = series(x_hi)
    return lo, hi


# ------------------------------------------------- arm 1: the 17/20 criterion

def arm_rational_1720():
    """Exact rational certificate for Corollary 2 of the note."""
    x0 = F(17, 20)
    b_hi = sum(2 * x0 ** (2 * j + 1) / ((2 * j + 1) * (2 * j + 3)) for j in range(7))
    b_hi += 2 * x0 ** 15 / (15 * 17 * (1 - x0 * x0))
    h_hi = sum(x0 ** (2 * j + 1) / (2 * j + 1) for j in range(7))
    h_hi += x0 ** 15 / (15 * (1 - x0 * x0))
    assert b_hi < F(7, 10), b_hi
    assert h_hi < F(101, 80), h_hi
    # The published chain bounds (1-b(x))*d^2 by 3/10, which needs b(x) >= 7/10
    # and is false for small x.  The repaired chain is the monotone one below.
    assert F(1) - b_hi > F(3, 10)
    # Case A: 4*artanh(x) <= 1 gives 1 + b(x)*(4 artanh x - 1) <= 1 < 767/200.
    # Case B: 4*artanh(x) > 1 and x <= 17/20 give the endpoint bound, because
    # both b and artanh increase and both factors are then nonnegative.
    case_b = 1 + F(7, 10) * (4 * F(101, 80) - 1)
    assert case_b == F(767, 200), case_b
    assert F(767, 200) < 4
    # the published arithmetic identity, kept because the target number agrees
    assert F(7, 10) * F(101, 20) + F(3, 10) == F(767, 200)
    length_hi_sq = F(767, 200)
    length_hi = math.sqrt(float(length_hi_sq))
    assert length_hi < 1.959
    return {
        "b_upper_at_17_20": str(b_hi),
        "artanh_upper_at_17_20": str(h_hi),
        "b_upper_float": float(b_hi),
        "artanh_upper_float": float(h_hi),
        "length_sq_bound": str(length_hi_sq),
        "length_bound_float": length_hi,
        "published_chain_step_valid": False,
        "repaired_chain_endpoint": str(case_b),
    }


# --------------------------------------------- arm 2: the rational cubic case

def arm_cubic():
    """Exact rational interval certificate for f = z^3 - p z - 1/4."""
    u = F(1011, 1600)
    p = u * u - F(1, 4) / u
    assert p == F(9364331, 2588160000)
    assert u ** 3 > F(1, 4)                       # p > 0
    assert u < 1 and 4 * u > 1                    # all roots inside the disc
    d_sq = 1 / u - u * u
    assert d_sq == F(3062635669, 2588160000)
    assert d_sq < 4                               # |a-b| < 2

    delta_sq = 4 * p ** 3 / 27
    delta_lo, delta_hi = sqrt_enclosure(delta_sq)
    assert delta_hi < F(1, 4)                     # v = 1/4 - delta > 0
    t_lo, t_hi = F(1, 4) + delta_lo, F(1, 4) + delta_hi
    v_lo, v_hi = F(1, 4) - delta_hi, F(1, 4) - delta_lo
    assert t_hi < 1                               # min(beta_2, 1) = beta_2 = T
    assert v_hi < 1                               # the arc sits in {|f| < 1}

    w_lo, _ = two_thirds_power_enclosure(t_lo / 2)
    _, w_hi = two_thirds_power_enclosure(t_hi / 2)

    log2_lo, log2_hi = log_enclosure(F(2), F(2))
    y_lo = 1 / (4 * 2048 * delta_hi)
    y_hi = 1 / (4 * 2048 * delta_lo)
    ly_lo, ly_hi = log_enclosure(y_lo, y_hi)
    log_lo = 11 * log2_lo + ly_lo                 # log((T+v)/(T-v)) = log(1/(4 delta))
    log_hi = 11 * log2_hi + ly_hi

    g_lo, g_hi = 2 * w_lo * log_lo, 2 * w_hi * log_hi
    assert g_lo > F(40014, 10000), float(g_lo)    # the corpus scalar criterion fails

    q_lo, q_hi = v_lo / t_hi, v_hi / t_lo
    assert q_hi < 1
    f_hi = d_sq + q_hi * (g_hi - d_sq)
    assert f_hi < F(39996, 10000), float(f_hi)    # the r02 coefficient fires

    # b(q) = (q - (1-q^2) artanh q)/q^2 with artanh q = log((1+q)/(1-q))/2
    # and (1+q)/(1-q) = 1/(4 delta), the same enclosed logarithm.
    b_hi = (q_hi - (1 - q_hi * q_hi) * log_lo / 2) / (q_lo * q_lo)
    b_lo = (q_lo - (1 - q_lo * q_lo) * log_hi / 2) / (q_hi * q_hi)
    assert 0 < b_lo <= b_hi < q_lo                # b(x) < x at the witness
    fb_hi = d_sq + b_hi * (g_hi - d_sq)
    assert fb_hi < F(39883, 10000), float(fb_hi)  # the r04 coefficient fires harder
    return {
        "p": str(p),
        "chord_sq": str(d_sq),
        "chord_sq_float": float(d_sq),
        "delta_lo": float(delta_lo),
        "delta_hi": float(delta_hi),
        "W_lo": float(w_lo),
        "W_hi": float(w_hi),
        "G_lo": float(g_lo),
        "G_hi": float(g_hi),
        "F_hi_coefficient_x": float(f_hi),
        "b_at_witness": float(b_hi),
        "F_hi_coefficient_b": float(fb_hi),
        "corpus_scalar_criterion_fires": bool(g_hi < 4),
    }


# ------------------------------------------- arm 3: the spectral coefficient

def b_r04(x):
    return (x - (1 - x * x) * math.atanh(x)) / (x * x)


def b_r02_odd(r):
    return ((1 + r * r) * math.atanh(r) - (1 - r * r) * math.atan(r)) / (4 * r)


def lower_bound(x):
    return 1 - math.log(1 + x) / math.atanh(x)


def bergman_matrix(r, size):
    """Matrix (14): T_{mn} in the orthonormal basis sqrt(j+1) z^j."""
    rows = []
    for m in range(size):
        row = [0.0] * size
        for n in range(size):
            if (m + n) % 2 == 0:
                row[n] = math.sqrt((m + 1) * (n + 1)) * (
                    r ** (m + n) / (m + n + 1) - r ** (m + n + 4) / (m + n + 3)
                )
        rows.append(row)
    return rows


def _sub_matvec(block, vec):
    out = []
    for row in block:
        s = 0.0
        for a, b in zip(row, vec):
            s += a * b
        out.append(s)
    return out


def _largest_tridiagonal(alpha, beta):
    """Largest eigenvalue of a symmetric tridiagonal matrix, by Sturm bisection."""
    lo = min(alpha) - 2 * (max(abs(b) for b in beta) if beta else 0.0) - 1.0
    hi = max(alpha) + 2 * (max(abs(b) for b in beta) if beta else 0.0) + 1.0
    n = len(alpha)

    def count_below(mu):
        d = alpha[0] - mu
        neg = 1 if d < 0 else 0
        for i in range(1, n):
            if d == 0.0:
                d = 1e-300
            d = alpha[i] - mu - beta[i - 1] * beta[i - 1] / d
            if d < 0:
                neg += 1
        return neg

    for _ in range(200):
        mid = (lo + hi) / 2
        if count_below(mid) >= n:
            hi = mid
        else:
            lo = mid
    return (lo + hi) / 2


def top_eigenvalue(block, deflate=None, steps=90):
    """Largest eigenvalue of a symmetric block, optionally on deflate^perp."""
    n = len(block)
    steps = min(steps, n)
    if deflate is not None:
        norm = math.sqrt(sum(v * v for v in deflate))
        deflate = [v / norm for v in deflate]

    def project(v):
        if deflate is None:
            return v
        c = sum(a * b for a, b in zip(v, deflate))
        return [a - c * b for a, b in zip(v, deflate)]

    rng = random.Random(1041)
    v = project([rng.uniform(-1.0, 1.0) for _ in range(n)])
    nv = math.sqrt(sum(a * a for a in v))
    v = [a / nv for a in v]
    alpha, beta, prev = [], [], None
    for _ in range(steps):
        w = project(_sub_matvec(block, v))
        a = sum(x * y for x, y in zip(w, v))
        alpha.append(a)
        w = [x - a * y for x, y in zip(w, v)]
        if prev is not None:
            w = [x - beta[-1] * y for x, y in zip(w, prev)]
        c = sum(x * y for x, y in zip(w, v))          # one reorthogonalisation
        w = [x - c * y for x, y in zip(w, v)]
        nw = math.sqrt(sum(x * x for x in w))
        if nw < 1e-13:
            break
        beta.append(nw)
        prev, v = v, [x / nw for x in w]
    return _largest_tridiagonal(alpha, beta)


def arm_spectrum():
    rows = []
    for x, size in ((0.0625, 200), (0.25, 200), (0.49, 240), (0.81, 320), (0.9801, 400)):
        r = math.sqrt(x)
        mat = bergman_matrix(r, size)
        odd = [m for m in range(size) if m % 2 == 1]
        even = [m for m in range(size) if m % 2 == 0]
        odd_block = [[mat[i][j] for j in odd] for i in odd]
        even_block = [[mat[i][j] for j in even] for i in even]
        # h(z) = 2r/(1 - r^2 z^2) has coordinates 2 r^{m+1}/sqrt(m+1) on even m
        h_even = [2 * r ** (m + 1) / math.sqrt(m + 1) for m in even]
        lam_odd = top_eigenvalue(odd_block)
        lam_even = top_eigenvalue(even_block, deflate=h_even)
        lam = max(lam_odd, lam_even)
        u04, u02 = b_r04(x), min(x, b_r02_odd(r))
        low = lower_bound(x)
        assert lam <= u04 * (1 + 1e-9), (x, lam, u04)
        assert lam <= u02 * (1 + 1e-9), (x, lam, u02)
        assert lam >= low - 1e-9, (x, lam, low)
        assert lam_odd >= lam_even                    # the extremal mode is odd
        rows.append({
            "x": x,
            "r": r,
            "lambda_numeric": lam,
            "lambda_odd": lam_odd,
            "lambda_even_deflated": lam_even,
            "b_r04": u04,
            "b_r02": u02,
            "b_r04_minus_b_r02": u04 - u02,
            "lower_bound_26": low,
            "truncation": size,
        })
    # trace identity for matrix (14), away from the truncation-sensitive end
    traces = []
    for r, size in ((0.25, 200), (0.5, 200), (0.7, 240), (0.9, 320)):
        mat = bergman_matrix(r, size)
        got = sum(mat[m][m] for m in range(size))
        want = 0.5 + (1 + r * r) * math.atanh(r) / (2 * r)
        assert abs(got - want) < 1e-8, (r, got, want)
        traces.append({"r": r, "trace": got, "closed_form": want})
    dominance = max(row["b_r04_minus_b_r02"] for row in rows)
    assert dominance < 0.0, dominance
    return {"rows": rows, "traces": traces, "max_b_r04_minus_b_r02": dominance}


# ---------------------------------- arm 4: random-polynomial falsification

def arm_random(trials=60):
    rng = random.Random(20260905)
    worst = 0.0
    count = 0
    for q in (0.2, 0.5, 0.8, 0.95):
        x = q * q
        lam = b_r04(x)
        lam_bulk = 4 * math.atanh(x)               # Lambda * pi
        for _ in range(trials):
            deg = rng.randint(1, 12)
            coeff = [complex(rng.gauss(0, 1), rng.gauss(0, 1)) for _ in range(deg + 1)]
            energy = math.pi * sum(abs(c) ** 2 / (j + 1) for j, c in enumerate(coeff))
            disp = sum(
                2 * c * q ** (j + 1) / (j + 1) for j, c in enumerate(coeff) if j % 2 == 0
            )
            steps = 2000
            h = 2 * q / steps
            total = 0.0
            for i in range(steps + 1):
                s = -q + i * h
                val = abs(sum(c * s ** j for j, c in enumerate(coeff)))
                w = 1.0 if i in (0, steps) else (4.0 if i % 2 else 2.0)
                total += w * val
            length = total * h / 3
            rhs = lam * lam_bulk * energy / math.pi + (1 - lam) * abs(disp) ** 2
            ratio = length * length / rhs
            assert ratio <= 1 + 1e-6, (q, deg, ratio)
            worst = max(worst, ratio)
            count += 1
    return {"instances": count, "worst_ratio": worst}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--part", default="all",
                        choices=["all", "rational", "cubic", "spectrum", "random"])
    args = parser.parse_args()
    out = {"status": "pass", "target": "erdos1041", "note":
           "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/ChordConditionedBergman.md"}
    if args.part in ("all", "rational"):
        out["rational_1720"] = arm_rational_1720()
    if args.part in ("all", "cubic"):
        out["cubic_witness"] = arm_cubic()
    if args.part in ("all", "spectrum"):
        out["spectrum"] = arm_spectrum()
    if args.part in ("all", "random"):
        out["random_falsification"] = arm_random()
    out["evidence_class"] = {
        "rational_1720": "exact_rational_certificate",
        "cubic_witness": "exact_rational_interval_certificate",
        "spectrum": "floating_point_truncated_matrix_falsification_only",
        "random_falsification": "floating_point_quadrature_falsification_only",
    }
    out["universal_authority"] = "ChordConditionedBergman.md"
    print(json.dumps(out))


if __name__ == "__main__":
    main()
