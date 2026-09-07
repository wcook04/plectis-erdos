#!/usr/bin/env python3
"""Exact rational certificate that the tangent pair has positive quadratic excess.

The selected arms and their slope bounds are replayed from the exact tangent
certificate.  All decisions in the new integration are made with Fraction
intervals.  Floating point is used only to propose enclosing boxes.
"""

from fractions import Fraction as Q
from concurrent.futures import ProcessPoolExecutor
import math
import multiprocessing as mp
import sys

import check_erdos1041_quintic_tangent_curved_excess as tangent


FAILURES = []
Iv = tangent.Iv
H = tangent.H
SUM_DEN = 10 ** 14


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


def root5_down(value, digits=10):
    """Rational lower enclosure of value^(1/5), value >= 0."""
    assert value >= 0
    if value == 0:
        return Q(0)
    den = 10 ** digits
    num = math.floor(float(value) ** 0.2 * den)
    while Q(num, den) ** 5 > value:
        num -= 1
    while Q(num + 1, den) ** 5 <= value:
        num += 1
    return Q(num, den)


def root5_up(value, digits=10):
    """Rational upper enclosure of value^(1/5), value >= 0."""
    assert value >= 0
    lo = root5_down(value, digits)
    if lo ** 5 == value:
        return lo
    return lo + Q(1, 10 ** digits)


def selected_q_float(a):
    """Floating proposal for the selected root; never used for a sign."""
    hh = (float(H.lo) + float(H.hi)) / 2
    aa = 5 * a * a * (a + hh)
    bb = (-10 * a ** 3 - 30 * hh * a * a
          - 60 * (1 - hh) * a - 60 * hh)
    cc = (a ** 3 + 5 * hh * a * a
          + 20 * (1 - hh) * a + 60 * hh)
    disc = bb * bb - 4 * aa * cc
    roots = [(-bb - math.sqrt(disc)) / (2 * aa),
             (-bb + math.sqrt(disc)) / (2 * aa)]
    band = (0.1, 1.0) if a > 0 else (0.9, 2.0)
    selected = [r for r in roots if band[0] < r < band[1]]
    assert len(selected) == 1
    return selected[0]


def P_iv(a, tt):
    q = tt ** 2
    return (a ** 3 * (5 * q ** 2 - 10 * q + 1)
            + 5 * H * a ** 2 * (q ** 2 - 6 * q + 1)
            + 20 * (1 - H) * a * (1 - 3 * q)
            + 60 * H * (1 - q))


def PA_iv(a, tt):
    q = tt ** 2
    return (3 * a ** 2 * (5 * q ** 2 - 10 * q + 1)
            + 10 * H * a * (q ** 2 - 6 * q + 1)
            + 20 * (1 - H) * (1 - 3 * q))


def Pt_iv(a, tt):
    q = tt ** 2
    return (20 * a ** 3 * tt * (q - 1)
            + 20 * H * a ** 2 * tt * (q - 3)
            - 120 * (1 - H) * a * tt - 120 * H * tt)


def P_centered_a(a, tt):
    """Exact cubic Taylor form in A, sharply centered on an A-cell."""
    m = Q(a.lo + a.hi, 2)
    d = a - m
    q = tt ** 2
    paa = (6 * Iv(m) * (5 * q ** 2 - 10 * q + 1)
           + 10 * H * (q ** 2 - 6 * q + 1))
    paaa = 6 * (5 * q ** 2 - 10 * q + 1)
    return (P_iv(Iv(m), tt) + PA_iv(Iv(m), tt) * d
            + paa * d ** 2 / 2 + paaa * d ** 3 / 6)


def selected_t_tube(a, side, digits=11):
    """Uniform exact selected-root tube over an A interval."""
    proposals = []
    for endpoint in (a.lo, (a.lo + a.hi) / 2, a.hi):
        proposals.append(math.sqrt(selected_q_float(float(endpoint))))
    den = 10 ** digits
    spread = max(proposals) - min(proposals)
    # A generous predictor hull makes the parametric Newton inclusion robust
    # against natural-interval dependency in the cubic A coefficients.
    pad = max(20, math.ceil(6 * spread * den))
    lo = Q(math.floor(min(proposals) * den) - pad, den)
    hi = Q(math.ceil(max(proposals) * den) + pad, den)
    tube = Iv(lo, hi)
    pt = Pt_iv(a, tube)
    if pt.sign() == 0:
        raise ArithmeticError("selected root did not isolate uniformly")
    # Parametric interval Newton: for each A in the cell, the unique zero
    # lies in this strict self-map.  This avoids dependency loss in endpoint
    # sign evaluation when the root moves across the A-cell.
    t0 = Q(lo + hi, 2)
    newton = Iv(t0) - P_centered_a(a, Iv(t0)) / pt
    if not (tube.lo < newton.lo <= newton.hi < tube.hi):
        raise ArithmeticError("selected root did not isolate uniformly")
    return newton


def energy_integrand(a, side):
    """Exact interval for |dV/d rho|^2-1 times d rho/dx."""
    sigma = 1 if side == "right" else -1
    tt = selected_t_tube(a, side)
    pa = PA_iv(a, tt)
    pt = Pt_iv(a, tt)
    p = tt - a * pa / pt

    q = tt ** 2
    # Stable critical-point factorization of Im(G(V)-G(h)).  Directly
    # expanding G loses the exact A^2 cancellation near the hub.
    b = (a ** 3 * (q ** 2 - 10 * q + 5)
         + 20 * H * a ** 2 * (1 - q)
         + 20 * (1 - H) * a * (3 - q) + 120 * H)
    s = a ** 2 * tt * b
    b_a = (3 * a ** 2 * (q ** 2 - 10 * q + 5)
           + 40 * H * a * (1 - q) + 20 * (1 - H) * (3 - q))
    b_t = (a ** 3 * (4 * tt ** 3 - 20 * tt)
           - 40 * H * a ** 2 * tt - 40 * (1 - H) * a * tt)
    s_a = 2 * a * tt * b + a ** 2 * tt * b_a
    s_t = a ** 2 * (b + tt * b_t)
    sx = sigma * (s_a - s_t * pa / pt)
    if s.lo <= 0 or sx.lo <= 0:
        raise ArithmeticError("ray height or orientation lost")
    rho = Iv(root5_down(s.lo), root5_up(s.hi))
    rho_x = sx / (5 * rho ** 4)
    if rho_x.lo <= 0:
        raise ArithmeticError("radial parameter is not increasing")
    integrand = (1 + p ** 2) / rho_x - rho_x
    return integrand, rho, p, tt


def integrate_block(side, lo, hi, count):
    """Lower Darboux sum with exact rational graph tubes."""
    step = (hi - lo) / count
    total = Q(0)
    worst_width = Q(0)
    for j in range(count):
        x = Iv(lo + j * step, lo + (j + 1) * step)
        a = x if side == "right" else -x
        try:
            value, _, _, _ = energy_integrand(a, side)
        except (ArithmeticError, ZeroDivisionError) as exc:
            # A handful of cells near a coefficient turn are too wide for the
            # parametric Newton self-map.  A fixed exact 16-way refinement is
            # enough; unlike unbounded recursion this is a replayable cost.
            substep = step / 16
            for k in range(16):
                subx = Iv(x.lo + k * substep, x.lo + (k + 1) * substep)
                suba = subx if side == "right" else -subx
                try:
                    subvalue, _, _, _ = energy_integrand(suba, side)
                except (ArithmeticError, ZeroDivisionError) as subexc:
                    raise ArithmeticError(
                        f"refined cell failure {side} [{subx.lo},{subx.hi}]: "
                        f"{subexc}") from subexc
                term = subvalue.lo * substep
                total += Q(term.numerator * SUM_DEN // term.denominator, SUM_DEN)
                worst_width = max(worst_width, subvalue.width())
            continue
        # Directed fixed-denominator rounding is part of the certificate: it
        # preserves the lower bound while preventing irrelevant denominator
        # growth across thousands of exact cells.
        term = value.lo * step
        total += Q(term.numerator * SUM_DEN // term.denominator, SUM_DEN)
        worst_width = max(worst_width, value.width())
    return total, worst_width


def block_task(task):
    side, lo, hi, count = task
    value, width = integrate_block(side, lo, hi, count)
    return side, value, width


def hub_debt(side, epsilon):
    """The omitted interval has integrand >= -rho_x, hence debt <= rho(eps)."""
    a = Iv(epsilon) if side == "right" else Iv(-epsilon)
    _, rho, _, _ = energy_integrand(a, side)
    return rho.hi


def tail_debt(M):
    """Universal exact lower debt on one arm beyond x=M.

    Put R=x-1.  For |V|>=R,
      |G(V)-G(h)-V^5|/|V|^5 <= 40/R^3+60/R^4+23/R^5,
      |G'(V)-5V^4|/(5|V|^4) <= 16/R^3+12/R^4.
    Thus |dV/d rho| >= 1-e and rho_x <= (7/4)/(1-e), using the
    already replayed global slope bounds.  Integration gives this debt.
    """
    R = M - 1
    e = Q(56, R ** 3) + Q(72, R ** 4) + Q(23, R ** 5)
    integral_e = Q(28, R ** 2) + Q(24, R ** 3) + Q(23, 4 * R ** 4)
    assert e < 1
    return Q(7, 2) * integral_e / (1 - e)


def replay_source_arm_certificate():
    tangent.FAILURES.clear()
    tangent.exact_algebra()
    tangent.algebraic_constant_boxes()
    tangent.global_branch_uniqueness()
    tangent.slope_bounds()
    ok = not tangent.FAILURES
    report("1 source exact arm chart, uniqueness, and global slope bounds", ok)


def exact_quadratic_obstruction():
    eps = Q(1, 100)
    M = 20
    # Concentrate cells where the hub singularity and sign transition live.
    blocks = [
        (Q(1, 100), Q(1, 10), 500),
        (Q(1, 10), Q(1), 1000),
        (Q(1), Q(10), 1800),
        (Q(10), Q(M), 1000),
    ]
    lower = {}
    widths = {}
    debts = {}
    subtotals = {"right": Q(0), "left": Q(0)}
    max_widths = {"right": Q(0), "left": Q(0)}
    tasks = [(side, lo, hi, count)
             for side in ("right", "left") for lo, hi, count in blocks]
    # The cells are completely independent exact computations.  Explicit
    # fork keeps the replay fast without changing any arithmetic decision.
    with ProcessPoolExecutor(max_workers=4, mp_context=mp.get_context("fork")) as pool:
        for side, value, width in pool.map(block_task, tasks):
            subtotals[side] += value
            max_widths[side] = max(max_widths[side], width)
    for side in ("right", "left"):
        subtotal = subtotals[side]
        max_width = max_widths[side]
        debts[side] = hub_debt(side, eps)
        lower[side] = subtotal - debts[side]
        widths[side] = max_width
        report(f"2 {side} exact compact-arm lower sum", True,
               f"> {float(lower[side]):.12f}; hub_debt<{float(debts[side]):.9f}")

    tail = tail_debt(M)
    # Qpair has the factor 1/2, and the same tail debt applies to both arms.
    q_normal_lower = (lower["right"] + lower["left"]) / 2 - tail
    report("3 analytic infinite-tail lower bound", tail < Q(29, 100),
           f"pair tail debt<{float(tail):.12f}")
    report("4 normal-form quadratic pair excess is positive",
           q_normal_lower > Q(1, 10),
           f"Q_G>{float(q_normal_lower):.12f} > 1/10")

    # Original tangent representative is the positive similarity
    # lambda=40^(-1/3).  Since 40*(29/100)^3<1, lambda>29/100.
    scale_gate = 40 * Q(29, 100) ** 3 < 1
    original_lower = Q(29, 100) * q_normal_lower
    report("5 original-gauge exact positive obstruction",
           scale_gate and original_lower > Q(29, 1000),
           f"Q_pair>{float(original_lower):.12f} > 29/1000")
    return q_normal_lower, original_lower, tail, widths


def main():
    replay_source_arm_certificate()
    q_normal, q_original, tail, widths = exact_quadratic_obstruction()
    print()
    print("exact lower bounds:")
    print("  normal-form Qpair >", q_normal)
    print("  original Qpair >", q_original)
    print("  pair tail debt <", tail)
    print("  max interval widths:", {k: f"{float(v):.9g}" for k, v in widths.items()})
    if FAILURES:
        print("FAIL:", FAILURES)
        return 1
    print("PASS: exact tangent quadratic-bridge obstruction")
    return 0


if __name__ == "__main__":
    sys.exit(main())
