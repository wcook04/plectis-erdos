"""Exact certificate for the central ``mu=-10`` quintic inverse-ray pair.

At ``(mu, phi)=(-10, 0)`` the universal quintic is

    F(x) = x^3 (x^2 + 5 x + 10).

The limiting two-arm pair is the conjugate pair born with arguments
``+-2*pi/3``.  The proof below is algebraic plus the support--oscillation
identity from ``TraceMaxEntropyAngularBudget.md``.  Floating point is used
only to choose rational root boxes; every accepted sign and every final
inequality is checked with exact rational arithmetic.
"""

from __future__ import annotations

from fractions import Fraction as Qq
import math
import sys

import numpy as np
import sympy as sp


FAILURES: list[str] = []


def report(name: str, ok: bool, detail: str = "") -> None:
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


class Iv:
    """A small closed rational interval implementation."""

    def __init__(self, lo, hi=None):
        self.lo = Qq(lo)
        self.hi = Qq(lo if hi is None else hi)
        if self.lo > self.hi:
            raise ValueError("reversed interval")

    def __add__(self, other):
        other = iv(other)
        return Iv(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Iv(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-iv(other))

    def __rsub__(self, other):
        return iv(other) + (-self)

    def __mul__(self, other):
        other = iv(other)
        values = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        return Iv(min(values), max(values))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = iv(other)
        if other.lo <= 0 <= other.hi:
            raise ZeroDivisionError("interval contains zero")
        reciprocals = (1 / other.lo, 1 / other.hi)
        return self * Iv(min(reciprocals), max(reciprocals))

    def __rtruediv__(self, other):
        return iv(other) / self

    def __pow__(self, exponent: int):
        if exponent < 0:
            return Iv(1) / (self ** (-exponent))
        if exponent == 0:
            return Iv(1)
        if exponent % 2 == 0 and self.lo <= 0 <= self.hi:
            return Iv(0, max(abs(self.lo), abs(self.hi)) ** exponent)
        values = (self.lo**exponent, self.hi**exponent)
        return Iv(min(values), max(values))

    def sign(self) -> int:
        if self.lo > 0:
            return 1
        if self.hi < 0:
            return -1
        return 0


def iv(value) -> Iv:
    return value if isinstance(value, Iv) else Iv(value)


def poly_iv(expr, boxes: dict[sp.Symbol, Iv]) -> Iv:
    variables = list(boxes)
    polynomial = sp.Poly(expr, *variables, domain=sp.QQ)
    result = Iv(0)
    for powers, coefficient in polynomial.terms():
        term = Iv(Qq(int(coefficient.p), int(coefficient.q)))
        for variable, exponent in zip(variables, powers):
            term *= boxes[variable] ** exponent
        result += term
    return result


def rational_box(value: float, digits: int = 15, padding: int = 2) -> Iv:
    denominator = 10**digits
    return Iv(
        Qq(math.floor(value * denominator) - padding, denominator),
        Qq(math.ceil(value * denominator) + padding, denominator),
    )


def sqrt_iv(box: Iv, digits: int = 18) -> Iv:
    """Outward rational square-root enclosure, with exact square checks."""
    assert box.lo >= 0
    denominator = 10**digits
    lo_scaled = (box.lo.numerator * denominator**2) // box.lo.denominator
    hi_scaled = (
        box.hi.numerator * denominator**2 + box.hi.denominator - 1
    ) // box.hi.denominator
    lo = Qq(math.isqrt(lo_scaled), denominator)
    hi_numerator = math.isqrt(hi_scaled)
    if hi_numerator**2 < hi_scaled:
        hi_numerator += 1
    hi = Qq(hi_numerator, denominator)
    assert lo >= 0 and lo**2 <= box.lo and hi**2 >= box.hi
    return Iv(lo, hi)


a, b, t, k, p, u, w, x = sp.symbols("a b t k p u w x", real=True)

F = x**3 * (x**2 + 5 * x + 10)
Pab = (
    5 * a**4
    + 20 * a**3
    - 10 * a**2 * b**2
    + 30 * a**2
    - 20 * a * b**2
    + b**4
    - 10 * b**2
)
A = 5 * t**4 - 10 * t**2 + 1
B = 20 * t * (t**2 - 1)
C = 10 * (3 * t**2 - 1)
Qcurve = sp.expand(A * b**2 + B * b + C)
Qt = sp.diff(Qcurve, t)
Qb = sp.diff(Qcurve, b)
P_slope = sp.expand((p - t) * Qt + b * Qb)
W_stationary = sp.expand((k - t) * Qt + b * Qb)
Kpoly = 5 * k**4 - 10 * k**2 + 1

K = Iv(Qq(324919696232906, 10**15), Qq(324919696232907, 10**15))
ROOT_THIRD = Iv(Qq(577350269189625, 10**15), Qq(577350269189626, 10**15))


def exact_normal_form() -> None:
    z = a + sp.I * b
    imag_factor = sp.factor(sp.im(sp.expand(z**3 * (z**2 + 5 * z + 10))) / b)
    level_t = sp.factor(Pab.subs(a, b * t) / b**2)
    derivative = sp.factor(sp.diff(F, x))
    critical_gap = sp.factor(6 * (-2 + sp.I * sp.sqrt(2)) ** 2)
    report(
        "1 mu=-10 cubic degeneration and chamber centre",
        derivative == 5 * x**2 * (x**2 + 4 * x + 6)
        and sp.expand(critical_gap - (12 - 24 * sp.sqrt(2) * sp.I)) == 0,
    )
    report(
        "2 conjugate inverse-ray level curve is quadratic in the radius",
        sp.expand(imag_factor - Pab) == 0 and sp.expand(level_t - Qcurve) == 0,
    )


def algebraic_endpoints_and_branch() -> None:
    k_ok = (
        poly_iv(Kpoly, {k: Iv(K.lo)}).sign()
        * poly_iv(Kpoly, {k: Iv(K.hi)}).sign()
        == -1
        and 0 < K.lo < K.hi < Qq(1, 3)
    )
    r_ok = ROOT_THIRD.lo**2 < Qq(1, 3) < ROOT_THIRD.hi**2
    discriminant = sp.factor(B**2 - 4 * A * C)
    discriminant_factor = 5 * t**6 - 15 * t**4 + 3 * t**2 - 1
    no_discriminant_zero = sp.count_roots(
        discriminant_factor, sp.Rational(-3, 5), sp.Rational(1, 3)
    ) == 0

    s = sp.symbols("s", real=True)
    terminal = sp.expand(
        s**2
        * Qcurve.subs({t: k - s, b: w / s})
    )
    terminal_reduced = sp.rem(
        sp.Poly(terminal, k), sp.Poly(Kpoly, k)
    ).as_expr()
    terminal_linear = sp.factor(sp.diff(terminal_reduced, s).subs(s, 0))
    expected_linear = -20 * k * w * (k - 1) * (k + 1) * (w - 1)
    report(
        "3 selected branch runs from t=-1/sqrt(3), b=0 to t=k, b(k-t)->1",
        k_ok
        and r_ok
        and sp.expand(discriminant + 40 * discriminant_factor) == 0
        and no_discriminant_zero
        and sp.expand(terminal_linear - expected_linear) == 0,
    )


def selected_b_approx(t_value: float) -> float:
    av = float(A.subs(t, t_value))
    bv = float(B.subs(t, t_value))
    cv = float(C.subs(t, t_value))
    roots = np.roots([av, bv, cv])
    positives = sorted(
        root.real for root in roots if abs(root.imag) < 1e-8 and root.real > 0
    )
    assert positives
    if t_value < -float(K.lo):
        return positives[0]
    return positives[-1]


def selected_b_box(t_value: Qq) -> Iv:
    approx = selected_b_approx(float(t_value))
    for digits in range(12, 18):
        box = rational_box(approx, digits, padding=4)
        lo_value = poly_iv(Qcurve, {t: Iv(t_value), b: Iv(box.lo)})
        hi_value = poly_iv(Qcurve, {t: Iv(t_value), b: Iv(box.hi)})
        qb_box = poly_iv(Qb, {t: Iv(t_value), b: box})
        if lo_value.hi < 0 < hi_value.lo and qb_box.lo > 0:
            return box
    raise AssertionError(f"failed to isolate selected b at t={t_value}")


def half_angle_box(p_box: Iv) -> Iv:
    numerator = K - p_box
    norm_p = sqrt_iv(1 + p_box**2)
    norm_k = sqrt_iv(1 + K**2)
    denominator = norm_p * norm_k + 1 + p_box * K
    return numerator / denominator


def central_partition_budget() -> Qq:
    # The tiny initial wedge is bounded on one rational rectangle containing
    # the algebraic starting point t=-1/sqrt(3), b=0.
    start = Qq(-577, 1000)
    cell_count = 256
    nodes = [start + Qq(i, cell_count) * (-start) for i in range(cell_count + 1)]
    b_nodes = [selected_b_box(node) for node in nodes]
    w_nodes = [b_box * (K - node) for node, b_box in zip(nodes, b_nodes)]

    initial_t = Iv(Qq(-289, 500), start)
    initial_b = Iv(0, b_nodes[0].hi)
    initial_qt = poly_iv(Qt, {t: initial_t, b: initial_b})
    initial_qb = poly_iv(Qb, {t: initial_t, b: initial_b})
    initial_wprime_numerator = (
        -(K - initial_t) * initial_qt - initial_b * initial_qb
    )
    initial_p = initial_t - initial_b * initial_qb / initial_qt
    initial_half_angle = half_angle_box(initial_p)
    ok = (
        initial_qt.hi < 0
        and initial_qb.lo > 0
        and initial_wprime_numerator.lo > 0
        and initial_p.hi < K.lo
        and initial_half_angle.hi < Qq(1, 2)
    )
    budget = Qq(1, 2) * w_nodes[0].hi

    for index in range(cell_count):
        t_box = Iv(nodes[index], nodes[index + 1])
        b_box = Iv(b_nodes[index].lo, b_nodes[index + 1].hi)
        qt_box = poly_iv(Qt, {t: t_box, b: b_box})
        qb_box = poly_iv(Qb, {t: t_box, b: b_box})
        wprime_numerator = -(K - t_box) * qt_box - b_box * qb_box
        ok &= qt_box.hi < 0 and qb_box.lo > 0 and wprime_numerator.lo > 0

        p_box = t_box - b_box * qb_box / qt_box
        ok &= p_box.hi < K.lo
        angle = half_angle_box(p_box)
        delta_w = w_nodes[index + 1].hi - w_nodes[index].lo
        ok &= delta_w > 0 and angle.lo >= 0
        budget += angle.hi * delta_w

    report(
        "4 exact 256-cell rising-branch tangent partition",
        ok,
        f"main weighted transverse budget < {float(budget):.12f}",
    )
    return budget


def tail_budget() -> Qq:
    # The selected root is unique and Q_b>0 for 0<=t<k.  Q_t cannot vanish
    # in the slightly larger rational interval 0<t<1/3.
    qt_resultant = sp.factor(sp.resultant(Qcurve, Qt, b) / 400)
    expected_qt = 75 * t**10 - 150 * t**8 + 50 * t**6 - 120 * t**4 - 21 * t**2 - 10
    qt_ok = (
        sp.expand(qt_resultant - expected_qt) == 0
        and sp.count_roots(expected_qt, 0, sp.Rational(1, 3)) == 0
    )

    slope_polys = []
    for slope in (sp.Rational(3, 10), sp.Rational(1, 3)):
        resultant = sp.Poly(sp.resultant(Qcurve, P_slope.subs(p, slope), b), t).sqf_part()
        slope_polys.append(resultant)
    no_slope_crossing = all(
        sp.count_roots(poly, 0, sp.Rational(1, 3)) == 0 for poly in slope_polys
    )
    # At t=0 the selected root is b=sqrt(10), hence p=1/sqrt(10).
    # These exact square comparisons orient both resultant exclusions.
    sample_slope_ok = (
        sp.Rational(3, 10) ** 2
        < sp.Rational(1, 10)
        < sp.Rational(1, 3) ** 2
    )

    # For w=1 the cleared level equation has an exact factorization after
    # t=k*u.  It is negative on 0<=u<1, so the selected root has w>1.
    cleared_w = sp.cancel((k - t) ** 2 * Qcurve.subs(b, w / (k - t)))
    cleared_u = sp.expand(cleared_w.subs(t, k * u))
    reduced_u = sp.rem(sp.Poly(cleared_u, k), sp.Poly(Kpoly, k)).as_expr()
    w_one = sp.factor(reduced_u.subs(w, 1))
    expected_w_one = (10 * k**2 - 1) * (u - 1) ** 3 * (3 * u + 1)

    # At w=26/25 the remaining cubic has four negative Bernstein
    # coefficients, so Q>0 and the selected root has w<26/25.
    w_hi = sp.Rational(26, 25)
    high_quotient = sp.factor(reduced_u.subs(w, w_hi) / (u - 1))
    high_poly = sp.Poly(high_quotient, u)
    power = [high_poly.nth(i) for i in range(4)]
    bernstein = [
        sp.factor(
            sum(
                power[i] * sp.binomial(j, i) / sp.binomial(3, i)
                for i in range(j + 1)
            )
        )
        for j in range(4)
    ]
    bernstein_ok = all(poly_iv(coef, {k: K}).hi < 0 for coef in bernstein)

    # Eliminate k from w'=0.  Apart from the terminal A(t)=0 factor, the
    # remaining degree-28 polynomial has exactly one root in (0,1/3).
    stationary_tk = sp.factor(sp.resultant(Qcurve, W_stationary, b) / 400)
    stationary_elim = sp.factor(sp.resultant(stationary_tk, Kpoly, k))
    stationary_core = sp.Poly(stationary_elim, t).sqf_part()
    # Remove the terminal-direction factor before counting the finite core.
    stationary_core = sp.div(stationary_core, sp.Poly(A, t))[0].sqf_part()
    stationary_ok = sp.count_roots(stationary_core, 0, sp.Rational(1, 3)) == 1

    p_tail = Iv(Qq(3, 10), Qq(1, 3))
    diff = Iv(0, max(K.hi - p_tail.lo, p_tail.hi - K.lo))
    denominator = (
        sqrt_iv(1 + p_tail**2) * sqrt_iv(1 + K**2)
        + 1
        + p_tail * K
    )
    tail_angle = diff / denominator
    tail_tv = Qq(2, 25)  # one turn, within 1 < w < 26/25
    budget = Qq(1, 80) * tail_tv
    ok = (
        qt_ok
        and no_slope_crossing
        and sample_slope_ok
        and sp.expand(w_one - expected_w_one) == 0
        and poly_iv(10 * k**2 - 1, {k: K}).lo > 0
        and bernstein_ok
        and stationary_ok
        and tail_angle.hi < Qq(1, 80)
        and budget == Qq(1, 1000)
    )
    report(
        "5 exact tail: 3/10<p<1/3, one transverse turn, TV<2/25",
        ok,
        f"tan(|theta|/2)<1/80, tail budget={budget}",
    )
    return budget


def final_fanin(main_budget: Qq, tail: Qq) -> None:
    total = main_budget + tail
    # For the upper arm, e <= c*(total-k), c=1/sqrt(1+k^2)>0.
    # Conjugation doubles the same bound, so the sign is decided by total-k.
    # A deliberately rounded rational ceiling makes the public margin compact.
    ceiling = Qq(309, 1000)
    margin = K.lo - ceiling
    direction_cosine = 1 / sqrt_iv(1 + K**2)
    rational_upper = -2 * Qq(951, 1000) * Qq(15, 1000)
    report(
        "6 exact negative conjugate-pair support--oscillation fan-in",
        total < ceiling < K.lo
        and margin > Qq(15, 1000)
        and direction_cosine.lo > Qq(951, 1000)
        and rational_upper == Qq(-2853, 100000),
        f"E_pair<-2853/100000, weighted budget<{ceiling}, "
        f"k-budget>{float(margin):.12f}",
    )


def main() -> int:
    exact_normal_form()
    algebraic_endpoints_and_branch()
    main_budget = central_partition_budget()
    tail = tail_budget()
    final_fanin(main_budget, tail)
    print()
    if FAILURES:
        print("FAIL:", FAILURES)
        return 1
    print("PASS: exact mu=-10, phi=0 curved-pair excess certificate")
    return 0


if __name__ == "__main__":
    sys.exit(main())
