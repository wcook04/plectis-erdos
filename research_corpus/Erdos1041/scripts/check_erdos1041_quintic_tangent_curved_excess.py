"""Exact certificate for the tangent curved inverse-ray excess in Erdős 1041.

The proof is algebraic except for the elementary support--oscillation lemma
already proved in TraceMaxEntropyAngularBudget.md.  This checker replays the
algebra with exact SymPy resultants/Sturm isolation and rational interval
arithmetic; floating point is used only to choose a candidate isolating box,
never to decide a sign.
"""

from fractions import Fraction as Q
import math
import sys

import numpy as np
import sympy as sp


FAILURES = []


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


class Iv:
    """Closed rational interval, sufficient for the small certificate boxes."""

    def __init__(self, lo, hi=None):
        self.lo = Q(lo)
        self.hi = Q(lo if hi is None else hi)
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
        values = (self.lo * other.lo, self.lo * other.hi,
                  self.hi * other.lo, self.hi * other.hi)
        return Iv(min(values), max(values))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = iv(other)
        if other.lo <= 0 <= other.hi:
            raise ZeroDivisionError("interval contains zero")
        return self * Iv(1 / other.hi, 1 / other.lo)

    def __rtruediv__(self, other):
        return iv(other) / self

    def __pow__(self, exponent):
        if exponent < 0:
            return Iv(1) / (self ** (-exponent))
        if exponent == 0:
            return Iv(1)
        if exponent % 2 == 0 and self.lo <= 0 <= self.hi:
            return Iv(0, max(abs(self.lo), abs(self.hi)) ** exponent)
        values = (self.lo ** exponent, self.hi ** exponent)
        return Iv(min(values), max(values))

    def sign(self):
        if self.lo > 0:
            return 1
        if self.hi < 0:
            return -1
        return 0

    def width(self):
        return self.hi - self.lo


def iv(value):
    return value if isinstance(value, Iv) else Iv(value)


def poly_iv(expr, boxes):
    """Natural exact interval evaluation of a rational polynomial."""
    variables = list(boxes)
    polynomial = sp.Poly(expr, *variables, domain=sp.QQ)
    result = Iv(0)
    for powers, coefficient in polynomial.terms():
        term = Iv(Q(int(coefficient.p), int(coefficient.q)))
        for variable, exponent in zip(variables, powers):
            term *= boxes[variable] ** exponent
        result += term
    return result


def rational_box(value, digits=12, padding=1):
    denominator = 10 ** digits
    return Iv(Q(math.floor(value * denominator) - padding, denominator),
              Q(math.ceil(value * denominator) + padding, denominator))


def sqrt_box(radicand, value, digits=12):
    box = rational_box(value, digits)
    radicand = Q(radicand)
    assert box.lo >= 0 and box.lo ** 2 < radicand < box.hi ** 2
    return box


A, t, h, k, x, mu = sp.symbols("A t h k x mu", real=True)
q = t ** 2
P = sp.expand(
    A ** 3 * (5 * q ** 2 - 10 * q + 1)
    + 5 * h * A ** 2 * (q ** 2 - 6 * q + 1)
    + 20 * (1 - h) * A * (1 - 3 * q)
    + 60 * h * (1 - q)
)
P_A = sp.diff(P, A)
P_t = sp.diff(P, t)


H = Iv(Q(732050807568877, 10 ** 15), Q(732050807568878, 10 ** 15))
K_R = Iv(Q(324919696232906, 10 ** 15), Q(324919696232907, 10 ** 15))
K_L = Iv(Q(1376381920471173, 10 ** 15), Q(1376381920471174, 10 ** 15))
C_R = Iv(Q(951056516295153, 10 ** 15), Q(951056516295154, 10 ** 15))
C_L = Iv(Q(587785252292473, 10 ** 15), Q(587785252292474, 10 ** 15))


def tangent_equation(slope):
    # Along P(A,t)=0, dt/dA=-P_A/P_t and d(At)/dA=t-A P_A/P_t.
    return sp.expand((t - slope) * P_t - A * P_A)


def eliminated_a_polynomial(slope, eliminate_slope=False):
    resultant_t = sp.resultant(P, tangent_equation(slope), t)
    resultant_h = sp.resultant(resultant_t, h ** 2 + 2 * h - 2, h)
    if eliminate_slope:
        resultant_h = sp.resultant(resultant_h, 5 * k ** 4 - 10 * k ** 2 + 1, k)
    return sp.Poly(resultant_h, A, domain=sp.QQ).sqf_part().as_expr()


def real_a_boxes(polynomial, side, eps_power=16):
    boxes = []
    intervals = sp.intervals(polynomial, eps=sp.Rational(1, 10 ** eps_power))
    for (lo, hi), multiplicity in intervals:
        assert multiplicity == 1
        loq = Q(int(lo.p), int(lo.q))
        hiq = Q(int(hi.p), int(hi.q))
        if loq == hiq == 0:
            continue
        if side == "right" and hiq > 0:
            boxes.append(Iv(max(loq, Q(0)), hiq))
        if side == "left" and loq < 0:
            boxes.append(Iv(loq, min(hiq, Q(0))))
    return boxes


def selected_t_box(a_box, side, min_digits=9):
    """Rationally trap the unique selected positive root, uniformly in A."""
    amid = float((a_box.lo + a_box.hi) / 2)
    hmid = float((H.lo + H.hi) / 2)
    coefficients = [
        5 * amid ** 3 + 5 * hmid * amid ** 2,
        -10 * amid ** 3 - 30 * hmid * amid ** 2
        - 60 * (1 - hmid) * amid - 60 * hmid,
        amid ** 3 + 5 * hmid * amid ** 2
        + 20 * (1 - hmid) * amid + 60 * hmid,
    ]
    q_roots = [z.real for z in np.roots(coefficients)
               if abs(z.imag) < 1e-7 and z.real > 0]
    band = (Q(1, 10), Q(1)) if side == "right" else (Q(9, 10), Q(2))
    q_roots = [z for z in q_roots if float(band[0]) < z < float(band[1])]
    assert len(q_roots) == 1
    t_approx = math.sqrt(q_roots[0])
    for digits in range(min_digits, 17):
        box = rational_box(t_approx, digits, padding=2)
        lo_value = poly_iv(P, {A: a_box, t: Iv(box.lo), h: H})
        hi_value = poly_iv(P, {A: a_box, t: Iv(box.hi), h: H})
        if lo_value.sign() * hi_value.sign() == -1:
            return box
    raise AssertionError(
        f"could not isolate selected t root: side={side}, "
        f"A=[{float(a_box.lo)}, {float(a_box.hi)}], t~{t_approx}")


def exact_algebra():
    G = lambda z: z ** 5 + 40 * z ** 2 - 60 * z
    level_factor = sp.factor(
        sp.re(G((sp.sqrt(3) - 1) + A * (1 + sp.I * t)))
        - G(sp.sqrt(3) - 1), extension=sp.sqrt(3))
    expected = A ** 2 * P.subs(h, sp.sqrt(3) - 1)
    report("1 exact tangent level-set factorization",
           sp.expand(level_factor - expected) == 0)

    critical = 5 * x ** 3 + 20 * x ** 2 + 30 * x + 20 + 2 * mu
    gap = sp.Rational(1, 2) * x ** 3 * (3 * x ** 2 + 10 * x + 10)
    quadratic_gap = x * (2 * mu + 20 - 3 * mu * x) / 5
    report("2 critical gap drops from quintic to quadratic modulo the cubic",
           sp.rem(gap - quadratic_gap, critical, x) == 0)

    y = sp.symbols("y")
    depressed = y ** 3 + sp.Rational(2, 3) * y + sp.Rational(20, 27) + sp.Rational(2, 5) * mu
    report("3 depressed critical cubic and bilinear gap identity",
           sp.expand(critical.subs(x, y - sp.Rational(4, 3)) / 5 - depressed) == 0
           and sp.rem(
               gap.subs(x, y - sp.Rational(4, 3))
               + (3 * y - 4) * (3 * mu * y - 6 * mu - 20) / 15,
               depressed, y) == 0)


def algebraic_constant_boxes():
    hpoly = lambda z: z ** 2 + 2 * z - 2
    kpoly = lambda z: 5 * z ** 4 - 10 * z ** 2 + 1
    h_ok = hpoly(H.lo) < 0 < hpoly(H.hi) and 0 < H.lo < H.hi < 1
    kr_ok = kpoly(K_R.lo) > 0 > kpoly(K_R.hi) and 0 < K_R.lo < K_R.hi < 1
    kl_ok = kpoly(K_L.lo) < 0 < kpoly(K_L.hi) and 1 < K_L.lo < K_L.hi

    def cosine_box_ok(k_box, c_box):
        lo_test = c_box.lo ** 2 * (1 + k_box.hi ** 2) - 1
        hi_test = c_box.hi ** 2 * (1 + k_box.lo ** 2) - 1
        return lo_test < 0 < hi_test and c_box.lo > 0

    report("4 rational isolation of h, terminal slopes, and direction cosines",
           h_ok and kr_ok and kl_ok
           and cosine_box_ok(K_R, C_R) and cosine_box_ok(K_L, C_L))


def global_branch_uniqueness():
    qsym, B = sp.symbols("q B", real=True)
    Pq = P.subs(t ** 2, qsym)
    right_derivative = sp.factor(sp.diff(Pq, qsym) / 10)
    expected = (-(1 - qsym) * A ** 3 - (3 - qsym) * h * A ** 2
                - 6 * (1 - h) * A - 6 * h)
    right_ok = sp.expand(right_derivative - expected) == 0

    left = sp.expand(Pq.subs(A, -B))
    left_lo = sp.Poly(left.subs({qsym: sp.Rational(9, 10),
                                 h: sp.sqrt(3) - 1}),
                      B, extension=sp.sqrt(3))
    left_hi = sp.Poly(left.subs({qsym: 2, h: sp.sqrt(3) - 1}),
                      B, extension=sp.sqrt(3))
    left_ok = (sp.count_roots(left_lo, 0, sp.oo) == 0
               and sp.count_roots(left_hi, 0, sp.oo) == 0
               and sp.sign(left_lo.eval(0)) == 1
               and sp.sign(left_hi.eval(0)) == -1)
    # Right: P(A,1/10)>0 coefficientwise and P(A,1)<0; P_q<0.
    right_lo = sp.Poly(Pq.subs(qsym, sp.Rational(1, 10)), A)
    right_hi = sp.factor(Pq.subs(qsym, 1))
    right_coeffs = right_lo.all_coeffs()
    right_ok &= (all(poly_iv(c, {h: H}).lo > 0 for c in right_coeffs)
                 and sp.factor(right_hi) == -4 * A * (A ** 2 + 5 * A * h - 10 * h + 10))
    report("5 unique simple selected graph on A>0 and A<0",
           right_ok and left_ok)


def no_selected_crossing(slope, side):
    polynomial = eliminated_a_polynomial(slope)
    candidates = real_a_boxes(polynomial, side)
    equation = tangent_equation(slope)
    signs = []
    for a_box in candidates:
        t_box = selected_t_box(a_box, side)
        value = poly_iv(equation, {A: a_box, t: t_box, h: H})
        signs.append(value.sign())
    return candidates, signs, all(sign != 0 for sign in signs)


def slope_bounds():
    c0, _, ok0 = no_selected_crossing(sp.Rational(0), "right")
    c1, _, ok1 = no_selected_crossing(sp.Rational(1), "right")
    clo, _, oklo = no_selected_crossing(sp.Rational(7, 8), "left")
    chi, _, okhi = no_selected_crossing(sp.Rational(7, 5), "left")
    counts_ok = (len(c0), len(c1), len(clo), len(chi)) == (2, 5, 2, 2)

    # One exact rational test point fixes the side of every excluded level.
    def slope_box(a_value, side):
        a_box = Iv(Q(a_value))
        t_box = selected_t_box(a_box, side)
        pa = poly_iv(P_A, {A: a_box, t: t_box, h: H})
        pt = poly_iv(P_t, {A: a_box, t: t_box, h: H})
        return t_box - a_box * pa / pt

    right_test = slope_box(1, "right")
    left_test = slope_box(-1, "left")
    report("6 exact resultant/Sturm tangent-slope enclosure",
           counts_ok and ok0 and ok1 and oklo and okhi
           and 0 < right_test.lo < right_test.hi < 1
           and Q(7, 8) < left_test.lo < left_test.hi < Q(7, 5),
           "right 0<p<1; left 7/8<p<7/5")


def stationary_boxes():
    polynomial = eliminated_a_polynomial(k, eliminate_slope=True)
    # A 10^-11 isolator is deliberately wider than the algebraic-constant
    # boxes, so its rational endpoints carry a comfortable exact sign.
    right_candidates = real_a_boxes(polynomial, "right", eps_power=11)
    left_candidates = real_a_boxes(polynomial, "left", eps_power=11)

    def classify(candidates, side, k_box, target_window, crossing_window):
        equation = tangent_equation(k)
        target = None
        excluded = 0
        for a_box in candidates:
            if target_window[0] < float(a_box.lo) and float(a_box.hi) < target_window[1]:
                target = a_box
                continue
            t_box = selected_t_box(a_box, side)
            value = poly_iv(equation, {A: a_box, t: t_box, h: H, k: k_box})
            if value.sign() != 0:
                excluded += 1
        assert target is not None

        # A slightly wider rational window around the isolated resultant root
        # gives comfortable opposite exact signs.  Since it contains no other
        # resultant root, the crossing itself lies in the tight target box.
        endpoint_signs = []
        for endpoint in crossing_window:
            endpoint_box = Iv(endpoint)
            t_box = selected_t_box(endpoint_box, side, min_digits=12)
            value = poly_iv(equation,
                            {A: endpoint_box, t: t_box, h: H, k: k_box})
            endpoint_signs.append(value.sign())
        return target, excluded, endpoint_signs

    right, rex, rsigns = classify(
        right_candidates, "right", K_R, (1.69, 1.71),
        (Q(17005, 10000), Q(17006, 10000)))
    left, lex, lsigns = classify(
        left_candidates, "left", K_L, (-3.88, -3.86),
        (Q(-38709, 10000), Q(-38708, 10000)))
    ok = (len(right_candidates) == 10 and len(left_candidates) == 2
          and rex == 9 and lex == 1
          and rsigns[0] * rsigns[1] == -1
          and lsigns[0] * lsigns[1] == -1)
    report("7 exactly one finite transverse extremum on each selected arm", ok,
           f"candidates=({len(right_candidates)},{len(left_candidates)}), "
           f"excluded=({rex},{lex}), endpoint_signs=({rsigns},{lsigns})")
    return right, left


def oscillation_bounds(right_a, left_a):
    right_t = selected_t_box(right_a, "right", min_digits=9)
    left_t = selected_t_box(left_a, "left", min_digits=9)

    y_right = right_a * (right_t - K_R) * C_R
    y_left = -left_a * (left_t - K_L) * C_L

    def terminal_y(k_box, c_box, sign):
        r_box = k_box ** 2
        M = r_box ** 2 - 6 * r_box + 1
        Lprime = 10 * r_box - 10
        e = -5 * H * M / Lprime
        return sign * c_box * e / (2 * k_box)

    y_right_inf = terminal_y(K_R, C_R, 1)
    y_left_inf = terminal_y(K_L, C_L, -1)
    osc_right = y_right - y_right_inf
    osc_left = y_left_inf - y_left
    ok = (osc_right.hi < Q(277, 1000)
          and osc_left.hi < Q(63, 2000)
          and y_right.lo > y_right_inf.hi > 0
          and y_left.hi < y_left_inf.lo < 0)
    report("8 rational transverse-oscillation bounds",
           ok,
           f"Osc_R<{float(osc_right.hi):.9f}, Osc_L<{float(osc_left.hi):.9f}")


def angular_and_final_budget():
    sqrt2 = sqrt_box(2, math.sqrt(2))
    sqrt74 = sqrt_box(74, math.sqrt(74))
    sqrt113 = sqrt_box(113, math.sqrt(113))

    right_from_zero = K_R / (1 / C_R + 1)
    right_from_one = (1 - K_R) / (sqrt2 / C_R + 1 + K_R)
    left_from_low = (K_L - Q(7, 8)) / (
        sqrt113 / (8 * C_L) + 1 + Q(7, 8) * K_L)
    left_from_high = (Q(7, 5) - K_L) / (
        sqrt74 / (5 * C_L) + 1 + Q(7, 5) * K_L)
    angle_ok = (max(right_from_zero.hi, right_from_one.hi) < Q(2401, 10000)
                and max(left_from_low.hi, left_from_high.hi) < Q(57, 500))
    report("9 rational half-angle budgets", angle_ok,
           "tan(alpha_R/2)<2401/10000, tan(alpha_L/2)<57/500")

    h_lo, h_hi = Q(73205, 100000), Q(732051, 10 ** 6)
    sin18 = K_R * C_R
    sin54 = K_L * C_L
    sin36 = 2 * K_R * C_R ** 2
    trig_ok = (
        h_lo < H.lo < H.hi < h_hi
        and sin18.hi < Q(309018, 10 ** 6)
        and C_R.lo > Q(951056, 10 ** 6)
        and sin54.hi < Q(809018, 10 ** 6)
        and sin36.hi < Q(587786, 10 ** 6)
    )
    bound = (
        Q(2401, 10000) * (h_hi * Q(309018, 10 ** 6) + 2 * Q(277, 1000))
        - h_lo * Q(951056, 10 ** 6)
        + Q(57, 500) * (h_hi * Q(809018, 10 ** 6) + 2 * Q(63, 2000))
        + h_hi * Q(587786, 10 ** 6)
    )
    expected = Q(-19517458527181, 5000000000000000)
    report("10 exact negative support--oscillation fan-in",
           trig_ok and bound == expected and bound < 0,
           f"upper bound={float(bound):.12f}")


def main():
    exact_algebra()
    algebraic_constant_boxes()
    global_branch_uniqueness()
    slope_bounds()
    right, left = stationary_boxes()
    oscillation_bounds(right, left)
    angular_and_final_budget()
    print()
    if FAILURES:
        print("FAIL:", FAILURES)
        return 1
    print("PASS: exact tangent curved-excess certificate")
    return 0


if __name__ == "__main__":
    sys.exit(main())
