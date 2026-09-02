"""Exact certificate for the two endpoints of the ``mu=-10`` phase arc.

The chamber endpoint has ``|tan(phi)|=1/(2*sqrt(2))``.  At ``mu=-10``
the two limiting arms are the upper branches for the two signed parameters
``q=tan(phi)`` and ``-q``.  Each arm is placed on a quadratic algebraic
curve.  Rational interval arithmetic bounds its support--oscillation budget;
floating point is used only to choose rational root boxes.
"""

from __future__ import annotations

from fractions import Fraction as Qq
import importlib.util
import math
from pathlib import Path
import sys

import numpy as np
import sympy as sp


CENTRAL = Path(__file__).with_name(
    "check_erdos1041_quintic_minus_ten_central_excess.py"
)
SPEC = importlib.util.spec_from_file_location("minus_ten_central", CENTRAL)
M = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(M)

Iv = M.Iv
poly_iv = M.poly_iv
sqrt_iv = M.sqrt_iv

FAILURES: list[str] = []


def report(name: str, ok: bool, detail: str = "") -> None:
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


def abs_iv(box: Iv) -> Iv:
    if box.lo <= 0 <= box.hi:
        return Iv(0, max(-box.lo, box.hi))
    return Iv(min(abs(box.lo), abs(box.hi)), max(abs(box.lo), abs(box.hi)))


q, k, t, b, w = sp.symbols("q k t b w", real=True)

A = q * (t**5 - 10 * t**3 + 5 * t) + 5 * t**4 - 10 * t**2 + 1
B = 5 * q * t**4 - 30 * q * t**2 + 5 * q + 20 * t**3 - 20 * t
C = 10 * q * t**3 - 30 * q * t + 30 * t**2 - 10
Qcurve = sp.expand(A * b**2 + B * b + C)

Ak = sp.expand(A.subs(t, k))
D = sp.cancel((A - Ak) / (t - k))
Scurve = sp.expand(-D * w**2 + B * w + C * (k - t))
St = sp.diff(Scurve, t)
Sw = sp.diff(Scurve, w)

A0k = 5 * k**4 - 10 * k**2 + 1
A1k = k**5 - 10 * k**3 + 5 * k
KPOLY = sp.expand(8 * A0k**2 - A1k**2)
QPOLY = 8 * q**2 - 1


Q0 = Iv(Qq(3535533905932737, 10**16), Qq(3535533905932738, 10**16))


ARM_SPECS = (
    {
        "name": "negative-q arm",
        "q": Iv(-Q0.hi, -Q0.lo),
        "k": Iv(Qq(251289438338469, 10**15), Qq(251289438338470, 10**15)),
        "start": Iv(Qq(-740, 1000), Qq(-7395, 10000)),
        "t_lo": Qq(-741, 1000),
        "t_hi": Qq(252, 1000),
        "cells": 640,
        "budget_ceiling": Qq(7, 20),
    },
    {
        "name": "positive-q arm",
        "q": Q0,
        "k": Iv(Qq(401880733924049, 10**15), Qq(401880733924050, 10**15)),
        "start": Iv(Qq(-4351, 10000), Qq(-4350, 10000)),
        "t_lo": Qq(-436, 1000),
        "t_hi": Qq(403, 1000),
        "cells": 640,
        "budget_ceiling": Qq(11, 40),
    },
)


def q_from_k(k_value: float) -> float:
    a0 = 5 * k_value**4 - 10 * k_value**2 + 1
    a1 = k_value**5 - 10 * k_value**3 + 5 * k_value
    return -a0 / a1


def exact_endpoint_algebra() -> None:
    z = b * (t + sp.I)
    F = sp.expand(z**3 * (z**2 + 5 * z + 10))
    level = sp.factor((sp.im(F) + q * sp.re(F)) / b**3)
    relation = sp.factor(Scurve.subs({t: k, w: 1}))
    q0_ok = Q0.lo**2 < Qq(1, 8) < Q0.hi**2
    root_counts = [
        sp.count_roots(sp.Poly(KPOLY, k), spec["k"].lo, spec["k"].hi)
        for spec in ARM_SPECS
    ]
    # KPOLY fixes |q| through 8q^2=1.  Exact interval signs of
    # -A0(k)/A1(k) select which of the two endpoint phases is attached to
    # each isolated terminal root; no floating-point equality is used.
    recovered_q = [
        -poly_iv(A0k, {k: spec["k"]}) / poly_iv(A1k, {k: spec["k"]})
        for spec in ARM_SPECS
    ]
    signs_ok = recovered_q[0].hi < 0 < recovered_q[1].lo
    ct = sp.diff(C, t)
    start_ok = all(
        -1 < spec["start"].lo < spec["start"].hi < 0
        and poly_iv(C, {q: spec["q"], t: Iv(spec["start"].lo)}).sign()
        * poly_iv(C, {q: spec["q"], t: Iv(spec["start"].hi)}).sign()
        == -1
        and poly_iv(ct, {q: spec["q"], t: spec["start"]}).sign() != 0
        for spec in ARM_SPECS
    )
    x = sp.symbols("x")
    derivative_factor_ok = sp.expand(
        sp.diff(x**3 * (x**2 + 5 * x + 10), x)
        - 5 * x**2 * (x**2 + 4 * x + 6)
    ) == 0
    # The only nonzero upper critical point is -2+i*sqrt(2), hence has
    # t=Re(x)/Im(x)=-sqrt(2)<-1.  Both certified arms stay in t>-1.
    upper_critical = -2 + sp.I * sp.sqrt(2)
    upper_zero = (-5 + sp.I * sp.sqrt(15)) / 2
    critical_domain_ok = (
        derivative_factor_ok
        and sp.simplify(upper_critical**2 + 4 * upper_critical + 6) == 0
        and sp.simplify(sp.re(upper_critical) / sp.im(upper_critical) + sp.sqrt(2)) == 0
        and bool(sp.sqrt(2) > 1)
        and all(spec["t_lo"] > -1 for spec in ARM_SPECS)
    )
    zero_domain_ok = (
        sp.simplify(upper_zero**2 + 5 * upper_zero + 10) == 0
        and bool(5 / sp.sqrt(15) > 1)
    )
    initial_ray_ok = all(
        poly_iv(10 * (t**3 - 3 * t), {t: spec["start"]}).sign() == 1
        for spec in ARM_SPECS
    )
    report(
        "1 exact endpoint chamber and quadratic arm equations",
        sp.expand(level - Qcurve) == 0
        and relation == 0
        and q0_ok
        and root_counts == [1, 1]
        and signs_ok
        and start_ok
        and critical_domain_ok
        and zero_domain_ok
        and initial_ray_ok,
        "8q^2=1; isolated positive-ray starts; critical-free t>-1; terminal degree 10",
    )


def numeric_roots(spec: dict, t_value: float) -> list[float]:
    q_value = float((spec["q"].lo + spec["q"].hi) / 2)
    k_value = float((spec["k"].lo + spec["k"].hi) / 2)
    polynomial = sp.Poly(Scurve.subs({q: q_value, k: k_value, t: t_value}), w)
    roots = np.roots([float(coefficient) for coefficient in polynomial.all_coeffs()])
    return sorted(root.real for root in roots if abs(root.imag) < 1e-7)


def tracked_approximations(spec: dict, nodes: list[Qq]) -> list[float]:
    values: list[float] = []
    previous = 0.0
    for index, node in enumerate(nodes):
        roots = numeric_roots(spec, float(node))
        assert roots
        chosen = min(roots, key=lambda value: abs(value - previous))
        if index == 0:
            chosen = min(roots, key=abs)
        values.append(chosen)
        previous = chosen
    return values


def node_root_box(spec: dict, t_value: Qq, approximation: float) -> Iv:
    for digits in range(10, 17):
        denominator = 10**digits
        for padding in (4, 12, 40, 120):
            box = Iv(
                Qq(math.floor(approximation * denominator) - padding, denominator),
                Qq(math.ceil(approximation * denominator) + padding, denominator),
            )
            boxes = {q: spec["q"], k: spec["k"], t: Iv(t_value)}
            lo_value = poly_iv(Scurve, {**boxes, w: Iv(box.lo)})
            hi_value = poly_iv(Scurve, {**boxes, w: Iv(box.hi)})
            sw_box = poly_iv(Sw, {**boxes, w: box})
            if (
                lo_value.sign() * hi_value.sign() == -1
                and sw_box.sign() != 0
            ):
                return box
    raise AssertionError(f"failed node isolation for {spec['name']} t={t_value}")


def cell_root_enclosure(
    spec: dict,
    t_box: Iv,
    approximations: list[float],
) -> Iv:
    for padding in (Qq(1, 1000), Qq(3, 1000), Qq(1, 100), Qq(3, 100)):
        lower = Qq(math.floor(min(approximations) * 10**9), 10**9) - padding
        upper = Qq(math.ceil(max(approximations) * 10**9), 10**9) + padding
        box = Iv(lower, upper)
        base = {q: spec["q"], k: spec["k"], t: t_box}
        lo_value = poly_iv(Scurve, {**base, w: Iv(box.lo)})
        hi_value = poly_iv(Scurve, {**base, w: Iv(box.hi)})
        sw_box = poly_iv(Sw, {**base, w: box})
        if lo_value.sign() * hi_value.sign() == -1 and sw_box.sign() != 0:
            return box
    raise AssertionError(
        f"failed cell enclosure for {spec['name']} t=[{t_box.lo},{t_box.hi}]"
    )


def half_angle_box(spec: dict, p_box: Iv) -> Iv:
    difference = abs_iv(spec["k"] - p_box)
    denominator = (
        sqrt_iv(1 + p_box**2) * sqrt_iv(1 + spec["k"] ** 2)
        + 1
        + p_box * spec["k"]
    )
    assert denominator.lo > 0
    return difference / denominator


def stationary_eliminant() -> sp.Poly:
    q_substitution = -A0k / A1k
    stationary = sp.resultant(
        Qcurve,
        (k - t) * sp.diff(Qcurve, t) + b * sp.diff(Qcurve, b),
        b,
    )
    numerator = sp.together(stationary.subs(q, q_substitution)).as_numer_denom()[0]
    # Retain the full square-free eliminant.  Its degree-ten terminal factor
    # contains the selected t=k endpoint as well as terminal roots belonging
    # to other algebraic branches.  Dividing the factor globally could erase
    # a genuine finite stationary point at one of those foreign roots.
    return sp.Poly(sp.resultant(numerator, KPOLY, k), t).sqf_part()


def arm_budget(spec: dict, stationary: sp.Poly) -> Qq:
    cell_count = spec["cells"]
    nodes = [
        spec["t_lo"]
        + Qq(index, cell_count) * (spec["t_hi"] - spec["t_lo"])
        for index in range(cell_count + 1)
    ]
    approximate_nodes = tracked_approximations(spec, nodes)
    node_boxes = [
        node_root_box(spec, node, approximation)
        for node, approximation in zip(nodes, approximate_nodes)
    ]

    cell_data = []
    for index in range(cell_count):
        t_box = Iv(nodes[index], nodes[index + 1])
        midpoint = float((nodes[index] + nodes[index + 1]) / 2)
        midpoint_roots = numeric_roots(spec, midpoint)
        midpoint_value = min(
            midpoint_roots,
            key=lambda value: abs(value - (approximate_nodes[index] + approximate_nodes[index + 1]) / 2),
        )
        w_box = cell_root_enclosure(
            spec,
            t_box,
            [approximate_nodes[index], midpoint_value, approximate_nodes[index + 1]],
        )
        assert (
            w_box.lo <= node_boxes[index].lo
            and node_boxes[index].hi <= w_box.hi
            and w_box.lo <= node_boxes[index + 1].lo
            and node_boxes[index + 1].hi <= w_box.hi
        )
        boxes = {q: spec["q"], k: spec["k"], t: t_box, w: w_box}
        st_box = poly_iv(St, boxes)
        sw_box = poly_iv(Sw, boxes)
        s_box = spec["k"] - t_box
        denominator = w_box * sw_box - s_box * st_box
        # These two positive signs certify both implicit regularity and
        # db/dt=(w*S_w-(k-t)*S_t)/(S_w*(k-t)^2)>0, so increasing t follows
        # the positive physical ray orientation.
        assert sw_box.sign() == 1 and denominator.sign() == 1
        p_box = t_box + w_box * s_box * sw_box / denominator
        angle = half_angle_box(spec, p_box)
        derivative_sign = (-st_box / sw_box).sign()
        cell_data.append((w_box, angle, derivative_sign))

    # The isolated branch begins at the cubic start direction with w=0 and
    # reaches the terminal direction with w=1.  The exact node/cell gluing
    # above makes these endpoint identities belong to the same branch.
    assert nodes[0] <= spec["start"].lo < spec["start"].hi <= nodes[1]
    assert (
        poly_iv(C, {q: spec["q"], t: Iv(nodes[0])}).sign()
        * poly_iv(C, {q: spec["q"], t: Iv(nodes[1])}).sign()
        == -1
    )
    assert cell_data[0][0].lo < 0 < cell_data[0][0].hi
    assert nodes[-2] <= spec["k"].lo < spec["k"].hi <= nodes[-1]
    assert cell_data[-1][0].lo < 1 < cell_data[-1][0].hi

    budget = Qq(0)
    unknown: list[int] = []
    for index, (w_box, angle, derivative_sign) in enumerate(cell_data):
        if derivative_sign > 0:
            variation = node_boxes[index + 1].hi - node_boxes[index].lo
        elif derivative_sign < 0:
            variation = node_boxes[index].hi - node_boxes[index + 1].lo
        else:
            unknown.append(index)
            continue
        assert variation > 0
        budget += angle.hi * variation

    clusters: list[list[int]] = []
    for index in unknown:
        if not clusters or index != clusters[-1][-1] + 1:
            clusters.append([index])
        else:
            clusters[-1].append(index)

    cluster_counts = []
    for cluster in clusters:
        lo = nodes[cluster[0]]
        hi = nodes[cluster[-1] + 1]
        root_count = sp.count_roots(stationary, sp.Rational(lo.numerator, lo.denominator), sp.Rational(hi.numerator, hi.denominator))
        cluster_counts.append(root_count)
        w_lo = min(cell_data[index][0].lo for index in cluster)
        w_hi = max(cell_data[index][0].hi for index in cluster)
        angle_hi = max(cell_data[index][1].hi for index in cluster)
        # Every actual turn is a zero of the full eliminated stationary
        # polynomial.  Retaining its terminal factor only overcounts turns.
        # Thus r roots split the branch into at most r+1 monotone pieces,
        # each with variation no larger than the certified w-range.
        budget += angle_hi * (root_count + 1) * (w_hi - w_lo)

    report(
        f"2 {spec['name']} exact support--oscillation partition",
        budget < spec["budget_ceiling"],
        f"J<{float(budget):.12f}; ceiling={spec['budget_ceiling']}; "
        f"turn clusters={len(clusters)}; root bounds={cluster_counts}",
    )
    return budget


def final_pair_fanin(negative_budget: Qq, positive_budget: Qq) -> None:
    # The negative-q arm is allowed the positive contribution
    # c_-(7/20-1/4)<1/10 because c_-<1.  The positive-q arm has
    # c_+>9/10 and 11/40-2/5=-1/8, hence contributes <-9/80.
    # Their sum is below -1/80.
    positive_part = Qq(7, 20) - Qq(1, 4)
    negative_part = Qq(9, 10) * (Qq(11, 40) - Qq(2, 5))
    pair_ceiling = positive_part + negative_part
    k_bounds_ok = (
        ARM_SPECS[0]["k"].lo > Qq(1, 4)
        and ARM_SPECS[1]["k"].lo > Qq(2, 5)
        and (1 / sqrt_iv(1 + ARM_SPECS[1]["k"] ** 2)).lo > Qq(9, 10)
    )
    report(
        "4 exact negative endpoint-pair fan-in",
        negative_budget < Qq(7, 20)
        and positive_budget < Qq(11, 40)
        and k_bounds_ok
        and pair_ceiling == Qq(-1, 80),
        "E_pair<-1/80 at both phase endpoints",
    )


def main() -> int:
    exact_endpoint_algebra()
    stationary = stationary_eliminant()
    budgets = [arm_budget(spec, stationary) for spec in ARM_SPECS]
    report(
        "3 stationary elimination is exact and finite",
        stationary.degree() == 120,
        f"degree={stationary.degree()}",
    )
    final_pair_fanin(budgets[0], budgets[1])
    print()
    if FAILURES:
        print("FAIL:", FAILURES)
        return 1
    print("PASS: exact mu=-10 phase-endpoint curved-pair excess certificate")
    return 0


if __name__ == "__main__":
    sys.exit(main())
