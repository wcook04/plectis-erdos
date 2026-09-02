"""Exact uniform certificate for the full ``mu=-10`` quintic phase arc.

For a signed phase parameter ``zeta=tan(phi)``, the selected upper arm is
written in the fixed coordinates

    t = r + (k-r)y,        0 <= y <= 1,
    w = b(k-t),

where ``C_zeta(r)=0`` is the positive-ray entrance and ``A_zeta(k)=0`` is
the terminal direction.  The cleared level equation is ``S=0``.  Its
implicit derivative and the tangent half-angle satisfy the exact square
identity

    tan(|theta|/2) |w_y|
      = (k-r)^3 (1-y)^2 S_t^2 / (S_w Delta).

Thus the transverse support--oscillation budget is a smooth fixed-box
integral: no stationary resultant, absolute-value split, or tail truncation
is needed.  Floating point is used only to propose boxes.  Every entrance,
terminal, branch, regularity, quadrature, and final sign assertion is
accepted with exact rational interval arithmetic.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
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

GRID_SCALE = 1 << 80


def _floor_scaled(value: Qq) -> int:
    return (value.numerator * GRID_SCALE) // value.denominator


def _ceil_scaled(value: Qq) -> int:
    return -((-value.numerator * GRID_SCALE) // value.denominator)


def _lower_grid(value) -> int:
    if isinstance(value, int):
        return value * GRID_SCALE
    return _floor_scaled(Qq(value))


def _upper_grid(value) -> int:
    if isinstance(value, int):
        return value * GRID_SCALE
    return _ceil_scaled(Qq(value))


def _floor_ratio(numerator: int, denominator: int) -> int:
    if denominator < 0:
        numerator, denominator = -numerator, -denominator
    return (numerator * GRID_SCALE) // denominator


def _ceil_ratio(numerator: int, denominator: int) -> int:
    if denominator < 0:
        numerator, denominator = -numerator, -denominator
    return -((-numerator * GRID_SCALE) // denominator)


class Iv:
    """Outward-rounded exact binary fixed-point interval.

    Every endpoint is an integer multiple of ``2^-80``.  Integer floor and
    ceiling operations make all arithmetic rigorous while preventing the
    denominator explosion of unrestricted ``Fraction`` arithmetic.
    """

    def __init__(self, lo, hi=None, *, _scaled: bool = False):
        if isinstance(lo, Iv) and hi is None:
            self._lo, self._hi = lo._lo, lo._hi
            return
        if _scaled:
            self._lo, self._hi = int(lo), int(lo if hi is None else hi)
        else:
            self._lo = _lower_grid(lo)
            self._hi = _upper_grid(lo if hi is None else hi)
        if self._lo > self._hi:
            raise ValueError("reversed interval")

    @property
    def lo(self) -> Qq:
        return Qq(self._lo, GRID_SCALE)

    @property
    def hi(self) -> Qq:
        return Qq(self._hi, GRID_SCALE)

    def __add__(self, other):
        other = iv(other)
        return Iv(self._lo + other._lo, self._hi + other._hi, _scaled=True)

    __radd__ = __add__

    def __neg__(self):
        return Iv(-self._hi, -self._lo, _scaled=True)

    def __sub__(self, other):
        return self + (-iv(other))

    def __rsub__(self, other):
        return iv(other) + (-self)

    def __mul__(self, other):
        other = iv(other)
        products = (
            self._lo * other._lo,
            self._lo * other._hi,
            self._hi * other._lo,
            self._hi * other._hi,
        )
        return Iv(
            min(products) // GRID_SCALE,
            -((-max(products)) // GRID_SCALE),
            _scaled=True,
        )

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = iv(other)
        if other._lo <= 0 <= other._hi:
            raise ZeroDivisionError("interval contains zero")
        candidates = (
            (self._lo, other._lo),
            (self._lo, other._hi),
            (self._hi, other._lo),
            (self._hi, other._hi),
        )
        return Iv(
            min(_floor_ratio(a, b) for a, b in candidates),
            max(_ceil_ratio(a, b) for a, b in candidates),
            _scaled=True,
        )

    def __rtruediv__(self, other):
        return iv(other) / self

    def __pow__(self, exponent: int):
        if exponent < 0:
            return Iv(1) / (self ** (-exponent))
        if exponent == 0:
            return Iv(1)
        if exponent % 2 == 0 and self._lo <= 0 <= self._hi:
            radius = max(-self._lo, self._hi)
            numerator = radius**exponent
            denominator = GRID_SCALE ** (exponent - 1)
            return Iv(0, -((-numerator) // denominator), _scaled=True)
        result = Iv(1)
        base = Iv(self)
        power = exponent
        while power:
            if power & 1:
                result = result * base
            power >>= 1
            if power:
                base = base * base
        return result

    def sign(self) -> int:
        if self._lo > 0:
            return 1
        if self._hi < 0:
            return -1
        return 0


def iv(value) -> Iv:
    return value if isinstance(value, Iv) else Iv(value)


def sqrt_iv(box: Iv) -> Iv:
    assert box._lo >= 0
    lo_radicand = box._lo * GRID_SCALE
    hi_radicand = box._hi * GRID_SCALE
    lo = math.isqrt(lo_radicand)
    hi = math.isqrt(hi_radicand)
    if hi * hi < hi_radicand:
        hi += 1
    return Iv(lo, hi, _scaled=True)


FAILURES: list[str] = []


def report(name: str, ok: bool, detail: str = "") -> None:
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


def hull(*boxes: Iv) -> Iv:
    return Iv(min(box.lo for box in boxes), max(box.hi for box in boxes))


def qfloor(value: float, denominator: int = 10**12) -> Qq:
    return Qq(math.floor(value * denominator), denominator)


def qceil(value: float, denominator: int = 10**12) -> Qq:
    return Qq(math.ceil(value * denominator), denominator)


def abs_iv(box: Iv) -> Iv:
    if box.lo <= 0 <= box.hi:
        return Iv(0, max(-box.lo, box.hi))
    return Iv(min(abs(box.lo), abs(box.hi)), max(abs(box.lo), abs(box.hi)))


q, k, t, r, y, w = sp.symbols("q k t r y w", real=True)

A_SYM = q * (t**5 - 10 * t**3 + 5 * t) + 5 * t**4 - 10 * t**2 + 1
B_SYM = sp.diff(A_SYM, t)
C_SYM = 10 * q * t**3 - 30 * q * t + 30 * t**2 - 10
AK_SYM = sp.expand(A_SYM.subs(t, k))
D_SYM = sp.cancel((A_SYM - AK_SYM) / (t - k))
E_SYM = sp.cancel((C_SYM - C_SYM.subs(t, r)) / (t - r))
S_SYM = sp.expand(-D_SYM * w**2 + B_SYM * w + (t - r) * E_SYM * (k - t))
ST_SYM = sp.diff(S_SYM, t)
SW_SYM = sp.diff(S_SYM, w)

Q0 = Iv(Qq(3535533905932737, 10**16), Qq(3535533905932738, 10**16))


def a_value(qv, tv):
    t2 = tv * tv
    t3 = t2 * tv
    t4 = t2 * t2
    return qv * (t4 * tv - 10 * t3 + 5 * tv) + 5 * t4 - 10 * t2 + 1


def b_value(qv, tv):
    t2 = tv * tv
    return qv * (5 * t2 * t2 - 30 * t2 + 5) + 20 * t2 * tv - 20 * tv


def c_value(qv, tv):
    return 10 * (qv * (tv**3 - 3 * tv) + 3 * tv**2 - 1)


def ct_value(qv, tv):
    return 30 * (qv * (tv**2 - 1) + 2 * tv)


def d_value(qv, kv, tv):
    t2, k2 = tv * tv, kv * kv
    t3, k3 = t2 * tv, k2 * kv
    t4, k4 = t2 * t2, k2 * k2
    p5 = t4 + kv * t3 + k2 * t2 + k3 * tv + k4
    p3 = t2 + kv * tv + k2
    p4 = t3 + kv * t2 + k2 * tv + k3
    return qv * (p5 - 10 * p3 + 5) + 5 * p4 - 10 * (tv + kv)


def dt_value(qv, kv, tv):
    return (
        qv
        * (
            4 * tv**3
            + 3 * kv * tv**2
            + 2 * kv**2 * tv
            + kv**3
            - 20 * tv
            - 10 * kv
        )
        + 15 * tv**2
        + 10 * kv * tv
        + 5 * kv**2
        - 10
    )


def dtt_value(qv, kv, tv):
    return qv * (12 * tv**2 + 6 * kv * tv + 2 * kv**2 - 20) + 30 * tv + 10 * kv


def bt_value(qv, tv):
    return qv * (20 * tv**3 - 60 * tv) + 60 * tv**2 - 20


def btt_value(qv, tv):
    return qv * (60 * tv**2 - 60) + 120 * tv


def e_value(qv, rv, tv):
    return 10 * (qv * (rv * rv + rv * tv + tv * tv - 3) + 3 * (rv + tv))


def et_value(qv, rv, tv):
    return 10 * (qv * (rv + 2 * tv) + 3)


@dataclass
class Geometry:
    s: Iv
    st: Iv
    sw: Iv
    ycoord: Iv
    xcoord: Iv
    delta: Iv
    integrand: Iv


@dataclass
class Dual:
    """First-order interval jet in the signed phase parameter."""

    value: Iv
    derivative: Iv

    def __init__(self, value, derivative=0):
        self.value = iv(value)
        self.derivative = iv(derivative)

    def __add__(self, other):
        other = dual(other)
        return Dual(self.value + other.value, self.derivative + other.derivative)

    __radd__ = __add__

    def __neg__(self):
        return Dual(-self.value, -self.derivative)

    def __sub__(self, other):
        return self + (-dual(other))

    def __rsub__(self, other):
        return dual(other) + (-self)

    def __mul__(self, other):
        other = dual(other)
        return Dual(
            self.value * other.value,
            self.derivative * other.value + self.value * other.derivative,
        )

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = dual(other)
        return Dual(
            self.value / other.value,
            (self.derivative * other.value - self.value * other.derivative)
            / other.value**2,
        )

    def __rtruediv__(self, other):
        return dual(other) / self

    def __pow__(self, exponent: int):
        if exponent == 0:
            return Dual(1, 0)
        if exponent < 0:
            return Dual(1, 0) / (self ** (-exponent))
        return Dual(
            self.value**exponent,
            exponent * self.value ** (exponent - 1) * self.derivative,
        )


def dual(value) -> Dual:
    return value if isinstance(value, Dual) else Dual(value)


def dual_sqrt(value: Dual) -> Dual:
    root = sqrt_iv(value.value)
    return Dual(root, value.derivative / (2 * root))


def s_and_sw(qb: Iv, rb: Iv, kb: Iv, yb: Iv, wb: Iv) -> tuple[Iv, Iv]:
    aa, bb, cc = s_coefficients(qb, rb, kb, yb)
    return aa * wb**2 + bb * wb + cc, 2 * aa * wb + bb


def s_coefficients(qb: Iv, rb: Iv, kb: Iv, yb: Iv) -> tuple[Iv, Iv, Iv]:
    d = kb - rb
    tv = rb + d * yb
    omt = 1 - yb
    ev = e_value(qb, rb, tv)
    fv = d**2 * yb * omt
    dv = d_value(qb, kb, tv)
    bv = b_value(qb, tv)
    return -dv, bv, fv * ev


def geometry(qb: Iv, rb: Iv, kb: Iv, yb: Iv, wb: Iv) -> Geometry:
    d = kb - rb
    tv = rb + d * yb
    omt = 1 - yb
    gap = d * omt
    ev = e_value(qb, rb, tv)
    fv = d**2 * yb * omt
    dv = d_value(qb, kb, tv)
    bv = b_value(qb, tv)
    s = -dv * wb**2 + bv * wb + fv * ev

    ft = kb + rb - 2 * tv
    gt = ft * ev + fv * et_value(qb, rb, tv)
    st = -dt_value(qb, kb, tv) * wb**2 + bt_value(qb, tv) * wb + gt
    sw = -2 * dv * wb + bv

    ycoord = wb * sw - gap * st
    xcoord = tv * ycoord + wb * gap * sw
    norm = sqrt_iv(xcoord**2 + ycoord**2)
    delta = norm * sqrt_iv(1 + kb**2) + ycoord + kb * xcoord
    numerator = d**3 * omt**2 * st**2
    integrand = numerator / (sw * delta)
    return Geometry(s, st, sw, ycoord, xcoord, delta, integrand)


def dual_integrand(
    qb: Iv,
    rb: Iv,
    kb: Iv,
    rprime: Iv,
    kprime: Iv,
    yb: Iv,
    wb: Iv,
) -> Dual:
    """Total signed-phase derivative of the squared integrand.

    The derivative of ``w`` is obtained from the same reduced implicit
    equation, so the value boxes may be rectangular while the derivative
    retains the algebraic ``q -> (r(q),k(q),w(q,y))`` correlation.
    """

    qd = Dual(qb, 1)
    rd = Dual(rb, rprime)
    kd = Dual(kb, kprime)
    yd = Dual(yb, 0)
    provisional_w = Dual(wb, 0)

    def arm_fields(wd: Dual):
        dd = kd - rd
        td = rd + dd * yd
        omt = 1 - yd
        gap = dd * omt
        ev = e_value(qd, rd, td)
        fv = dd**2 * yd * omt
        dv = d_value(qd, kd, td)
        bv = b_value(qd, td)
        sd = -dv * wd**2 + bv * wd + fv * ev

        ft = kd + rd - 2 * td
        gt = ft * ev + fv * et_value(qd, rd, td)
        std = -dt_value(qd, kd, td) * wd**2 + bt_value(qd, td) * wd + gt
        swd = -2 * dv * wd + bv
        return dd, td, omt, gap, sd, std, swd

    _, _, _, _, provisional_s, _, provisional_sw = arm_fields(provisional_w)
    wprime = -provisional_s.derivative / provisional_sw.value
    wd = Dual(wb, wprime)
    dd, td, omt, gap, _, std, swd = arm_fields(wd)
    ycoord = wd * swd - gap * std
    xcoord = td * ycoord + wd * gap * swd
    norm = dual_sqrt(xcoord**2 + ycoord**2)
    terminal_norm = dual_sqrt(1 + kd**2)
    delta = norm * terminal_norm + ycoord + kd * xcoord
    numerator = dd**3 * omt**2 * std**2
    return numerator / (swd * delta)


def numeric_real_roots(coefficients: list[float]) -> list[float]:
    first = 0
    while first < len(coefficients) - 1 and abs(coefficients[first]) < 1e-14:
        first += 1
    roots = np.roots(coefficients[first:])
    return sorted(float(root.real) for root in roots if abs(root.imag) < 1e-8)


def numeric_r(qv: float) -> float:
    roots = numeric_real_roots([10 * qv, 30, -30 * qv, -10])
    selected = [root for root in roots if -0.9 < root < -0.3]
    assert len(selected) == 1
    return selected[0]


def numeric_k(qv: float) -> float:
    roots = numeric_real_roots([qv, 5, -10 * qv, -10, 5 * qv, 1])
    selected = [root for root in roots if 0.2 < root < 0.5]
    assert len(selected) == 1
    return selected[0]


def numeric_s(qv: float, rv: float, kv: float, yv: float, wv: float) -> float:
    dv = kv - rv
    tv = rv + dv * yv
    ev = 10 * (qv * (rv * rv + rv * tv + tv * tv - 3) + 3 * (rv + tv))
    return (
        -float(d_value(qv, kv, tv)) * wv * wv
        + float(b_value(qv, tv)) * wv
        + dv * dv * yv * (1 - yv) * ev
    )


def numeric_w_track(qv: float, nodes: list[Qq]) -> list[float]:
    rv = numeric_r(qv)
    kv = numeric_k(qv)
    previous = 0.0
    result: list[float] = []
    for index, node in enumerate(nodes):
        yv = float(node)
        dv = kv - rv
        tv = rv + dv * yv
        ev = 10 * (qv * (rv * rv + rv * tv + tv * tv - 3) + 3 * (rv + tv))
        aa = -float(d_value(qv, kv, tv))
        bb = float(b_value(qv, tv))
        cc = dv * dv * yv * (1 - yv) * ev
        discriminant = bb * bb - 4 * aa * cc
        assert discriminant >= -1e-10 and abs(aa) > 1e-12
        radical = math.sqrt(max(0.0, discriminant))
        roots = sorted(((-bb - radical) / (2 * aa), (-bb + radical) / (2 * aa)))
        assert roots
        if index == 0:
            chosen = min(roots, key=abs)
        else:
            chosen = min(roots, key=lambda value: abs(value - previous))
        result.append(chosen)
        previous = chosen
    return result


def isolate_parameter_root(qb: Iv, which: str) -> Iv:
    samples = [float(qb.lo), float((qb.lo + qb.hi) / 2), float(qb.hi)]
    approximations = [numeric_r(value) if which == "r" else numeric_k(value) for value in samples]
    for padding in (Qq(1, 10**11), Qq(1, 10**10), Qq(1, 10**9), Qq(1, 10**8)):
        box = Iv(qfloor(min(approximations)) - padding, qceil(max(approximations)) + padding)
        if which == "r":
            lo = c_value(qb, Iv(box.lo))
            hi = c_value(qb, Iv(box.hi))
            derivative = ct_value(qb, box)
        else:
            lo = a_value(qb, Iv(box.lo))
            hi = a_value(qb, Iv(box.hi))
            derivative = b_value(qb, box)
        if lo.sign() * hi.sign() == -1 and derivative.sign() != 0:
            if which == "r":
                assert Qq(-3, 4) < box.lo < box.hi < Qq(-2, 5)
            else:
                assert Qq(1, 5) < box.lo < box.hi < Qq(1, 2)
            return box
    raise AssertionError(f"failed to isolate {which} on q={qb.lo}..{qb.hi}")


def cell_w_box(
    qb: Iv,
    rb: Iv,
    kb: Iv,
    yb: Iv,
    approximations: list[float],
) -> Iv:
    aa, bb, cc = s_coefficients(qb, rb, kb, yb)
    for padding in (
        Qq(1, 10**3),
        Qq(3, 10**3),
        Qq(1, 10**2),
        Qq(3, 10**2),
        Qq(1, 20),
        Qq(1, 10),
    ):
        box = Iv(qfloor(min(approximations), 10**9) - padding, qceil(max(approximations), 10**9) + padding)
        lo_w, hi_w = Iv(box.lo), Iv(box.hi)
        lo_s = aa * lo_w**2 + bb * lo_w + cc
        hi_s = aa * hi_w**2 + bb * hi_w + cc
        joined_sw = 2 * aa * box + bb
        if lo_s.hi < 0 < hi_s.lo and joined_sw.lo > 0:
            return box
    raise AssertionError(
        f"failed w enclosure q={float(qb.lo):.6f}..{float(qb.hi):.6f}, "
        f"y={float(yb.lo):.6f}..{float(yb.hi):.6f}"
    )


def node_w_box(qb: Iv, rb: Iv, kb: Iv, yv: Qq, approximation: float) -> Iv:
    for digits in range(8, 16):
        denominator = 10**digits
        for padding in (4, 12, 40, 120):
            box = Iv(
                Qq(math.floor(approximation * denominator) - padding, denominator),
                Qq(math.ceil(approximation * denominator) + padding, denominator),
            )
            lo_s, _ = s_and_sw(qb, rb, kb, Iv(yv), Iv(box.lo))
            hi_s, _ = s_and_sw(qb, rb, kb, Iv(yv), Iv(box.hi))
            _, sw = s_and_sw(qb, rb, kb, Iv(yv), box)
            if lo_s.hi < 0 < hi_s.lo and sw.lo > 0:
                return box
    raise AssertionError(f"failed node root isolation at y={yv}")


def turn_value(qb: Iv, rb: Iv, kb: Iv, yb: Iv, wb: Iv) -> Iv:
    d = kb - rb
    tv = rb + d * yb
    omt = 1 - yb
    ev = e_value(qb, rb, tv)
    et = et_value(qb, rb, tv)
    fv = d**2 * yb * omt
    ft = kb + rb - 2 * tv
    gtt = -2 * ev + 2 * ft * et + fv * (20 * qb)
    st = (
        -dt_value(qb, kb, tv) * wb**2
        + bt_value(qb, tv) * wb
        + ft * ev
        + fv * et
    )
    stt = -dtt_value(qb, kb, tv) * wb**2 + btt_value(qb, tv) * wb + gtt
    sw = -2 * d_value(qb, kb, tv) * wb + b_value(qb, tv)
    stw = -2 * dt_value(qb, kb, tv) * wb + bt_value(qb, tv)
    return stt * sw - stw * st


@dataclass
class ArmBound:
    qbox: Iv
    rbox: Iv
    kbox: Iv
    integral_upper: Qq
    excess: Iv
    max_w: Qq
    min_sw: Qq
    min_ycoord: Qq
    min_delta: Qq


@dataclass
class ArmDerivativeBound:
    excess_derivative_abs: Qq
    integral_derivative_abs: Qq
    integral_upper: Qq
    rprime: Iv
    kprime: Iv
    rbox: Iv
    kbox: Iv


@dataclass
class ArmVariationBound:
    integral_upper: Qq
    excess: Iv
    turn_cells: int
    max_w: Qq
    min_sw: Qq
    min_ycoord: Qq
    min_delta: Qq
    rbox: Iv
    kbox: Iv


def arm_bound(qb: Iv, y_cells: int) -> ArmBound:
    rb = isolate_parameter_root(qb, "r")
    kb = isolate_parameter_root(qb, "k")
    assert (10 * (rb**3 - 3 * rb)).lo > 0
    nodes = [Qq(index, y_cells) for index in range(y_cells + 1)]
    half_nodes = [Qq(index, 2 * y_cells) for index in range(2 * y_cells + 1)]
    q_samples = list(dict.fromkeys([float(qb.lo), float((qb.lo + qb.hi) / 2), float(qb.hi)]))
    tracks = [numeric_w_track(value, nodes) for value in q_samples]
    half_tracks = [numeric_w_track(value, half_nodes) for value in q_samples]

    integral_upper = Qq(0)
    max_w = Qq(0)
    min_sw: Qq | None = None
    min_ycoord: Qq | None = None
    min_delta: Qq | None = None
    previous: Iv | None = None
    width = Qq(1, y_cells)

    for index in range(y_cells):
        yb = Iv(nodes[index], nodes[index + 1])
        approximations = [
            tracks[sample][node]
            for sample in range(len(tracks))
            for node in (index, index + 1)
        ]
        approximations.extend(half_tracks[sample][2 * index + 1] for sample in range(len(half_tracks)))

        wb = cell_w_box(qb, rb, kb, yb, approximations)
        if previous is not None:
            assert max(previous.lo, wb.lo) <= min(previous.hi, wb.hi)
        previous = wb
        data = geometry(qb, rb, kb, yb, wb)
        assert data.sw.lo > 0 and data.ycoord.lo > 0 and data.delta.lo > 0
        assert data.integrand.lo >= 0
        integral_upper += width * data.integrand.hi
        max_w = max(max_w, wb.hi)
        min_sw = data.sw.lo if min_sw is None else min(min_sw, data.sw.lo)
        min_ycoord = data.ycoord.lo if min_ycoord is None else min(min_ycoord, data.ycoord.lo)
        min_delta = data.delta.lo if min_delta is None else min(min_delta, data.delta.lo)

    # Endpoint cells contain the exact selected roots w(0)=0 and w(1)=1.
    first = geometry(qb, rb, kb, Iv(0), Iv(0))
    last = geometry(qb, rb, kb, Iv(1), Iv(1))
    assert first.s.lo <= 0 <= first.s.hi and last.s.lo <= 0 <= last.s.hi
    cosine = 1 / sqrt_iv(1 + kb**2)
    excess = (Iv(0, integral_upper) - kb) * cosine
    assert min_sw is not None and min_ycoord is not None and min_delta is not None
    return ArmBound(qb, rb, kb, integral_upper, excess, max_w, min_sw, min_ycoord, min_delta)


def arm_variation_bound(qb: Iv, y_cells: int) -> ArmVariationBound:
    """Tight point-phase budget using exact node variation.

    This routine is used only on a rational phase anchor (up to the fixed
    ``2^-80`` outward rounding).  Sign-certain cells use endpoint variation;
    the remaining cells use the exact squared integrand directly.
    """

    assert qb.hi - qb.lo <= Qq(1, 10**20)
    rb = isolate_parameter_root(qb, "r")
    kb = isolate_parameter_root(qb, "k")
    assert (10 * (rb**3 - 3 * rb)).lo > 0
    nodes = [Qq(index, y_cells) for index in range(y_cells + 1)]
    qv = float((qb.lo + qb.hi) / 2)
    track = numeric_w_track(qv, nodes)
    half_track = numeric_w_track(qv, [Qq(index, 2 * y_cells) for index in range(2 * y_cells + 1)])
    node_boxes = [
        node_w_box(qb, rb, kb, node, approximation)
        for node, approximation in zip(nodes, track)
    ]

    cells: list[tuple[Iv, Iv, int, Iv]] = []
    max_w = Qq(0)
    min_sw: Qq | None = None
    min_ycoord: Qq | None = None
    min_delta: Qq | None = None
    for index in range(y_cells):
        yb = Iv(nodes[index], nodes[index + 1])
        approximations = [track[index], half_track[2 * index + 1], track[index + 1]]
        wb = cell_w_box(qb, rb, kb, yb, approximations)
        assert wb.lo <= node_boxes[index].lo <= node_boxes[index].hi <= wb.hi
        assert wb.lo <= node_boxes[index + 1].lo <= node_boxes[index + 1].hi <= wb.hi
        data = geometry(qb, rb, kb, yb, wb)
        assert data.sw.lo > 0 and data.ycoord.lo > 0 and data.delta.lo > 0
        d = kb - rb
        gap = d * (1 - yb)
        angle = gap**2 * abs_iv(data.st) / data.delta
        derivative_sign = (-data.st / data.sw).sign()
        cells.append((wb, angle, derivative_sign, data.integrand))
        max_w = max(max_w, wb.hi)
        min_sw = data.sw.lo if min_sw is None else min(min_sw, data.sw.lo)
        min_ycoord = data.ycoord.lo if min_ycoord is None else min(min_ycoord, data.ycoord.lo)
        min_delta = data.delta.lo if min_delta is None else min(min_delta, data.delta.lo)

    budget = Qq(0)
    unknown = [index for index, (_, _, sign, _) in enumerate(cells) if sign == 0]
    width = Qq(1, y_cells)
    for index, (_, angle, derivative_sign, squared_integrand) in enumerate(cells):
        if derivative_sign == 0:
            # The exact square identity is strongest at the genuine turn
            # and at the terminal tail, where S_t or (1-y)^2 vanishes.
            budget += width * squared_integrand.hi
            continue
        if derivative_sign > 0:
            variation = node_boxes[index + 1].hi - node_boxes[index].lo
        else:
            variation = node_boxes[index].hi - node_boxes[index + 1].lo
        assert variation > 0
        budget += angle.hi * variation

    assert node_boxes[0].lo < 0 < node_boxes[0].hi
    assert node_boxes[-1].lo < 1 < node_boxes[-1].hi
    cosine = 1 / sqrt_iv(1 + kb**2)
    excess = (Iv(0, budget) - kb) * cosine
    assert min_sw is not None and min_ycoord is not None and min_delta is not None
    return ArmVariationBound(
        budget,
        excess,
        len(unknown),
        max_w,
        min_sw,
        min_ycoord,
        min_delta,
        rb,
        kb,
    )


def arm_derivative_bound(qb: Iv, y_cells: int) -> ArmDerivativeBound:
    rb = isolate_parameter_root(qb, "r")
    kb = isolate_parameter_root(qb, "k")
    assert (10 * (rb**3 - 3 * rb)).lo > 0
    cq = 10 * (rb**3 - 3 * rb)
    rprime = -cq / ct_value(qb, rb)
    aq = kb**5 - 10 * kb**3 + 5 * kb
    kprime = -aq / b_value(qb, kb)
    assert 0 < rprime.lo < rprime.hi < Qq(1, 2)
    assert 0 < kprime.lo < kprime.hi < Qq(1, 4)

    nodes = [Qq(index, y_cells) for index in range(y_cells + 1)]
    half_nodes = [Qq(index, 2 * y_cells) for index in range(2 * y_cells + 1)]
    q_samples = list(dict.fromkeys([float(qb.lo), float((qb.lo + qb.hi) / 2), float(qb.hi)]))
    tracks = [numeric_w_track(value, nodes) for value in q_samples]
    half_tracks = [numeric_w_track(value, half_nodes) for value in q_samples]

    integral_upper = Qq(0)
    integral_derivative_abs = Qq(0)
    width = Qq(1, y_cells)
    previous: Iv | None = None
    first_wb: Iv | None = None
    last_wb: Iv | None = None
    for index in range(y_cells):
        yb = Iv(nodes[index], nodes[index + 1])
        approximations = [
            tracks[sample][node]
            for sample in range(len(tracks))
            for node in (index, index + 1)
        ]
        approximations.extend(half_tracks[sample][2 * index + 1] for sample in range(len(half_tracks)))
        wb = cell_w_box(qb, rb, kb, yb, approximations)
        if first_wb is None:
            first_wb = wb
        last_wb = wb
        if previous is not None:
            assert max(previous.lo, wb.lo) <= min(previous.hi, wb.hi)
        previous = wb
        primal = geometry(qb, rb, kb, yb, wb)
        assert primal.sw.lo > 0 and primal.ycoord.lo > 0 and primal.delta.lo > 0
        jet = dual_integrand(qb, rb, kb, rprime, kprime, yb, wb)
        assert jet.value.lo >= 0
        integral_upper += width * jet.value.hi
        integral_derivative_abs += width * abs_iv(jet.derivative).hi

    assert kb.lo > rb.hi
    assert first_wb is not None and first_wb.lo < 0 < first_wb.hi
    assert last_wb is not None and last_wb.lo < 1 < last_wb.hi

    terminal_norm = sqrt_iv(1 + kb**2)
    cosine = 1 / terminal_norm
    cosine_prime = -kb * kprime / terminal_norm**3
    jprime = Iv(-integral_derivative_abs, integral_derivative_abs)
    excess_prime = cosine * (jprime - kprime) + cosine_prime * (Iv(0, integral_upper) - kb)
    return ArmDerivativeBound(
        abs_iv(excess_prime).hi,
        integral_derivative_abs,
        integral_upper,
        rprime,
        kprime,
        rb,
        kb,
    )


def exact_algebra() -> None:
    x = sp.symbols("x", real=True)
    z = sp.symbols("z", real=True)
    level = sp.expand(A_SYM * z**2 + B_SYM * z + C_SYM)
    original_s = sp.expand(-D_SYM * w**2 + B_SYM * w + C_SYM * (k - t))
    reduction_error = sp.factor(original_s - S_SYM)
    st = sp.diff(S_SYM, t)
    sw = sp.diff(S_SYM, w)
    ycoord = sp.expand(w * sw - (k - t) * st)
    xcoord = sp.expand(t * ycoord + w * (k - t) * sw)
    determinant = sp.factor(k * ycoord - xcoord)
    polynomial = x**3 * (x**2 + 5 * x + 10)
    upper_critical = -2 + sp.I * sp.sqrt(2)
    upper_zero = (-5 + sp.I * sp.sqrt(15)) / 2
    critical_free_strip = (
        sp.expand(sp.diff(polynomial, x) - 5 * x**2 * (x**2 + 4 * x + 6)) == 0
        and sp.simplify(upper_critical**2 + 4 * upper_critical + 6) == 0
        and sp.simplify(sp.re(upper_critical) / sp.im(upper_critical) + sp.sqrt(2)) == 0
        and sp.simplify(upper_zero**2 + 5 * upper_zero + 10) == 0
        and bool(sp.sqrt(2) > 1)
        and bool(5 / sp.sqrt(15) > 1)
    )
    q0_ok = Q0.lo**2 < Qq(1, 8) < Q0.hi**2
    report(
        "1 exact fixed-box arm and squared-integrand identities",
        sp.expand(B_SYM - sp.diff(A_SYM, t)) == 0
        and sp.factor(E_SYM - 10 * (q * (r**2 + r * t + t**2 - 3) + 3 * (r + t))) == 0
        and sp.expand(reduction_error - C_SYM.subs(t, r) * (k - t)) == 0
        and sp.expand(determinant + (k - t) ** 2 * st) == 0
        and sp.Poly(level, z).degree() == 2
        and critical_free_strip
        and q0_ok,
        "C(r)=0 reduction; kY-X=-(k-t)^2 S_t; critical-free t>-1; q0^2=1/8",
    )


def full_arc(q_cells: int, y_cells: int, derivative_y_cells: int, target: Qq) -> None:
    """Mean-value atlas with tight rational anchors and dual slab bounds."""

    pair_uppers: list[Qq] = []
    global_max_w = Qq(0)
    global_min_sw: Qq | None = None
    global_min_ycoord: Qq | None = None
    global_min_delta: Qq | None = None
    global_lipschitz = Qq(0)
    total_hybrid_cells = 0
    worst_index = -1
    previous_positive_derivative: ArmDerivativeBound | None = None
    previous_negative_derivative: ArmDerivativeBound | None = None

    for index in range(q_cells):
        qa = Q0.hi * Qq(index, q_cells)
        qb = Q0.hi * Qq(index + 1, q_cells)
        center = (qa + qb) / 2
        radius = (qb - qa) / 2

        positive = arm_variation_bound(Iv(center), y_cells)
        negative = arm_variation_bound(Iv(-center), y_cells)
        positive_derivative = arm_derivative_bound(Iv(qa, qb), derivative_y_cells)
        negative_derivative = arm_derivative_bound(Iv(-qb, -qa), derivative_y_cells)
        assert (
            positive_derivative.rbox.lo <= positive.rbox.lo
            <= positive.rbox.hi <= positive_derivative.rbox.hi
            and positive_derivative.kbox.lo <= positive.kbox.lo
            <= positive.kbox.hi <= positive_derivative.kbox.hi
            and negative_derivative.rbox.lo <= negative.rbox.lo
            <= negative.rbox.hi <= negative_derivative.rbox.hi
            and negative_derivative.kbox.lo <= negative.kbox.lo
            <= negative.kbox.hi <= negative_derivative.kbox.hi
        )
        if previous_positive_derivative is not None:
            assert max(previous_positive_derivative.rbox.lo, positive_derivative.rbox.lo) <= min(
                previous_positive_derivative.rbox.hi, positive_derivative.rbox.hi
            )
            assert max(previous_positive_derivative.kbox.lo, positive_derivative.kbox.lo) <= min(
                previous_positive_derivative.kbox.hi, positive_derivative.kbox.hi
            )
            assert previous_negative_derivative is not None
            assert max(previous_negative_derivative.rbox.lo, negative_derivative.rbox.lo) <= min(
                previous_negative_derivative.rbox.hi, negative_derivative.rbox.hi
            )
            assert max(previous_negative_derivative.kbox.lo, negative_derivative.kbox.lo) <= min(
                previous_negative_derivative.kbox.hi, negative_derivative.kbox.hi
            )
        previous_positive_derivative = positive_derivative
        previous_negative_derivative = negative_derivative
        lipschitz = (
            positive_derivative.excess_derivative_abs
            + negative_derivative.excess_derivative_abs
        )
        anchor_upper = positive.excess.hi + negative.excess.hi
        pair_upper = anchor_upper + radius * lipschitz
        pair_uppers.append(pair_upper)
        if pair_upper == max(pair_uppers):
            worst_index = index
        global_lipschitz = max(global_lipschitz, lipschitz)
        total_hybrid_cells += positive.turn_cells + negative.turn_cells
        for arm in (positive, negative):
            global_max_w = max(global_max_w, arm.max_w)
            global_min_sw = arm.min_sw if global_min_sw is None else min(global_min_sw, arm.min_sw)
            global_min_ycoord = (
                arm.min_ycoord if global_min_ycoord is None else min(global_min_ycoord, arm.min_ycoord)
            )
            global_min_delta = arm.min_delta if global_min_delta is None else min(global_min_delta, arm.min_delta)
        print(
            f"CELL q={index + 1}/{q_cells} "
            f"anchor<{float(anchor_upper):.9f} "
            f"L<{float(lipschitz):.6f} "
            f"uniform<{float(pair_upper):.9f}",
            flush=True,
        )

    worst = max(pair_uppers)
    report(
        "2 exact anchor branches are regular and positive-ray oriented",
        global_max_w < Qq(11, 10)
        and global_min_sw is not None
        and global_min_sw > 0
        and global_min_ycoord is not None
        and global_min_ycoord > 0
        and global_min_delta is not None
        and global_min_delta > 0,
        f"anchor w<11/10; anchor S_w>{float(global_min_sw):.6f}; "
        f"Y>{float(global_min_ycoord):.6f}; Delta>{float(global_min_delta):.6f}",
    )
    report(
        "3 dual mean-value transport pays phase uncertainty once per slab",
        global_lipschitz < Qq(20)
        and total_hybrid_cells < 2 * q_cells * y_cells,
        f"pair Lipschitz<{float(global_lipschitz):.6f}; "
        f"square-integrand fallback cells={total_hybrid_cells}",
    )
    report(
        "4 full signed phase-pair excess is uniformly negative",
        worst < target,
        f"{q_cells} anchors, {y_cells} point cells, {derivative_y_cells} dual cells; "
        f"worst q-slab={worst_index + 1}; "
        f"E_pair<{float(worst):.12f}<{float(target):.12f}",
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--q-cells", type=int, default=64)
    parser.add_argument("--y-cells", type=int, default=640)
    parser.add_argument("--derivative-y-cells", type=int, default=128)
    parser.add_argument("--target", type=Qq, default=Qq(-1, 100))
    args = parser.parse_args()
    exact_algebra()
    full_arc(args.q_cells, args.y_cells, args.derivative_y_cells, args.target)
    print()
    if FAILURES:
        print("FAIL:", FAILURES)
        return 1
    print("PASS: exact uniform mu=-10 full phase-arc excess certificate")
    return 0


if __name__ == "__main__":
    sys.exit(main())
