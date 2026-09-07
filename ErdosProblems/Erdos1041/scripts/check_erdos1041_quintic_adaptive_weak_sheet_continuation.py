#!/usr/bin/env python3
"""Exact adaptive support probe for the weak positive cusp sheet.

This file is deliberately self-contained at the carrier boundary.  Floating
arithmetic supplies only Newton scouts; every accepted root tube and support
payment is an outward rational complex-ball calculation.
"""

from __future__ import annotations

from fractions import Fraction as Fr
import importlib.util
from pathlib import Path
import sys

import mpmath as mp
import sympy as sp


HERE = Path(__file__).resolve().parent
LIB = HERE / "lib_erdos1041_support_engine.py"
SPEC = importlib.util.spec_from_file_location("adaptive_weak_support", LIB)
SUPPORT = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules[SPEC.name] = SUPPORT
SPEC.loader.exec_module(SUPPORT)
CB, cb, cb_pt = SUPPORT.CB, SUPPORT.cb, SUPPORT.cb_pt
WALL = SUPPORT.wall
BASE_KRAWCZYK = WALL.krawczyk
mp.mp.dps = 70


def report(name: str, ok: bool, detail: str = "") -> None:
    print(("PASS " if ok else "FAIL ") + name + ((" :: " + detail) if detail else ""))
    if not ok:
        raise AssertionError(name)


def fr(value):
    value = sp.Rational(value)
    return Fr(int(value.p), int(value.q))


def exact_abs_ball(value):
    lo = WALL.sqrt_lo(value.cabs2()) - value.r
    hi = WALL.sqrt_hi(value.cabs2()) + value.r
    if lo <= 0:
        raise RuntimeError("direction tube meets zero")
    return CB((lo + hi) / 2, 0, WALL.snap_up((hi - lo) / 2), _raw=True)


u, z = sp.symbols("u z")
kappa = u**3
mu_expr = -10 + u*z
A = 4*(mu_expr+4)
B = -sp.Rational(12, 25)*(3*mu_expr**3-5*mu_expr**2-100*mu_expr-200)
C = sp.Rational(4, 3125)*(mu_expr+10)**3*(27*mu_expr**2+140*mu_expr+200)
K = sp.expand(
    C**2*(1+kappa)**3
    - A*B*C*kappa*(1+kappa)*(1+4*kappa)
    + (A**3*C+B**3)*kappa**2*(1+2*kappa)
    - A**2*B**2*kappa**3
)
H = sp.expand(sp.cancel(K/u**6))
HZ = sp.diff(H, z)
D = A**2*kappa-B*(1+kappa)
P = sp.cancel((C*(1+kappa)**2-A*B*kappa**2)/(kappa*D))
HFUN = sp.lambdify((u, z), H, "mpmath")


def coeffs_in_z(expr, u_ball):
    poly = sp.Poly(sp.expand(expr), z)
    result = []
    for degree in range(poly.degree(), -1, -1):
        coefficient = sp.Poly(poly.nth(degree), u)
        value = cb(0)
        for power in range(coefficient.degree(), -1, -1):
            value = value*u_ball+cb(fr(coefficient.nth(power)))
        result.append(value)
    return result


def eval_rational(expr, u_ball, z_ball):
    numerator, denominator = map(sp.expand, sp.fraction(sp.cancel(expr)))

    def eval_poly(poly_expr):
        poly = sp.Poly(poly_expr, z)
        value = cb(0)
        for degree in range(poly.degree(), -1, -1):
            coefficient = sp.Poly(poly.nth(degree), u)
            coefficient_value = cb(0)
            for power in range(coefficient.degree(), -1, -1):
                coefficient_value = coefficient_value*u_ball+cb(fr(coefficient.nth(power)))
            value = value*z_ball+coefficient_value
        return value

    return eval_poly(numerator)/eval_poly(denominator)


qplus = -8100 + 16200j*mp.sqrt(2)
LIMIT_ROOTS = []
for value in (qplus, qplus.conjugate()):
    root = mp.exp(mp.log(value)/3)
    LIMIT_ROOTS.extend(root*mp.exp(2j*mp.pi*j/3) for j in range(3))
LIMIT_ROOTS = [root for root in LIMIT_ROOTS if root.imag > 0]


def carrier_cell(u_lo: Fr, u_hi: Fr, branch: int = 1):
    u_mid_exact = (u_lo+u_hi)/2
    u_ball = CB(u_mid_exact, 0, (u_hi-u_lo)/2, _raw=True)
    u_mid = mp.mpf(u_mid_exact.numerator)/u_mid_exact.denominator
    scout = mp.findroot(
        lambda zz: HFUN(u_mid, zz), LIMIT_ROOTS[branch],
        tol=mp.mpf("1e-55"), maxsteps=100,
    )
    root_ball = None
    for radius in (Fr(1,100), Fr(1,20), Fr(1,10), Fr(1,2), Fr(1), Fr(2)):
        root_ball = WALL.krawczyk(
            coeffs_in_z(H, u_ball), coeffs_in_z(HZ, u_ball), cb(0),
            cb_pt(scout), radius, iters=35,
        )
        if root_ball is not None:
            break
    if root_ball is None or root_ball.b-root_ball.r <= 0:
        raise RuntimeError("weak carrier failure")
    mu_ball = cb(-10)+u_ball*root_ball
    pair_sum = eval_rational(P, u_ball, root_ball)
    third = -cb(4)*(mu_ball+cb(4))-pair_sum
    cross = pair_sum.conj()*third
    if abs(cross.b) <= cross.r:
        raise RuntimeError("wall chamber failure")
    epsilon = -1 if cross.b > 0 else 1
    ray_ball = -cb(epsilon)*cb(0,1)*pair_sum*exact_abs_ball(pair_sum).inv()
    mu_scout = -10+u_mid*scout
    pair_scout = mp.mpc(
        mp.mpf(pair_sum.a.numerator)/pair_sum.a.denominator,
        mp.mpf(pair_sum.b.numerator)/pair_sum.b.denominator,
    )
    ray_scout = -epsilon*1j*pair_scout/abs(pair_scout)
    return mu_ball, ray_ball, mu_scout, ray_scout, root_ball


def wide_krawczyk(coeffs, dcoeffs, target, centre, radius, *, iters=25):
    for candidate in (
        radius, Fr(1,10**12), Fr(1,10**10), Fr(1,10**8), Fr(1,10**6),
        Fr(1,10**5), Fr(1,10**4), Fr(1,1000), Fr(1,100), Fr(1,10), Fr(1),
    ):
        if candidate < radius:
            continue
        result = BASE_KRAWCZYK(
            coeffs, dcoeffs, target, centre, candidate, iters=iters
        )
        if result is not None:
            return result
    return None


def wall_excess(muC, wC, mu, ray, *, gradient_only=False):
    original = WALL.krawczyk
    WALL.krawczyk = wide_krawczyk
    try:
        return WALL.certified_excess(
            mu, ray, muC=CB(muC.a,muC.b,muC.r,_raw=True),
            wC=CB(wC.a,wC.b,wC.r,_raw=True), k=20,
            s0=Fr(1,10**14), ratio=.06, eps_step=Fr(1,10000),
            want_grad=True, gradient_only=gradient_only,
        )
    finally:
        WALL.krawczyk = original


def direct_anchor(u_exact: Fr, branch: int = 1):
    muC, wC, mu, ray, rootC = carrier_cell(u_exact, u_exact, branch)
    excess = wall_excess(muC, wC, mu, ray)
    return {
        "u": u_exact, "branch": branch, "hi": excess["hi"],
        "lo": excess["lo"], "gmu": excess["grad_mu_q"],
        "gphi": excess["grad_phi_q"], "root": rootC,
    }


HU = sp.diff(H, u)
PU = sp.diff(P, u)
PZ = sp.diff(P, z)


def gradient_cell(u_lo: Fr, u_hi: Fr, branch: int = 1):
    muC, wC, mu, ray, rootC = carrier_cell(u_lo, u_hi, branch)
    uC = CB((u_lo+u_hi)/2, 0, (u_hi-u_lo)/2, _raw=True)
    zprime = -eval_rational(HU, uC, rootC)/eval_rational(HZ, uC, rootC)
    muprime = rootC+uC*zprime
    pair = eval_rational(P, uC, rootC)
    logpprime = (
        eval_rational(PU, uC, rootC)+eval_rational(PZ, uC, rootC)*zprime
    )/pair
    phiprime = abs(logpprime.b)+logpprime.r
    gradient = wall_excess(muC, wC, mu, ray, gradient_only=True)
    chain = (
        gradient["grad_mu_q"]*muprime.abs_hi()
        + gradient["grad_phi_q"]*phiprime
    )
    return {
        "u_lo": u_lo, "u_hi": u_hi, "branch": branch,
        "payment": WALL.snap_up(chain*(u_hi-u_lo)), "chain": chain,
        "gmu": gradient["grad_mu_q"], "gphi": gradient["grad_phi_q"],
        "muprime": muprime.abs_hi(), "phiprime": phiprime, "root": rootC,
    }


ROOT_RADII = (
    Fr(1,10**18), Fr(1,10**15), Fr(1,10**12), Fr(1,10**10),
    Fr(1,10**8), Fr(1,10**6), Fr(1,10**4), Fr(1,10**3),
    Fr(1,10**2), Fr(1,10), Fr(1),
)


def isolate_y(muC, wC, rC, centre, *, variation=None, iters=30):
    cs = SUPPORT.compact_coeffs(muC, wC, rC)
    ds = SUPPORT.compact_dcoeffs(cs)
    radii = []
    if variation is not None:
        radii.extend(
            Fr(mp.nstr(max(variation*grow, mp.mpf("1e-30")), 50))
            for grow in (2, 4, 8, 16, 40, 100, 400)
        )
    radii.extend(ROOT_RADII)
    for radius in radii:
        result = WALL.krawczyk(cs, ds, cb(0), cb_pt(centre), radius, iters=iters)
        if result is not None:
            return result
    raise RuntimeError("compact Krawczyk failure")


def adaptive_arm(muC, wC, mu, ray, sign, *, base_cells=128, max_depth=7):
    """Certify one arm, recursively resolving every ambiguous velocity cell."""
    rmax = Fr(4,5)
    nodes = [rmax*Fr(j*j, base_cells*base_cells) for j in range(base_cells+1)]
    y0 = sign*mp.sqrt(ray/(10+mu))
    yterm = y0
    for endpoint in nodes[1:]:
        yterm = SUPPORT.scout(
            mp.mpf(endpoint.numerator)/endpoint.denominator, yterm, mu, ray
        )
    etaC = WALL.fifth_root_of_w(wC, ray, yterm)
    stats = {
        "monotone_cells": 0, "direct_cells": 0, "split_cells": 0,
        "max_depth": 0, "direct_width": Fr(0), "direct_payment": Fr(0),
    }

    def one_cell(ra, rc, yleft, xleftC, depth):
        mid = (ra+rc)/2
        rm = mp.mpf(mid.numerator)/mid.denominator
        rend = mp.mpf(rc.numerator)/rc.denominator
        ymid = SUPPORT.scout(rm, yleft, mu, ray)
        yright = SUPPORT.scout(rend, ymid, mu, ray)
        rC = CB(mid, 0, (rc-ra)/2, _raw=True)
        variation = max(abs(ymid-yleft), abs(yright-ymid), mp.mpf("1e-30"))
        try:
            Y = isolate_y(muC, wC, rC, ymid, variation=variation)
        except RuntimeError:
            if depth >= max_depth:
                raise RuntimeError(
                    f"compact Krawczyk failure on [{ra},{rc}] at depth {depth}"
                )
            stats["split_cells"] += 1
            left_pay, y_at_mid, x_at_mid = one_cell(ra, mid, yleft, xleftC, depth+1)
            right_pay, y_at_right, x_at_right = one_cell(mid, rc, y_at_mid, x_at_mid, depth+1)
            return WALL.snap_up(left_pay+right_pay), y_at_right, x_at_right
        om = cb(1)-rC
        Gy = (
            cb(5)*SUPPORT.cpow(rC,15)*SUPPORT.cpow(Y,4)
            + cb(20)*SUPPORT.cpow(rC,10)*SUPPORT.cpow(om,2)*SUPPORT.cpow(Y,3)
            + cb(30)*SUPPORT.cpow(rC,5)*SUPPORT.cpow(om,4)*SUPPORT.cpow(Y,2)
            + cb(2)*(cb(10)+muC)*SUPPORT.cpow(om,6)*Y
        )
        Gr = (
            cb(15)*SUPPORT.cpow(rC,14)*SUPPORT.cpow(Y,5)
            + cb(50)*SUPPORT.cpow(rC,9)*SUPPORT.cpow(om,2)*SUPPORT.cpow(Y,4)
            - cb(10)*SUPPORT.cpow(rC,10)*om*SUPPORT.cpow(Y,4)
            + cb(50)*SUPPORT.cpow(rC,4)*SUPPORT.cpow(om,4)*SUPPORT.cpow(Y,3)
            - cb(40)*SUPPORT.cpow(rC,5)*SUPPORT.cpow(om,3)*SUPPORT.cpow(Y,3)
            - cb(6)*(cb(10)+muC)*SUPPORT.cpow(om,5)*SUPPORT.cpow(Y,2)
        )
        if Gy.contains_zero():
            raise RuntimeError("G_y contains zero")
        scale = SUPPORT.cpow(rC,5)/SUPPORT.cpow(om,2)
        scale_prime = (
            cb(5)*SUPPORT.cpow(rC,4)/SUPPORT.cpow(om,2)
            + cb(2)*SUPPORT.cpow(rC,5)/SUPPORT.cpow(om,3)
        )
        velocity = scale_prime*Y-scale*Gr/Gy
        rotated = etaC.conj()*velocity
        re_lo = rotated.re_lo()
        denominator = WALL.snap_dn(rotated.abs_lo()+re_lo)
        monotone = abs(rotated.b) > rotated.r and denominator > 0
        if not monotone and depth < max_depth:
            stats["split_cells"] += 1
            left_pay, y_at_mid, x_at_mid = one_cell(ra, mid, yleft, xleftC, depth+1)
            right_pay, y_at_right, x_at_right = one_cell(mid, rc, y_at_mid, x_at_mid, depth+1)
            return WALL.snap_up(left_pay+right_pay), y_at_right, x_at_right

        rpoint = cb(rc)
        Yn = isolate_y(muC, wC, rpoint, yright, iters=35)
        xrightC = SUPPORT.cpow(rpoint,5)/SUPPORT.cpow(cb(1)-rpoint,2)*Yn
        if monotone:
            qleft, qright = etaC.conj()*xleftC, etaC.conj()*xrightC
            dv = WALL.snap_up(abs(qright.b-qleft.b)+qright.r+qleft.r)
            tau = WALL.snap_up((abs(rotated.b)+rotated.r)/denominator)
            payment = WALL.snap_up(tau*dv)
            stats["monotone_cells"] += 1
        else:
            im_hi = abs(rotated.b)+rotated.r
            if re_lo > 0:
                defect = WALL.snap_up(im_hi*im_hi/(2*re_lo))
            else:
                defect = WALL.snap_up(rotated.abs_hi()-rotated.re_lo())
            payment = WALL.snap_up(defect*(rc-ra))
            stats["direct_cells"] += 1
            stats["direct_width"] += rc-ra
            stats["direct_payment"] = WALL.snap_up(stats["direct_payment"]+payment)
        stats["max_depth"] = max(stats["max_depth"], depth)
        return payment, yright, xrightC

    total = Fr(0)
    yleft = y0
    xleftC = cb(0)
    for ra, rc in zip(nodes[:-1], nodes[1:]):
        payment, yleft, xleftC = one_cell(ra, rc, yleft, xleftC, 0)
        total = WALL.snap_up(total+payment)

    rC = cb(rmax)
    Y = isolate_y(muC, wC, rC, yterm, iters=40)
    scale = SUPPORT.cpow(rC,5)/SUPPORT.cpow(cb(1)-rC,2)
    yS = cb(1)+scale*Y
    tail, _, _, _, _ = WALL.tail_bound(muC, wC, yS, 16, etaC)
    upper = WALL.snap_up(total+tail-etaC.re_lo())
    stats.update({"support": total, "tail": tail, "eta_re_lo": etaC.re_lo()})
    return upper, stats


U0 = Fr(1,1000)
U1 = Fr(1,500)
anchor = direct_anchor(U0)
cell = gradient_cell(U0,U1)
transport_upper = WALL.snap_up(anchor["hi"]+cell["payment"])
report("AWS1 exact weak endpoint anchor is negative", anchor["hi"] < 0,
       f"upper={float(anchor['hi']):.12f}")
report("AWS2 direct L1 transport crosses the old endpoint", transport_upper < 0,
       f"u1={float(U1):.9f}, upper={float(transport_upper):.12f}, "
       f"chain={float(cell['chain']):.6f}")
print("ALL CHECKS PASSED")
