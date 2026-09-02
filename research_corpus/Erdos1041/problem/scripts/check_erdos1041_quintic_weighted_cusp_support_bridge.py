#!/usr/bin/env python3
"""Exact boundary test for fixed-strip support transport at u=10^-3.

This is an exact method falsifier, not an Erdős-1041 sign certificate.  It
reconstructs the three positive-cusp mu=-10 carrier sheets, runs the current
square-root-free support engine, and proves that its weak-sheet upper bound is
already positive at the zero-width endpoint.  Hence parameter bisection alone
cannot turn this particular support schedule into a collar extension.
"""

from __future__ import annotations

from fractions import Fraction as Fr
import importlib.util
import multiprocessing as multiprocessing
from pathlib import Path
import sys

import mpmath as mp
import sympy as sp


HERE = Path(__file__).resolve().parent
LIB = HERE / "lib_erdos1041_support_engine.py"
SPEC = importlib.util.spec_from_file_location("weighted_cusp_support_engine", LIB)
SUPPORT = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules[SPEC.name] = SUPPORT
SPEC.loader.exec_module(SUPPORT)
CB, cb, cb_pt = SUPPORT.CB, SUPPORT.cb, SUPPORT.cb_pt
mp.mp.dps = 70


def report(name: str, ok: bool, detail: str = "") -> None:
    print(("PASS " if ok else "FAIL ") + name + ((" :: " + detail) if detail else ""))
    if not ok:
        raise AssertionError(name)


BASE_KRAWCZYK = SUPPORT.krawczyk


def wide_krawczyk(coeffs, dcoeffs, target, centre, radius, *, iters=25):
    for candidate in (
        radius,
        Fr(1, 10**12), Fr(1, 10**10), Fr(1, 10**8), Fr(1, 10**6),
        Fr(1, 10**4), Fr(1, 1000), Fr(1, 100), Fr(1, 10), Fr(1),
    ):
        if candidate < radius:
            continue
        result = BASE_KRAWCZYK(
            coeffs, dcoeffs, target, centre, candidate, iters=iters
        )
        if result is not None:
            return result
    return None


SUPPORT.krawczyk = wide_krawczyk


u, z = sp.symbols("u z")
kappa = u**3
mu = -10 + u*z
A = 4*(mu+4)
B = -sp.Rational(12, 25)*(3*mu**3-5*mu**2-100*mu-200)
C = sp.Rational(4, 3125)*(mu+10)**3*(27*mu**2+140*mu+200)
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


def fr(value):
    value = sp.Rational(value)
    return Fr(int(value.p), int(value.q))


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


def exact_abs_ball(value):
    lo = SUPPORT.wall.sqrt_lo(value.cabs2())-value.r
    hi = SUPPORT.wall.sqrt_hi(value.cabs2())+value.r
    if lo <= 0:
        raise RuntimeError("direction tube meets zero")
    return CB((lo+hi)/2, 0, SUPPORT.wall.snap_up((hi-lo)/2), _raw=True)


def support_cell(task):
    branch, u_lo, u_hi = task
    u_mid_exact = (u_lo+u_hi)/2
    u_ball = CB(u_mid_exact, 0, (u_hi-u_lo)/2, _raw=True)
    u_mid = mp.mpf(u_mid_exact.numerator)/u_mid_exact.denominator
    scout = mp.findroot(
        lambda zz: HFUN(u_mid, zz), LIMIT_ROOTS[branch],
        tol=mp.mpf("1e-55"), maxsteps=100,
    )
    root_ball = None
    for radius in (Fr(1,100), Fr(1,20), Fr(1,10), Fr(1,2), Fr(1), Fr(2)):
        root_ball = wide_krawczyk(
            coeffs_in_z(H, u_ball), coeffs_in_z(HZ, u_ball), cb(0),
            cb_pt(scout), radius, iters=30,
        )
        if root_ball is not None:
            break
    if root_ball is None or root_ball.b-root_ball.r <= 0:
        raise RuntimeError(f"carrier failure branch={branch}")

    mu_ball = cb(-10)+u_ball*root_ball
    pair_sum = eval_rational(P, u_ball, root_ball)
    third = -cb(4)*(mu_ball+cb(4))-pair_sum
    cross = pair_sum.conj()*third
    if abs(cross.b) <= cross.r:
        raise RuntimeError(f"wall chamber failure branch={branch}")
    epsilon = -1 if cross.b > 0 else 1
    ray_ball = -cb(epsilon)*cb(0,1)*pair_sum*exact_abs_ball(pair_sum).inv()
    mu_scout = -10+u_mid*scout
    pair_scout = mp.mpc(
        mp.mpf(pair_sum.a.numerator)/pair_sum.a.denominator,
        mp.mpf(pair_sum.b.numerator)/pair_sum.b.denominator,
    )
    ray_scout = -epsilon*1j*pair_scout/abs(pair_scout)
    arms = [
        SUPPORT.certified_arm(
            SUPPORT.CB(mu_ball.a,mu_ball.b,mu_ball.r,_raw=True),
            SUPPORT.CB(ray_ball.a,ray_ball.b,ray_ball.r,_raw=True),
            mu_scout, ray_scout, sign, cells=1024,
        )
        for sign in (+1,-1)
    ]
    upper = SUPPORT.wall.snap_up(arms[0][0]+arms[1][0])
    return {
        "branch": branch,
        "u_lo": u_lo,
        "u_hi": u_hi,
        "upper": upper,
        "za": root_ball.a,
        "zb": root_ball.b,
        "zr": root_ball.r,
        "direct": tuple(arm[1]["direct_cells"] for arm in arms),
        "monotone": tuple(arm[1]["monotone_cells"] for arm in arms),
    }


def disks_disjoint(left, right):
    return (
        (left["za"]-right["za"])**2+(left["zb"]-right["zb"])**2
        > (left["zr"]+right["zr"])**2
    )


def run_parallel(tasks):
    with multiprocessing.get_context("fork").Pool(processes=3) as pool:
        return pool.map(support_cell, tasks)


U0 = Fr(1,1000)
U1 = Fr(1001,1000000)
micro = run_parallel([(branch,U0,U1) for branch in range(3)])
point = support_cell((1,U0,U0))

report(
    "SB1 microcell has three distinct upper carrier sheets",
    all(disks_disjoint(micro[i],micro[j]) for i in range(3) for j in range(i)),
)
report(
    "SB2 strong cusp sheets pass square-root-free support",
    micro[0]["upper"] < 0 and micro[2]["upper"] < 0,
    f"uppers={float(micro[0]['upper']):.9f},{float(micro[2]['upper']):.9f}",
)
report(
    "SB3 weak cusp sheet fails on width 10^-6",
    micro[1]["upper"] > 0,
    f"upper={float(micro[1]['upper']):.9f}, direct={micro[1]['direct']}",
)
report(
    "SB4 obstruction persists at the exact endpoint",
    point["upper"] > 0,
    f"upper={float(point['upper']):.9f}, direct={point['direct']}",
)
report(
    "SB5 parameter refinement alone cannot repair this schedule",
    point["u_lo"] == point["u_hi"] == U0 and point["upper"] > 0,
)

print("EXACT METHOD BOUNDARY: current support schedule gives no five-sheet extension beyond u=10^-3.")
print("ALL CHECKS PASSED")
