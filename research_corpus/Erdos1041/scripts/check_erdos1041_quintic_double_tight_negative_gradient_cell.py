#!/usr/bin/env python3
"""Exact macroscopic affine/gradient cell on the negative ordered branch."""

from __future__ import annotations

from fractions import Fraction as Fr
import importlib.util
from pathlib import Path
import sys

import mpmath as mp


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "erdos1041_negative_gradient_affine_engine",
    HERE / "lib_erdos1041_affine_tcell_engine.py",
)
ENGINE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = ENGINE
assert SPEC.loader is not None
SPEC.loader.exec_module(ENGINE)


def report(name: str, ok: bool, detail: str = "") -> None:
    print(("PASS " if ok else "FAIL ") + name + ((" :: " + detail) if detail else ""))
    if not ok:
        raise AssertionError(name)


mp.mp.dps = 90
T0 = Fr(-1, 1000)
RADIUS = Fr(1, 90_000)
A_SEED = mp.mpc("32.612244055311", "43.090878126976")
MU_SEED = mp.mpc("-12.476212477852", "2.472960355017")

cell = ENGINE.certify_affine_cell(
    T0,
    RADIUS,
    A_SEED,
    MU_SEED,
    correction_a=Fr(1, 1000),
    correction_mu=Fr(1, 10000),
    support_cells=0,
)
report(
    "NGC1 affine Krawczyk self-map",
    cell.krawczyk_a < Fr(1, 1000) and cell.krawczyk_mu < Fr(1, 10000),
    f"Ka<{float(cell.krawczyk_a):.12g}, Kmu<{float(cell.krawczyk_mu):.12g}",
)
report(
    "NGC2 regular wall chamber",
    cell.det_lower > 10_000 and cell.cross_margin > 1_700,
    f"|det|>{float(cell.det_lower):.6f}, cross>{float(cell.cross_margin):.6f}",
)
report(
    "NGC3 controlled carrier tube",
    cell.mu_box.r < Fr(1, 50) and cell.w_box.r < Fr(1, 200),
    f"rad(mu)<{float(cell.mu_box.r):.12g}, rad(w)<{float(cell.w_box.r):.12g}",
)

tC = ENGINE.CB(T0, 0, RADIUS, _raw=True)
a_radius = ENGINE.CB_MOD.snap_up(cell.a1.abs_hi() * RADIUS + cell.correction_a)
aC = ENGINE.CB(cell.a0.a, cell.a0.b, a_radius, _raw=True)
muC = cell.mu_box
J = ENGINE.jacobian(tC, aC, muC)
det = J[0][0] * J[1][1] - J[0][1] * J[1][0]
Ft = ENGINE.t_derivative(tC, aC, muC)
a_t = -(J[1][1] * Ft[0] - J[0][1] * Ft[1]) / det
mu_t = -(-J[1][0] * Ft[0] + J[0][0] * Ft[1]) / det
p = (ENGINE.cb(1) + tC) * aC
p_t = aC + (ENGINE.cb(1) + tC) * a_t
logp_t = p_t / p
phi_t = abs(logp_t.b) + logp_t.r
report(
    "NGC4 exact parameter derivatives",
    a_t.abs_hi() < 12_000 and mu_t.abs_hi() < 1_800 and phi_t < 130,
    f"|a_t|<{float(a_t.abs_hi()):.6f}, |mu_t|<{float(mu_t.abs_hi()):.6f}, "
    f"|phi_t|<{float(phi_t):.6f}",
)

SUPPORT = ENGINE.SUPPORT
KAPPA0 = Fr(-1000, 1_000_001)
mu_point_C, w_point_C, mu_point, w_point, _ = SUPPORT.certified_carrier_input(
    KAPPA0, scout_mu=MU_SEED
)
point = SUPPORT.wall.certified_excess(
    mu_point,
    w_point,
    muC=mu_point_C,
    wC=w_point_C,
    k=20,
    s0=Fr(1, 10**10),
    ratio=0.06,
    msub=6,
    eps_step=Fr(1, 10**7),
    want_grad=True,
)
report(
    "NGC5 exact centre excess",
    point["hi"] < -Fr(1, 100),
    f"E0<{point['hi_f']:.12f}<-1/100",
)

mu_support = SUPPORT.CB(cell.mu_box.a, cell.mu_box.b, cell.mu_box.r, _raw=True)
w_support = SUPPORT.CB(cell.w_box.a, cell.w_box.b, cell.w_box.r, _raw=True)
tube = SUPPORT.wall.certified_excess(
    cell.mu_scout,
    cell.ray_scout,
    muC=mu_support,
    wC=w_support,
    k=20,
    s0=Fr(1, 10**10),
    ratio=0.06,
    msub=6,
    eps_step=Fr(1, 10**7),
    want_grad=True,
    gradient_only=True,
)
transport_lipschitz = tube["grad_mu_q"] * mu_t.abs_hi() + tube["grad_phi_q"] * phi_t
transport_upper = point["hi"] + transport_lipschitz * RADIUS
report(
    "NGC6 exact whole-cell gradient transport",
    tube["grad_mu_q"] < Fr(1, 2)
    and tube["grad_phi_q"] < 10
    and transport_lipschitz < 2_000
    and transport_upper < -Fr(1, 10),
    f"Gmu<{tube['grad_mu']:.6f}, Gphi<{tube['grad_phi']:.6f}, "
    f"L<{float(transport_lipschitz):.6f}, E<{float(transport_upper):.12f}",
)

report(
    "NGC7 macroscopic rational interval and seed overlap",
    cell.left == Fr(-91, 90_000)
    and cell.right == Fr(-89, 90_000)
    and cell.left < Fr(-101, 100_000)
    and cell.left < Fr(-100_001, 100_000_000)
    and Fr(-99_999, 100_000_000) < cell.right,
    f"[{cell.left},{cell.right}], width={cell.right-cell.left}",
)

print("ALL CHECKS PASSED")
