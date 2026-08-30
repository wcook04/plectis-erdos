#!/usr/bin/env python3
"""Exact five-sheet replay on a macroscopic negative ordered t-cell."""

from __future__ import annotations

from fractions import Fraction as Fr
import importlib.util
from pathlib import Path
import sys

import mpmath as mp


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "erdos1041_complete_negative_affine_engine",
    HERE / "lib_erdos1041_affine_tcell_engine.py",
)
ENGINE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = ENGINE
assert SPEC.loader is not None
SPEC.loader.exec_module(ENGINE)
SUPPORT = ENGINE.SUPPORT


def report(name: str, ok: bool, detail: str = "") -> None:
    print(("PASS " if ok else "FAIL ") + name + ((" :: " + detail) if detail else ""))
    if not ok:
        raise AssertionError(name)


def mp_pair_sum(kappa: Fr, mu: mp.mpc) -> mp.mpc:
    k = mp.mpf(kappa.numerator) / kappa.denominator
    A, B, C = ENGINE._mp_abc(mu)
    D = A**2 * k - B * (1 + k)
    return (C * (1 + k) ** 2 - A * B * k**2) / (k * D)


def carrier_mu_scout(kappa: Fr, seed: mp.mpc) -> mp.mpc:
    """Floating Newton scout for the exact univariate carrier root."""
    k = mp.mpf(kappa.numerator) / kappa.denominator

    def value(mu: mp.mpc) -> mp.mpc:
        A, B, C = ENGINE._mp_abc(mu)
        return (
            C**2 * (1 + k) ** 3
            - A * B * C * k * (1 + k) * (1 + 4 * k)
            + (A**3 * C + B**3) * k**2 * (1 + 2 * k)
            - A**2 * B**2 * k**3
        )

    mu = mp.mpc(seed)
    for _ in range(30):
        step = value(mu) / mp.diff(value, mu)
        mu -= step
        if abs(step) < mp.mpf("1e-70"):
            break
    return mu


def cell_derivatives(cell: ENGINE.AffineCell) -> tuple:
    tC = ENGINE.CB(cell.t0, 0, cell.radius, _raw=True)
    a_radius = ENGINE.CB_MOD.snap_up(
        cell.a1.abs_hi() * cell.radius + cell.correction_a
    )
    aC = ENGINE.CB(cell.a0.a, cell.a0.b, a_radius, _raw=True)
    J = ENGINE.jacobian(tC, aC, cell.mu_box)
    det = J[0][0] * J[1][1] - J[0][1] * J[1][0]
    Ft = ENGINE.t_derivative(tC, aC, cell.mu_box)
    a_t = -(J[1][1] * Ft[0] - J[0][1] * Ft[1]) / det
    mu_t = -(-J[1][0] * Ft[0] + J[0][0] * Ft[1]) / det
    p = (ENGINE.cb(1) + tC) * aC
    p_t = aC + (ENGINE.cb(1) + tC) * a_t
    logp_t = p_t / p
    phi_t = abs(logp_t.b) + logp_t.r
    return a_t, mu_t, phi_t


mp.mp.dps = 90
T0 = Fr(-1, 1000)
RADIUS = Fr(1, 25000)
KAPPA0 = Fr(-1000, 1000001)

rows = []
for index, initial_mu in enumerate(SUPPORT.FIBRE_SCOUTS[Fr(-1, 1000)]):
    initial_mu = carrier_mu_scout(KAPPA0, initial_mu)
    mu_point_C, w_point_C, mu_point, w_point, carrier = (
        SUPPORT.certified_carrier_input(KAPPA0, scout_mu=initial_mu)
    )
    a_seed = mp_pair_sum(KAPPA0, mu_point) / (1 - mp.mpf(1) / 1000)
    cell = ENGINE.certify_affine_cell(
        T0,
        RADIUS,
        a_seed,
        mu_point,
        correction_a=Fr(1, 100) if index < 3 else Fr(1, 10**7),
        correction_mu=Fr(1, 1000) if index < 3 else Fr(1, 10**8),
        support_cells=0,
    )
    a_t, mu_t, phi_t = cell_derivatives(cell)
    point = SUPPORT.wall.certified_excess(
        mu_point, w_point, muC=mu_point_C, wC=w_point_C, k=20,
        s0=Fr(1, 10**10), ratio=0.06, msub=6,
        eps_step=Fr(1, 10**7), want_grad=True,
    )
    mu_tube = SUPPORT.CB(cell.mu_box.a, cell.mu_box.b, cell.mu_box.r, _raw=True)
    w_tube = SUPPORT.CB(cell.w_box.a, cell.w_box.b, cell.w_box.r, _raw=True)
    tube = SUPPORT.wall.certified_excess(
        cell.mu_scout, cell.ray_scout, muC=mu_tube, wC=w_tube, k=20,
        s0=Fr(1, 10**10), ratio=0.06, msub=6,
        eps_step=Fr(1, 10**7), want_grad=True, gradient_only=True,
    )
    L = tube["grad_mu_q"] * mu_t.abs_hi() + tube["grad_phi_q"] * phi_t
    upper = point["hi"] + L * RADIUS
    rows.append((cell, point, tube, a_t, mu_t, phi_t, L, upper, carrier))
    report(
        f"CNC{1 + 3*index} sheet {index} carrier regular",
        cell.krawczyk_a < cell.correction_a
        and cell.krawczyk_mu < cell.correction_mu
        and cell.det_lower > 0 and cell.cross_margin > 0,
        f"Ka={float(cell.krawczyk_a):.4g}, Kmu={float(cell.krawczyk_mu):.4g}, "
        f"det>{float(cell.det_lower):.4g}",
    )
    report(
        f"CNC{2 + 3*index} sheet {index} exact centre sign",
        point["hi"] < -Fr(1, 100),
        f"E0<{point['hi_f']:.9f}",
    )
    report(
        f"CNC{3 + 3*index} sheet {index} whole-cell sign",
        upper < -Fr(1, 100),
        f"L<{float(L):.6g}, E<{float(upper):.9f}",
    )

report(
    "CNC16 complete upper-sheet exhaustion",
    all(cell.mu_box.b - cell.mu_box.r > 0 for cell, *_ in rows)
    and all(
        (rows[i][0].mu_box - rows[j][0].mu_box).abs_lo() > 0
        for i in range(len(rows)) for j in range(i)
    ),
    "five pairwise-disjoint upper carrier tubes",
)
report(
    "CNC17 common macroscopic interval",
    all(cell.left == Fr(-13, 12500) and cell.right == Fr(-3, 3125)
        for cell, *_ in rows)
    and all(row[7] < -Fr(1, 100) for row in rows),
    "all five sheets negative on [-13/12500,-3/3125]",
)

print("ALL CHECKS PASSED")
