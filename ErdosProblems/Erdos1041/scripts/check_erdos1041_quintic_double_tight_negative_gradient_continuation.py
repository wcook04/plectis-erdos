#!/usr/bin/env python3
"""Exact connected negative-t continuation from -0.00121 through -0.002."""

from __future__ import annotations

from fractions import Fraction as Fr
import importlib.util
from pathlib import Path
import sys

import mpmath as mp


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "erdos1041_negative_gradient_continuation_engine",
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


def parameter_derivatives(cell):
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
    return a_t.abs_hi(), mu_t.abs_hi(), phi_t


def certify_gradient_sign(cell):
    kappa = cell.t0 / (1 + cell.t0 * cell.t0)
    mu_point_C, w_point_C, mu_point, w_point, _ = SUPPORT.certified_carrier_input(
        kappa, scout_mu=cell.mu_scout
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
    mu_support = SUPPORT.CB(
        cell.mu_box.a, cell.mu_box.b, cell.mu_box.r, _raw=True
    )
    w_support = SUPPORT.CB(
        cell.w_box.a, cell.w_box.b, cell.w_box.r, _raw=True
    )
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
    a_t, mu_t, phi_t = parameter_derivatives(cell)
    lipschitz = tube["grad_mu_q"] * mu_t + tube["grad_phi_q"] * phi_t
    upper = point["hi"] + lipschitz * cell.radius
    return point, tube, lipschitz, upper


mp.mp.dps = 90
A_SEED = mp.mpc("32.612244055311", "43.090878126976")
MU_SEED = mp.mpc("-12.476212477852", "2.472960355017")

# Replay the last already-proved cell only as a carrier box for exact gluing.
previous = ENGINE.certify_affine_cell(
    Fr(-118, 100_000),
    Fr(3, 100_000),
    A_SEED,
    MU_SEED,
    correction_a=Fr(1, 50),
    correction_mu=Fr(1, 250),
    support_cells=0,
)

centres = tuple(Fr(-n, 100_000) for n in range(125, 198, 8))
RADIUS = Fr(1, 20_000)
CORRECTION_A = Fr(1, 20)
CORRECTION_MU = Fr(1, 100)
cells = []
a_seed, mu_seed = previous.a_scout, previous.mu_scout
for index, centre in enumerate(centres):
    cell = ENGINE.certify_affine_cell(
        centre,
        RADIUS,
        a_seed,
        mu_seed,
        correction_a=CORRECTION_A,
        correction_mu=CORRECTION_MU,
        support_cells=0,
    )
    cells.append(cell)
    a_seed, mu_seed = cell.a_scout, cell.mu_scout
    report(
        f"NGCO{1 + 3*index} affine Krawczyk cell {index}",
        cell.krawczyk_a < CORRECTION_A
        and cell.krawczyk_mu < CORRECTION_MU
        and cell.det_lower > 11_000,
        f"[{cell.left},{cell.right}], Ka/Ra<{float(cell.krawczyk_a/CORRECTION_A):.6g}, "
        f"Kmu/Rmu<{float(cell.krawczyk_mu/CORRECTION_MU):.6g}, "
        f"det>{float(cell.det_lower):.3f}",
    )
    report(
        f"NGCO{2 + 3*index} wall chamber cell {index}",
        cell.cross_margin > 1_700 and cell.w_box.r < Fr(1, 50),
        f"cross>{float(cell.cross_margin):.3f}, rad(w)<{float(cell.w_box.r):.6f}",
    )
    point, tube, lipschitz, upper = certify_gradient_sign(cell)
    cell.sign_data = (point, tube, lipschitz, upper)
    report(
        f"NGCO{3 + 3*index} exact gradient sign cell {index}",
        upper < -Fr(1, 100),
        f"E0<{point['hi_f']:.12f}, Gmu<{tube['grad_mu']:.6f}, "
        f"Gphi<{tube['grad_phi']:.6f}, L<{float(lipschitz):.3f}, "
        f"E<{float(upper):.12f}",
    )

all_cells = [previous] + cells
match_points = [Fr(-241, 200_000)] + [
    Fr(-(129 + 8*j), 100_000) for j in range(9)
]
overlaps = [
    ENGINE.certify_overlap(all_cells[j], all_cells[j + 1], match_points[j])
    for j in range(10)
]
report(
    "NGCO31 ten exact overlap-uniqueness boxes",
    all(
        overlap["krawczyk_a"] < overlap["radius_a"]
        and overlap["krawczyk_mu"] < overlap["radius_mu"]
        for overlap in overlaps
    ),
    "matches at " + ", ".join(str(overlap["t"]) for overlap in overlaps),
)
report(
    "NGCO32 connected reach through t=-0.002",
    all(all_cells[j + 1].right > all_cells[j].left for j in range(10))
    and cells[-1].left == Fr(-101, 50_000)
    and cells[-1].left < Fr(-1, 500) < cells[-1].right,
    f"continuation union [{cells[-1].left},{previous.right}]",
)

print("ALL CHECKS PASSED")
