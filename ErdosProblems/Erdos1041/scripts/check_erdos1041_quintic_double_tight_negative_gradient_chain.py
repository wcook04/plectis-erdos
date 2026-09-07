#!/usr/bin/env python3
"""Exact connected negative-t affine/gradient chain through t=-0.0012."""

from __future__ import annotations

from fractions import Fraction as Fr
import importlib.util
from pathlib import Path
import sys

import mpmath as mp


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "erdos1041_negative_gradient_chain_engine",
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
    return {
        "point": point,
        "tube": tube,
        "a_t": a_t,
        "mu_t": mu_t,
        "phi_t": phi_t,
        "lipschitz": lipschitz,
        "upper": upper,
    }


mp.mp.dps = 90
A_SEED = mp.mpc("32.612244055311", "43.090878126976")
MU_SEED = mp.mpc("-12.476212477852", "2.472960355017")

# Cell zero is the already-proved macroscopic seed.  It is replayed here only
# as a carrier box so that the overlap uniqueness proof is standalone.
specifications = (
    (Fr(-1, 1000), Fr(1, 90_000), Fr(1, 1000), Fr(1, 10_000), False),
    (Fr(-103, 100_000), Fr(3, 100_000), Fr(1, 50), Fr(1, 250), True),
    (Fr(-108, 100_000), Fr(3, 100_000), Fr(1, 50), Fr(1, 250), True),
    (Fr(-113, 100_000), Fr(3, 100_000), Fr(1, 50), Fr(1, 250), True),
    (Fr(-118, 100_000), Fr(3, 100_000), Fr(1, 50), Fr(1, 250), True),
)

cells = []
a_seed, mu_seed = A_SEED, MU_SEED
for index, (centre, radius, corr_a, corr_mu, needs_sign) in enumerate(specifications):
    cell = ENGINE.certify_affine_cell(
        centre,
        radius,
        a_seed,
        mu_seed,
        correction_a=corr_a,
        correction_mu=corr_mu,
        support_cells=0,
    )
    cells.append(cell)
    a_seed, mu_seed = cell.a_scout, cell.mu_scout
    report(
        f"NGCH{1 + 3*index} affine Krawczyk cell {index}",
        cell.krawczyk_a < corr_a
        and cell.krawczyk_mu < corr_mu
        and cell.det_lower > 9_000,
        f"[{cell.left},{cell.right}], Ka/Ra<{float(cell.krawczyk_a/corr_a):.6g}, "
        f"Kmu/Rmu<{float(cell.krawczyk_mu/corr_mu):.6g}, "
        f"det>{float(cell.det_lower):.6f}",
    )
    report(
        f"NGCH{2 + 3*index} wall chamber cell {index}",
        cell.cross_margin > 1_600 and cell.w_box.r < Fr(1, 25),
        f"cross>{float(cell.cross_margin):.6f}, rad(w)<{float(cell.w_box.r):.6f}",
    )
    if needs_sign:
        sign = certify_gradient_sign(cell)
        cell.sign_data = sign
        report(
            f"NGCH{3 + 3*index} exact gradient sign cell {index}",
            sign["upper"] < -Fr(3, 50),
            f"E0<{sign['point']['hi_f']:.12f}, "
            f"Gmu<{sign['tube']['grad_mu']:.6f}, "
            f"Gphi<{sign['tube']['grad_phi']:.6f}, "
            f"L<{float(sign['lipschitz']):.6f}, "
            f"E<{float(sign['upper']):.12f}",
        )
    else:
        report(
            f"NGCH{3 + 3*index} seed-cell containment",
            cell.left == Fr(-91, 90_000) and cell.right == Fr(-89, 90_000),
        )

match_points = (
    Fr(-201, 200_000),
    Fr(-211, 200_000),
    Fr(-221, 200_000),
    Fr(-231, 200_000),
)
overlaps = [
    ENGINE.certify_overlap(cells[j], cells[j + 1], match_points[j])
    for j in range(4)
]
report(
    "NGCH16 four exact overlap-uniqueness boxes",
    all(
        overlap["krawczyk_a"] < overlap["radius_a"]
        and overlap["krawczyk_mu"] < overlap["radius_mu"]
        for overlap in overlaps
    ),
    "matches at " + ", ".join(str(overlap["t"]) for overlap in overlaps),
)
report(
    "NGCH17 connected reach through t=-0.0012",
    all(cells[j + 1].right > cells[j].left for j in range(4))
    and cells[-1].left == Fr(-121, 100_000)
    and cells[-1].left < Fr(-3, 2500) < cells[-1].right,
    f"connected union [{cells[-1].left},{cells[0].right}]",
)

print("ALL CHECKS PASSED")
