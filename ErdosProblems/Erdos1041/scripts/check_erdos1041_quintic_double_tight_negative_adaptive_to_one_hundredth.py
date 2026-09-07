#!/usr/bin/env python3
"""Exact adaptive negative-t continuation from -0.00202 toward -0.01."""

from __future__ import annotations

from fractions import Fraction as Fr
from concurrent.futures import ProcessPoolExecutor
import importlib.util
import multiprocessing
from pathlib import Path
import sys

import mpmath as mp


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "erdos1041_negative_adaptive_one_hundredth_engine",
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


A_SEED = mp.mpc("32.612244055311", "43.090878126976")
MU_SEED = mp.mpc("-12.476212477852", "2.472960355017")


def sign_worker(args):
    """Rebuild one already-scouted branch cell and return serializable bounds."""
    centre, radius, corr_a, corr_mu, ar, ai, mr, mi = args
    cell = ENGINE.certify_affine_cell(
        centre,
        radius,
        mp.mpc(ar, ai),
        mp.mpc(mr, mi),
        correction_a=corr_a,
        correction_mu=corr_mu,
        support_cells=0,
    )
    point, tube, lipschitz, upper = certify_gradient_sign(cell)
    return {
        "point_hi_f": point["hi_f"],
        "grad_mu": tube["grad_mu"],
        "grad_phi": tube["grad_phi"],
        "lipschitz": lipschitz,
        "upper": upper,
    }


def main() -> None:
    mp.mp.dps = 90
    # Last old cell, replayed only to make the first overlap check standalone.
    previous = ENGINE.certify_affine_cell(
        Fr(-197, 100_000),
        Fr(1, 20_000),
        A_SEED,
        MU_SEED,
        correction_a=Fr(1, 20),
        correction_mu=Fr(1, 100),
        support_cells=0,
    )

    # Four adaptive scales.  Neighbouring centres are closer than the sum of
    # their radii, including at all three scale transitions.
    specifications = []
    specifications += [
        (Fr(-(207 + 10*k), 100_000), Fr(6, 100_000), Fr(1, 10), Fr(1, 50))
        for k in range(10)
    ]
    specifications += [
        (Fr(-(308 + 14*k), 100_000), Fr(8, 100_000), Fr(3, 20), Fr(3, 100))
        for k in range(7)
    ]
    specifications += [
        (Fr(-(408 + 18*k), 100_000), Fr(10, 100_000), Fr(1, 5), Fr(1, 25))
        for k in range(11)
    ]
    specifications += [
        (Fr(-(608 + 22*k), 100_000), Fr(12, 100_000), Fr(3, 10), Fr(3, 50))
        for k in range(19)
    ]

    cells = []
    worker_args = []
    a_seed, mu_seed = previous.a_scout, previous.mu_scout
    for index, (centre, radius, corr_a, corr_mu) in enumerate(specifications):
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
            f"NGA{1 + 2*index} affine Krawczyk cell {index}",
            cell.krawczyk_a < corr_a
            and cell.krawczyk_mu < corr_mu
            and cell.det_lower > 10_000,
            f"[{cell.left},{cell.right}], Ka/Ra<{float(cell.krawczyk_a/corr_a):.6g}, "
            f"Kmu/Rmu<{float(cell.krawczyk_mu/corr_mu):.6g}, "
            f"det>{float(cell.det_lower):.3f}",
        )
        report(
            f"NGA{2 + 2*index} wall chamber cell {index}",
            cell.cross_margin > 2_000 and cell.w_box.r < Fr(1, 40),
            f"cross>{float(cell.cross_margin):.3f}, rad(w)<{float(cell.w_box.r):.6f}",
        )
        worker_args.append((
            centre,
            radius,
            corr_a,
            corr_mu,
            str(cell.a_scout.real),
            str(cell.a_scout.imag),
            str(cell.mu_scout.real),
            str(cell.mu_scout.imag),
        ))

    # The expensive arc integrations are independent exact computations.  A
    # fixed four-process pool changes wall time only, never arithmetic or gates.
    context = multiprocessing.get_context("fork")
    with ProcessPoolExecutor(max_workers=4, mp_context=context) as pool:
        signs = list(pool.map(sign_worker, worker_args))
    for index, sign in enumerate(signs):
        report(
            f"NGA{2*len(cells) + 1 + index} exact gradient sign cell {index}",
            sign["upper"] < 0,
            f"E0<{sign['point_hi_f']:.12f}, Gmu<{sign['grad_mu']:.6f}, "
            f"Gphi<{sign['grad_phi']:.6f}, L<{float(sign['lipschitz']):.3f}, "
            f"E<{float(sign['upper']):.12f}",
        )

    all_cells = [previous] + cells
    match_points = [
        (max(all_cells[j].left, all_cells[j + 1].left)
         + min(all_cells[j].right, all_cells[j + 1].right)) / 2
        for j in range(len(cells))
    ]
    overlaps = [
        ENGINE.certify_overlap(all_cells[j], all_cells[j + 1], match_points[j])
        for j in range(len(cells))
    ]
    report(
        f"NGA{3*len(cells)+1} exact overlap uniqueness",
        all(
            overlap["krawczyk_a"] < overlap["radius_a"]
            and overlap["krawczyk_mu"] < overlap["radius_mu"]
            for overlap in overlaps
        ),
        f"{len(overlaps)} matching boxes",
    )
    report(
        f"NGA{3*len(cells)+2} connected reach through t=-0.01",
        all(all_cells[j + 1].right > all_cells[j].left
            for j in range(len(cells)))
        and cells[-1].left == Fr(-127, 12_500)
        and cells[-1].left < Fr(-1, 100) < cells[-1].right,
        f"continuation union [{cells[-1].left},{previous.right}]",
    )
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
