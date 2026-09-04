#!/usr/bin/env python3
"""Exact replay of the positive double-tight continuation beyond t=1/100."""

from __future__ import annotations

from fractions import Fraction as Fr
import importlib.util
from pathlib import Path
import sys

import mpmath as mp


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "erdos1041_positive_decade_affine_engine",
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


def exact_derivatives(cell: ENGINE.AffineCell) -> tuple[Fr, Fr]:
    tC = ENGINE.CB(cell.t0, 0, cell.radius, _raw=True)
    ar = ENGINE.CB_MOD.snap_up(cell.a1.abs_hi() * cell.radius + cell.correction_a)
    aC = ENGINE.CB(cell.a0.a, cell.a0.b, ar, _raw=True)
    J = ENGINE.jacobian(tC, aC, cell.mu_box)
    det = J[0][0] * J[1][1] - J[0][1] * J[1][0]
    Ft = ENGINE.t_derivative(tC, aC, cell.mu_box)
    a_t = -(J[1][1] * Ft[0] - J[0][1] * Ft[1]) / det
    mu_t = -(-J[1][0] * Ft[0] + J[0][0] * Ft[1]) / det
    p = (ENGINE.cb(1) + tC) * aC
    p_t = aC + (ENGINE.cb(1) + tC) * a_t
    z = p_t / p
    return mu_t.abs_hi(), abs(z.b) + z.r


def certify_sign(cell: ENGINE.AffineCell) -> tuple[Fr, Fr, Fr, Fr, Fr]:
    kappa = cell.t0 / (1 + cell.t0 * cell.t0)
    mu0C, w0C, mu0, w0, _ = SUPPORT.certified_carrier_input(
        kappa, scout_mu=cell.mu_scout
    )
    point = SUPPORT.wall.certified_excess(
        mu0,
        w0,
        muC=mu0C,
        wC=w0C,
        k=20,
        s0=Fr(1, 10**10),
        ratio=0.06,
        msub=6,
        eps_step=Fr(1, 10**7),
        want_grad=True,
    )
    muC = SUPPORT.CB(cell.mu_box.a, cell.mu_box.b, cell.mu_box.r, _raw=True)
    wC = SUPPORT.CB(cell.w_box.a, cell.w_box.b, cell.w_box.r, _raw=True)
    tube = SUPPORT.wall.certified_excess(
        cell.mu_scout,
        cell.ray_scout,
        muC=muC,
        wC=wC,
        k=20,
        s0=Fr(1, 10**10),
        ratio=0.06,
        msub=6,
        eps_step=Fr(1, 10**7),
        want_grad=True,
        gradient_only=True,
    )
    mu_t, phi_t = exact_derivatives(cell)
    lip = tube["grad_mu_q"] * mu_t + tube["grad_phi_q"] * phi_t
    upper = point["hi"] + lip * cell.radius
    return point["hi"], tube["grad_mu_q"], tube["grad_phi_q"], lip, upper


def macro_sign(
    cells: list[ENGINE.AffineCell],
    centres: list[Fr],
    sheet: int,
    block_size: int,
) -> list[Fr]:
    """Prove signs on blocks by exact parameter-hull gradient transport."""
    uppers = []
    for lo in range(0, len(cells), block_size):
        block = cells[lo : lo + block_size]
        middle = lo + len(block) // 2
        cell0 = cells[middle]
        t0 = centres[middle]
        kappa = t0 / (1 + t0 * t0)
        mu0C, w0C, mu0, w0, _ = SUPPORT.certified_carrier_input(
            kappa, scout_mu=cell0.mu_scout
        )
        point = SUPPORT.wall.certified_excess(
            mu0,
            w0,
            muC=mu0C,
            wC=w0C,
            k=20,
            s0=Fr(1, 10**10),
            ratio=0.06,
            msub=6,
            eps_step=Fr(1, 10**7),
            want_grad=True,
        )
        mu_mid, w_mid = mu0C.mid(), w0C.mid()
        mu_radius = max(
            (
                SUPPORT.CB(c.mu_box.a, c.mu_box.b, c.mu_box.r, _raw=True)
                - mu_mid
            ).abs_hi()
            for c in block
        )
        w_radius = max(
            (
                SUPPORT.CB(c.w_box.a, c.w_box.b, c.w_box.r, _raw=True)
                - w_mid
            ).abs_hi()
            for c in block
        )
        if w_radius >= 1:
            raise RuntimeError("macro phase hull reaches the origin")
        mu_hull = SUPPORT.CB(mu_mid.a, mu_mid.b, mu_radius, _raw=True)
        w_hull = SUPPORT.CB(w_mid.a, w_mid.b, w_radius, _raw=True)
        tube = SUPPORT.wall.certified_excess(
            cell0.mu_scout,
            cell0.ray_scout,
            muC=mu_hull,
            wC=w_hull,
            k=20,
            s0=Fr(1, 10**10),
            ratio=0.06,
            msub=6,
            eps_step=Fr(1, 10**7),
            want_grad=True,
            gradient_only=True,
        )
        # For unit directions, chord distance d gives
        # |Delta phi| <= 2d/(1-d), a deliberately coarse rational majorant.
        phase_radius = 2 * w_radius / (1 - w_radius)
        upper = (
            point["hi"]
            + tube["grad_mu_q"] * mu_radius
            + tube["grad_phi_q"] * phase_radius
        )
        uppers.append(upper)
        report(
            f"PDC macro sign sheet {sheet} block {lo}:{lo+len(block)}",
            upper < 0,
            f"E0<{point['hi_f']:.9f}, rad(mu)<{float(mu_radius):.6g}, "
            f"rad(w)<{float(w_radius):.6g}, E<{float(upper):.9f}",
        )
    return uppers


mp.mp.dps = 90
A_SEED = mp.mpc(
    "6.81037351291131349533675529051033966781454967749276693432113",
    "-56.0253967664757432057546974556872290565201325754425564087594",
)
MU_SEED = mp.mpc(
    "-13.1212730489269275803414246629045547501488310966193728200182",
    "1.7637781695171781718210306195912684115951886828383777239068",
)

# Reconstruct floating scouts for all five upper carrier sheets from the exact
# complete kappa=1/1000 fibre.  The scouts carry no proof authority; every new
# tube below is independently Krawczyk certified.
t_anchor = Fr(1, 1000)
kappa_anchor = t_anchor / (1 + t_anchor * t_anchor)
km = mp.mpf(kappa_anchor.numerator) / kappa_anchor.denominator
seeds = []
for root_scout in SUPPORT.FIBRE_SCOUTS[Fr(1, 1000)]:
    _, _, mu, _, _ = SUPPORT.certified_carrier_input(
        kappa_anchor, scout_mu=root_scout
    )
    A, B, C = ENGINE._mp_abc(mu)
    D = A * A * km - B * (1 + km)
    pair_sum = (C * (1 + km) ** 2 - A * B * km**2) / (km * D)
    a = pair_sum / (1 + mp.mpf(1) / 1000)
    seeds.append(ENGINE.newton_scout(t_anchor, a, mu))

scout_centres = []
t = Fr(209, 100000)
for _ in range(9):
    scout_centres.append(t)
    t *= Fr(53, 50)
for _ in range(26):
    scout_centres.append(t)
    t *= Fr(26, 25)
scout_centres.append(Fr(49, 5000))
for t in scout_centres:
    seeds = [ENGINE.newton_scout(t, a, mu) for a, mu in seeds]

parameters = []
t = Fr(101, 10000)
for _ in range(18):
    parameters.append((t, t / 50))
    t *= Fr(207, 200)

sheet_cells = [[] for _ in range(5)]
for j, (centre, radius) in enumerate(parameters):
    row = []
    for sheet, (a_seed, mu_seed) in enumerate(seeds):
        correction_a, correction_mu = (
            (Fr(1, 20), Fr(1, 200))
            if sheet < 3
            else (Fr(1, 1000), Fr(1, 10000))
        )
        cell = ENGINE.certify_affine_cell(
            centre,
            radius,
            a_seed,
            mu_seed,
            correction_a=correction_a,
            correction_mu=correction_mu,
            support_cells=0,
        )
        row.append(cell)
        sheet_cells[sheet].append(cell)
    seeds = [(cell.a_scout, cell.mu_scout) for cell in row]
    report(
        f"PDC common Krawczyk row {j}",
        all(
            cell.krawczyk_a < cell.correction_a
            and cell.krawczyk_mu < cell.correction_mu
            for cell in row
        ),
        f"t={centre}, max Ka<{float(max(c.krawczyk_a for c in row)):.9g}, "
        f"max Kmu<{float(max(c.krawczyk_mu for c in row)):.9g}",
    )
    report(
        f"PDC regular oriented five-sheet row {j}",
        all(cell.det_lower > 0 and cell.cross_margin > 0 for cell in row),
        f"min |det|>{float(min(c.det_lower for c in row)):.9g}, "
        f"min cross>{float(min(c.cross_margin for c in row)):.9g}",
    )
    roots = [cell.mu_box for cell in row]
    report(
        f"PDC upper disjoint exhaustive row {j}",
        all(root.b - root.r > 0 for root in roots)
        and all(
            (roots[i] - roots[k]).abs_lo() > 0
            for i in range(5)
            for k in range(i)
        ),
        f"min Im(mu)>{float(min(r.b-r.r for r in roots)):.9g}, "
        f"min separation>{float(min((roots[i]-roots[k]).abs_lo() for i in range(5) for k in range(i))):.9g}",
    )
    point, gmu, gphi, lip, upper = certify_sign(row[0])
    report(
        f"PDC weak-sheet exact sign row {j}",
        upper < 0,
        f"E0<{float(point):.9f}, Gmu<{float(gmu):.6f}, "
        f"Gphi<{float(gphi):.6f}, L<{float(lip):.6f}, E<{float(upper):.9f}",
    )

# Robust sheets 1 and 2 use two-cell parameter hulls; the near-twin sheets 3
# and 4 remain in one macro hull across the entire certified interval.
macro_sign(sheet_cells[1], [t for t, _ in parameters], 1, 2)
macro_sign(sheet_cells[2], [t for t, _ in parameters], 2, 2)
macro_sign(sheet_cells[3], [t for t, _ in parameters], 3, len(parameters))
macro_sign(sheet_cells[4], [t for t, _ in parameters], 4, len(parameters))

for sheet, cells in enumerate(sheet_cells):
    for j, (left, right) in enumerate(zip(cells, cells[1:])):
        match = (right.left + left.right) / 2
        overlap = ENGINE.certify_overlap(left, right, match)
        report(
            f"PDC overlap sheet {sheet} row {j}/{j+1}",
            overlap["krawczyk_a"] < overlap["radius_a"]
            and overlap["krawczyk_mu"] < overlap["radius_mu"],
            f"Ka/Ra<{float(overlap['krawczyk_a']/overlap['radius_a']):.6g}, "
            f"Kmu/Rmu<{float(overlap['krawczyk_mu']/overlap['radius_mu']):.6g}",
        )

report(
    "PDC exact common five-sheet surviving interval",
    all(
        all(right.left < left.right for left, right in zip(cells, cells[1:]))
        for cells in sheet_cells
    )
    and sheet_cells[0][0].left == Fr(4949, 500000)
    and sheet_cells[0][-1].right
    == Fr(
        12116785580404918688981310598233490936176657,
        655360000000000000000000000000000000000000000,
    ),
    f"[{sheet_cells[0][0].left},{sheet_cells[0][-1].right}], "
    f"rows={len(parameters)}, sheets=5",
)

print("ALL CHECKS PASSED")
