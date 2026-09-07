#!/usr/bin/env python3
"""Exact five-sheet replay for the recentered positive row-18 carrier cell."""

from __future__ import annotations

from fractions import Fraction as Fr
import importlib.util
from pathlib import Path
import sys

import mpmath as mp


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "erdos1041_positive_row18_affine_engine",
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


def certify_weak_sign(cell: ENGINE.AffineCell) -> tuple[Fr, Fr, Fr, Fr, Fr]:
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


def certify_macro_sign(cell: ENGINE.AffineCell) -> tuple[Fr, Fr, Fr, Fr]:
    """Exact one-cell parameter-hull sign used for each robust sheet."""
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
    mu_mid, w_mid = mu0C.mid(), w0C.mid()
    mu_radius = (
        SUPPORT.CB(cell.mu_box.a, cell.mu_box.b, cell.mu_box.r, _raw=True)
        - mu_mid
    ).abs_hi()
    w_radius = (
        SUPPORT.CB(cell.w_box.a, cell.w_box.b, cell.w_box.r, _raw=True)
        - w_mid
    ).abs_hi()
    if w_radius >= 1:
        raise RuntimeError("macro phase hull reaches the origin")
    mu_hull = SUPPORT.CB(mu_mid.a, mu_mid.b, mu_radius, _raw=True)
    w_hull = SUPPORT.CB(w_mid.a, w_mid.b, w_radius, _raw=True)
    tube = SUPPORT.wall.certified_excess(
        cell.mu_scout,
        cell.ray_scout,
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
    phase_radius = 2 * w_radius / (1 - w_radius)
    upper = (
        point["hi"]
        + tube["grad_mu_q"] * mu_radius
        + tube["grad_phi_q"] * phase_radius
    )
    return point["hi"], mu_radius, w_radius, upper


mp.mp.dps = 90

# Reconstruct all five upper carrier sheets from the exact kappa=1/1000 fibre.
# Floating Newton values are scouts only; every accepted tube below is rebuilt
# independently with exact dyadic-disc arithmetic.
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

# Follow the already-landed floating scout schedule to its first common row.
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

# Advance scouts through rows 0,...,16.  Row 17 is rebuilt below so that the
# overlap with the new recentered row is a standalone exact certificate.
t = Fr(101, 10000)
for _ in range(17):
    seeds = [ENGINE.newton_scout(t, a, mu) for a, mu in seeds]
    t *= Fr(207, 200)

OLD_CENTER = t
OLD_RADIUS = OLD_CENTER / 50
NEW_CENTER = OLD_CENTER * Fr(207, 200)
NEW_RADIUS = Fr(1, 3000)
T17 = Fr(
    12116785580404918688981310598233490936176657,
    655360000000000000000000000000000000000000000,
)
LEFT18 = Fr(
    144918243243754009918772429049078389634621647,
    7864320000000000000000000000000000000000000000,
)
RIGHT18 = Fr(
    150161123243754009918772429049078389634621647,
    7864320000000000000000000000000000000000000000,
)


def build_row(centre: Fr, radius: Fr, row_seeds: list[tuple[mp.mpc, mp.mpc]]):
    row = []
    for sheet, (a_seed, mu_seed) in enumerate(row_seeds):
        correction_a, correction_mu = (
            (Fr(1, 20), Fr(1, 200))
            if sheet < 3
            else (Fr(1, 1000), Fr(1, 10000))
        )
        row.append(
            ENGINE.certify_affine_cell(
                centre,
                radius,
                a_seed,
                mu_seed,
                correction_a=correction_a,
                correction_mu=correction_mu,
                support_cells=0,
            )
        )
    return row


old_row = build_row(OLD_CENTER, OLD_RADIUS, seeds)
new_row = build_row(
    NEW_CENTER,
    NEW_RADIUS,
    [(cell.a_scout, cell.mu_scout) for cell in old_row],
)

report(
    "PR18 exact recentered endpoints and T17 overlap",
    new_row[0].left == LEFT18
    and new_row[0].right == RIGHT18
    and old_row[0].right == T17
    and LEFT18 < T17 < RIGHT18,
    f"[{LEFT18},{RIGHT18}], overlap={T17-LEFT18}",
)
report(
    "PR18 five Krawczyk self-maps",
    all(
        cell.krawczyk_a < cell.correction_a
        and cell.krawczyk_mu < cell.correction_mu
        for cell in new_row
    ),
    f"max Ka<{float(max(c.krawczyk_a for c in new_row)):.9g}, "
    f"max Kmu<{float(max(c.krawczyk_mu for c in new_row)):.9g}",
)
report(
    "PR18 regular oriented five-sheet row",
    all(cell.det_lower > 0 and cell.cross_margin > 0 for cell in new_row),
    f"min |det|>{float(min(c.det_lower for c in new_row)):.9g}, "
    f"min cross>{float(min(c.cross_margin for c in new_row)):.9g}",
)
roots = [cell.mu_box for cell in new_row]
report(
    "PR18 upper disjoint exhaustive row",
    all(root.b - root.r > 0 for root in roots)
    and all(
        (roots[i] - roots[j]).abs_lo() > 0
        for i in range(5)
        for j in range(i)
    ),
    f"min Im(mu)>{float(min(r.b-r.r for r in roots)):.9g}, "
    f"min separation>{float(min((roots[i]-roots[j]).abs_lo() for i in range(5) for j in range(i))):.9g}",
)

point, gmu, gphi, lip, upper = certify_weak_sign(new_row[0])
report(
    "PR18 weak-sheet exact sign",
    upper < 0,
    f"E0<{float(point):.9f}, Gmu<{float(gmu):.6f}, "
    f"Gphi<{float(gphi):.6f}, L<{float(lip):.6f}, E<{float(upper):.9f}",
)

for sheet in range(1, 5):
    point, mu_radius, w_radius, upper = certify_macro_sign(new_row[sheet])
    report(
        f"PR18 robust-sheet exact sign {sheet}",
        upper < 0,
        f"E0<{float(point):.9f}, rad(mu)<{float(mu_radius):.6g}, "
        f"rad(w)<{float(w_radius):.6g}, E<{float(upper):.9f}",
    )

for sheet, (old_cell, new_cell) in enumerate(zip(old_row, new_row)):
    match = (new_cell.left + old_cell.right) / 2
    overlap = ENGINE.certify_overlap(old_cell, new_cell, match)
    report(
        f"PR18 exact branch overlap sheet {sheet}",
        overlap["krawczyk_a"] < overlap["radius_a"]
        and overlap["krawczyk_mu"] < overlap["radius_mu"],
        f"t={match}, Ka/Ra<{float(overlap['krawczyk_a']/overlap['radius_a']):.6g}, "
        f"Kmu/Rmu<{float(overlap['krawczyk_mu']/overlap['radius_mu']):.6g}",
    )

print("ALL CHECKS PASSED")
