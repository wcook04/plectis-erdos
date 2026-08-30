#!/usr/bin/env python3
"""Exact replay of the geometric positive double-tight continuation to t>1/100."""

from __future__ import annotations

from fractions import Fraction as Fr
import importlib.util
from pathlib import Path
import sys

import mpmath as mp


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "erdos1041_positive_continuation_affine_engine",
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
    logp_t = p_t / p
    phi_t = abs(logp_t.b) + logp_t.r
    return mu_t.abs_hi(), phi_t


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
    lipschitz = tube["grad_mu_q"] * mu_t + tube["grad_phi_q"] * phi_t
    upper = point["hi"] + lipschitz * cell.radius
    return point["hi"], tube["grad_mu_q"], tube["grad_phi_q"], lipschitz, upper


mp.mp.dps = 90
A_SEED = mp.mpc(
    "6.81037351291131349533675529051033966781454967749276693432113",
    "-56.0253967664757432057546974556872290565201325754425564087594",
)
MU_SEED = mp.mpc(
    "-13.1212730489269275803414246629045547501488310966193728200182",
    "1.7637781695171781718210306195912684115951886828383777239068",
)

# The first nine centres grow by 6% with 3.5% radii.  Beyond the exact radius
# transition near t=.00345, centres grow by 4% with 2.5% radii.  Both schedules
# and their junction overlap strictly.
parameters = []
t = Fr(209, 100000)
for _ in range(9):
    parameters.append((t, t * Fr(7, 200)))
    t *= Fr(53, 50)
for _ in range(26):
    parameters.append((t, t / 40))
    t *= Fr(26, 25)
# A final recentered cell narrows the only transport-limited endpoint tube.
parameters.append((Fr(49, 5000), Fr(21, 100000)))

cells = []
sign_data = []
a_seed, mu_seed = A_SEED, MU_SEED
for j, (centre, radius) in enumerate(parameters):
    cell = ENGINE.certify_affine_cell(
        centre,
        radius,
        a_seed,
        mu_seed,
        correction_a=Fr(1, 20),
        correction_mu=Fr(1, 200),
        support_cells=0,
    )
    cells.append(cell)
    a_seed, mu_seed = cell.a_scout, cell.mu_scout
    report(
        f"PCC{4*j+1} affine Krawczyk cell {j}",
        cell.krawczyk_a < cell.correction_a
        and cell.krawczyk_mu < cell.correction_mu,
        f"t={centre}, Ka<{float(cell.krawczyk_a):.9g}, "
        f"Kmu<{float(cell.krawczyk_mu):.9g}",
    )
    report(
        f"PCC{4*j+2} regular oriented wall cell {j}",
        cell.det_lower > 24000 and cell.cross_margin > 2400,
        f"|det|>{float(cell.det_lower):.6f}, cross>{float(cell.cross_margin):.6f}",
    )
    datum = certify_sign(cell)
    sign_data.append(datum)
    point, gmu, gphi, lip, upper = datum
    report(
        f"PCC{4*j+3} exact gradient sign cell {j}",
        upper < 0,
        f"E0<{float(point):.9f}, Gmu<{float(gmu):.6f}, "
        f"Gphi<{float(gphi):.6f}, L<{float(lip):.6f}, E<{float(upper):.9f}",
    )
    report(
        f"PCC{4*j+4} controlled tube cell {j}",
        cell.mu_box.r < Fr(11, 50) and cell.w_box.r < Fr(1, 25),
        f"rad(mu)<{float(cell.mu_box.r):.9g}, rad(w)<{float(cell.w_box.r):.9g}",
    )

for j, (left, right) in enumerate(zip(cells, cells[1:])):
    match = (right.left + left.right) / 2
    overlap = ENGINE.certify_overlap(left, right, match)
    report(
        f"PCC{4*len(cells)+1+j} overlap identity {j}/{j+1}",
        overlap["krawczyk_a"] < overlap["radius_a"]
        and overlap["krawczyk_mu"] < overlap["radius_mu"],
        f"Ka/Ra<{float(overlap['krawczyk_a']/overlap['radius_a']):.6g}, "
        f"Kmu/Rmu<{float(overlap['krawczyk_mu']/overlap['radius_mu']):.6g}",
    )

# Exact connection to the final cell of the preceding [0.00096,0.00202] chain.
old_last = ENGINE.certify_affine_cell(
    Fr(99, 50000),
    Fr(1, 25000),
    A_SEED,
    MU_SEED,
    correction_a=Fr(1, 100),
    correction_mu=Fr(1, 1000),
    support_cells=0,
)
match = (old_last.right + cells[0].left) / 2
old_overlap = ENGINE.certify_overlap(old_last, cells[0], match)
report(
    f"PCC{5*len(cells)} previous-chain identity",
    old_overlap["krawczyk_a"] < old_overlap["radius_a"]
    and old_overlap["krawczyk_mu"] < old_overlap["radius_mu"],
    f"t={match}, Ka/Ra<{float(old_overlap['krawczyk_a']/old_overlap['radius_a']):.6g}, "
    f"Kmu/Rmu<{float(old_overlap['krawczyk_mu']/old_overlap['radius_mu']):.6g}",
)

covered_left, covered_right = cells[0].left, cells[-1].right
report(
    f"PCC{5*len(cells)+1} connected continuation beyond 1/100",
    old_last.right > covered_left
    and all(right.left < left.right for left, right in zip(cells, cells[1:]))
    and covered_left == Fr(40337, 20000000)
    and covered_right > Fr(1, 100),
    f"[{covered_left},{covered_right}], cells={len(cells)}",
)

print("ALL CHECKS PASSED")
