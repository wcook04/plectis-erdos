#!/usr/bin/env python3
"""Exact gradient transport of all five weighted-cusp sheets to u=10^-3.

This replay imports the preceding full bridge cell as its exact anchor, then
uses overlapping rational u-cells.  Every gradient tube, carrier derivative,
and transport payment is an outward Fraction bound.  Floating arithmetic is
used only to scout Krawczyk centres.
"""

from __future__ import annotations

from fractions import Fraction as Fr
import importlib.util
import multiprocessing as multiprocessing
from pathlib import Path

import mpmath as mp


HERE = Path(__file__).resolve().parent
ANCHOR_PATH = HERE / "check_erdos1041_quintic_weighted_cusp_bridge_cell.py"


def load_anchor():
    spec = importlib.util.spec_from_file_location("weighted_cusp_anchor", ANCHOR_PATH)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


# Importing the anchor deliberately replays its exact five-sheet certificate.
ANCHOR = load_anchor()
CB, cb, cb_pt = ANCHOR.CB, ANCHOR.cb, ANCHOR.cb_pt
BALL, WALL = ANCHOR.BALL, ANCHOR.WALL
BASE_WALL_KRAWCZYK = WALL.krawczyk
mp.mp.dps = 70


def report(name: str, ok: bool, detail: str = "") -> None:
    print(("PASS " if ok else "FAIL ") + name + ((" :: " + detail) if detail else ""))
    if not ok:
        raise AssertionError(name)


def wide_krawczyk(coeffs, dcoeffs, target, centre, radius, *, iters=25):
    """Exact Krawczyk with parameter-tube radii added to the usual point list."""
    candidates = (
        radius,
        Fr(1, 10**12), Fr(1, 10**10), Fr(1, 10**8), Fr(1, 10**6),
        Fr(1, 10**5), Fr(1, 10**4), Fr(1, 1000), Fr(1, 100),
        Fr(1, 10), Fr(1),
    )
    for candidate in candidates:
        if candidate < radius:
            continue
        result = BASE_WALL_KRAWCZYK(
            coeffs, dcoeffs, target, centre, candidate, iters=iters
        )
        if result is not None:
            return result
    return None


def exact_abs_ball(value):
    lo = WALL.sqrt_lo(value.cabs2()) - value.r
    hi = WALL.sqrt_hi(value.cabs2()) + value.r
    if lo <= 0:
        raise RuntimeError("direction tube meets zero")
    return CB((lo + hi) / 2, 0, WALL.snap_up((hi - lo) / 2), _raw=True)


def wall_gradient_tube(mu_ball, ray_ball, mu_scout, ray_scout, *, cusp):
    original = WALL.krawczyk
    WALL.krawczyk = wide_krawczyk
    try:
        return WALL.certified_excess(
            mu_scout,
            ray_scout,
            muC=WALL.CB(mu_ball.a, mu_ball.b, mu_ball.r, _raw=True),
            wC=WALL.CB(ray_ball.a, ray_ball.b, ray_ball.r, _raw=True),
            k=20,
            s0=Fr(1, 10**14) if cusp else Fr(1, 10**10),
            ratio=0.06,
            eps_step=Fr(1, 10000),
            want_grad=True,
            gradient_only=True,
        )
    finally:
        WALL.krawczyk = original


def cusp_cell(task):
    cell_index, branch, u_lo, u_hi = task
    u_ball = CB((u_lo + u_hi) / 2, 0, (u_hi - u_lo) / 2, _raw=True)
    u_mid = mp.mpf((u_lo + u_hi).numerator) / (u_lo + u_hi).denominator / 2
    scout = mp.findroot(
        lambda zz: ANCHOR.hfun(u_mid, zz),
        ANCHOR.upper_scouts[branch],
        tol=mp.mpf("1e-55"),
        maxsteps=100,
    )
    z_ball = None
    for radius in (Fr(1, 100), Fr(1, 20), Fr(1, 10), Fr(1, 2), Fr(1), Fr(2)):
        z_ball = BALL.krawczyk(
            ANCHOR.coeffs_in_z(ANCHOR.hs, u_ball),
            ANCHOR.coeffs_in_z(ANCHOR.hz, u_ball),
            cb(0),
            cb_pt(scout),
            radius,
            iters=30,
        )
        if z_ball is not None:
            break
    if z_ball is None or z_ball.b - z_ball.r <= 0:
        raise RuntimeError(f"cusp carrier failure cell={cell_index} branch={branch}")

    h_u = ANCHOR.sp.diff(ANCHOR.hs, ANCHOR.u)
    z_prime = -ANCHOR.eval_uz(h_u, u_ball, z_ball) / ANCHOR.eval_uz(
        ANCHOR.hz, u_ball, z_ball
    )
    mu_prime = z_ball + u_ball * z_prime
    mu_ball = cb(-10) + u_ball * z_ball
    pair_sum = ANCHOR.eval_rational(ANCHOR.ps, u_ball, z_ball)
    p_u = ANCHOR.sp.diff(ANCHOR.ps, ANCHOR.u)
    p_z = ANCHOR.sp.diff(ANCHOR.ps, ANCHOR.z)
    logarithmic_p_prime = (
        ANCHOR.eval_rational(p_u, u_ball, z_ball)
        + ANCHOR.eval_rational(p_z, u_ball, z_ball) * z_prime
    ) / pair_sum
    phi_prime = abs(logarithmic_p_prime.b) + logarithmic_p_prime.r

    third = -cb(4) * (mu_ball + cb(4)) - pair_sum
    cross = pair_sum.conj() * third
    if abs(cross.b) <= cross.r:
        raise RuntimeError(f"cusp chamber failure cell={cell_index} branch={branch}")
    epsilon = -1 if cross.b > 0 else 1
    ray_ball = -cb(epsilon) * cb(0, 1) * pair_sum * exact_abs_ball(pair_sum).inv()
    mu_scout = -10 + u_mid * scout
    pair_scout = mp.mpc(
        mp.mpf(pair_sum.a.numerator) / pair_sum.a.denominator,
        mp.mpf(pair_sum.b.numerator) / pair_sum.b.denominator,
    )
    ray_scout = -epsilon * 1j * pair_scout / abs(pair_scout)
    gradient = wall_gradient_tube(mu_ball, ray_ball, mu_scout, ray_scout, cusp=True)
    if not (gradient["grad_mu_q"] < 2 and gradient["grad_phi_q"] < 8):
        raise RuntimeError(f"cusp gradient failure cell={cell_index} branch={branch}")
    chain = (
        gradient["grad_mu_q"] * mu_prime.abs_hi()
        + gradient["grad_phi_q"] * phi_prime
    )
    return {
        "cell": cell_index,
        "branch": branch,
        "chain": chain,
        "payment": WALL.snap_up(chain * (u_hi - u_lo)),
        "gmu": gradient["grad_mu_q"],
        "gphi": gradient["grad_phi_q"],
        "muprime": mu_prime.abs_hi(),
        "phiprime": phi_prime,
    }


def mustar_cell(task):
    cell_index, branch, u_lo, u_hi = task
    kappa_lo, kappa_hi = u_lo**3, u_hi**3
    t_lo = kappa_lo
    t_hi = kappa_hi + 4 * kappa_hi**3
    t_mid_exact = (t_lo + t_hi) / 2
    t_ball = CB(t_mid_exact, 0, (t_hi - t_lo) / 2, _raw=True)
    t_mid = mp.mpf(t_mid_exact.numerator) / t_mid_exact.denominator
    a_scout, mu_scout = mp.findroot(
        lambda av, mv: (
            (1 + t_mid + t_mid**2) * av**2
            + (1 + t_mid) * 4 * (mv + 4) * av
            - mp.mpf(12) / 25 * (3 * mv**3 - 5 * mv**2 - 100 * mv - 200),
            t_mid * (1 + t_mid) * av**3
            + t_mid * 4 * (mv + 4) * av**2
            - mp.mpf(4) / 3125 * (mv + 10) ** 3 * (27 * mv**2 + 140 * mv + 200),
        ),
        (ANCHOR.a_starts[branch], ANCHOR.mu_star),
        tol=mp.mpf("1e-58"),
        maxsteps=100,
    )
    a0, mu0 = cb_pt(a_scout), cb_pt(mu_scout)

    # A numerical derivative supplies only the size of the candidate box.
    # The exact self-map below proves the whole tube.
    jac_scout = mp.matrix(
        [
            [
                2 * (1 + t_mid + t_mid**2) * a_scout + (1 + t_mid) * 4 * (mu_scout + 4),
                4 * (1 + t_mid) * a_scout
                - mp.mpf(12) / 25 * (9 * mu_scout**2 - 10 * mu_scout - 100),
            ],
            [
                3 * t_mid * (1 + t_mid) * a_scout**2
                + 2 * t_mid * 4 * (mu_scout + 4) * a_scout,
                4 * t_mid * a_scout**2
                - mp.mpf(4) / 3125
                * (
                    3 * (mu_scout + 10) ** 2 * (27 * mu_scout**2 + 140 * mu_scout + 200)
                    + (mu_scout + 10) ** 3 * (54 * mu_scout + 140)
                ),
            ],
        ]
    )
    ft_scout = mp.matrix(
        [
            (1 + 2 * t_mid) * a_scout**2 + 4 * (mu_scout + 4) * a_scout,
            (1 + 2 * t_mid) * a_scout**3 + 4 * (mu_scout + 4) * a_scout**2,
        ]
    )
    derivative_scout = -(jac_scout**-1) * ft_scout
    t_radius = mp.mpf((t_hi - t_lo).numerator) / (t_hi - t_lo).denominator / 2
    # The two-equation ball dependency is larger than the true branch motion
    # near t=0.  Multiples of the exact t-width dominate both effects and are
    # still microscopic compared with the separation of the two a-germs.
    t_width = t_hi - t_lo
    a_floor = Fr(1, 10**13) if branch == 0 else Fr(1, 2 * 10**12)
    mu_floor = Fr(1, 10**14) if branch == 0 else Fr(1, 3 * 10**13)
    a_radius = max(a_floor, 64 * t_width)
    mu_radius = max(mu_floor, 16 * t_width)
    a_ball = CB(a0.a, a0.b, a_radius, _raw=True)
    mu_ball = CB(mu0.a, mu0.b, mu_radius, _raw=True)

    inverse = jac_scout**-1
    inverse_ball = [[cb_pt(inverse[i, j]) for j in range(2)] for i in range(2)]
    residual = ANCHOR.matvec(inverse_ball, ANCHOR.carrier(t_ball, a0, mu0))
    defect = ANCHOR.matmul(inverse_ball, ANCHOR.jacobian(t_ball, a_ball, mu_ball))
    defect = [[cb(1 if i == j else 0) - defect[i][j] for j in range(2)] for i in range(2)]
    radii = (a_radius, mu_radius)
    kraw_radii = [
        residual[i].abs_hi() + sum(defect[i][j].abs_hi() * radii[j] for j in range(2))
        for i in range(2)
    ]
    if not (kraw_radii[0] < a_radius and kraw_radii[1] < mu_radius):
        raise RuntimeError(f"mu_* Krawczyk failure cell={cell_index} branch={branch}")

    jacobian = ANCHOR.jacobian(t_ball, a_ball, mu_ball)
    determinant = jacobian[0][0] * jacobian[1][1] - jacobian[0][1] * jacobian[1][0]
    aa, _, _ = ANCHOR.abc(mu_ball)
    ft = (
        (cb(1) + cb(2) * t_ball) * a_ball * a_ball + aa * a_ball,
        (cb(1) + cb(2) * t_ball) * ANCHOR.cpow(a_ball, 3) + aa * a_ball * a_ball,
    )
    a_prime = -(jacobian[1][1] * ft[0] - jacobian[0][1] * ft[1]) / determinant
    mu_prime = -(-jacobian[1][0] * ft[0] + jacobian[0][0] * ft[1]) / determinant
    pair_sum = (cb(1) + t_ball) * a_ball
    p_prime = a_ball + (cb(1) + t_ball) * a_prime
    log_p_prime = p_prime / pair_sum
    phi_prime = abs(log_p_prime.b) + log_p_prime.r
    # The cross itself vanishes at t=0 and loses correlation in a product
    # ball.  Differentiate it along the certified branch instead.  Its exact
    # derivative keeps one sign on every cell, so integration from the zero
    # endpoint fixes the chamber orientation without a spurious interval
    # ambiguity.
    third = -aa - pair_sum
    third_prime = -cb(4) * mu_prime - p_prime
    cross_prime = p_prime.conj() * third + pair_sum.conj() * third_prime
    if cross_prime.b - cross_prime.r > 0:
        epsilon = -1
        orientation = 1
    elif cross_prime.b + cross_prime.r < 0:
        epsilon = 1
        orientation = -1
    else:
        raise RuntimeError(f"mu_* orientation derivative failure cell={cell_index} branch={branch}")
    ray_ball = -cb(epsilon) * cb(0, 1) * pair_sum * exact_abs_ball(pair_sum).inv()
    pair_scout = (1 + t_mid) * a_scout
    ray_scout = -epsilon * 1j * pair_scout / abs(pair_scout)
    gradient = wall_gradient_tube(mu_ball, ray_ball, mu_scout, ray_scout, cusp=False)
    if not (gradient["grad_mu_q"] < 2 and gradient["grad_phi_q"] < 8):
        raise RuntimeError(f"mu_* gradient failure cell={cell_index} branch={branch}")
    chain = (
        gradient["grad_mu_q"] * mu_prime.abs_hi()
        + gradient["grad_phi_q"] * phi_prime
    )
    return {
        "cell": cell_index,
        "branch": branch,
        "chain": chain,
        "payment": WALL.snap_up(chain * (t_hi - t_lo)),
        "gmu": gradient["grad_mu_q"],
        "gphi": gradient["grad_phi_q"],
        "muprime": mu_prime.abs_hi(),
        "phiprime": phi_prime,
        "orientation": orientation,
    }


U_START = Fr(10005, 100000000)  # lies strictly inside the anchor interval
U_TARGET = Fr(1, 1000)
points = [U_START]
while points[-1] < U_TARGET:
    points.append(min(U_TARGET, points[-1] * Fr(11, 10)))
cells = list(zip(points[:-1], points[1:]))
report("TR1 exact overlap with anchor", U_START < ANCHOR.U_HI,
       f"overlap={float(ANCHOR.U_HI-U_START):.9g}")
report("TR2 geometric schedule reaches u=10^-3", points[-1] == U_TARGET,
       f"cells={len(cells)}")


def run_parallel(function, tasks, processes):
    # The exact symbolic carrier is already resident; fork preserves it
    # read-only and avoids three independent symbolic rebuilds.
    context = multiprocessing.get_context("fork")
    with context.Pool(processes=processes) as pool:
        return pool.map(function, tasks)


cusp_tasks = [
    (cell_index, branch, u_lo, u_hi)
    for cell_index, (u_lo, u_hi) in enumerate(cells)
    for branch in range(3)
]
cusp_data = run_parallel(cusp_cell, cusp_tasks, 3)
cusp_bounds = [result["hi"] for result in ANCHOR.cusp_results]
cusp_payments = [Fr(0), Fr(0), Fr(0)]
for row in cusp_data:
    cusp_payments[row["branch"]] += row["payment"]
    cusp_bounds[row["branch"]] += row["payment"]
report(
    "TR3 three cusp sheets remain negative through u=10^-3",
    all(value < 0 for value in cusp_bounds),
    "final uppers=" + ",".join(f"{float(value):.8f}" for value in cusp_bounds),
)
report(
    "TR4 every cusp transport cell satisfies SS22",
    all(row["gmu"] < 2 and row["gphi"] < 8 for row in cusp_data),
    f"max Gmu={float(max(row['gmu'] for row in cusp_data)):.6f}, "
    f"max Gphi={float(max(row['gphi'] for row in cusp_data)):.6f}",
)

mustar_tasks = [
    (cell_index, branch, u_lo, u_hi)
    for cell_index, (u_lo, u_hi) in enumerate(cells)
    for branch in range(2)
]
mustar_data = run_parallel(mustar_cell, mustar_tasks, 2)
mustar_bounds = [result["hi"] for result in ANCHOR.mustar_results]
mustar_payments = [Fr(0), Fr(0)]
for row in mustar_data:
    mustar_payments[row["branch"]] += row["payment"]
    mustar_bounds[row["branch"]] += row["payment"]
report(
    "TR5 two mu_* sheets remain negative through u=10^-3",
    all(value < 0 for value in mustar_bounds),
    "final uppers=" + ",".join(f"{float(value):.8f}" for value in mustar_bounds),
)
report(
    "TR6 every mu_* transport cell satisfies SS22",
    all(row["gmu"] < 2 and row["gphi"] < 8 for row in mustar_data),
    f"max Gmu={float(max(row['gmu'] for row in mustar_data)):.6f}, "
    f"max Gphi={float(max(row['gphi'] for row in mustar_data)):.6f}",
)
report(
    "TR7 full five-sheet connected collar",
    max(cusp_bounds + mustar_bounds) < 0,
    f"worst upper={float(max(cusp_bounds+mustar_bounds)):.8f}",
)

print("CERTIFIED connected five-sheet collar: 0 <= u <= 10^-3.")
print("ALL CHECKS PASSED")
