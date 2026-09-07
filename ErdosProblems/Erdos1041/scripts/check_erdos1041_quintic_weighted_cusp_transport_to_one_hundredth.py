#!/usr/bin/env python3
"""RED proof attempt: recentered five-sheet weighted-cusp transport to u=10^-2.

The preceding theorem WCT is replayed as the connected left anchor.  On the
three mu=-10 sheets, full exact excess certificates are recomputed at four
rational u-anchors.  Gradient cells between consecutive anchors are paid from
whichever endpoint gives the smaller outward upper bound.  Thus no error
payment is carried across an anchor.  The two separated mu_* germs have more
than unit margin, so their exact WCT endpoint bounds safely pay the whole new
t-transport.

The current replay intentionally fails at OH4 with worst selected upper
+0.04284646; it is retained only as an exact obstruction/prototype and is not
a certificate.  All proof arithmetic before that gate is rational outward
complex-ball arithmetic.  Floating
arithmetic supplies Newton centres only, each subsequently enclosed by an
exact Krawczyk test.
"""

from __future__ import annotations

from fractions import Fraction as Fr
import importlib.util
import multiprocessing as multiprocessing
from pathlib import Path
import sys

import mpmath as mp


HERE = Path(__file__).resolve().parent
PREDECESSOR_PATH = (
    HERE / "check_erdos1041_quintic_weighted_cusp_transport_to_one_thousandth.py"
)


def load_predecessor():
    spec = importlib.util.spec_from_file_location("weighted_cusp_to_001", PREDECESSOR_PATH)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    # The predecessor launches forked exact workers during replay.  Register
    # its synthetic import name so multiprocessing can resolve those workers.
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


# Importing WCT deliberately replays the connected five-sheet theorem through
# u=10^-3 before any new outer cell is accepted.
PRE = load_predecessor()
ANCHOR = PRE.ANCHOR
CB, cb, cb_pt = PRE.CB, PRE.cb, PRE.cb_pt
BALL, WALL = PRE.BALL, PRE.WALL
mp.mp.dps = 70


def report(name: str, ok: bool, detail: str = "") -> None:
    print(("PASS " if ok else "FAIL ") + name + ((" :: " + detail) if detail else ""))
    if not ok:
        raise AssertionError(name)


def run_parallel(function, tasks, processes):
    context = multiprocessing.get_context("fork")
    with context.Pool(processes=processes) as pool:
        return pool.map(function, tasks)


def cusp_cell_with_root(task):
    """Exact cusp cell with its actual rational gradient, not an SS22 cutoff."""
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
    ray_ball = -cb(epsilon) * cb(0, 1) * pair_sum * PRE.exact_abs_ball(pair_sum).inv()
    mu_scout = -10 + u_mid * scout
    pair_scout = mp.mpc(
        mp.mpf(pair_sum.a.numerator) / pair_sum.a.denominator,
        mp.mpf(pair_sum.b.numerator) / pair_sum.b.denominator,
    )
    ray_scout = -epsilon * 1j * pair_scout / abs(pair_scout)
    try:
        gradient = outer_wall_gradient_tube(mu_ball, ray_ball, mu_scout, ray_scout)
    except RuntimeError as error:
        raise RuntimeError(
            f"outer cusp wall failure cell={cell_index} branch={branch} "
            f"u=[{u_lo},{u_hi}]: {error}"
        ) from error
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
        "za": z_ball.a,
        "zb": z_ball.b,
        "zr": z_ball.r,
    }


def disks_disjoint(left, right):
    return (
        (left["za"] - right["za"]) ** 2
        + (left["zb"] - right["zb"]) ** 2
        > (left["zr"] + right["zr"]) ** 2
    )


def outer_wall_gradient_tube(mu_ball, ray_ball, mu_scout, ray_scout):
    """Exact gradient tube; geometric conditioning is handled by cell bisection."""
    original = WALL.krawczyk
    WALL.krawczyk = PRE.wide_krawczyk
    try:
        return WALL.certified_excess(
            mu_scout,
            ray_scout,
            muC=WALL.CB(mu_ball.a, mu_ball.b, mu_ball.r, _raw=True),
            wC=WALL.CB(ray_ball.a, ray_ball.b, ray_ball.r, _raw=True),
            k=20,
            s0=Fr(1, 10**14),
            ratio=0.06,
            eps_step=Fr(1, 10000),
            want_grad=True,
            gradient_only=True,
        )
    finally:
        WALL.krawczyk = original


def cusp_cell_group(task):
    """Common exact adaptive partition for all three upper cusp roots."""
    segment_index, cell_index, u_lo, u_hi, depth = task
    try:
        rows = [
            cusp_cell_with_root((cell_index, branch, u_lo, u_hi))
            for branch in range(3)
        ]
        return [{
            "segment": segment_index,
            "u_lo": u_lo,
            "u_hi": u_hi,
            "depth": depth,
            "rows": rows,
        }]
    except RuntimeError as error:
        if depth >= 6:
            raise RuntimeError(
                f"adaptive cusp failure segment={segment_index} cell={cell_index} "
                f"u=[{u_lo},{u_hi}] depth={depth}: {error}"
            ) from error
        midpoint = (u_lo + u_hi) / 2
        left = cusp_cell_group((segment_index, 2 * cell_index, u_lo, midpoint, depth + 1))
        right = cusp_cell_group((segment_index, 2 * cell_index + 1, midpoint, u_hi, depth + 1))
        return left + right


def cusp_anchor(task):
    """Full exact wall excess at one rational u on one mu=-10 sheet."""
    anchor_index, branch, u_exact = task
    u_ball = CB(u_exact, 0, 0, _raw=True)
    u_scout = mp.mpf(u_exact.numerator) / u_exact.denominator
    scout = mp.findroot(
        lambda zz: ANCHOR.hfun(u_scout, zz),
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
        raise RuntimeError(f"cusp anchor carrier failure anchor={anchor_index} branch={branch}")

    mu_ball = cb(-10) + u_ball * z_ball
    pair_sum = ANCHOR.eval_rational(ANCHOR.ps, u_ball, z_ball)
    third = -cb(4) * (mu_ball + cb(4)) - pair_sum
    cross = pair_sum.conj() * third
    if abs(cross.b) <= cross.r:
        raise RuntimeError(f"cusp anchor chamber failure anchor={anchor_index} branch={branch}")
    epsilon = -1 if cross.b > 0 else 1
    ray_ball = -cb(epsilon) * cb(0, 1) * pair_sum * PRE.exact_abs_ball(pair_sum).inv()
    mu_scout = -10 + u_scout * scout
    pair_scout = mp.mpc(
        mp.mpf(pair_sum.a.numerator) / pair_sum.a.denominator,
        mp.mpf(pair_sum.b.numerator) / pair_sum.b.denominator,
    )
    ray_scout = -epsilon * 1j * pair_scout / abs(pair_scout)

    original = WALL.krawczyk
    WALL.krawczyk = PRE.wide_krawczyk
    try:
        excess = WALL.certified_excess(
            mu_scout,
            ray_scout,
            muC=WALL.CB(mu_ball.a, mu_ball.b, mu_ball.r, _raw=True),
            wC=WALL.CB(ray_ball.a, ray_ball.b, ray_ball.r, _raw=True),
            k=20,
            s0=Fr(1, 10**14),
            ratio=0.06,
            eps_step=Fr(1, 10000),
            want_grad=True,
        )
    finally:
        WALL.krawczyk = original
    return {
        "anchor": anchor_index,
        "branch": branch,
        "u": u_exact,
        "hi": excess["hi"],
        "lo": excess["lo"],
        "gmu": excess["grad_mu_q"],
        "gphi": excess["grad_phi_q"],
        "za": z_ball.a,
        "zb": z_ball.b,
        "zr": z_ball.r,
    }


U_START = Fr(1, 1000)
U_TARGET = Fr(1, 100)
ANCHOR_POINTS = (U_START, Fr(1, 250), Fr(7, 1000), U_TARGET)


def geometric_segment(left, right):
    points = [left]
    while points[-1] < right:
        points.append(min(right, points[-1] * Fr(11, 10)))
    return list(zip(points[:-1], points[1:]))


segments = [geometric_segment(left, right) for left, right in zip(ANCHOR_POINTS[:-1], ANCHOR_POINTS[1:])]
cells = [cell for segment in segments for cell in segment]
report("OH1 predecessor reaches the new left endpoint", PRE.U_TARGET == U_START)
report(
    "OH2 rational recenter schedule reaches u=10^-2",
    ANCHOR_POINTS[0] == U_START and ANCHOR_POINTS[-1] == U_TARGET,
    f"segments={len(segments)}, cells={len(cells)}",
)


anchor_tasks = [
    (anchor_index, branch, u_exact)
    for anchor_index, u_exact in enumerate(ANCHOR_POINTS)
    for branch in range(3)
]
anchor_data = run_parallel(cusp_anchor, anchor_tasks, 3)
anchor_hi = {
    (row["anchor"], row["branch"]): row["hi"]
    for row in anchor_data
}
report(
    "OH3 all twelve recenter anchors have negative exact excess",
    all(row["hi"] < 0 for row in anchor_data),
    "weakest=" + f"{float(max(row['hi'] for row in anchor_data)):.8f}",
)
report(
    "OH3a every recenter anchor contains three distinct upper roots",
    all(
        disks_disjoint(rows[i], rows[j])
        for anchor_index in range(len(ANCHOR_POINTS))
        for rows in [[row for row in anchor_data if row["anchor"] == anchor_index]]
        for i in range(3)
        for j in range(i + 1, 3)
    ),
)


cusp_tasks = []
cell_index = 0
for segment_index, segment in enumerate(segments):
    for local_index, (u_lo, u_hi) in enumerate(segment):
        cusp_tasks.append((segment_index, cell_index, u_lo, u_hi, 0))
        cell_index += 1
cusp_groups_nested = run_parallel(cusp_cell_group, cusp_tasks, 3)
cusp_groups = [group for groups in cusp_groups_nested for group in groups]
cusp_data = [row for group in cusp_groups for row in group["rows"]]
report(
    "OH3b every cusp cell contains three distinct upper roots",
    all(
        disks_disjoint(group["rows"][i], group["rows"][j])
        for group in cusp_groups
        for i in range(3)
        for j in range(i + 1, 3)
    ),
    f"degree six plus conjugation makes {len(cusp_groups)} three-disk cells exhaustive",
)

# Rows come back in cell-major/branch-minor order.  Bind each segment from both
# of its exact endpoints and accept a cell only when at least one whole-cell
# payment remains strictly below zero.
covered_bounds = []
for segment_index, segment in enumerate(segments):
    segment_groups = [group for group in cusp_groups if group["segment"] == segment_index]
    for branch in range(3):
        rows = [group["rows"][branch] for group in segment_groups]
        left_running = anchor_hi[(segment_index, branch)]
        left_bounds = []
        for row in rows:
            left_running += row["payment"]
            left_bounds.append(left_running)
        right_running = anchor_hi[(segment_index + 1, branch)]
        right_bounds = [None] * len(rows)
        for local_index in range(len(rows) - 1, -1, -1):
            right_running += rows[local_index]["payment"]
            right_bounds[local_index] = right_running
        covered_bounds.extend(min(left, right) for left, right in zip(left_bounds, right_bounds))

report(
    "OH4 every cusp cell is covered from a recentered endpoint",
    all(bound < 0 for bound in covered_bounds),
    f"worst selected upper={float(max(covered_bounds)):.8f}",
)
report(
    "OH5 every cusp gradient cell has a finite exact wall bound",
    all(row["gmu"] > 0 and row["gphi"] > 0 for row in cusp_data),
    f"max Gmu={float(max(row['gmu'] for row in cusp_data)):.6f}, "
    f"max Gphi={float(max(row['gphi'] for row in cusp_data)):.6f}",
)


mustar_tasks = [
    (cell_index, branch, u_lo, u_hi)
    for cell_index, (u_lo, u_hi) in enumerate(cells)
    for branch in range(2)
]
mustar_data = run_parallel(PRE.mustar_cell, mustar_tasks, 2)
mustar_bounds = list(PRE.mustar_bounds)
for row in mustar_data:
    mustar_bounds[row["branch"]] += row["payment"]
report(
    "OH6 two separated mu_* germs remain negative through u=10^-2",
    all(bound < 0 for bound in mustar_bounds),
    "final uppers=" + ",".join(f"{float(bound):.8f}" for bound in mustar_bounds),
)
report(
    "OH7 every mu_* gradient cell satisfies SS22",
    all(row["gmu"] < 2 and row["gphi"] < 8 for row in mustar_data),
    f"max Gmu={float(max(row['gmu'] for row in mustar_data)):.6f}, "
    f"max Gphi={float(max(row['gphi'] for row in mustar_data)):.6f}",
)
report(
    "OH8 full connected positive five-sheet collar reaches u=10^-2",
    max(covered_bounds + mustar_bounds) < 0,
    f"worst selected upper={float(max(covered_bounds+mustar_bounds)):.8f}",
)

print("CERTIFIED connected positive five-sheet collar: 0 <= u <= 10^-2.")
print("ALL CHECKS PASSED")
