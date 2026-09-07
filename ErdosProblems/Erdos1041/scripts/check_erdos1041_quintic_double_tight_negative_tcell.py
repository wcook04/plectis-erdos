#!/usr/bin/env python3
"""Exact negative-t carrier tube and support certificate for Erdős 1041.

The only floating-point objects below are Newton scouts.  Acceptance uses the
exact dyadic complex-disc arithmetic in ``lib_erdos1041_affine_tcell_engine``
and its support--Stieltjes integrator.  In particular the excess is bounded on
the whole parameter tube, not transported from its centre by a gradient bound.
"""

from __future__ import annotations

from fractions import Fraction as Fr
import importlib.util
from pathlib import Path
import sys

import mpmath as mp


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "erdos1041_negative_affine_tcell",
    HERE / "lib_erdos1041_affine_tcell_engine.py",
)
AFF = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = AFF
assert SPEC.loader is not None
SPEC.loader.exec_module(AFF)


def report(name: str, ok: bool, detail: str = "") -> None:
    print(("PASS " if ok else "FAIL ") + name + ((" :: " + detail) if detail else ""))
    if not ok:
        raise AssertionError(name)


def kappa(t: Fr) -> Fr:
    return t / (1 + t * t)


T0 = Fr(-1, 1000)
T_RADIUS = Fr(1, 100_000_000)
A_CORRECTION = Fr(1, 1_000_000_000)
MU_CORRECTION = Fr(1, 8_000_000_000)

# Newton scouts at t=-1/1000.  No decimal comparison is an acceptance gate.
A_SCOUT = mp.mpc(
    "32.612244055311",
    "43.090878126976",
)
MU_SCOUT = mp.mpc(
    "-12.476212477852",
    "2.472960355017",
)

cell = AFF.certify_affine_cell(
    T0,
    T_RADIUS,
    A_SCOUT,
    MU_SCOUT,
    correction_a=A_CORRECTION,
    correction_mu=MU_CORRECTION,
    support_cells=2048,
)

report(
    "NTC1 nonzero ordered t-cell",
    cell.left == Fr(-100_001, 100_000_000)
    and cell.right == Fr(-99_999, 100_000_000)
    and cell.left < cell.right < 0,
    f"{cell.left} <= t <= {cell.right}",
)
report(
    "NTC2 affine two-equation Krawczyk self-map",
    cell.krawczyk_a < A_CORRECTION and cell.krawczyk_mu < MU_CORRECTION,
    f"Ka<{float(cell.krawczyk_a):.12g}<{float(A_CORRECTION):.12g}, "
    f"Kmu<{float(cell.krawczyk_mu):.12g}<{float(MU_CORRECTION):.12g}",
)
report(
    "NTC3 interval Jacobian nonsingular",
    cell.det_lower > 11_000,
    f"|det d(E1,E2)/d(a,mu)|>{float(cell.det_lower):.9f}",
)
report(
    "NTC4 wall chamber and ray quadrant fixed",
    cell.cross_margin > 1_700
    and cell.w_box.a - cell.w_box.r > 0
    and cell.w_box.b + cell.w_box.r < 0,
    f"cross margin>{float(cell.cross_margin):.9f}, "
    f"ray radius<{float(cell.w_box.r):.12g}",
)

# kappa(t)=t/(1+t^2) is strictly increasing for |t|<1.  The exact comparisons
# prove that the unique preimage of the already-certified kappa=-1/1000 fibre
# lies inside this same analytic carrier cell.
report(
    "NTC5 kappa=-1/1000 anchor lies inside the t-cell",
    kappa(cell.left) < Fr(-1, 1000) < kappa(T0),
    f"kappa(left)={kappa(cell.left)}, kappa(t0)={kappa(T0)}",
)

assert cell.pair_upper is not None
report(
    "NTC6 direct whole-tube support--Stieltjes sign",
    cell.pair_upper < Fr(-1, 50),
    f"E<{float(cell.pair_upper):.12f}<-1/50; exact upper={cell.pair_upper}",
)

assert cell.arm_data is not None
report(
    "NTC7 both compact arms completely partitioned",
    all(
        arm[1]["monotone_cells"] + arm[1]["direct_cells"] == 2048
        for arm in cell.arm_data
    ),
    ", ".join(
        f"arm {j}: monotone={arm[1]['monotone_cells']}, "
        f"direct={arm[1]['direct_cells']}"
        for j, arm in enumerate(cell.arm_data)
    ),
)

print("ALL CHECKS PASSED")
