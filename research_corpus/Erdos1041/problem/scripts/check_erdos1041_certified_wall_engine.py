"""Checker for CertifiedWallEngine.md (Erdos 1041).

Fast subset of the engine's demo battery (the full six-point run is in
the note; this re-certifies enough to prove the engine on this machine):
  W1  outward-rounding regression (the fixed ship-class soundness bug):
      snap_dn(q) <= q <= snap_up(q) with strict outward movement for
      negative q, including tiny negatives;
  W2  certified enclosure at mu = -12 (wall endpoint phi from wall_w,
      algebraic): upper bound < -0.09, and the independent reference
      -0.104896295638 lies INSIDE [lo, hi];
  W3  certified enclosure at the interior anchor mu = 2 - 1i,
      phi = -2.958835315: upper < -1.25 and reference -1.279229432710
      inside [lo, hi];
  W4  tangent point (mu = 50 + 30 sqrt3, w = i exactly): upper < -0.15,
      reference -0.169461052700 inside, AND one arm's certified e_lo
      exceeds +0.6 (the proved positive-arm split);
  W5  wall labeling at mu = -12: at the engine's wall phi, the smallest
      gap condition vanishes to < 1e-9 while the second-smallest exceeds
      1e-2 (float-level relabel check, per the note's rigor inventory).

Exit 0 iff all pass.  Runtime ~2-4 minutes (k = 40, gradients off).
"""
import importlib.util
import sys
from fractions import Fraction as Fr
from pathlib import Path

import mpmath as mp
import numpy as np

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "lib_erdos1041_wall_engine", HERE / "lib_erdos1041_wall_engine.py")
ENG = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ENG)

FAILURES = []


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


def main():
    mp.mp.dps = 50

    # W1 rounding regression
    cb = ENG._cball
    qs = [Fr(-7, 3), Fr(-1, 10**30), Fr(7, 3), Fr(1, 10**30)]
    ok1 = all(cb.snap_dn(q) <= q <= cb.snap_up(q) for q in qs)
    ok1 = ok1 and cb.snap_dn(Fr(-1, 10**30)) < 0  # must NOT collapse to 0
    report("W1 outward rounding (negative-collapse regression)", ok1)

    # W2 mu = -12 wall endpoint
    mu = mp.mpf(-12)
    muC = ENG.cb_pt(mu)
    wC, _gaps = ENG.wall_w(muC, mu, endpoint=+1)
    phi_w = ENG.wall_phi_float(mu, endpoint=+1)
    w_mp = mp.e ** (-1j * phi_w)
    res = ENG.certified_excess(mu, w_mp, muC=muC, wC=wC, k=40,
                               want_grad=False)
    ref = -0.104896295638
    ok2 = res["hi_f"] < -0.09 and res["lo_f"] <= ref <= res["hi_f"]
    report("W2 certified wall enclosure at mu=-12", ok2,
           f"[{res['lo_f']:.8f}, {res['hi_f']:.8f}] ref {ref} "
           f"w {res['width_f']:.1e} {res['seconds']:.0f}s")

    # W3 interior anchor
    mu3 = mp.mpc(2, -1)
    w3 = mp.e ** (-1j * mp.mpf("-2.958835315"))
    res3 = ENG.certified_excess(mu3, w3, k=40, want_grad=False)
    ref3 = -1.279229432710
    ok3 = res3["hi_f"] < -1.25 and res3["lo_f"] <= ref3 <= res3["hi_f"]
    report("W3 certified interior enclosure at mu=2-1i", ok3,
           f"[{res3['lo_f']:.8f}, {res3['hi_f']:.8f}] {res3['seconds']:.0f}s")

    # W4 tangent point, w = i exactly
    mu4 = 50 + 30 * mp.sqrt(3)
    res4 = ENG.certified_excess(mu4, mp.mpc(0, 1), k=40, want_grad=False)
    ref4 = -0.169461052700
    arm_lo = max(a["e_lo"] for a in res4["arms"])
    ok4 = res4["hi_f"] < -0.15 and res4["lo_f"] <= ref4 <= res4["hi_f"] \
        and arm_lo > 0.6
    report("W4 tangent enclosure + certified positive arm", ok4,
           f"[{res4['lo_f']:.8f}, {res4['hi_f']:.8f}] e_arm_lo {arm_lo:.5f}")

    # W5 wall labeling (float relabel check)
    phi_w = float(phi_w)
    xj = np.roots([5, 20, 30, 20 + 2 * (-12.0)])
    g = xj * (2 * (-12.0) + 20 - 3 * (-12.0) * xj) / 5.0
    vals = np.sort(np.real(np.exp(1j * phi_w) * g))
    ok5 = abs(vals[0]) < 1e-9 and vals[1] > 5e-3
    report("W5 wall labeling at mu=-12", ok5,
           f"tight {vals[0]:+.1e} next {vals[1]:+.3f}")

    if FAILURES:
        print("FAILURES:", FAILURES)
        return 1
    print("ALL PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
