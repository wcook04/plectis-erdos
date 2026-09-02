#!/usr/bin/env python3
"""Exact five-sheet replay for the recentered positive row-29 carrier cell."""

from __future__ import annotations

from fractions import Fraction as Fr
import importlib.util
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "erdos1041_positive_row28_source_for_row29",
    HERE / "check_erdos1041_quintic_double_tight_positive_row28_recentered.py",
)
ROW28 = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = ROW28
assert SPEC.loader is not None
SPEC.loader.exec_module(ROW28)

ROW18 = ROW28.ROW18
ENGINE = ROW28.ENGINE
report = ROW28.report

CENTER = ROW28.CENTER + Fr(1, 2000)
RADIUS = Fr(1, 3000)
LEFT29 = Fr(
    520848968207598988776321604095665343002137748290698656005120847,
    20132659200000000000000000000000000000000000000000000000000000000,
)
RIGHT29 = Fr(
    534270741007598988776321604095665343002137748290698656005120847,
    20132659200000000000000000000000000000000000000000000000000000000,
)

old_row = ROW28.new_row
new_row = ROW18.build_row(
    CENTER, RADIUS, [(cell.a_scout, cell.mu_scout) for cell in old_row]
)

report(
    "PR29 exact recentered endpoints and R28 overlap",
    new_row[0].left == LEFT29
    and new_row[0].right == RIGHT29
    and LEFT29 < old_row[0].right < RIGHT29
    and old_row[0].right - LEFT29 == Fr(1, 6000),
    f"[{LEFT29},{RIGHT29}], overlap={old_row[0].right-LEFT29}",
)
report(
    "PR29 five Krawczyk self-maps",
    all(c.krawczyk_a < c.correction_a and c.krawczyk_mu < c.correction_mu for c in new_row),
    f"max Ka<{float(max(c.krawczyk_a for c in new_row)):.9g}, max Kmu<{float(max(c.krawczyk_mu for c in new_row)):.9g}",
)
report(
    "PR29 regular oriented five-sheet row",
    all(c.det_lower > 0 and c.cross_margin > 0 for c in new_row),
    f"min |det|>{float(min(c.det_lower for c in new_row)):.9g}, min cross>{float(min(c.cross_margin for c in new_row)):.9g}",
)
roots = [c.mu_box for c in new_row]
report(
    "PR29 upper disjoint exhaustive row",
    all(r.b-r.r > 0 for r in roots) and all((roots[i]-roots[j]).abs_lo() > 0 for i in range(5) for j in range(i)),
    f"min Im(mu)>{float(min(r.b-r.r for r in roots)):.9g}, min separation>{float(min((roots[i]-roots[j]).abs_lo() for i in range(5) for j in range(i))):.9g}",
)

point, gmu, gphi, lip, upper = ROW18.certify_weak_sign(new_row[0])
report("PR29 weak-sheet exact sign", upper < 0, f"E0<{float(point):.9f}, Gmu<{float(gmu):.6f}, Gphi<{float(gphi):.6f}, L<{float(lip):.6f}, E<{float(upper):.9f}")
for sheet in range(1, 5):
    point, mu_radius, w_radius, upper = ROW18.certify_macro_sign(new_row[sheet])
    report(f"PR29 robust-sheet exact sign {sheet}", upper < 0, f"E0<{float(point):.9f}, rad(mu)<{float(mu_radius):.6g}, rad(w)<{float(w_radius):.6g}, E<{float(upper):.9f}")
for sheet, (old_cell, new_cell) in enumerate(zip(old_row, new_row)):
    match = (new_cell.left + old_cell.right) / 2
    overlap = ENGINE.certify_overlap(old_cell, new_cell, match)
    report(f"PR29 exact branch overlap sheet {sheet}", overlap["krawczyk_a"] < overlap["radius_a"] and overlap["krawczyk_mu"] < overlap["radius_mu"], f"t={match}, Ka/Ra<{float(overlap['krawczyk_a']/overlap['radius_a']):.6g}, Kmu/Rmu<{float(overlap['krawczyk_mu']/overlap['radius_mu']):.6g}")

print("ALL ROW-29 CHECKS PASSED")
