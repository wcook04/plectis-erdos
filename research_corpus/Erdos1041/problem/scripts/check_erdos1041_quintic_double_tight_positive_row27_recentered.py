#!/usr/bin/env python3
"""Exact five-sheet replay for the recentered positive row-27 carrier cell."""

from __future__ import annotations

from fractions import Fraction as Fr
import importlib.util
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "erdos1041_positive_row26_source_for_row27",
    HERE / "check_erdos1041_quintic_double_tight_positive_row26_recentered.py",
)
ROW26 = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = ROW26
assert SPEC.loader is not None
SPEC.loader.exec_module(ROW26)

ROW18 = ROW26.ROW18
ENGINE = ROW26.ENGINE
report = ROW26.report

CENTER = ROW26.CENTER + Fr(1, 2000)
RADIUS = Fr(1, 3000)
LEFT27 = Fr(
    500716309007598988776321604095665343002137748290698656005120847,
    20132659200000000000000000000000000000000000000000000000000000000,
)
RIGHT27 = Fr(
    514138081807598988776321604095665343002137748290698656005120847,
    20132659200000000000000000000000000000000000000000000000000000000,
)

old_row = ROW26.new_row
new_row = ROW18.build_row(
    CENTER, RADIUS, [(cell.a_scout, cell.mu_scout) for cell in old_row]
)

report(
    "PR27 exact recentered endpoints and R26 overlap",
    new_row[0].left == LEFT27
    and new_row[0].right == RIGHT27
    and LEFT27 < old_row[0].right < RIGHT27
    and old_row[0].right - LEFT27 == Fr(1, 4000),
    f"[{LEFT27},{RIGHT27}], overlap={old_row[0].right-LEFT27}",
)
report(
    "PR27 five Krawczyk self-maps",
    all(
        cell.krawczyk_a < cell.correction_a
        and cell.krawczyk_mu < cell.correction_mu
        for cell in new_row
    ),
    f"max Ka<{float(max(c.krawczyk_a for c in new_row)):.9g}, "
    f"max Kmu<{float(max(c.krawczyk_mu for c in new_row)):.9g}",
)
report(
    "PR27 regular oriented five-sheet row",
    all(cell.det_lower > 0 and cell.cross_margin > 0 for cell in new_row),
    f"min |det|>{float(min(c.det_lower for c in new_row)):.9g}, "
    f"min cross>{float(min(c.cross_margin for c in new_row)):.9g}",
)
roots = [cell.mu_box for cell in new_row]
report(
    "PR27 upper disjoint exhaustive row",
    all(root.b - root.r > 0 for root in roots)
    and all(
        (roots[i] - roots[j]).abs_lo() > 0
        for i in range(5)
        for j in range(i)
    ),
    f"min Im(mu)>{float(min(r.b-r.r for r in roots)):.9g}, "
    f"min separation>{float(min((roots[i]-roots[j]).abs_lo() for i in range(5) for j in range(i))):.9g}",
)

point, gmu, gphi, lip, upper = ROW18.certify_weak_sign(new_row[0])
report(
    "PR27 weak-sheet exact sign", upper < 0,
    f"E0<{float(point):.9f}, Gmu<{float(gmu):.6f}, "
    f"Gphi<{float(gphi):.6f}, L<{float(lip):.6f}, E<{float(upper):.9f}",
)

for sheet in range(1, 5):
    point, mu_radius, w_radius, upper = ROW18.certify_macro_sign(new_row[sheet])
    report(
        f"PR27 robust-sheet exact sign {sheet}", upper < 0,
        f"E0<{float(point):.9f}, rad(mu)<{float(mu_radius):.6g}, "
        f"rad(w)<{float(w_radius):.6g}, E<{float(upper):.9f}",
    )

for sheet, (old_cell, new_cell) in enumerate(zip(old_row, new_row)):
    match = (new_cell.left + old_cell.right) / 2
    overlap = ENGINE.certify_overlap(old_cell, new_cell, match)
    report(
        f"PR27 exact branch overlap sheet {sheet}",
        overlap["krawczyk_a"] < overlap["radius_a"]
        and overlap["krawczyk_mu"] < overlap["radius_mu"],
        f"t={match}, Ka/Ra<{float(overlap['krawczyk_a']/overlap['radius_a']):.6g}, "
        f"Kmu/Rmu<{float(overlap['krawczyk_mu']/overlap['radius_mu']):.6g}",
    )

print("ALL ROW-27 CHECKS PASSED")
