#!/usr/bin/env python3
"""Exact five-sheet replay for the recentered positive row-25 carrier cell."""

from __future__ import annotations

from fractions import Fraction as Fr
import importlib.util
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "erdos1041_positive_row24_source",
    HERE / "check_erdos1041_quintic_double_tight_positive_row24_recentered.py",
)
ROW24 = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = ROW24
assert SPEC.loader is not None
SPEC.loader.exec_module(ROW24)

ROW18 = ROW24.ROW18
ENGINE = ROW18.ENGINE
report = ROW18.report

CENTER = ROW24.CENTER * Fr(207, 200)
RADIUS = Fr(1, 2350)
LEFT25 = Fr(
    36971360140929392065196643144116378616908976118619705043865829,
    1577058304000000000000000000000000000000000000000000000000000000,
)
RIGHT25 = Fr(
    38313537420929392065196643144116378616908976118619705043865829,
    1577058304000000000000000000000000000000000000000000000000000000,
)
R24 = ROW24.RIGHT24

old_row = ROW24.new_row
new_row = ROW18.build_row(
    CENTER, RADIUS, [(cell.a_scout, cell.mu_scout) for cell in old_row]
)

report(
    "PR25 exact recentered endpoints and R24 overlap",
    new_row[0].left == LEFT25
    and new_row[0].right == RIGHT25
    and old_row[0].right == R24
    and LEFT25 < R24 < RIGHT25,
    f"[{LEFT25},{RIGHT25}], overlap={R24-LEFT25}",
)
report(
    "PR25 five Krawczyk self-maps",
    all(
        cell.krawczyk_a < cell.correction_a
        and cell.krawczyk_mu < cell.correction_mu
        for cell in new_row
    ),
    f"max Ka<{float(max(c.krawczyk_a for c in new_row)):.9g}, "
    f"max Kmu<{float(max(c.krawczyk_mu for c in new_row)):.9g}",
)
report(
    "PR25 regular oriented five-sheet row",
    all(cell.det_lower > 0 and cell.cross_margin > 0 for cell in new_row),
    f"min |det|>{float(min(c.det_lower for c in new_row)):.9g}, "
    f"min cross>{float(min(c.cross_margin for c in new_row)):.9g}",
)
roots = [cell.mu_box for cell in new_row]
report(
    "PR25 upper disjoint exhaustive row",
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
    "PR25 weak-sheet exact sign", upper < 0,
    f"E0<{float(point):.9f}, Gmu<{float(gmu):.6f}, "
    f"Gphi<{float(gphi):.6f}, L<{float(lip):.6f}, E<{float(upper):.9f}",
)

for sheet in range(1, 5):
    point, mu_radius, w_radius, upper = ROW18.certify_macro_sign(new_row[sheet])
    report(
        f"PR25 robust-sheet exact sign {sheet}", upper < 0,
        f"E0<{float(point):.9f}, rad(mu)<{float(mu_radius):.6g}, "
        f"rad(w)<{float(w_radius):.6g}, E<{float(upper):.9f}",
    )

for sheet, (old_cell, new_cell) in enumerate(zip(old_row, new_row)):
    match = (new_cell.left + old_cell.right) / 2
    overlap = ENGINE.certify_overlap(old_cell, new_cell, match)
    report(
        f"PR25 exact branch overlap sheet {sheet}",
        overlap["krawczyk_a"] < overlap["radius_a"]
        and overlap["krawczyk_mu"] < overlap["radius_mu"],
        f"t={match}, Ka/Ra<{float(overlap['krawczyk_a']/overlap['radius_a']):.6g}, "
        f"Kmu/Rmu<{float(overlap['krawczyk_mu']/overlap['radius_mu']):.6g}",
    )

print("ALL ROW-25 CHECKS PASSED")
