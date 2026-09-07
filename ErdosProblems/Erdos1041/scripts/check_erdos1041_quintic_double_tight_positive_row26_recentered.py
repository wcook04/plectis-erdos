#!/usr/bin/env python3
"""Exact five-sheet replay for the recentered positive row-26 carrier cell."""

from __future__ import annotations

from fractions import Fraction as Fr
import importlib.util
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "erdos1041_positive_row18_source_for_row26",
    HERE / "check_erdos1041_quintic_double_tight_positive_row18_recentered.py",
)
ROW18 = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = ROW18
assert SPEC.loader is not None
SPEC.loader.exec_module(ROW18)

ENGINE = ROW18.ENGINE
report = ROW18.report

row19 = ROW18.build_row(
    ROW18.NEW_CENTER * Fr(207, 200), Fr(1, 3000),
    [(cell.a_scout, cell.mu_scout) for cell in ROW18.new_row],
)
row20 = ROW18.build_row(
    ROW18.NEW_CENTER * Fr(207, 200) ** 2, Fr(1, 2850),
    [(cell.a_scout, cell.mu_scout) for cell in row19],
)
row21 = ROW18.build_row(
    ROW18.NEW_CENTER * Fr(207, 200) ** 3, Fr(1, 2750),
    [(cell.a_scout, cell.mu_scout) for cell in row20],
)
row22 = ROW18.build_row(
    ROW18.NEW_CENTER * Fr(207, 200) ** 4, Fr(1, 2650),
    [(cell.a_scout, cell.mu_scout) for cell in row21],
)
row23 = ROW18.build_row(
    ROW18.NEW_CENTER * Fr(207, 200) ** 5, Fr(1, 2550),
    [(cell.a_scout, cell.mu_scout) for cell in row22],
)
row24 = ROW18.build_row(
    ROW18.NEW_CENTER * Fr(207, 200) ** 6, Fr(1, 2550),
    [(cell.a_scout, cell.mu_scout) for cell in row23],
)
row25 = ROW18.build_row(
    ROW18.NEW_CENTER * Fr(207, 200) ** 7, Fr(1, 2350),
    [(cell.a_scout, cell.mu_scout) for cell in row24],
)

CENTER = ROW18.NEW_CENTER * Fr(207, 200) ** 8
RADIUS = Fr(1, 2400)
LEFT26 = Fr(
    488972257807598988776321604095665343002137748290698656005120847,
    20132659200000000000000000000000000000000000000000000000000000000,
)
RIGHT26 = Fr(
    505749473807598988776321604095665343002137748290698656005120847,
    20132659200000000000000000000000000000000000000000000000000000000,
)
R25 = Fr(
    38313537420929392065196643144116378616908976118619705043865829,
    1577058304000000000000000000000000000000000000000000000000000000,
)

old_row = row25
new_row = ROW18.build_row(
    CENTER, RADIUS, [(cell.a_scout, cell.mu_scout) for cell in old_row]
)

report(
    "PR26 exact recentered endpoints and R25 overlap",
    new_row[0].left == LEFT26
    and new_row[0].right == RIGHT26
    and old_row[0].right == R25
    and LEFT26 < R25 < RIGHT26,
    f"[{LEFT26},{RIGHT26}], overlap={R25-LEFT26}",
)
report(
    "PR26 five Krawczyk self-maps",
    all(
        cell.krawczyk_a < cell.correction_a
        and cell.krawczyk_mu < cell.correction_mu
        for cell in new_row
    ),
    f"max Ka<{float(max(c.krawczyk_a for c in new_row)):.9g}, "
    f"max Kmu<{float(max(c.krawczyk_mu for c in new_row)):.9g}",
)
report(
    "PR26 regular oriented five-sheet row",
    all(cell.det_lower > 0 and cell.cross_margin > 0 for cell in new_row),
    f"min |det|>{float(min(c.det_lower for c in new_row)):.9g}, "
    f"min cross>{float(min(c.cross_margin for c in new_row)):.9g}",
)
roots = [cell.mu_box for cell in new_row]
report(
    "PR26 upper disjoint exhaustive row",
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
    "PR26 weak-sheet exact sign", upper < 0,
    f"E0<{float(point):.9f}, Gmu<{float(gmu):.6f}, "
    f"Gphi<{float(gphi):.6f}, L<{float(lip):.6f}, E<{float(upper):.9f}",
)

for sheet in range(1, 5):
    point, mu_radius, w_radius, upper = ROW18.certify_macro_sign(new_row[sheet])
    report(
        f"PR26 robust-sheet exact sign {sheet}", upper < 0,
        f"E0<{float(point):.9f}, rad(mu)<{float(mu_radius):.6g}, "
        f"rad(w)<{float(w_radius):.6g}, E<{float(upper):.9f}",
    )

for sheet, (old_cell, new_cell) in enumerate(zip(old_row, new_row)):
    match = (new_cell.left + old_cell.right) / 2
    overlap = ENGINE.certify_overlap(old_cell, new_cell, match)
    report(
        f"PR26 exact branch overlap sheet {sheet}",
        overlap["krawczyk_a"] < overlap["radius_a"]
        and overlap["krawczyk_mu"] < overlap["radius_mu"],
        f"t={match}, Ka/Ra<{float(overlap['krawczyk_a']/overlap['radius_a']):.6g}, "
        f"Kmu/Rmu<{float(overlap['krawczyk_mu']/overlap['radius_mu']):.6g}",
    )

print("ALL ROW-26 CHECKS PASSED")
