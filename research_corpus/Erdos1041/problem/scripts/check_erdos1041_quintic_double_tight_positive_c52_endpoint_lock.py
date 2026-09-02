#!/usr/bin/env python3
"""Exact c/52 suffix taking the positive carrier from row 29 to 2 R29."""

from __future__ import annotations

from fractions import Fraction as Fr
import importlib.util
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "erdos1041_positive_row29_source_for_c52_endpoint_lock",
    HERE / "check_erdos1041_quintic_double_tight_positive_row29_recentered.py",
)
ROW29 = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = ROW29
assert SPEC.loader is not None
SPEC.loader.exec_module(ROW29)

ROW18 = ROW29.ROW18
ENGINE = ROW29.ENGINE
report = ROW29.report

R29 = ROW29.RIGHT29
RATIO = Fr(207, 200)
GREEN_PREFIX_CELLS = 18


def weak_sign_subdivision(outer: ENGINE.AffineCell) -> tuple[int, list[Fr]]:
    """Certify the weak sheet after local exact support re-anchoring."""
    for parts in (2, 4, 8):
        uppers: list[Fr] = []
        ok = True
        for j in range(parts):
            centre = outer.left + (2 * j + 1) * outer.radius / parts
            radius = outer.radius / parts
            try:
                sub = ENGINE.certify_affine_cell(
                    centre,
                    radius,
                    outer.a_scout,
                    outer.mu_scout,
                    correction_a=outer.correction_a,
                    correction_mu=outer.correction_mu,
                    support_cells=0,
                )
                point, gmu, gphi, lip, upper = ROW18.certify_weak_sign(sub)
                uppers.append(upper)
                print(
                    f"C52 weak subdivision {parts} part {j}: "
                    f"E0<{float(point):.9f}, Gmu<{float(gmu):.6f}, "
                    f"Gphi<{float(gphi):.6f}, L<{float(lip):.6f}, "
                    f"E<{float(upper):.9f}"
                )
                ok = ok and upper < 0
            except RuntimeError as error:
                print(f"C52 weak subdivision {parts} part {j}: carrier failure {error}")
                ok = False
        if ok:
            return parts, uppers
    raise AssertionError("C52 weak sheet remains uncertified through eight re-anchors")


def certify_suffix_row(label: str, old_row: list[ENGINE.AffineCell], centre: Fr, radius: Fr) -> list[ENGINE.AffineCell]:
    """Run every exact carrier, sign, and predecessor-overlap gate."""
    row = ROW18.build_row(centre, radius, [(c.a_scout, c.mu_scout) for c in old_row])
    report(
        f"{label} carrier",
        all(c.krawczyk_a < c.correction_a and c.krawczyk_mu < c.correction_mu for c in row),
        f"max Ka<{float(max(c.krawczyk_a for c in row)):.9g}, max Kmu<{float(max(c.krawczyk_mu for c in row)):.9g}",
    )
    report(
        f"{label} regular",
        all(c.det_lower > 0 and c.cross_margin > 0 for c in row),
        f"min det>{float(min(c.det_lower for c in row)):.9g}, min cross>{float(min(c.cross_margin for c in row)):.9g}",
    )
    roots = [c.mu_box for c in row]
    report(
        f"{label} exhaustive",
        all(r.b-r.r > 0 for r in roots)
        and all((roots[i]-roots[k]).abs_lo() > 0 for i in range(5) for k in range(i)),
        f"min Im>{float(min(r.b-r.r for r in roots)):.9g}, min sep>{float(min((roots[i]-roots[k]).abs_lo() for i in range(5) for k in range(i))):.9g}",
    )
    parts, uppers = weak_sign_subdivision(row[0])
    report(f"{label} weak sign", max(uppers) < 0, f"parts={parts}, max E<{float(max(uppers)):.9f}")
    for sheet in range(1, 5):
        point, mu_radius, w_radius, upper = ROW18.certify_macro_sign(row[sheet])
        report(
            f"{label} robust sign {sheet}",
            upper < 0,
            f"E0<{float(point):.9f}, rad(mu)<{float(mu_radius):.6g}, rad(w)<{float(w_radius):.6g}, E<{float(upper):.9f}",
        )
    for sheet, (left, right) in enumerate(zip(old_row, row)):
        match = (left.right + right.left) / 2
        overlap = ENGINE.certify_overlap(left, right, match)
        report(
            f"{label} overlap sheet {sheet}",
            overlap["krawczyk_a"] < overlap["radius_a"]
            and overlap["krawczyk_mu"] < overlap["radius_mu"],
            f"Ka/Ra<{float(overlap['krawczyk_a']/overlap['radius_a']):.6g}, Kmu/Rmu<{float(overlap['krawczyk_mu']/overlap['radius_mu']):.6g}",
        )
    return row


# Reconstruct only the already-certified prefix carrier geometry.  Its signs
# remain authority of the geometric-prefix checker; this suffix checker needs
# its final exact branch boxes solely as predecessor data.
old_row = ROW29.new_row
centre = Fr(51, 50) * R29
for j in range(GREEN_PREFIX_CELLS):
    radius = centre / 50
    row = ROW18.build_row(centre, radius, [(c.a_scout, c.mu_scout) for c in old_row])
    report(
        f"C52 predecessor geometry {j}",
        all(c.krawczyk_a < c.correction_a and c.krawczyk_mu < c.correction_mu for c in row),
        f"max Ka<{float(max(c.krawczyk_a for c in row)):.9g}, max Kmu<{float(max(c.krawczyk_mu for c in row)):.9g}",
    )
    old_row = row
    centre *= RATIO

# The first omitted c/50 tube is repaired at the same centre by c/52.
c52_centre = centre
c52_radius = c52_centre / 52
c52_row = certify_suffix_row("C52 repaired nineteenth row", old_row, c52_centre, c52_radius)

# First test the tempting one-cell c/52 endpoint lock.
direct_centre = 104 * R29 / 53
direct_radius = 2 * R29 / 53
report(
    "C52 direct target geometry",
    direct_radius == direct_centre / 52
    and direct_centre - direct_radius < c52_centre + c52_radius
    and direct_centre + direct_radius == 2 * R29,
    f"left/R29={float((direct_centre-direct_radius)/R29):.12g}, right/R29={float((direct_centre+direct_radius)/R29):.12g}",
)

# The direct predictor jump is a genuine exact boundary event: it misses only
# the sheet-zero a-radius by about 0.49 percent.  Preserve that failed route,
# then insert a narrow exact bridge whose interval overlaps both neighbours.
try:
    ENGINE.certify_affine_cell(
        direct_centre,
        direct_radius,
        c52_row[0].a_scout,
        c52_row[0].mu_scout,
        correction_a=c52_row[0].correction_a,
        correction_mu=c52_row[0].correction_mu,
        support_cells=0,
    )
except RuntimeError as error:
    report(
        "C52 direct endpoint predictor fails exactly",
        "affine Krawczyk failure" in str(error),
        str(error),
    )
else:
    raise AssertionError("C52 direct endpoint predictor obstruction disappeared")

bridge_centre = (c52_centre + direct_centre) / 2
bridge_radius = bridge_centre / 100
post_bridge_centre = 101 * bridge_centre / 100
post_bridge_radius = post_bridge_centre / 100
final_centre = 200 * R29 / 101
final_radius = 2 * R29 / 101
report(
    "C52 c/100 chain geometry",
    bridge_centre - bridge_radius < c52_centre + c52_radius
    and post_bridge_centre - post_bridge_radius < bridge_centre + bridge_radius
    and final_centre - final_radius < post_bridge_centre + post_bridge_radius
    and final_radius == final_centre / 100
    and final_centre + final_radius == 2 * R29,
    f"bridge=[{bridge_centre-bridge_radius},{bridge_centre+bridge_radius}], right/R29={float((final_centre+final_radius)/R29):.12g}",
)
bridge_row = certify_suffix_row("C52 narrow recenter bridge", c52_row, bridge_centre, bridge_radius)
post_bridge_row = certify_suffix_row("C52 second narrow bridge", bridge_row, post_bridge_centre, post_bridge_radius)
certify_suffix_row("C52 c/100 endpoint-locked final row", post_bridge_row, final_centre, final_radius)

print("ALL C52 ENDPOINT-LOCK CHECKS PASSED")
