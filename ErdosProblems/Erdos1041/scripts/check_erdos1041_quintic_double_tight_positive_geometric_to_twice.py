#!/usr/bin/env python3
"""Exact proportional-radius positive continuation from row 29 to twice its edge."""

from __future__ import annotations

from fractions import Fraction as Fr
import importlib.util
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "erdos1041_positive_row29_source_for_geometric_to_twice",
    HERE / "check_erdos1041_quintic_double_tight_positive_row29_recentered.py",
)
ROW29 = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = ROW29
assert SPEC.loader is not None
SPEC.loader.exec_module(ROW29)

ROW18 = ROW29.ROW18
ENGINE = ROW29.ENGINE
SUPPORT = ENGINE.SUPPORT
report = ROW29.report

R29 = ROW29.RIGHT29
RATIO = Fr(207, 200)
FIRST_FACTOR = Fr(51, 50)
GREEN_PREFIX_CELLS = 18


def macro_sign(cells: list[ENGINE.AffineCell], centres: list[Fr], sheet: int, block_size: int) -> list[Fr]:
    """Exact support-gradient transport over a block of certified carrier tubes."""
    # The support evaluator may retain its list-valued input while building its
    # exact hull.  Freeze this certificate carrier before iterating blocks.
    cells = tuple(cells)
    uppers = []
    for lo in range(0, len(cells), block_size):
        block = cells[lo : lo + block_size]
        if not block:
            raise AssertionError(f"empty PG2 macro block at {lo}")
        local_mid = len(block) // 2
        mid = lo + local_mid
        cell = block[local_mid]
        kappa = centres[mid] / (1 + centres[mid] * centres[mid])
        mu0C, w0C, mu0, w0, _ = SUPPORT.certified_carrier_input(kappa, scout_mu=cell.mu_scout)
        point = SUPPORT.wall.certified_excess(mu0, w0, muC=mu0C, wC=w0C, k=20, s0=Fr(1, 10**10), ratio=0.06, msub=6, eps_step=Fr(1, 10**7), want_grad=True)
        mu_mid, w_mid = mu0C.mid(), w0C.mid()
        mu_radius = max((SUPPORT.CB(c.mu_box.a, c.mu_box.b, c.mu_box.r, _raw=True) - mu_mid).abs_hi() for c in block)
        w_radius = max((SUPPORT.CB(c.w_box.a, c.w_box.b, c.w_box.r, _raw=True) - w_mid).abs_hi() for c in block)
        if w_radius >= 1:
            raise RuntimeError("macro phase hull reaches the origin")
        tube = SUPPORT.wall.certified_excess(cell.mu_scout, cell.ray_scout, muC=SUPPORT.CB(mu_mid.a, mu_mid.b, mu_radius, _raw=True), wC=SUPPORT.CB(w_mid.a, w_mid.b, w_radius, _raw=True), k=20, s0=Fr(1, 10**10), ratio=0.06, msub=6, eps_step=Fr(1, 10**7), want_grad=True, gradient_only=True)
        # If d bounds the chord of two unit directions, their angular gap is
        # at most 2 asin(d/2) <= d/sqrt(1-d^2/4).  This is exact rational
        # interval arithmetic and replaces the former 2d/(1-d) payment.
        chord_phase = w_radius / ENGINE.CB_MOD.sqrt_lo(Fr(1) - w_radius * w_radius / 4)
        upper = point["hi"] + tube["grad_mu_q"] * mu_radius + tube["grad_phi_q"] * chord_phase
        report(f"PG2 macro sign sheet {sheet} block {lo}:{lo + len(block)}", upper < 0, f"E0<{float(point['hi']):.9f}, rad(mu)<{float(mu_radius):.6g}, rad(w)<{float(w_radius):.6g}, E<{float(upper):.9f}")
        uppers.append(upper)
    return uppers


def weak_sign_subdivision(outer: ENGINE.AffineCell) -> tuple[int, list[Fr]]:
    """Find the coarsest exact re-anchoring of one geometric carrier tube.

    The carrier geometry remains certified on ``outer``.  Only the weak-sheet
    support transport is subdivided, each subcell receiving a fresh exact
    excess anchor and a local implicit derivative bound.
    """
    for parts in (2, 4, 8):
        uppers: list[Fr] = []
        ok = True
        for j in range(parts):
            centre = outer.left + (2 * j + 1) * outer.radius / parts
            radius = outer.radius / parts
            try:
                sub = ENGINE.certify_affine_cell(
                    centre, radius, outer.a_scout, outer.mu_scout,
                    correction_a=outer.correction_a,
                    correction_mu=outer.correction_mu,
                    support_cells=0,
                )
                point, gmu, gphi, lip, upper = ROW18.certify_weak_sign(sub)
                uppers.append(upper)
                print(
                    f"PG2 weak subdivision {parts} part {j}: "
                    f"E0<{float(point):.9f}, Gmu<{float(gmu):.6f}, "
                    f"Gphi<{float(gphi):.6f}, L<{float(lip):.6f}, "
                    f"E<{float(upper):.9f}"
                )
                ok = ok and upper < 0
            except RuntimeError as error:
                print(f"PG2 weak subdivision {parts} part {j}: carrier failure {error}")
                ok = False
        print(f"PG2 weak subdivision trial parts={parts}: {'PASS' if ok else 'FAIL'}")
        if ok:
            report("PG2 coarsest weak-sheet re-anchor", True, f"parts={parts}, max E<{float(max(uppers)):.9f}")
            return parts, uppers
    raise AssertionError("PG2 weak sheet remains uncertified through eight re-anchors")


all_parameters: list[tuple[Fr, Fr]] = []
centre = R29 * FIRST_FACTOR
while True:
    radius = centre / 50
    all_parameters.append((centre, radius))
    if centre + radius >= 2 * R29:
        break
    centre *= RATIO

report("PG2 proportional schedule has twenty cells", len(all_parameters) == 20, f"rows={len(all_parameters)}, final=[{all_parameters[-1][0]-all_parameters[-1][1]},{all_parameters[-1][0]+all_parameters[-1][1]}]")
parameters = all_parameters[:GREEN_PREFIX_CELLS]

old_row = ROW29.new_row
sheet_cells = [[] for _ in range(5)]
for j, (centre, radius) in enumerate(parameters):
    row = ROW18.build_row(centre, radius, [(c.a_scout, c.mu_scout) for c in old_row])
    report(f"PG2 Krawczyk row {j}", all(c.krawczyk_a < c.correction_a and c.krawczyk_mu < c.correction_mu for c in row), f"t={centre}, max Ka<{float(max(c.krawczyk_a for c in row)):.9g}, max Kmu<{float(max(c.krawczyk_mu for c in row)):.9g}")
    report(f"PG2 regular five-sheet row {j}", all(c.det_lower > 0 and c.cross_margin > 0 for c in row), f"min det>{float(min(c.det_lower for c in row)):.9g}, min cross>{float(min(c.cross_margin for c in row)):.9g}")
    roots = [c.mu_box for c in row]
    report(f"PG2 exhaustive upper row {j}", all(r.b-r.r > 0 for r in roots) and all((roots[i]-roots[k]).abs_lo() > 0 for i in range(5) for k in range(i)), f"min Im>{float(min(r.b-r.r for r in roots)):.9g}, min sep>{float(min((roots[i]-roots[k]).abs_lo() for i in range(5) for k in range(i))):.9g}")
    parts, uppers = weak_sign_subdivision(row[0])
    report(f"PG2 weak sign row {j}", max(uppers) < 0, f"parts={parts}, max E<{float(max(uppers)):.9f}")
    for sheet, cell in enumerate(row):
        sheet_cells[sheet].append(cell)
    for sheet, (left, right) in enumerate(zip(old_row, row)):
        match = (left.right + right.left) / 2
        overlap = ENGINE.certify_overlap(left, right, match)
        report(f"PG2 overlap sheet {sheet} into row {j}", overlap["krawczyk_a"] < overlap["radius_a"] and overlap["krawczyk_mu"] < overlap["radius_mu"], f"Ka/Ra<{float(overlap['krawczyk_a']/overlap['radius_a']):.6g}, Kmu/Rmu<{float(overlap['krawczyk_mu']/overlap['radius_mu']):.6g}")
    old_row = row

# The next proportional c/50 tube is only an exact boundary event.  It is not
# in the certificate: sheet zero fails its affine Krawczyk self-map there.
next_centre, next_radius = all_parameters[GREEN_PREFIX_CELLS]
try:
    ENGINE.certify_affine_cell(next_centre, next_radius, old_row[0].a_scout, old_row[0].mu_scout, correction_a=old_row[0].correction_a, correction_mu=old_row[0].correction_mu, support_cells=0)
except RuntimeError as error:
    report("PG2 first omitted c/50 carrier fails exactly", "affine Krawczyk failure" in str(error), str(error))
else:
    raise AssertionError("PG2 expected first omitted c/50 carrier obstruction disappeared")

# Stronger sheets are transported from periodically re-anchored exact excess;
# the near twins retain the large shared hull already viable in the decade run.
macro_sign(sheet_cells[1], [c for c, _ in parameters], 1, 3)
macro_sign(sheet_cells[2], [c for c, _ in parameters], 2, 3)
macro_sign(sheet_cells[3], [c for c, _ in parameters], 3, len(parameters))
macro_sign(sheet_cells[4], [c for c, _ in parameters], 4, len(parameters))

report("PG2 green-prefix overlap with row 29", parameters[0][0]-parameters[0][1] < R29 < parameters[0][0]+parameters[0][1], f"[{parameters[0][0]-parameters[0][1]},{parameters[-1][0]+parameters[-1][1]}]")
print("ALL GEOMETRIC GREEN-PREFIX CHECKS PASSED")

# Immediate collar probe at the first omitted centre: retain its predictor but
# shrink the carrier from c/50 to c/52.  This tests whether the obstruction is
# purely the proportional radius, before committing to a second geometric run.
c52_centre = all_parameters[GREEN_PREFIX_CELLS][0]
c52_radius = c52_centre / 52
c52_row = ROW18.build_row(c52_centre, c52_radius, [(c.a_scout, c.mu_scout) for c in old_row])
report("PG2 c/52 first omitted carrier", all(c.krawczyk_a < c.correction_a and c.krawczyk_mu < c.correction_mu for c in c52_row), f"max Ka<{float(max(c.krawczyk_a for c in c52_row)):.9g}, max Kmu<{float(max(c.krawczyk_mu for c in c52_row)):.9g}")
report("PG2 c/52 first omitted regular", all(c.det_lower > 0 and c.cross_margin > 0 for c in c52_row), f"min det>{float(min(c.det_lower for c in c52_row)):.9g}, min cross>{float(min(c.cross_margin for c in c52_row)):.9g}")
roots = [c.mu_box for c in c52_row]
report("PG2 c/52 first omitted exhaustive", all(r.b-r.r > 0 for r in roots) and all((roots[i]-roots[k]).abs_lo() > 0 for i in range(5) for k in range(i)), f"min Im>{float(min(r.b-r.r for r in roots)):.9g}, min sep>{float(min((roots[i]-roots[k]).abs_lo() for i in range(5) for k in range(i))):.9g}")
parts, uppers = weak_sign_subdivision(c52_row[0])
report("PG2 c/52 first omitted weak sign", max(uppers) < 0, f"parts={parts}, max E<{float(max(uppers)):.9f}")
for sheet in range(1, 5):
    point, mu_radius, w_radius, upper = ROW18.certify_macro_sign(c52_row[sheet])
    report(f"PG2 c/52 first omitted robust sign {sheet}", upper < 0, f"E0<{float(point):.9f}, rad(mu)<{float(mu_radius):.6g}, rad(w)<{float(w_radius):.6g}, E<{float(upper):.9f}")
for sheet, (left, right) in enumerate(zip(old_row, c52_row)):
    overlap = ENGINE.certify_overlap(left, right, (left.right + right.left) / 2)
    report(f"PG2 c/52 first omitted overlap sheet {sheet}", overlap["krawczyk_a"] < overlap["radius_a"] and overlap["krawczyk_mu"] < overlap["radius_mu"], f"Ka/Ra<{float(overlap['krawczyk_a']/overlap['radius_a']):.6g}, Kmu/Rmu<{float(overlap['krawczyk_mu']/overlap['radius_mu']):.6g}")

# Recenter once more on the repaired nineteenth row.  Lock the right edge to
# exactly 2 R29 while retaining the successful c/52 collar: if c+c/52=2 R29,
# then c=104 R29/53 and rho=2 R29/53.  This is only 0.07 percent to the right
# of the nominal twentieth centre and overlaps the repaired row broadly.
direct_centre = 104 * R29 / 53
direct_radius = 2 * R29 / 53
report("PG2 exact direct c/52 endpoint geometry", direct_radius == direct_centre / 52 and direct_centre + direct_radius == 2 * R29, f"right/R29={float((direct_centre+direct_radius)/R29):.12g}")

try:
    ENGINE.certify_affine_cell(direct_centre, direct_radius, c52_row[0].a_scout, c52_row[0].mu_scout, correction_a=c52_row[0].correction_a, correction_mu=c52_row[0].correction_mu, support_cells=0)
except RuntimeError as error:
    report("PG2 direct endpoint predictor fails exactly", "affine Krawczyk failure" in str(error), str(error))
else:
    raise AssertionError("PG2 direct endpoint predictor obstruction disappeared")


def certify_tail_row(label: str, predecessor: list[ENGINE.AffineCell], centre: Fr, radius: Fr) -> list[ENGINE.AffineCell]:
    row = ROW18.build_row(centre, radius, [(c.a_scout, c.mu_scout) for c in predecessor])
    report(f"{label} carrier", all(c.krawczyk_a < c.correction_a and c.krawczyk_mu < c.correction_mu for c in row), f"max Ka<{float(max(c.krawczyk_a for c in row)):.9g}, max Kmu<{float(max(c.krawczyk_mu for c in row)):.9g}")
    report(f"{label} regular", all(c.det_lower > 0 and c.cross_margin > 0 for c in row), f"min det>{float(min(c.det_lower for c in row)):.9g}, min cross>{float(min(c.cross_margin for c in row)):.9g}")
    roots = [c.mu_box for c in row]
    report(f"{label} exhaustive", all(r.b-r.r > 0 for r in roots) and all((roots[i]-roots[k]).abs_lo() > 0 for i in range(5) for k in range(i)), f"min Im>{float(min(r.b-r.r for r in roots)):.9g}, min sep>{float(min((roots[i]-roots[k]).abs_lo() for i in range(5) for k in range(i))):.9g}")
    parts, uppers = weak_sign_subdivision(row[0])
    report(f"{label} weak sign", max(uppers) < 0, f"parts={parts}, max E<{float(max(uppers)):.9f}")
    for sheet in range(1, 5):
        point, mu_radius, w_radius, upper = ROW18.certify_macro_sign(row[sheet])
        report(f"{label} robust sign {sheet}", upper < 0, f"E0<{float(point):.9f}, rad(mu)<{float(mu_radius):.6g}, rad(w)<{float(w_radius):.6g}, E<{float(upper):.9f}")
    for sheet, (left, right) in enumerate(zip(predecessor, row)):
        overlap = ENGINE.certify_overlap(left, right, (left.right + right.left) / 2)
        report(f"{label} overlap sheet {sheet}", overlap["krawczyk_a"] < overlap["radius_a"] and overlap["krawczyk_mu"] < overlap["radius_mu"], f"Ka/Ra<{float(overlap['krawczyk_a']/overlap['radius_a']):.6g}, Kmu/Rmu<{float(overlap['krawczyk_mu']/overlap['radius_mu']):.6g}")
    return row


bridge_centre = (c52_centre + direct_centre) / 2
bridge_radius = bridge_centre / 100
post_bridge_centre = 101 * bridge_centre / 100
post_bridge_radius = post_bridge_centre / 100
final_centre = 200 * R29 / 101
final_radius = 2 * R29 / 101
report("PG2 c/100 chain reaches twice", bridge_centre-bridge_radius < c52_centre+c52_radius and post_bridge_centre-post_bridge_radius < bridge_centre+bridge_radius and final_centre-final_radius < post_bridge_centre+post_bridge_radius and final_radius == final_centre/100 and final_centre+final_radius == 2*R29, f"bridge=[{bridge_centre-bridge_radius},{bridge_centre+bridge_radius}], right/R29={float((final_centre+final_radius)/R29):.12g}")
bridge_row = certify_tail_row("PG2 narrow recenter bridge", c52_row, bridge_centre, bridge_radius)
post_bridge_row = certify_tail_row("PG2 second narrow bridge", bridge_row, post_bridge_centre, post_bridge_radius)
certify_tail_row("PG2 c/100 endpoint-locked final row", post_bridge_row, final_centre, final_radius)
print("ALL GEOMETRIC TO-TWICE CHECKS PASSED")
