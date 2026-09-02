#!/usr/bin/env python3
"""Exact connected positive double-tight continuation beyond ``2 R29``.

This is deliberately an exhaustion probe as well as a checker: it reuses the
target-locked final row, advances by overlapping ``c/50`` cells, certifies all
five physical upper sheets on every successful cell, and stops only at the
first exact carrier/sign/overlap obstruction (or after the cell has passed the
rational ceiling ``12/25`` containing the positive event).
"""

from __future__ import annotations

from fractions import Fraction as Fr
import importlib.util
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "erdos1041_positive_c52_source_for_beyond_twice",
    HERE / "check_erdos1041_quintic_double_tight_positive_c52_endpoint_lock.py",
)
SOURCE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = SOURCE
assert SPEC.loader is not None
SPEC.loader.exec_module(SOURCE)

ENGINE = SOURCE.ENGINE
ROW18 = SOURCE.ROW18
report = SOURCE.report

# Reconstruct the already-certified endpoint row as exact predecessor data.
old_row = ROW18.build_row(
    SOURCE.final_centre,
    SOURCE.final_radius,
    [(cell.a_scout, cell.mu_scout) for cell in SOURCE.post_bridge_row],
)
report(
    "B2 endpoint row reconstruction",
    all(cell.krawczyk_a < cell.correction_a and cell.krawczyk_mu < cell.correction_mu for cell in old_row),
    f"right={old_row[0].right}, target={2 * SOURCE.R29}",
)

# Every new cell is centred at the preceding right endpoint, so its left half
# gives strict rational overlap regardless of which adaptive width is chosen.
# We try the widest profile first.  The first three sheets need macroscopic
# correction boxes; the last two use their much tighter natural boxes.
centre = 2 * SOURCE.R29
RATIONAL_EVENT_CEILING = Fr(12, 25)

PROFILES = (
    ("c/10 broad", 10, Fr(3, 10), Fr(3, 100), Fr(1, 100), Fr(1, 1000)),
    ("c/12 broad", 12, Fr(1, 4), Fr(1, 40), Fr(1, 125), Fr(1, 1250)),
    ("c/16 broad", 16, Fr(1, 5), Fr(1, 50), Fr(1, 150), Fr(1, 1500)),
    ("c/20 broad", 20, Fr(3, 20), Fr(3, 200), Fr(1, 200), Fr(1, 2000)),
    ("c/24 broad", 24, Fr(1, 8), Fr(1, 80), Fr(1, 250), Fr(1, 2500)),
    ("c/30 broad", 30, Fr(1, 10), Fr(1, 100), Fr(1, 300), Fr(1, 3000)),
    ("c/40 widened", 40, Fr(3, 40), Fr(3, 400), Fr(1, 400), Fr(1, 4000)),
    ("c/50 widened", 50, Fr(3, 50), Fr(3, 500), Fr(1, 500), Fr(1, 5000)),
    ("c/60 standard", 60, Fr(1, 20), Fr(1, 200), Fr(1, 1000), Fr(1, 10000)),
    ("c/80 standard", 80, Fr(1, 20), Fr(1, 200), Fr(1, 1000), Fr(1, 10000)),
    ("c/100 standard", 100, Fr(1, 20), Fr(1, 200), Fr(1, 1000), Fr(1, 10000)),
)


def build_profile_row(
    centre: Fr,
    denominator: int,
    correction_a: Fr,
    correction_mu: Fr,
    correction_a_tight: Fr,
    correction_mu_tight: Fr,
) -> list[ENGINE.AffineCell]:
    radius = centre / denominator
    row = []
    for sheet, cell in enumerate(old_row):
        ca, cm = (
            (correction_a, correction_mu)
            if sheet < 3
            else (correction_a_tight, correction_mu_tight)
        )
        row.append(
            ENGINE.certify_affine_cell(
                centre,
                radius,
                cell.a_scout,
                cell.mu_scout,
                correction_a=ca,
                correction_mu=cm,
                support_cells=0,
            )
        )
    return row


def accept_profile_row(label: str, row: list[ENGINE.AffineCell]) -> tuple[bool, Fr]:
    """Run all non-carrier gates; return the weakest exact sign margin."""
    roots = [cell.mu_box for cell in row]
    if not (
        all(cell.det_lower > 0 and cell.cross_margin > 0 for cell in row)
        and all(root.b - root.r > 0 for root in roots)
        and all(
            (roots[i] - roots[k]).abs_lo() > 0
            for i in range(5)
            for k in range(i)
        )
    ):
        print(f"REJECT {label}: regularity/exhaustion")
        return False, Fr(0)
    try:
        overlaps = []
        for left, right in zip(old_row, row):
            match = (left.right + right.left) / 2
            overlap = ENGINE.certify_overlap(left, right, match)
            if not (
                overlap["krawczyk_a"] < overlap["radius_a"]
                and overlap["krawczyk_mu"] < overlap["radius_mu"]
            ):
                print(f"REJECT {label}: overlap gate")
                return False, Fr(0)
            overlaps.append(overlap)
    except RuntimeError as error:
        print(f"REJECT {label}: overlap carrier {error}")
        return False, Fr(0)
    try:
        parts, weak_uppers = SOURCE.weak_sign_subdivision(row[0])
    except (AssertionError, RuntimeError) as error:
        print(f"REJECT {label}: weak sign {error}")
        return False, Fr(0)
    sign_uppers = list(weak_uppers)
    macro_data = []
    for sheet in range(1, 5):
        data = ROW18.certify_macro_sign(row[sheet])
        macro_data.append(data)
        sign_uppers.append(data[3])
    if max(sign_uppers) >= 0:
        print(f"REJECT {label}: robust sign max={float(max(sign_uppers)):.12g}")
        return False, max(sign_uppers)

    report(
        f"{label} carrier",
        True,
        f"max Ka<{float(max(cell.krawczyk_a for cell in row)):.9g}, "
        f"max Kmu<{float(max(cell.krawczyk_mu for cell in row)):.9g}",
    )
    report(
        f"{label} regular/exhaustive",
        True,
        f"min det>{float(min(cell.det_lower for cell in row)):.9g}, "
        f"min cross>{float(min(cell.cross_margin for cell in row)):.9g}, "
        f"min Im>{float(min(root.b-root.r for root in roots)):.9g}",
    )
    report(
        f"{label} all-five sign",
        True,
        f"weak parts={parts}, max E<{float(max(sign_uppers)):.9f}",
    )
    report(
        f"{label} predecessor overlap",
        True,
        f"max Ka/Ra<{float(max(o['krawczyk_a']/o['radius_a'] for o in overlaps)):.6g}, "
        f"max Kmu/Rmu<{float(max(o['krawczyk_mu']/o['radius_mu'] for o in overlaps)):.6g}",
    )
    return True, max(sign_uppers)

for index in range(160):
    accepted = None
    weakest = None
    for profile_name, denominator, ca, cm, cat, cmt in PROFILES:
        radius = centre / denominator
        label = f"B2 row {index} {profile_name}"
        print(
            f"B2 attempting {label}: centre={centre}, "
            f"left={centre-radius}, right={centre+radius}"
        )
        try:
            candidate = build_profile_row(centre, denominator, ca, cm, cat, cmt)
        except RuntimeError as error:
            print(f"REJECT {label}: carrier {error}")
            continue
        ok, weakest = accept_profile_row(label, candidate)
        if ok:
            accepted = candidate
            break
    if accepted is None:
        raise AssertionError(
            f"B2 exact obstruction at centre={centre}; every adaptive profile failed"
        )
    old_row = accepted
    frontier = old_row[0].right
    print(
        f"B2 ACCEPTED row {index}: frontier={frontier}, "
        f"weakest E<{float(weakest):.12g}"
    )
    if frontier > RATIONAL_EVENT_CEILING:
        print(
            "B2 CARRIER PASSED RATIONAL POSITIVE-EVENT CEILING; "
            "regular continuation must now be truncated at the exact event"
        )
        break
    centre = frontier
else:
    raise AssertionError("B2 exhaustion cap reached before an exact obstruction")

print("ALL BEYOND-TWICE CONTINUATION CHECKS PASSED")
