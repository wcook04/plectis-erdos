#!/usr/bin/env python3
"""Exact replay of a connected affine-predictor double-tight t-chain.

The two cell signs are obtained by direct support--Stieltjes integration over
the entire parameter tubes.  No point-value gradient transport is imported.
"""

from __future__ import annotations

from fractions import Fraction as Fr
import importlib.util
from pathlib import Path
import sys

import mpmath as mp


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "erdos1041_affine_tcell_engine", HERE / "lib_erdos1041_affine_tcell_engine.py"
)
ENGINE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = ENGINE
assert SPEC.loader is not None
SPEC.loader.exec_module(ENGINE)


def report(name: str, ok: bool, detail: str = "") -> None:
    print(("PASS " if ok else "FAIL ") + name + ((" :: " + detail) if detail else ""))
    if not ok:
        raise AssertionError(name)


mp.mp.dps = 90
A_SEED = mp.mpc(
    "6.81037351291131349533675529051033966781454967749276693432113",
    "-56.0253967664757432057546974556872290565201325754425564087594",
)
MU_SEED = mp.mpc(
    "-13.1212730489269275803414246629045547501488310966193728200182",
    "1.7637781695171781718210306195912684115951886828383777239068",
)

RADIUS = Fr(1, 100000000)
CORRECTION_A = Fr(1, 1000000000)
CORRECTION_MU = Fr(1, 10000000000)
CENTRES = (Fr(1, 1000), Fr(200003, 200000000))

cells = []
a_seed, mu_seed = A_SEED, MU_SEED
for index, centre in enumerate(CENTRES):
    cell = ENGINE.certify_affine_cell(
        centre,
        RADIUS,
        a_seed,
        mu_seed,
        correction_a=CORRECTION_A,
        correction_mu=CORRECTION_MU,
        support_cells=2048,
    )
    cells.append(cell)
    a_seed, mu_seed = cell.a_scout, cell.mu_scout
    report(
        f"ATC{1 + 4*index} affine Krawczyk cell {index}",
        cell.krawczyk_a < CORRECTION_A and cell.krawczyk_mu < CORRECTION_MU,
        f"Ka<{float(cell.krawczyk_a):.12g}, Kmu<{float(cell.krawczyk_mu):.12g}",
    )
    report(
        f"ATC{2 + 4*index} regular wall chamber {index}",
        cell.det_lower > 13000 and cell.cross_margin > 1900,
        f"|det|>{float(cell.det_lower):.6f}, cross>{float(cell.cross_margin):.6f}",
    )
    report(
        f"ATC{3 + 4*index} direct support sign {index}",
        cell.pair_upper is not None and cell.pair_upper < -Fr(7, 200),
        f"E<{float(cell.pair_upper):.12f}<-7/200",
    )
    report(
        f"ATC{4 + 4*index} parameter tube widths {index}",
        cell.mu_box.r < Fr(3, 200000) and cell.w_box.r < Fr(1, 250000),
        f"rad(mu)<{float(cell.mu_box.r):.12g}, rad(w)<{float(cell.w_box.r):.12g}",
    )

match_t = Fr(400003, 400000000)
overlap = ENGINE.certify_overlap(cells[0], cells[1], match_t)
report(
    "ATC9 overlap branch identity",
    overlap["krawczyk_a"] < overlap["radius_a"]
    and overlap["krawczyk_mu"] < overlap["radius_mu"],
    f"t={match_t}, Ka/Ra<{float(overlap['krawczyk_a']/overlap['radius_a']):.6g}, "
    f"Kmu/Rmu<{float(overlap['krawczyk_mu']/overlap['radius_mu']):.6g}",
)

covered_left = cells[0].left
covered_right = cells[1].right
covered_width = covered_right - covered_left
overlap_width = cells[0].right - cells[1].left
report(
    "ATC10 connected union and scale gain",
    cells[1].left < cells[0].right
    and covered_width == Fr(7, 200000000)
    and covered_width > 100 * Fr(2, 10000000000),
    f"[{covered_left},{covered_right}], width={covered_width}, overlap={overlap_width}",
)

print("ALL CHECKS PASSED")
