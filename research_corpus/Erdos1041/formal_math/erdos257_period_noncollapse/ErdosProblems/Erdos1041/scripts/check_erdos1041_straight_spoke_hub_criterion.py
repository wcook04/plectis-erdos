#!/usr/bin/env python3
"""Erdős #1041: which straight-spoke criterion a critical hub can carry.

Two different containment tests have been used interchangeably for the
two-spoke critical-hub mechanism, and they are not the same statement.

``hub_sublevel``     the spoke stays in ``{|f| <= |f(c)|}``
``open_lemniscate``  the spoke stays in ``{|f| < 1}``

The landed degree-three theorem proves the *sublevel* form: its identity
``P_b(t w) = 1 - t^2 - t^2(1-t) w^3`` gives ``|P_b(t w)| <= 1 - t^3 <= 1``,
and ``|P_b| <= 1`` is exactly ``|f| <= |f(c)|``.  Only the weaker
``open_lemniscate`` form is needed for the short-path statement, since
``|f(c)| < 1`` already.

This probe separates them, and then kills both.

An exact Gaussian-rational quartic is exhibited on which *every* admissible
critical point carries at most one sublevel-contained spoke -- so the sublevel
mechanism yields no two-spoke path at all -- while the same hubs still carry
three open-contained spokes with best pair length 1.7877 < 2.  So the two
criteria genuinely separate, and the degree-three theorem's own inequality is
the wrong generalisation target.

The weaker criterion then fails as well, two degrees later.  Two witnesses, at
degree six and degree nine, have *every* admissible critical point carrying at
most one open-contained spoke.  At those configurations no critical point
supplies a two-straight-spoke path at all, while the two descending inverse-ray
branches at the same hubs give 1.763942 and 1.545995.

Consequence for the proof search: straight spokes from a single critical point
are not enough at any degree from six onward, and curvature is forced.  The
packet's negative result 4 is confirmed rather than relaxed.

Segment maxima are *located*, not sampled: ``|f|^2`` restricted to a segment is
a real polynomial in the segment parameter, so its maximum is read off the roots
of its derivative.  A sampled test can miss a narrow excursion and report a
containment that does not hold.

Numerical continuation and floating evaluation are candidate evidence.  The
witness is recorded as exact integer data so the statement is reproducible, and
the residual exact-arithmetic certification is named in the receipt.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any

import mpmath as mp
import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)
from system.lib.formal_math_lemniscate import (  # noqa: E402
    HUB_SUBLEVEL,
    OPEN_LEMNISCATE,
    coefficients_from_roots,
    critical_table,
    hub_pair_objective,
    spoke_table,
)

SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/"
    "check_erdos1041_straight_spoke_hub_criterion.py"
)
ENGINE_REF = "system/lib/formal_math_lemniscate.py"
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "StraightSpokeHubCriterionLab.md"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/research_packet.json"
)
CUBIC_ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/CubicCriticalHub.md"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1041_straight_spoke_hub_criterion_receipt.json"
)

#: Exact witness.  Roots are ``(a + b i)/WITNESS_DENOMINATOR``.
WITNESS_DENOMINATOR = 10000
WITNESS_ROOT_INTEGERS: tuple[tuple[int, int], ...] = (
    (9999, 4),
    (-125, 9998),
    (-9999, -14),
    (-23, -9999),
)

#: Degrees carried by the near-extremal stress family.
STRESS_DEGREES: tuple[int, ...] = (3, 4, 5, 6, 7, 8)

#: Witnesses on which the *open* criterion also fails: every admissible critical
#: point carries at most one open-contained spoke.  Stored as exact IEEE-754
#: hexadecimal literals so the configuration round-trips bit for bit; the
#: separation margins are near 1e-5 and would not survive decimal rounding.
QC_REFUTATION_WITNESSES: dict[int, tuple[tuple[str, str], ...]] = {
    6: (
        ("0x1.fffffaead1dfdp-1", "-0x1.c7f97b12bedcep-15"),
        ("0x1.004ed623acd87p-1", "0x1.bb3a1b3208ad6p-1"),
        ("-0x1.ffded10fb5c87p-2", "0x1.bb713c92edfe4p-1"),
        ("-0x1.fffff9e87dd68p-1", "-0x1.0766ef919e3d1p-12"),
        ("-0x1.00485f6af598cp-1", "-0x1.bb3dd8051992dp-1"),
        ("0x1.00198d2225a68p-1", "-0x1.bb58e733c06dcp-1"),
    ),
    9: (
        ("0x1.fffffadb279edp-1", "-0x1.54cbe5f38764ep-14"),
        ("0x1.882fdda9ba317p-1", "0x1.4922d6b3868dfp-1"),
        ("0x1.63e8c845cba7bp-3", "0x1.f83590b0811ebp-1"),
        ("-0x1.fffb9be200080p-2", "0x1.bb68ed350eca4p-1"),
        ("-0x1.e121a80180737p-1", "0x1.5e2df749c719cp-2"),
        ("-0x1.e11b7beb2b6bep-1", "-0x1.5e4fe150117d8p-2"),
        ("-0x1.0005816d133a1p-1", "-0x1.bb647aee76a86p-1"),
        ("0x1.637127244f7d2p-3", "-0x1.f83ad6df31cf7p-1"),
        ("0x1.8833eebb49d0cp-1", "-0x1.491f0e2e50785p-1"),
    ),
}


def witness_roots() -> np.ndarray:
    return np.asarray(
        [(a + 1j * b) / WITNESS_DENOMINATOR for a, b in WITNESS_ROOT_INTEGERS],
        dtype=np.complex128,
    )


def roots_are_strictly_inside_unit_disk() -> bool:
    """Exact integer check that every witness root has modulus below one."""

    limit = WITNESS_DENOMINATOR * WITNESS_DENOMINATOR
    return all(a * a + b * b < limit for a, b in WITNESS_ROOT_INTEGERS)


# --------------------------------------------------------------------------
# high-precision re-verification of the witness
# --------------------------------------------------------------------------


def _mp_roots() -> list[mp.mpc]:
    return [
        mp.mpc(mp.mpf(a) / WITNESS_DENOMINATOR, mp.mpf(b) / WITNESS_DENOMINATOR)
        for a, b in WITNESS_ROOT_INTEGERS
    ]


def _mp_value(roots: list[mp.mpc], point: mp.mpc) -> mp.mpc:
    out = mp.mpc(1)
    for root in roots:
        out *= point - root
    return out


def _mp_derivative(roots: list[mp.mpc], point: mp.mpc) -> mp.mpc:
    total = mp.mpc(0)
    for skipped in range(len(roots)):
        term = mp.mpc(1)
        for index, root in enumerate(roots):
            if index != skipped:
                term *= point - root
        total += term
    return total


def _mp_segment_max(roots: list[mp.mpc], start: mp.mpc, end: mp.mpc) -> mp.mpf:
    """Maximum of ``|f|`` on ``[start, end]``, located via ``d|f|^2/dt = 0``."""

    direction = end - start
    # coefficients of P(t) = f(start + t*direction), ascending powers
    poly = [mp.mpc(1)]
    for root in roots:
        shift = start - root
        nxt = [mp.mpc(0)] * (len(poly) + 1)
        for index, coefficient in enumerate(poly):
            nxt[index] += coefficient * shift
            nxt[index + 1] += coefficient * direction
        poly = nxt
    squared = [mp.mpf(0)] * (2 * len(poly) - 1)
    for i, left in enumerate(poly):
        for j, right in enumerate(poly):
            squared[i + j] += (left * mp.conj(right)).real
    derivative = [squared[k] * k for k in range(1, len(squared))]
    candidates = [mp.mpf(0), mp.mpf(1)]
    while derivative and derivative[-1] == 0:
        derivative.pop()
    if len(derivative) > 1:
        for root in mp.polyroots(list(reversed(derivative)), maxsteps=200, extraprec=200):
            if abs(mp.im(root)) < mp.mpf("1e-25"):
                value = mp.re(root)
                if 0 <= value <= 1:
                    candidates.append(value)
    best = mp.mpf(0)
    for parameter in candidates:
        total = mp.mpf(0)
        power = mp.mpf(1)
        for coefficient in squared:
            total += coefficient * power
            power *= parameter
        best = max(best, total)
    return mp.sqrt(max(mp.mpf(0), best))


def verify_witness_high_precision(digits: int = 60) -> dict[str, Any]:
    """Re-derive the witness separation at ``digits`` decimal places."""

    previous = mp.mp.dps
    mp.mp.dps = digits
    try:
        roots = _mp_roots()
        seeds = np.roots(np.polyder(coefficients_from_roots(witness_roots())))
        hubs: list[dict[str, Any]] = []
        located: list[mp.mpc] = []
        for seed in seeds:
            point = mp.findroot(lambda z: _mp_derivative(roots, z), mp.mpc(complex(seed)))
            located.append(point)
        separations = [
            float(abs(located[i] - located[j]))
            for i in range(len(located))
            for j in range(i + 1, len(located))
        ]
        for point in located:
            value = abs(_mp_value(roots, point))
            row: dict[str, Any] = {
                "critical_point": [str(mp.nstr(mp.re(point), 25)), str(mp.nstr(mp.im(point), 25))],
                "critical_value_modulus": str(mp.nstr(value, 25)),
                "derivative_residual": str(mp.nstr(abs(_mp_derivative(roots, point)), 5)),
                "admissible": bool(value < 1),
            }
            if row["admissible"]:
                sublevel, openair, ratios = [], [], []
                for index, root in enumerate(roots):
                    maximum = _mp_segment_max(roots, point, root)
                    ratios.append(str(mp.nstr(maximum / value, 18)))
                    if maximum <= value:
                        sublevel.append(index)
                    if maximum < 1:
                        openair.append(index)
                row["sublevel_contained_root_indices"] = sublevel
                row["open_contained_root_indices"] = openair
                row["spoke_maximum_over_hub_value"] = ratios
                if len(openair) >= 2:
                    lengths = sorted(float(abs(roots[k] - point)) for k in openair)
                    row["open_best_pair_length"] = lengths[0] + lengths[1]
            hubs.append(row)
        admissible = [row for row in hubs if row["admissible"]]
        return {
            "decimal_digits": digits,
            "critical_point_count": len(hubs),
            "minimum_critical_point_separation": min(separations) if separations else None,
            "hubs": hubs,
            "admissible_hub_count": len(admissible),
            "sublevel_mechanism_refuted": all(
                len(row["sublevel_contained_root_indices"]) < 2 for row in admissible
            ),
            "open_mechanism_survives": all(
                len(row["open_contained_root_indices"]) >= 2 for row in admissible
            ),
            "open_best_pair_length": min(
                (row["open_best_pair_length"] for row in admissible if "open_best_pair_length" in row),
                default=None,
            ),
        }
    finally:
        mp.mp.dps = previous


# --------------------------------------------------------------------------
# deterministic near-extremal stress family
# --------------------------------------------------------------------------


def stress_family_rows(seed: int = 20260823, trials: int = 480) -> list[dict[str, Any]]:
    """Perturbations of ``z**n - r**n``, the family that attains the constant 2."""

    rng = np.random.default_rng(seed)
    rows: list[dict[str, Any]] = []
    for degree in STRESS_DEGREES:
        best_open = -1.0
        best_sublevel_failures = 0
        counted = 0
        for radius in (0.9999999, 0.99999, 0.999, 0.99):
            base = radius * np.exp(2j * np.pi * np.arange(degree) / degree)
            for scale in (1.0e-1, 1.0e-2, 1.0e-3, 1.0e-4):
                for _ in range(trials // 4):
                    roots = base * np.exp(
                        scale * (rng.standard_normal(degree) + 1j * rng.standard_normal(degree))
                    )
                    modulus = np.abs(roots)
                    roots = np.where(modulus >= 0.9999999, roots / modulus * 0.99999985, roots)
                    hubs = [row for row in critical_table(roots) if row["admissible"]]
                    if not hubs:
                        continue
                    counted += 1
                    open_best = min(
                        hub_pair_objective(roots, row["critical_point"], criterion=OPEN_LEMNISCATE)[0]
                        for row in hubs
                    )
                    if np.isfinite(open_best):
                        best_open = max(best_open, open_best)
                    if all(
                        sum(
                            entry["contained"]
                            for entry in spoke_table(
                                roots, row["critical_point"], criterion=HUB_SUBLEVEL
                            )
                        )
                        < 2
                        for row in hubs
                    ):
                        best_sublevel_failures += 1
        rows.append(
            {
                "degree": degree,
                "configurations_with_an_admissible_hub": counted,
                "maximum_open_criterion_pair_length": best_open,
                "maximum_open_pair_below_two_in_this_family": bool(best_open < 2.0),
                "configurations_with_no_sublevel_two_spoke_hub": best_sublevel_failures,
            }
        )
    return rows


def qc_refutation_rows() -> list[dict[str, Any]]:
    """Witnesses on which *no* critical point supplies two open-contained spokes.

    Also records what does work there: the two descending inverse-ray branches
    at the same admissible hubs.  Without that the row would look like a
    counterexample to the target rather than to one mechanism.
    """

    from system.lib.formal_math_lemniscate import descending_pair

    rows: list[dict[str, Any]] = []
    for degree, literals in QC_REFUTATION_WITNESSES.items():
        roots = np.asarray(
            [complex(float.fromhex(re), float.fromhex(im)) for re, im in literals],
            dtype=np.complex128,
        )
        if len(roots) != degree:
            raise AssertionError(f"witness for degree {degree} has {len(roots)} roots")
        hubs: list[dict[str, Any]] = []
        best_straight = float("inf")
        best_curved = float("inf")
        for row in critical_table(roots):
            entry = {
                "critical_value_modulus": row["critical_value_modulus"],
                "admissible": row["admissible"],
            }
            if row["admissible"]:
                table = spoke_table(roots, row["critical_point"], criterion=OPEN_LEMNISCATE)
                contained = [item["root_index"] for item in table if item["contained"]]
                pair, _ = hub_pair_objective(
                    roots, row["critical_point"], criterion=OPEN_LEMNISCATE
                )
                best_straight = min(best_straight, pair)
                entry["open_contained_root_indices"] = contained
                entry["straight_pair_length"] = None if not np.isfinite(pair) else float(pair)
                curved = descending_pair(
                    roots,
                    row["critical_point"],
                    relative_tolerance=1.0e-11,
                    absolute_tolerance=1.0e-13,
                )
                if curved is not None and curved["maximum_endpoint_error"] < 1.0e-8:
                    best_curved = min(best_curved, curved["total_length"])
                    entry["descending_branch_pair_length"] = curved["total_length"]
                    entry["descending_branch_root_pair"] = list(curved["root_pair"])
            hubs.append(entry)
        rows.append(
            {
                "degree": degree,
                "root_hex_literals": [list(pair) for pair in literals],
                "roots_strictly_inside_unit_disk": bool(np.all(np.abs(roots) < 1.0)),
                "maximum_root_modulus": float(np.abs(roots).max()),
                "hubs": hubs,
                "admissible_hub_count": sum(1 for row in hubs if row["admissible"]),
                "no_hub_gives_two_open_contained_spokes": not np.isfinite(best_straight),
                "minimum_descending_branch_pair_length": (
                    None if not np.isfinite(best_curved) else float(best_curved)
                ),
            }
        )
    return rows


def pinned_corpus_rows() -> list[dict[str, Any]]:
    """The exact witnesses the packet already pins, re-read through this engine."""

    rows: list[dict[str, Any]] = []

    cubic = (99 / 100) * np.exp(2j * np.pi * np.arange(3) / 3)
    total, _ = hub_pair_objective(cubic, 0.0 + 0j, criterion=HUB_SUBLEVEL)
    rows.append(
        {
            "witness": "z^3 - (99/100)^3",
            "statement": "two sublevel-contained radial spokes through 0, total 99/50",
            "hub_sublevel_pair_length": total,
            "agrees_with_packet": abs(total - 99 / 50) < 1.0e-12,
        }
    )

    quintic = np.asarray(
        [
            900099 / 902000,
            999j / 1000,
            -999j / 1000,
            -450549 / 901000 + 38961j / 45050,
            -450549 / 901000 - 38961j / 45050,
        ],
        dtype=np.complex128,
    )
    nearest = spoke_table(quintic, 0.0 + 0j, criterion=OPEN_LEMNISCATE)
    nearest_index = int(np.argmin([row["length"] for row in nearest]))
    best_open = min(
        hub_pair_objective(quintic, row["critical_point"], criterion=OPEN_LEMNISCATE)[0]
        for row in critical_table(quintic)
        if row["admissible"]
    )
    rows.append(
        {
            "witness": "balanced quintic (packet unique_nearest_straight_spoke_counterexample)",
            "statement": "the nearest root's spoke at the metric hub 0 leaves |f|<1",
            "nearest_root_spoke_maximum": nearest[nearest_index]["maximum_modulus"],
            "nearest_root_spoke_escapes": bool(nearest[nearest_index]["maximum_modulus"] > 1.0),
            "best_open_criterion_pair_over_all_hubs": best_open,
            "another_hub_supplies_a_short_pair": bool(best_open < 2.0),
        }
    )

    cassini = np.asarray([9 / 10, -9 / 10], dtype=np.complex128)
    total, _ = hub_pair_objective(cassini, 0.0 + 0j, criterion=OPEN_LEMNISCATE)
    rows.append(
        {
            "witness": "Cassini a=9/10",
            "statement": "root distance 2 - 2/m leaves no polynomial-independent slack",
            "open_criterion_pair_length": total,
            "agrees_with_root_distance": abs(total - 9 / 5) < 1.0e-12,
        }
    )
    return rows


def build_payload() -> dict[str, Any]:
    roots = witness_roots()
    inside = roots_are_strictly_inside_unit_disk()
    float_hubs: list[dict[str, Any]] = []
    for row in critical_table(roots):
        entry = {
            "critical_point": [row["critical_point"].real, row["critical_point"].imag],
            "critical_value_modulus": row["critical_value_modulus"],
            "admissible": row["admissible"],
        }
        if row["admissible"]:
            for criterion in (HUB_SUBLEVEL, OPEN_LEMNISCATE):
                table = spoke_table(roots, row["critical_point"], criterion=criterion)
                pair, _ = hub_pair_objective(roots, row["critical_point"], criterion=criterion)
                entry[criterion] = {
                    "contained_root_indices": [
                        item["root_index"] for item in table if item["contained"]
                    ],
                    "pair_length": None if not np.isfinite(pair) else float(pair),
                    "spoke_maximum_modulus": [item["maximum_modulus"] for item in table],
                }
        float_hubs.append(entry)

    high_precision = verify_witness_high_precision()
    stress = stress_family_rows()
    pinned = pinned_corpus_rows()
    refutations = qc_refutation_rows()

    admissible = [row for row in float_hubs if row["admissible"]]
    sublevel_refuted = all(
        len(row[HUB_SUBLEVEL]["contained_root_indices"]) < 2 for row in admissible
    )
    open_pairs = [
        row[OPEN_LEMNISCATE]["pair_length"]
        for row in admissible
        if row[OPEN_LEMNISCATE]["pair_length"] is not None
    ]
    open_best = min(open_pairs) if open_pairs else None

    if not inside:
        raise AssertionError("witness roots must lie strictly inside the unit disk")
    if not admissible:
        raise AssertionError("witness must retain at least one admissible critical hub")
    if not sublevel_refuted:
        raise AssertionError("witness no longer refutes the hub-sublevel spoke mechanism")
    if open_best is None or open_best >= 2.0:
        raise AssertionError("witness must still carry a short open-criterion pair")
    if not high_precision["sublevel_mechanism_refuted"]:
        raise AssertionError("high-precision pass disagrees on the sublevel refutation")
    if not high_precision["open_mechanism_survives"]:
        raise AssertionError("high-precision pass disagrees on open-criterion survival")
    for row in refutations:
        if not row["roots_strictly_inside_unit_disk"]:
            raise AssertionError(f"degree {row['degree']} witness left the unit disk")
        if not row["no_hub_gives_two_open_contained_spokes"]:
            raise AssertionError(
                f"degree {row['degree']} witness no longer refutes the open criterion"
            )
        curved = row["minimum_descending_branch_pair_length"]
        if curved is None or curved >= 2.0:
            raise AssertionError(
                f"degree {row['degree']} witness must still admit a short curved pair"
            )

    return {
        "witness": {
            "denominator": WITNESS_DENOMINATOR,
            "root_integer_pairs": [list(pair) for pair in WITNESS_ROOT_INTEGERS],
            "roots_strictly_inside_unit_disk": inside,
            "hubs": float_hubs,
            "hub_sublevel_mechanism_refuted": sublevel_refuted,
            "open_criterion_best_pair_length": open_best,
        },
        "high_precision_reverification": high_precision,
        "near_extremal_stress_family": stress,
        "open_criterion_refutation_witnesses": refutations,
        "pinned_corpus_witnesses": pinned,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--print-only", action="store_true")
    args = parser.parse_args()

    payload = build_payload()
    contract = build_experiment_contract(
        problem_id="erdos_1041",
        target_statement=(
            "If a monic polynomial f(z)=product_i(z-z_i) has all roots in the open unit "
            "disk, prove that two roots can be joined by a curve of length less than 2 "
            "contained in the open lemniscate |f|<1."
        ),
        claim_ceiling=(
            "This probe separates two containment criteria for the two-spoke critical-hub "
            "mechanism and then eliminates both. The hub-sublevel form fails from degree "
            "four and the open-lemniscate form from degree six. It eliminates straight "
            "two-spoke paths through a single critical point; it says nothing against "
            "curved descending branches, non-critical hubs, or multi-segment paths, and "
            "it does not settle Erdos #1041."
        ),
        hypothesis_id="straight_spoke_hub_criterion_separation",
        hypothesis_statement=(
            "The degree-three theorem proves spoke containment in the hub sublevel set "
            "{|f| <= |f(c)|}, which is strictly stronger than the {|f| < 1} containment "
            "the short-path statement needs. The two criteria genuinely separate at "
            "degree four, and the weaker one also fails by degree six, so straight spokes "
            "through a single critical point are not a viable higher-degree mechanism."
        ),
        probe_id="erdos1041_straight_spoke_hub_criterion",
        probe_question=(
            "Do the two containment criteria separate, and does either one survive in "
            "higher degree? Concretely: is there a monic quartic with all roots in the "
            "open unit disk whose every admissible critical point carries at most one "
            "hub-sublevel-contained spoke while still carrying two open-contained spokes "
            "of total length below two, and is there a higher-degree configuration whose "
            "every admissible critical point carries at most one open-contained spoke?"
        ),
        computation=(
            "Segment maxima are located from the real roots of the derivative of |f|^2 "
            "restricted to the segment, not sampled. The exact Gaussian-rational quartic "
            "with roots (9999+4i)/10000, (-125+9998i)/10000, (-9999-14i)/10000 and "
            "(-23-9999i)/10000 is checked in float64 and re-derived at 60 decimal digits. "
            "A deterministic near-extremal stress family perturbs z^n - r^n for degrees "
            "three through eight, and the packet's pinned cubic, balanced-quintic and "
            "Cassini witnesses are re-read through the same engine. Two further witnesses "
            "at degree six and degree nine, stored as exact IEEE-754 hexadecimal literals "
            "so they round-trip bit for bit, are checked for open-criterion failure at "
            "every admissible hub, together with the descending inverse-ray branch pair "
            "that still works there."
        ),
        falsifier=(
            "The separation fails if some admissible hub of the quartic carries two "
            "hub-sublevel-contained spokes, or if no hub of the quartic carries two "
            "open-contained spokes of total length below two. The open-criterion "
            "elimination fails if some admissible hub of the degree-six or degree-nine "
            "witness does carry two open-contained spokes, or if those witnesses stop "
            "admitting a descending branch pair below two, which would make them "
            "counterexamples to the target rather than to one mechanism."
        ),
        stop_condition=(
            "Stop once the separation is exhibited on one witness and the open criterion "
            "is eliminated on at least one witness above degree five. Sweeping further "
            "random configurations for more of the same failures is a longer horizon, not "
            "new evidence."
        ),
        survival_consequence=(
            "Straight two-spoke paths through a single critical point are eliminated as a "
            "higher-degree mechanism, so curvature is forced and the packet's negative "
            "result 4 stands. The surviving hub route is the descending inverse-ray branch "
            "pair, which delivers 1.763942 and 1.545995 on the same witnesses."
        ),
        falsification_consequence=(
            "If an admissible hub carried two sublevel-contained spokes on the quartic, the "
            "degree-three inequality would remain a live generalisation target. If some hub "
            "of the degree-six or degree-nine witness carried two open-contained spokes, "
            "straight spokes would remain live and only the selection rule would be at issue."
        ),
        consumer_ref=PACKET_REF,
        analysis_refs=[ANALYSIS_REF, CUBIC_ANALYSIS_REF],
        source_refs=[SOURCE_REF, ENGINE_REF],
        # mixed: a witness-level counterexample to the sublevel form, plus finite
        # support for the open form.  The witness roots are exact integer data,
        # but its critical points are located numerically rather than by exact
        # rational Rouche disks, so this is not yet an exact_one_way_result.
        result_status="mixed",
        result_summary=(
            "The exact quartic refutes the hub-sublevel two-spoke mechanism at every "
            "admissible critical point while still carrying an open-contained pair of "
            f"length {payload['witness']['open_criterion_best_pair_length']:.9f} < 2, so "
            "the two criteria separate. The degree-six and degree-nine witnesses then "
            "refute the open criterion as well: every admissible hub there carries at most "
            "one open-contained spoke, while the descending inverse-ray branch pairs give "
            + ", ".join(
                f"{row['minimum_descending_branch_pair_length']:.6f}"
                for row in payload["open_criterion_refutation_witnesses"]
            )
            + ". Straight spokes through a single critical point are eliminated; curvature "
            "is forced."
        ),
        resource_bounds={
            "witness_denominator": WITNESS_DENOMINATOR,
            "high_precision_decimal_digits": 60,
            "stress_family_maximum_degree": max(STRESS_DEGREES),
        },
        progress_class="mechanism_eliminated",
        decision_basis=(
            "One exact-data witness decides the sublevel form; the stress family is finite "
            "evidence for the surviving open form."
        ),
        next_analytic_target=(
            "Bound the arc length of the two descending inverse-ray branches at a selected "
            "critical point. The Lean-checked critical-pair metric scale bounds the straight "
            "distance by 2|f(c)|^(1/n) < 2, so the missing quantity is exactly the excess of "
            "branch length over straight distance. On the degree-six and degree-nine "
            "witnesses that excess is what keeps the pair at 1.763942 and 1.545995 rather "
            "than at the straight distance."
        ),
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    payload["experiment_contract"] = contract
    payload["sources"] = [
        source_record(REPO_ROOT, SOURCE_REF),
        source_record(REPO_ROOT, ENGINE_REF),
    ]

    text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.print_only:
        print(text)
        return 0
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(args.output.suffix + ".tmp")
    temporary.write_text(text, encoding="utf-8")
    temporary.replace(args.output)
    print(f"wrote {args.output.relative_to(REPO_ROOT)}")
    print(
        "  hub-sublevel two-spoke mechanism refuted on the exact quartic: "
        f"{payload['witness']['hub_sublevel_mechanism_refuted']}"
    )
    print(
        "  open-lemniscate best pair length: "
        f"{payload['witness']['open_criterion_best_pair_length']:.9f}"
    )
    for row in payload["near_extremal_stress_family"]:
        print(
            f"  degree {row['degree']}: max open pair "
            f"{row['maximum_open_criterion_pair_length']:.9f}; "
            f"{row['configurations_with_no_sublevel_two_spoke_hub']} configurations with no "
            "sublevel two-spoke hub"
        )
    for row in payload["open_criterion_refutation_witnesses"]:
        print(
            f"  degree {row['degree']} witness: no hub with two open-contained spokes = "
            f"{row['no_hub_gives_two_open_contained_spokes']}; shortest descending branch "
            f"pair there = {row['minimum_descending_branch_pair_length']:.6f}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
