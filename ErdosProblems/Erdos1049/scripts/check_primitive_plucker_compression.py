#!/usr/bin/env python3
"""Measure which q-Apéry exterior divisors survive across whole row families.

The adjacent primitive determinants at q=3/2 have large 2-adic and 3-adic
valuation.  The Bézout--Plücker jet argument can use that arithmetic only when
it is shared by every anchor minor in the selected family.  This checker
computes the exact determinantal divisor of prefixes and contiguous windows,
so an impressive adjacent minor cannot silently stand in for a family-wide
image compression.

This is finite exact arithmetic on the displayed q-Apéry rows.  It is a
calibration of the congruence-selection mechanism, not an irrationality proof
and not a claim about a genuinely independent Hermite--Padé deformation.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import sys


REPO_ROOT = Path(__file__).resolve().parents[5]
SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(REPO_ROOT))
sys.path.insert(0, str(SCRIPT_DIR))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
)
from system.lib.formal_math_determinantal import (  # noqa: E402
    contiguous_tail_profiles,
    determinantal_divisor,
    minor,
    valuation,
)
from verify_qapery_remainder_at_three_halves import cleared_row  # noqa: E402


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "scripts/check_primitive_plucker_compression.py"
)
ROW_SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "scripts/verify_qapery_remainder_at_three_halves.py"
)
TRANSDUCTION_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "scripts/verify_qapery_transduction.py"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "PrimitivePluckerComputationalLab.md"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "BezoutPluckerJets.lean"
)
CONSUMER_DECLARATIONS = [
    "adjacent_det_zero_forces_all_det_zero",
    "zmod_tail_pair_det_zero_of_adjacent_det_zero",
    "zmod_binary_tail_collision_of_adjacent_det_zero",
    "zmod_binary_tail_collision_of_two_three_depth",
]
DETERMINANTAL_REF = "system/lib/formal_math_determinantal.py"


def family_record(rows: list[tuple[int, int]], start: int, end: int) -> dict[str, object]:
    family = rows[start:end]
    minors = [
        minor(family[i], family[j])
        for i in range(len(family))
        for j in range(i + 1, len(family))
    ]
    divisor = determinantal_divisor(family)
    return {
        "start_n": start,
        "end_n_exclusive": end,
        "row_count": len(family),
        "minor_count": len(minors),
        "zero_minor_count": sum(value == 0 for value in minors),
        "determinantal_divisor": divisor,
        "determinantal_divisor_v2": valuation(divisor, 2),
        "determinantal_divisor_v3": valuation(divisor, 3),
        "all_rows_collinear": divisor == 0,
    }


def cached_rows_from_receipt(
    output: Path | None, row_count: int
) -> tuple[list[tuple[int, int]] | None, dict[str, object]]:
    """Reuse costly exact rows only when both generator digests still match."""

    if output is None or not output.exists():
        return None, {"mode": "fresh_exact_reconstruction", "cache_reason": "no_receipt"}
    try:
        prior = json.loads(output.read_text(encoding="utf-8"))
        prior_sources = {
            source["path"]: source["sha256"] for source in prior.get("sources", [])
        }
        generator_refs = [ROW_SOURCE_REF, TRANSDUCTION_REF]
        current = {
            ref: source_record(REPO_ROOT, ref)["sha256"] for ref in generator_refs
        }
        if any(prior_sources.get(ref) != digest for ref, digest in current.items()):
            return None, {
                "mode": "fresh_exact_reconstruction",
                "cache_reason": "row_generator_digest_changed",
            }
        records = prior["scan"]["rows"]
        if len(records) < row_count or any(records[n]["n"] != n for n in range(row_count)):
            return None, {
                "mode": "fresh_exact_reconstruction",
                "cache_reason": "insufficient_or_noncanonical_cached_rows",
            }
        rows = [(int(records[n]["A"]), int(records[n]["B"])) for n in range(row_count)]
        return rows, {
            "mode": "validated_prior_receipt_cache",
            "cache_reason": "exact_row_generator_digests_match",
            "validated_source_digests": current,
        }
    except (KeyError, TypeError, ValueError, json.JSONDecodeError):
        return None, {
            "mode": "fresh_exact_reconstruction",
            "cache_reason": "malformed_prior_receipt",
        }


def compute(
    row_count: int, rows: list[tuple[int, int]] | None = None
) -> dict[str, object]:
    if rows is None:
        rows = [cleared_row(n) for n in range(row_count)]
    if len(rows) != row_count:
        raise ValueError("row materialization length must equal row_count")
    row_records = [
        {
            "n": n,
            "A": row[0],
            "B": row[1],
            "primitive_gcd": math.gcd(abs(row[0]), abs(row[1])),
            "B_is_unit_mod_6": math.gcd(row[1], 6) == 1,
        }
        for n, row in enumerate(rows)
    ]
    adjacent = []
    for n in range(row_count - 1):
        value = minor(rows[n], rows[n + 1])
        adjacent.append(
            {
                "n": n,
                "m": n + 1,
                "determinant": value,
                "v2": valuation(value, 2),
                "v3": valuation(value, 3),
            }
        )
    prefixes = [family_record(rows, 0, end) for end in range(2, row_count + 1)]
    windows = [
        family_record(rows, start, end)
        for width in range(2, row_count + 1)
        for start in range(0, row_count - width + 1)
        for end in [start + width]
    ]
    whole = family_record(rows, 0, row_count)
    tail_profiles = contiguous_tail_profiles(rows)
    formula_matches = []
    for profile in tail_profiles:
        start = int(profile["start_n"])
        depths = profile["first_adjacent_local_depths"]
        assert isinstance(depths, dict)
        formula_matches.append(
            {
                "start_n": start,
                "v2_matches_3ss_plus_3s_plus_1": depths["2"]
                == 3 * start * start + 3 * start + 1,
                "v3_matches_s_plus_1": depths["3"] == start + 1,
                "all_tested_windows_match_first_adjacent_local_depths": profile[
                    "all_tested_windows_match_first_adjacent_local_depths"
                ],
                "maximum_tested_width": profile["maximum_tested_width"],
            }
        )
    max_adjacent_v2 = max(record["v2"] or 0 for record in adjacent)
    max_adjacent_v3 = max(record["v3"] or 0 for record in adjacent)
    whole_v2 = whole["determinantal_divisor_v2"] or 0
    whole_v3 = whole["determinantal_divisor_v3"] or 0
    propagation_falsified = (
        whole_v2 < max_adjacent_v2 or whole_v3 < max_adjacent_v3
    )
    first_two = prefixes[0]
    first_three = prefixes[1]
    irreversible_cap = {
        "local_depth_certificate_prefix_end_exclusive": 2,
        "local_depth_certificate_divisor": first_two["determinantal_divisor"],
        "every_future_prefix_v2_at_most": first_two["determinantal_divisor_v2"],
        "every_future_prefix_v3_at_most": first_two["determinantal_divisor_v3"],
        "exact_divisor_certificate_prefix_end_exclusive": 3,
        "exact_divisor_certificate": first_three["determinantal_divisor"],
        "every_future_prefix_divisor_must_divide": first_three[
            "determinantal_divisor"
        ],
        "growing_common_2_3_depth_impossible_for_initial_prefix_family": True,
        "reason": (
            "Adding rows only adds minors to the gcd. The first two rows give "
            "D=42, already capping both local depths at one; the first three "
            "give D=6, so every later prefix divisor must divide 6."
        ),
    }
    return {
        "rows": row_records,
        "adjacent_minors": adjacent,
        "prefix_determinantal_divisors": prefixes,
        "contiguous_window_determinantal_divisors": windows,
        "moving_tail_profiles": tail_profiles,
        "moving_tail_formula_checks": formula_matches,
        "moving_tail_opening": {
            "every_tested_tail_matches_local_depth_formulas": all(
                row["v2_matches_3ss_plus_3s_plus_1"]
                and row["v3_matches_s_plus_1"]
                for row in formula_matches
            ),
            "every_tested_window_preserves_its_first_adjacent_local_depths": all(
                row["all_tested_windows_match_first_adjacent_local_depths"]
                for row in formula_matches
            ),
            "distinct_from_natural_prefix_cap": True,
            "claim_boundary": (
                "Finite exact tail-window arithmetic only. An all-index adjacent "
                "divisibility theorem and unit second coordinates would propagate "
                "this collapse to every later pair; those q-Apery hypotheses are "
                "not proved here."
            ),
        },
        "whole_family": whole,
        "irreversible_extension_cap": irreversible_cap,
        "comparison": {
            "max_adjacent_v2": max_adjacent_v2,
            "max_adjacent_v3": max_adjacent_v3,
            "whole_family_v2": whole_v2,
            "whole_family_v3": whole_v3,
            "adjacent_depth_propagates_to_whole_family": not propagation_falsified,
            "adjacent_depth_propagation_falsified": propagation_falsified,
        },
    }


def emit(result: dict[str, object], output: Path | None, check: bool) -> int:
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if output is None:
        print(rendered, end="")
        return 0
    resolved = output.resolve()
    if check:
        if not resolved.exists() or resolved.read_text(encoding="utf-8") != rendered:
            print(f"stale receipt: {resolved}", file=sys.stderr)
            return 1
        print(json.dumps({"status": "current", "output": str(resolved)}))
        return 0
    resolved.parent.mkdir(parents=True, exist_ok=True)
    resolved.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(resolved)}))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--row-count", type=int, default=8)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.row_count < 3:
        parser.error("--row-count must be at least three")
    if args.check and args.output is None:
        parser.error("--check requires --output")

    cached_rows, materialization = cached_rows_from_receipt(args.output, args.row_count)
    scan = compute(args.row_count, cached_rows)
    falsified = scan["comparison"]["adjacent_depth_propagation_falsified"]
    tail_open = scan["moving_tail_opening"][
        "every_tested_window_preserves_its_first_adjacent_local_depths"
    ]
    status = (
        "mixed"
        if falsified and tail_open
        else "finite_counterexample"
        if falsified
        else "finite_support"
    )
    if falsified:
        summary = (
            "The first two primitive rows cap every future prefix at v2,v3<=1 "
            "and the first three force every future determinantal divisor to "
            "divide 6. In contrast, every tested moving tail window preserves "
            "the first adjacent depths v2=3s^2+3s+1 and v3=s+1, opening a "
            "structurally distinct non-prefix compression mechanism whose "
            "all-index q-Apery hypotheses remain unproved."
        )
    else:
        summary = (
            "Every maximum adjacent determinant depth survives in the whole "
            "displayed primitive row family; this finite pattern merits an "
            "all-rank divisibility conjecture."
        )
    result = {
        "schema": "erdos1049-primitive-plucker-compression/1",
        "claim_ceiling": (
            "Finite q-Apery row arithmetic only; no irrationality result and "
            "no conclusion for an independent Hermite-Pade deformation."
        ),
        "parameters": {"row_count": args.row_count, "n_range": [0, args.row_count - 1]},
        "row_materialization": materialization,
        "scan": scan,
        "experiment_contract": build_experiment_contract(
            problem_id="erdos_1049",
            target_statement=(
                "Prove irrationality of the rational-base Lambert value at q=3/2."
            ),
            claim_ceiling=(
                "The q-Apery specialization is a finite calibration family and "
                "does not decide the target or a new deformation."
            ),
            hypothesis_id="adjacent_minor_depth_propagates_to_family_image",
            hypothesis_statement=(
                "The large 2-adic and 3-adic depths of adjacent primitive "
                "q-Apery determinants persist in the common determinantal "
                "divisor of a collision-sized row family."
            ),
            probe_id="primitive_plucker_determinantal_divisor_scan",
            probe_question=(
                "Do adjacent exterior valuations really compress the whole "
                "two-coordinate congruence image, or disappear when all row "
                "directions are admitted?"
            ),
            computation=(
                "Construct exact primitive q-Apery rows at q=3/2 and compute "
                "all pairwise minors plus their gcd for every prefix and "
                "contiguous window."
            ),
            falsifier=(
                "The full-family determinantal divisor has smaller v2 or v3 "
                "than a displayed adjacent minor."
            ),
            stop_condition=(
                "If the common depth collapses, retire adjacent-minor "
                "extrapolation for this family; if it persists, formulate the "
                "exact Smith/Plucker compression theorem and test remainder escape."
            ),
            survival_consequence=(
                "Persistent common depth reduces the exact congruence-image "
                "cardinality in the Bezout-Plucker collision consumer and can "
                "lower the selector rank before analytic nonvanishing is tested."
            ),
            falsification_consequence=(
                "Large adjacent determinant valuations cannot be booked as a "
                "family-wide jet entropy saving; a new deformation must supply "
                "common Plucker depth, not isolated local minors."
            ),
            consumer_ref=CONSUMER_REF,
            consumer_declarations=CONSUMER_DECLARATIONS,
            analysis_refs=[ANALYSIS_REF],
            source_refs=[
                SOURCE_REF,
                ROW_SOURCE_REF,
                TRANSDUCTION_REF,
                DETERMINANTAL_REF,
            ],
            result_status=status,
            result_summary=summary,
        ),
        "sources": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, ROW_SOURCE_REF),
            source_record(REPO_ROOT, TRANSDUCTION_REF),
            source_record(REPO_ROOT, DETERMINANTAL_REF),
            source_record(REPO_ROOT, CONSUMER_REF),
        ],
    }
    return emit(result, args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
