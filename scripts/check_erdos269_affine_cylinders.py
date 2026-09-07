#!/usr/bin/env python3
"""Construct exact long affine-cylinder traps for Erdős #269.

This is not a denominator rectangle scan.  Once the modular lift is zero, a
post-clear residue chain is equivalent to an exact rational interval for
``q / B``.  Continued-fraction reconstruction inside that interval produces
one denominator whose actual canonical residues remain below the proved carry
bound for the requested number of steps.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import check_erdos269_dyadic_windows as dyadic  # noqa: E402
from system.lib.formal_math_affine_cylinder import (  # noqa: E402
    AffineCylinderConstraint,
    certify_affine_cylinder_nesting,
    find_rational_in_denominator_band,
    intersect_affine_cylinder,
)
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
)


SCRIPT_PATH = Path(__file__).resolve()
SOURCE_REF = str(SCRIPT_PATH.relative_to(REPO_ROOT))
DYADIC_SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos269_dyadic_windows.py"
)
LIBRARY_REF = "system/lib/formal_math_affine_cylinder.py"
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "DyadicWindowComputationalLab.md"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "ResidueEscape.lean"
)
LEAN_NESTING_REF = CONSUMER_REF
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "erdos269_affine_cylinder_depth_receipt.json"
)
DEFAULT_DEPTHS = (8, 16, 24, 32, 40, 50, 64, 80, 100, 120, 150, 200)


def parse_depths(value: str) -> tuple[int, ...]:
    depths = tuple(sorted({int(part) for part in value.split(",") if part.strip()}))
    if not depths or any(depth < 1 for depth in depths):
        raise argparse.ArgumentTypeError("depths must be positive comma-separated integers")
    return depths


def short_bound_coefficient(jump_index: int) -> int:
    return jump_index * jump_index + 10 * jump_index + 27


def denominator_band(
    blocks: list[tuple[int, int, int]], anchor: int, first_clear_length: int
) -> tuple[int, int]:
    previous_base, _, previous_index = dyadic.window(
        blocks, anchor, first_clear_length - 1
    )
    current_base, _, current_index = dyadic.window(
        blocks, anchor, first_clear_length
    )
    previous_coefficient = short_bound_coefficient(previous_index)
    current_coefficient = short_bound_coefficient(current_index)
    minimum = (9 * previous_base + previous_coefficient - 1) // previous_coefficient
    maximum = (9 * current_base - 1) // current_coefficient
    return minimum, maximum


def cylinder_for_depth(
    blocks: list[tuple[int, int, int]],
    anchor: int,
    first_clear_length: int,
    depth: int,
):
    rows: list[dict[str, int | None]] = []
    constraints: list[AffineCylinderConstraint] = []
    previous_coefficient: int | None = None
    for offset in range(depth):
        length = first_clear_length + offset
        modulus, forcing, ending_index = dyadic.window(blocks, anchor, length)
        coefficient = short_bound_coefficient(ending_index)
        appended_base: int | None = None
        appended_digit: int | None = None
        upper_nesting_slack: int | None = None
        if previous_coefficient is not None:
            appended_base, appended_digit, _ = blocks[anchor + length - 2]
            upper_nesting_slack = (
                appended_base * previous_coefficient
                - 9 * appended_digit
                - coefficient
            )
        rows.append(
            {
                "length": length,
                "modulus": modulus,
                "forcing": forcing,
                "ending_jump_index": ending_index,
                "bound_coefficient_numerator": coefficient,
                "appended_block_base": appended_base,
                "appended_block_digit": appended_digit,
                "upper_nesting_slack_numerator": upper_nesting_slack,
            }
        )
        constraints.append(
            AffineCylinderConstraint(
                modulus=modulus,
                forcing=forcing,
                upper=Fraction(coefficient, 9),
                label=f"offset_{offset}",
            )
        )
        previous_coefficient = coefficient
    nesting = certify_affine_cylinder_nesting(constraints)
    return intersect_affine_cylinder(constraints), rows, nesting


def digest_rows(rows: list[dict[str, int | bool | None]]) -> str:
    payload = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(payload).hexdigest()


def reconstruct_depth(
    blocks: list[tuple[int, int, int]],
    anchor: int,
    depth: int,
    max_first_clear_length: int,
) -> dict[str, object] | None:
    for first_clear_length in range(depth + 3, max_first_clear_length + 1):
        interval, cylinder_rows, nesting = cylinder_for_depth(
            blocks, anchor, first_clear_length, depth
        )
        if not interval.nonempty:
            continue
        minimum_denominator, maximum_denominator = denominator_band(
            blocks, anchor, first_clear_length
        )
        if minimum_denominator > maximum_denominator:
            continue
        witness = find_rational_in_denominator_band(
            interval,
            minimum_denominator,
            maximum_denominator,
            coprime_to=30,
        )
        if witness is None:
            continue

        denominator = witness.denominator
        numerator = witness.numerator
        trajectory: list[dict[str, int | bool | None]] = []
        first_base_clear: int | None = None
        first_fire: int | None = None
        previous: dict[str, int | bool | None] | None = None
        max_length = first_clear_length + max(3 * depth, depth + 64)
        for length in range(1, max_length + 1):
            current = dyadic.certificate(blocks, denominator, anchor, length)
            if current["base_clears_bound"] and first_base_clear is None:
                first_base_clear = length
            if first_base_clear is not None and length >= first_base_clear:
                if previous is None:
                    current["residue_transition_lift"] = None
                else:
                    unwrapped = (
                        current["last_block_base"]
                        * previous["least_positive_residue"]
                        - denominator * current["last_block_digit"]
                    )
                    current["residue_transition_lift"] = (
                        current["least_positive_residue"] - unwrapped
                    ) // current["window_base"]
                trajectory.append(current)
                previous = current
                if current["consumer_fires"]:
                    first_fire = length
                    break

        if first_base_clear != first_clear_length:
            raise AssertionError(("first base clear mismatch", first_base_clear, first_clear_length))
        if len(trajectory) < depth:
            raise AssertionError(("trajectory shorter than requested depth", len(trajectory), depth))
        for offset, (current, row) in enumerate(zip(trajectory[:depth], cylinder_rows)):
            if current["consumer_fires"] or current["residue_escapes"]:
                raise AssertionError(("cylinder escaped early", depth, offset, current))
            exact_residue = numerator * row["modulus"] - denominator * row["forcing"]
            if exact_residue != current["least_positive_residue"]:
                raise AssertionError(("rational reconstruction mismatch", depth, offset))
            if offset > 0 and current["residue_transition_lift"] != 0:
                raise AssertionError(("nonzero modular lift", depth, offset, current))
        if first_fire is None:
            raise AssertionError(("escape horizon too short", depth, max_length))

        firing_row = trajectory[-1]
        nesting_slacks = [
            row["upper_nesting_slack_numerator"]
            for row in cylinder_rows
            if row["upper_nesting_slack_numerator"] is not None
        ]
        capacity_utilizations = [
            Fraction(
                9 * row["appended_block_digit"],
                row["appended_block_base"]
                * cylinder_rows[index - 1]["bound_coefficient_numerator"]
                - row["bound_coefficient_numerator"],
            )
            for index, row in enumerate(cylinder_rows)
            if index > 0
        ]
        maximum_capacity_utilization = max(capacity_utilizations, default=Fraction(0))
        return {
            "requested_trap_depth": depth,
            "dyadic_anchor": anchor,
            "first_base_clear_length": first_clear_length,
            "first_firing_length": first_fire,
            "exact_residue_delay": first_fire - first_clear_length,
            "rational_reconstruction": {
                "numerator": numerator,
                "denominator": denominator,
                "reduced_numerator": witness.reduced_value.numerator,
                "reduced_denominator": witness.reduced_value.denominator,
                "denominator_band_minimum": minimum_denominator,
                "denominator_band_maximum": maximum_denominator,
                "target_subdivision_numerator": witness.target_numerator,
                "target_subdivision_denominator": witness.target_denominator,
                "denominator_cap": witness.denominator_cap,
            },
            "cylinder": {
                "constraint_count": depth,
                "active_lower_label": interval.active_lower_label,
                "active_upper_label": interval.active_upper_label,
                "width_numerator": interval.width.numerator,
                "width_denominator": interval.width.denominator,
                "consecutive_nesting_certified": nesting.nested,
                "first_nesting_failure_index": nesting.first_failure_index,
                "collapses_to_final_constraint": (
                    nesting.collapses_to_final_constraint
                    and interval.active_lower_label == f"offset_{depth - 1}"
                    and interval.active_upper_label == f"offset_{depth - 1}"
                ),
                "minimum_upper_nesting_slack_numerator": (
                    min(nesting_slacks) if nesting_slacks else None
                ),
                "maximum_digit_capacity_utilization": {
                    "numerator": maximum_capacity_utilization.numerator,
                    "denominator": maximum_capacity_utilization.denominator,
                },
                "all_upper_nesting_slacks_nonnegative": all(
                    slack >= 0 for slack in nesting_slacks
                ),
            },
            "verification": {
                "all_requested_steps_trapped": True,
                "zero_lift_transition_count": depth - 1,
                "trajectory_row_count_through_escape": len(trajectory),
                "trajectory_sha256": digest_rows(trajectory),
                "first_trapped_row": trajectory[0],
                "last_requested_trapped_row": trajectory[depth - 1],
                "firing_row": firing_row,
            },
        }
    return None


def build_result(
    anchor: int, depths: tuple[int, ...], max_first_clear_length: int
) -> dict[str, object]:
    max_depth = max(depths)
    blocks = dyadic.build_dyadic_blocks(
        anchor + max_first_clear_length + 3 * max_depth + 4
    )
    witnesses = []
    for depth in depths:
        witness = reconstruct_depth(
            blocks, anchor, depth, max_first_clear_length
        )
        if witness is None:
            raise RuntimeError(f"no affine-cylinder witness reconstructed at depth {depth}")
        witnesses.append(witness)
    strongest = max(witnesses, key=lambda row: row["exact_residue_delay"])
    strongest_delay = strongest["exact_residue_delay"]
    result_summary = (
        f"Exact rational reconstruction produced a canonical residue delay of "
        f"{strongest_delay} at dyadic anchor {anchor}, falsifying every proposed "
        f"uniform post-clear delay cap K <= {strongest_delay - 1}."
    )
    return {
        "schema": "erdos269-affine-cylinder-reconstruction/1",
        "claim_ceiling": (
            "The exact witnesses eliminate bounded-delay constants through the stated "
            "maximum; finite reconstruction does not prove that residue delay is unbounded."
        ),
        "parameters": {
            "dyadic_anchor": anchor,
            "requested_depths": list(depths),
            "max_first_base_clear_length": max_first_clear_length,
            "required_denominator_coprime_to": 30,
        },
        "structural_reduction": {
            "state_variable": "z = q / B",
            "constraint": "0 < M_t*z - F_t <= A_t/9",
            "interval": "max_t(F_t/M_t) < z <= min_t((9*F_t+A_t)/(9*M_t))",
            "one_step_nesting_condition": "9*d_t + A_(t+1) <= b_t*A_t",
            "lean_theorem": "ErdosProblems.Erdos269.affineCylinder_step_nested",
            "nested_interval_consequence": (
                "When consecutive lower endpoints increase and the one-step cap "
                "inequality holds, every constraint contains its successor and the "
                "full depth-d intersection is exactly the final constraint."
            ),
            "meaning": (
                "A rational point in the interval with denominator B in the exact "
                "first-base-clear band reconstructs an actual zero-lift canonical "
                "residue trap; denominator scanning is unnecessary."
            ),
        },
        "strongest_exact_counterexample": strongest,
        "witnesses": witnesses,
        "experiment_contract": build_experiment_contract(
            problem_id="erdos_269",
            target_statement=(
                "Prove irrationality for the running-LCM series generated by the "
                "prime support {2,3,5}."
            ),
            claim_ceiling=(
                "Exact finite-depth witnesses do not prove unbounded delay or the "
                "universal denominator/cofinal-anchor theorem."
            ),
            hypothesis_id="small_uniform_post_clear_delay",
            hypothesis_statement=(
                f"The actual canonical residue always escapes within some post-clear "
                f"delay cap K <= {strongest_delay - 1}."
            ),
            probe_id="exact_affine_cylinder_rational_reconstruction",
            probe_question=(
                "Do the zero-lift affine cylinders contain denominator-admissible "
                "rational points at depths far beyond the scanned delay-seven traps?"
            ),
            computation=(
                "Intersect the exact affine residue inequalities, reconstruct q/B by "
                "continued fractions inside the exact first-base-clear denominator "
                "band, and replay the canonical integer recurrence through escape."
            ),
            falsifier=(
                f"One exact reconstructed witness with residue delay greater than "
                f"{strongest_delay - 1}."
            ),
            stop_condition=(
                "After a depth-100 reconstruction, retire small fixed-delay laws and "
                "move to a scale-dependent delay bound or an arbitrary-depth theorem; "
                "do not continue by merely increasing a rectangle."
            ),
            survival_consequence=(
                "Failure to populate deep exact cylinders would support a bounded "
                "symbolic obstruction suitable for the Lean residue consumer."
            ),
            falsification_consequence=(
                "Deep admissible cylinders eliminate all small uniform caps and redirect "
                "the producer toward quantitative delay growth in denominator height."
            ),
            consumer_ref=CONSUMER_REF,
            analysis_refs=[ANALYSIS_REF],
            source_refs=[SOURCE_REF, DYADIC_SOURCE_REF, LIBRARY_REF, LEAN_NESTING_REF],
            result_status="exact_one_way_result",
            result_summary=result_summary,
        ),
        "sources": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, DYADIC_SOURCE_REF),
            source_record(REPO_ROOT, LIBRARY_REF),
            source_record(REPO_ROOT, LEAN_NESTING_REF),
        ],
    }


def emit(result: dict[str, object], output: Path, check: bool) -> int:
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    output = output.resolve()
    if check:
        if not output.exists() or output.read_text(encoding="utf-8") != rendered:
            print(f"stale receipt: {output}", file=sys.stderr)
            return 1
        print(json.dumps({"status": "current", "output": str(output)}))
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(output)}))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--anchor", type=int, default=100)
    parser.add_argument(
        "--depths",
        type=parse_depths,
        default=DEFAULT_DEPTHS,
        help="comma-separated requested trap depths",
    )
    parser.add_argument("--max-first-clear-length", type=int, default=220)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.anchor < 1:
        parser.error("--anchor must be positive")
    if args.max_first_clear_length <= max(args.depths) + 2:
        parser.error("--max-first-clear-length must exceed max(depths)+2")
    return emit(
        build_result(args.anchor, args.depths, args.max_first_clear_length),
        args.output,
        args.check,
    )


if __name__ == "__main__":
    raise SystemExit(main())
