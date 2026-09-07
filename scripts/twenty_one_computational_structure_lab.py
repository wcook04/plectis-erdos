#!/usr/bin/env python3
"""Exact finite structure probes for the denominator-21 greedy defect.

This lab replays the canonical quotient-greedy recurrence while its lower
state remains closed.  It is designed to discriminate proposed all-depth
mechanisms, not to promote a longer finite horizon to a proof.

The main probe concerns *strict record ranks* of the Lambert defect ``Q``.
At such a rank ``n`` it tests

    supportCoeff(n + 1) >= Q_n + targetBit(n + 1).

If this held at every strict record rank, then the next defect would not
exceed the record and, more importantly, ``Q_n <= tau(n + 1)``.  The
elementary bound ``tau(m) <= 2 sqrt(m)`` would make the whole defect
subexponential, feeding the existing Lean-checked 1/21 membership consumer.
The script only falsifies or supports this producer on the requested finite
range.
"""

from __future__ import annotations

import argparse
import base64
import difflib
import hashlib
import json
from math import isqrt
from pathlib import Path
import platform
from typing import Any


problem_id = "erdos_257"


REPO_ROOT = Path(__file__).resolve().parents[3]
DEFAULT_RECEIPT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "twenty_one_computational_structure_receipt.json"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/"
    "TwentyOneComputationalStructureLab.md"
)
DIVISOR_SUPPLY_ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/"
    "TwentyOneRecordDivisorSupplyNoGo.md"
)
DEFAULT_RANKS = 500_002
INDEPENDENT_OVERLAP_RANKS = 200_000
INDEPENDENT_OVERLAP_ITINERARY_SHA256 = (
    "d69ba5800ef8d6bd020af6e9b688d62c015d2c43bd0429347bf74106d6e7f921"
)


def canonical_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def canonical_payload_sha256(payload: dict[str, Any]) -> str:
    encoded = json.dumps(
        payload, separators=(",", ":"), sort_keys=True
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def target_bit(rank: int) -> int:
    return int(rank % 6 in (5, 0))


def factorization(value: int) -> list[list[int]]:
    """Return the prime factorization of a positive integer."""

    result: list[list[int]] = []
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            exponent = 0
            while value % divisor == 0:
                value //= divisor
                exponent += 1
            result.append([divisor, exponent])
        divisor = 3 if divisor == 2 else divisor + 2
    if value > 1:
        result.append([value, 1])
    return result


def divisor_count_from_factorization(factors: list[list[int]]) -> int:
    result = 1
    for _, exponent in factors:
        result *= exponent + 1
    return result


def pack_itinerary(bits: bytearray, ranks: int) -> bytes:
    itinerary = bytearray((ranks + 7) // 8)
    for rank in range(1, ranks + 1):
        if bits[rank]:
            itinerary[(rank - 1) // 8] |= 1 << ((rank - 1) % 8)
    return bytes(itinerary)


def packed_itinerary_sha256(bits: bytearray, ranks: int) -> str:
    return hashlib.sha256(pack_itinerary(bits, ranks)).hexdigest()


def replay(ranks: int, window_scales: tuple[int, ...]) -> dict[str, Any]:
    pulse_limit = 2 * ranks + 3
    selected_divisor_counts = [0] * pulse_limit
    bits = bytearray(ranks + 1)
    prefix_counts = [0] * (ranks + 1)
    defects = [0] * (ranks + 1)
    density_debts = [0] * (ranks + 1)
    reservoirs = [0] * (ranks + 1)
    compensated = [0] * (ranks + 1)

    quotient_state = 0
    source_count = 0
    strict_record_ranks: list[int] = []
    # Q_0 = 0 belongs to the record comparison.  Do not count an initial
    # equality Q_1 = Q_0 as a strict record.
    maximum_defect = 0
    minimum_density_debt = (10**18, 0)
    minimum_reservoir = (10**18, 0)
    minimum_compensated = (10**18, 0)
    maximum_reservoir = 0
    maximum_reservoir_rank = 0
    maximum_reservoir_drawdown = (0, 0, 0)

    for rank in range(1, ranks + 1):
        if rank == 1:
            bit = 0
        else:
            previous = rank - 1
            pulse = (
                2 * selected_divisor_counts[2 * previous + 1]
                + selected_divisor_counts[2 * previous + 2]
            )
            source = (4 * pow(2, 2 * previous, 21)) // 21
            core = 4 * quotient_state + source - pulse
            if core < 0:
                raise AssertionError(
                    f"negative quotient core at rank {rank}"
                )
            coin = (1 << rank) + 1
            bit = int(coin <= core)
            quotient_state = core - bit * coin
            if quotient_state > 1 << rank:
                raise AssertionError(
                    f"closed quotient state failed at rank {rank}"
                )

        bits[rank] = bit
        prefix_counts[rank] = prefix_counts[rank - 1] + bit
        if bit:
            for multiple in range(rank, pulse_limit, rank):
                selected_divisor_counts[multiple] += 1

        source_count += target_bit(rank)
        defect = (
            2 * defects[rank - 1]
            + target_bit(rank)
            - selected_divisor_counts[rank]
        )
        if defect < 0:
            raise AssertionError(f"negative defect at rank {rank}")
        defects[rank] = defect

        density_debt = (
            source_count + prefix_counts[rank // 2] - prefix_counts[rank]
        )
        reservoir = density_debt + 3 - defect
        endpoint_compensated = density_debt + 4 - 2 * defect
        density_debts[rank] = density_debt
        reservoirs[rank] = reservoir
        compensated[rank] = endpoint_compensated

        minimum_density_debt = min(
            minimum_density_debt, (density_debt, rank)
        )
        minimum_reservoir = min(minimum_reservoir, (reservoir, rank))
        minimum_compensated = min(
            minimum_compensated, (endpoint_compensated, rank)
        )
        if reservoir > maximum_reservoir:
            maximum_reservoir = reservoir
            maximum_reservoir_rank = rank
        else:
            drawdown = maximum_reservoir - reservoir
            if drawdown > maximum_reservoir_drawdown[0]:
                maximum_reservoir_drawdown = (
                    drawdown,
                    maximum_reservoir_rank,
                    rank,
                )

        if defect > maximum_defect:
            maximum_defect = defect
            strict_record_ranks.append(rank)

    record_rows: list[dict[str, object]] = []
    record_repair_violations: list[dict[str, object]] = []
    for rank in strict_record_ranks:
        if rank == ranks:
            continue
        successor = rank + 1
        successor_factors = factorization(successor)
        repair_margin = (
            selected_divisor_counts[successor]
            - defects[rank]
            - target_bit(successor)
        )
        row: dict[str, object] = {
            "rank": rank,
            "defect": defects[rank],
            "selected": bits[rank],
            "selected_divisor_load": selected_divisor_counts[rank],
            "half_rank": rank // 2,
            "half_rank_defect": defects[rank // 2],
            "successor": successor,
            "successor_selected": bits[successor],
            "successor_factorization": successor_factors,
            "successor_divisor_count": divisor_count_from_factorization(
                successor_factors
            ),
            "successor_selected_divisor_load": (
                selected_divisor_counts[successor]
            ),
            "successor_target_bit": target_bit(successor),
            "successor_defect": defects[successor],
            "successor_defect_change": defects[successor] - defects[rank],
            "record_repair_margin": repair_margin,
            "density_debt_P": density_debts[rank],
            "reservoir_R": reservoirs[rank],
            "endpoint_compensated_F": compensated[rank],
        }
        record_rows.append(row)
        if repair_margin < 0:
            record_repair_violations.append(row)

    record_reset_bound = 4
    record_reset_violations = [
        row
        for row in record_rows
        if int(row["successor_defect"]) > record_reset_bound
    ]
    maximum_record_successor = max(
        (int(row["successor_defect"]), int(row["rank"]))
        for row in record_rows
    )

    strict_record_set = set(strict_record_ranks)
    dyadic_inheritance_rows: list[dict[str, object]] = []
    for parent_rank in strict_record_ranks:
        child_rank = 2 * parent_rank + 1
        child_successor = child_rank + 1
        if child_successor > ranks:
            continue
        parent_successor = parent_rank + 1
        inherited_load = selected_divisor_counts[parent_successor]
        required_load = defects[child_rank] + target_bit(child_successor)
        dyadic_inheritance_rows.append(
            {
                "parent_record_rank": parent_rank,
                "parent_record_defect": defects[parent_rank],
                "parent_successor": parent_successor,
                "parent_successor_defect": defects[parent_successor],
                "inherited_selected_divisor_load": inherited_load,
                "child_rank": child_rank,
                "child_defect": defects[child_rank],
                "child_is_strict_record": child_rank in strict_record_set,
                "child_successor": child_successor,
                "child_successor_target_bit": target_bit(child_successor),
                "child_successor_selected_divisor_load": (
                    selected_divisor_counts[child_successor]
                ),
                "inherited_repair_margin": inherited_load - required_load,
            }
        )
    dyadic_inheritance_violations = [
        row
        for row in dyadic_inheritance_rows
        if int(row["inherited_repair_margin"]) < 0
    ]
    child_record_inheritance_rows = [
        row
        for row in dyadic_inheritance_rows
        if bool(row["child_is_strict_record"])
    ]
    child_record_inheritance_violations = [
        row
        for row in child_record_inheritance_rows
        if int(row["inherited_repair_margin"]) < 0
    ]
    dyadic_child_record_ranks = {
        int(row["child_rank"]) for row in child_record_inheritance_rows
    }
    root_record_ranks = [
        rank
        for rank in strict_record_ranks
        if rank not in dyadic_child_record_ranks
    ]

    dyadic_ranges: list[dict[str, object]] = []
    lower = 1
    while lower <= ranks:
        upper = min(ranks, 2 * lower - 1)
        density_min = min(
            (density_debts[n], n) for n in range(lower, upper + 1)
        )
        reservoir_min = min(
            (reservoirs[n], n) for n in range(lower, upper + 1)
        )
        compensated_min = min(
            (compensated[n], n) for n in range(lower, upper + 1)
        )
        defect_max = max(
            (defects[n], -n) for n in range(lower, upper + 1)
        )
        dyadic_ranges.append(
            {
                "lower": lower,
                "upper": upper,
                "minimum_density_debt": list(density_min),
                "minimum_reservoir": list(reservoir_min),
                "minimum_endpoint_compensated": list(compensated_min),
                "maximum_defect": [defect_max[0], -defect_max[1]],
                "selected_count": (
                    prefix_counts[upper] - prefix_counts[lower - 1]
                ),
            }
        )
        lower *= 2

    sliding_windows: list[dict[str, int]] = []
    for length in window_scales:
        if length > ranks:
            continue
        minimum_change, start = min(
            (reservoirs[n + length] - reservoirs[n], n + 1)
            for n in range(ranks - length + 1)
        )
        sliding_windows.append(
            {
                "length": length,
                "minimum_reservoir_change": minimum_change,
                "first_start_rank": start,
            }
        )

    maximum_sqrt_gap = max(
        defects[n] - 2 * isqrt(n + 1) for n in range(1, ranks + 1)
    )
    independent_overlap: dict[str, Any] | None = None
    if ranks >= INDEPENDENT_OVERLAP_RANKS:
        overlap_digest = packed_itinerary_sha256(
            bits, INDEPENDENT_OVERLAP_RANKS
        )
        overlap_maximum = max(
            (defects[n], -n)
            for n in range(1, INDEPENDENT_OVERLAP_RANKS + 1)
        )
        if overlap_digest != INDEPENDENT_OVERLAP_ITINERARY_SHA256:
            raise AssertionError(
                "the quotient replay disagrees with the independent "
                "dyadic itinerary through rank 200000"
            )
        if prefix_counts[INDEPENDENT_OVERLAP_RANKS] != 99_926:
            raise AssertionError("rank-200000 selected-count regression")
        if (overlap_maximum[0], -overlap_maximum[1]) != (40, 180_179):
            raise AssertionError("rank-200000 defect-record regression")
        independent_overlap = {
            "status": "matched",
            "ranks": INDEPENDENT_OVERLAP_RANKS,
            "validator_ref": (
                "formal_math/erdos257_period_noncollapse/scripts/"
                "check_twenty_one_greedy.py"
            ),
            "packed_itinerary_sha256": overlap_digest,
            "selected_count": prefix_counts[INDEPENDENT_OVERLAP_RANKS],
            "maximum_defect": [overlap_maximum[0], -overlap_maximum[1]],
        }

    packed_itinerary = pack_itinerary(bits, ranks)
    itinerary_sha256 = hashlib.sha256(packed_itinerary).hexdigest()
    payload: dict[str, Any] = {
        "schema": "twenty_one_computational_structure_lab_v1",
        "parameters": {
            "ranks": ranks,
            "window_scales": list(window_scales),
        },
        "authority": {
            "script_ref": str(Path(__file__).resolve().relative_to(REPO_ROOT)),
            "script_sha256": hashlib.sha256(
                Path(__file__).read_bytes()
            ).hexdigest(),
            "analysis_ref": ANALYSIS_REF,
            "companion_analysis_refs": [DIVISOR_SUPPLY_ANALYSIS_REF],
            "python_version": platform.python_version(),
            "method": (
                "exact integer canonical quotient-greedy replay while "
                "every lower state is certified closed"
            ),
            "floating_point_used": False,
            "lean_consumers": [
                "one_div_twenty_one_mem_mersenneAchievementSet_of_"
                "defectSubexponential",
                "finiteErdosSum_ne_one_div_twenty_one",
            ],
            "independent_dyadic_overlap": independent_overlap,
        },
        "selected_count": prefix_counts[ranks],
        "itinerary_sha256": itinerary_sha256,
        "packed_itinerary": {
            "encoding": "base64_little_endian_rank_bitset_v1",
            "rank_mapping": (
                "rank n is bit ((n-1) mod 8) of byte ((n-1) div 8)"
            ),
            "byte_length": len(packed_itinerary),
            "sha256": itinerary_sha256,
            "data_base64": base64.b64encode(packed_itinerary).decode("ascii"),
            "analytic_use": (
                "Downstream divisor, residue, genealogy, and adversarial "
                "probes can recover every selected rank without replaying "
                "the quotient recurrence."
            ),
        },
        "closed_state_verified": True,
        "global_extrema": {
            "minimum_density_debt_P": list(minimum_density_debt),
            "minimum_reservoir_R": list(minimum_reservoir),
            "minimum_endpoint_compensated_F": list(
                minimum_compensated
            ),
            "maximum_defect_Q": [
                maximum_defect,
                strict_record_ranks[-1],
            ],
            "maximum_reservoir_drawdown": list(
                maximum_reservoir_drawdown
            ),
            "maximum_Q_minus_two_floor_sqrt_rank_plus_one": (
                maximum_sqrt_gap
            ),
        },
        "strict_record_count": len(strict_record_ranks),
        "audited_record_successor_count": len(record_rows),
        "strict_record_rows": record_rows,
        "record_reset_candidate": {
            "inequality": (
                "Q_(n+1) <= 4 at every strict Q-record rank n"
            ),
            "maximum_successor_defect": list(maximum_record_successor),
            "violation_count": len(record_reset_violations),
            "violations": record_reset_violations,
            "all_depth_consequence_if_proved": (
                "If strict record ranks are infinite, their successors "
                "give cofinal returns to Q<=4; if they are finite, Q is "
                "globally bounded. Either case feeds the Lean-checked "
                "cofinally-bounded-defect membership theorem."
            ),
            "claim_status": "finite falsification evidence only",
        },
        "record_repair_candidate": {
            "inequality": (
                "supportCoeff(n+1) >= Q_n + targetBit(n+1) "
                "at every strict Q-record rank n"
            ),
            "violation_count": len(record_repair_violations),
            "violations": record_repair_violations,
            "minimum_margin": min(
                (
                    row["record_repair_margin"],
                    row["rank"],
                )
                for row in record_rows
            ),
            "all_depth_consequence_if_proved": (
                "Q_N is bounded by the divisor function at a record "
                "successor, hence Q_N <= 2*sqrt(N+1), which feeds the "
                "Lean-checked subexponential-defect membership theorem"
            ),
            "claim_status": "finite falsification evidence only",
        },
        "dyadic_record_inheritance_candidate": {
            "inequality": (
                "supportCoeff(r+1) >= Q_(2r+1) + targetBit(2r+2) "
                "at every strict record rank r"
            ),
            "tested_parent_record_count": len(dyadic_inheritance_rows),
            "minimum_margin": list(
                min(
                    (
                        int(row["inherited_repair_margin"]),
                        int(row["parent_record_rank"]),
                    )
                    for row in dyadic_inheritance_rows
                )
            ),
            "violation_count": len(dyadic_inheritance_violations),
            "violations": dyadic_inheritance_violations,
            "rows": dyadic_inheritance_rows,
            "strict_child_record_count": len(child_record_inheritance_rows),
            "strict_child_record_ranks": sorted(dyadic_child_record_ranks),
            "strict_child_violation_count": len(
                child_record_inheritance_violations
            ),
            "strict_child_violations": child_record_inheritance_violations,
            "root_record_ranks": root_record_ranks,
            "one_way_consequence_if_proved": (
                "If 2r+1 is also a strict record, then r+1 divides 2r+2. "
                "Selected-divisor inclusion transfers the inherited load "
                "to the child successor and proves RR at that child."
            ),
            "claim_status": "finite falsification evidence only",
        },
        "dyadic_ranges": dyadic_ranges,
        "sliding_reservoir_windows": sliding_windows,
        "claim_status": (
            "finite exact structure evidence; no all-depth producer proved"
        ),
        "mathematical_consequence": {
            "finite_result": (
                "No strict-record repair violation occurs in the requested "
                "canonical quotient-greedy replay."
            ),
            "open_producer": (
                "Prefer the observed strict-record reset Q_(n+1)<=4; "
                "fallback to supportCoeff(n+1) >= Q_n + targetBit(n+1) "
                "at every strict record of the actual 1/21 greedy word. "
                "The dyadic inheritance candidate proves that fallback on "
                "the child-record class, leaving root-record birth separate."
            ),
            "proved_implication": (
                "The reset producer gives cofinal bounded returns or a "
                "global bound. The fallback gives Q_N <= 2*sqrt(N+1). "
                "Either reaches an existing checked 1/21 membership endpoint."
            ),
            "not_claimed": [
                "the strict-record reset bound at all depths",
                "the strict-record repair inequality at all depths",
                "the dyadic record-inheritance inequality at all depths",
                "an all-depth closed quotient trajectory",
                "1/21 achievement-set membership",
                "an infinite rational Mersenne support",
                "a decision of Erdos 257",
            ],
        },
        "analysis_lineage": {
            "motivating_questions": [
                {
                    "id": "RB4",
                    "analysis_ref": ANALYSIS_REF,
                    "machine_field": "record_reset_candidate",
                },
                {
                    "id": "RR",
                    "analysis_ref": ANALYSIS_REF,
                    "machine_field": "record_repair_candidate",
                },
                {
                    "id": "DI",
                    "analysis_ref": DIVISOR_SUPPLY_ANALYSIS_REF,
                    "machine_field": "dyadic_record_inheritance_candidate",
                },
            ],
            "analytic_consumers": [
                {
                    "result": "RB4",
                    "consequence": (
                        "cofinal bounded returns or a global defect bound"
                    ),
                },
                {
                    "result": "RR",
                    "consequence": (
                        "Q_N <= 2*sqrt(N+1), hence subexponential defect"
                    ),
                },
                {
                    "result": "DI on strict child records",
                    "consequence": (
                        "RR follows by divisor inclusion; only root records "
                        "need an independent repair producer"
                    ),
                },
            ],
            "lean_consumers": [
                "one_div_twenty_one_mem_mersenneAchievementSet_of_"
                "defectSubexponential",
                "finiteErdosSum_ne_one_div_twenty_one",
            ],
        },
    }
    payload["receipt_payload_sha256"] = canonical_payload_sha256(payload)
    return payload


def parse_window_scales(raw: str) -> tuple[int, ...]:
    if not raw:
        return ()
    scales = tuple(sorted({int(item) for item in raw.split(",")}))
    if any(scale <= 0 for scale in scales):
        raise ValueError("window scales must be positive")
    return scales


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ranks", type=int, default=DEFAULT_RANKS)
    parser.add_argument(
        "--window-scales",
        default="6,12,24,48,96,192,384,768,1536,3072",
    )
    action = parser.add_mutually_exclusive_group()
    action.add_argument(
        "--write",
        nargs="?",
        const=DEFAULT_RECEIPT,
        type=Path,
        metavar="PATH",
        help="write a source-bound canonical receipt",
    )
    action.add_argument(
        "--check",
        nargs="?",
        const=DEFAULT_RECEIPT,
        type=Path,
        metavar="PATH",
        help="require a saved receipt to match a fresh exact replay",
    )
    args = parser.parse_args()
    if args.ranks < 20:
        raise SystemExit("ranks must be at least twenty")
    result = replay(args.ranks, parse_window_scales(args.window_scales))
    rendered = canonical_json(result)
    if args.write is not None:
        args.write.parent.mkdir(parents=True, exist_ok=True)
        args.write.write_text(rendered, encoding="utf-8")
        print(
            f"WROTE {args.write} ranks={args.ranks} "
            f"sha256={result['receipt_payload_sha256']}"
        )
        return
    if args.check is not None:
        try:
            current = args.check.read_text(encoding="utf-8")
        except FileNotFoundError as error:
            raise SystemExit(f"receipt missing: {args.check}") from error
        if current != rendered:
            diff = "".join(
                difflib.unified_diff(
                    current.splitlines(keepends=True),
                    rendered.splitlines(keepends=True),
                    fromfile=str(args.check),
                    tofile="fresh exact replay",
                )
            )
            raise SystemExit(f"receipt mismatch:\n{diff}")
        print(
            f"CURRENT {args.check} ranks={args.ranks} "
            f"sha256={result['receipt_payload_sha256']}"
        )
        return
    print(rendered, end="")


if __name__ == "__main__":
    main()
