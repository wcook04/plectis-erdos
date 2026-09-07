#!/usr/bin/env python3
"""Exact bounded scan for real lifts of characteristic-two Lambert supports.

For a periodic binary word ``g`` define the unique Boolean support

    b(n) = sum_{d|n} g(d) mu(n/d)  (mod 2).

Then the selected-divisor multiplicity is ``g`` modulo two, so this is an
infinite rational Lambert construction in characteristic two whenever the
support is infinite.  Boolean reduction is injective, hence there is no
Hensel freedom above this first layer: for a fixed ``g`` this ``b`` is the
only possible real Boolean lift.

The program exhausts all source words through a declared period, encloses
the corresponding real Mersenne sum by exact dyadic integers, and challenges
all eventually-periodic real binary outputs inside declared preperiod/period
bounds.  One certified mismatch rules out that bounded real lift; a survivor
is only a construction candidate, never an infinite proof.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


SCRIPT_PATH = Path(__file__).resolve()
REPO_ROOT = SCRIPT_PATH.parents[3]
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "characteristic_two_real_lift_scan_receipt.json"
)


def canonical_bytes(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def squarefree_sieve(limit: int) -> bytearray:
    result = bytearray([1]) * (limit + 1)
    result[0] = 0
    for prime in range(2, int(limit**0.5) + 1):
        square = prime * prime
        for multiple in range(square, limit + 1, square):
            result[multiple] = 0
    return result


def source_bit(word: int, preperiod: int, period: int, rank: int) -> int:
    index = rank - 1 if rank <= preperiod else preperiod + (rank - preperiod - 1) % period
    return (word >> index) & 1


def support_for_word(
    word: int, preperiod: int, period: int, depth: int, squarefree: bytearray
) -> bytearray:
    """Return ``(g * mu) mod 2``; modulo two, mu is squarefree support."""
    support = bytearray(depth + 1)
    for divisor in range(1, depth + 1):
        if not source_bit(word, preperiod, period, divisor):
            continue
        for quotient in range(1, depth // divisor + 1):
            if squarefree[quotient]:
                support[divisor * quotient] ^= 1
    return support


def verify_characteristic_two(
    word: int, preperiod: int, period: int, support: bytearray, depth: int
) -> int:
    load_parity = bytearray(depth + 1)
    for divisor in range(1, depth + 1):
        if support[divisor]:
            for multiple in range(divisor, depth + 1, divisor):
                load_parity[multiple] ^= 1
    return sum(
        load_parity[rank] != source_bit(word, preperiod, period, rank)
        for rank in range(1, depth + 1)
    )


def mersenne_scaled_weights(depth: int, precision: int) -> list[int]:
    scale = 1 << precision
    return [0] + [scale // ((1 << rank) - 1) for rank in range(1, depth + 1)]


def certified_fraction_bits(
    support: bytearray, weights: list[int], depth: int, precision: int
) -> tuple[str, dict[str, int]]:
    selected = [rank for rank in range(1, depth + 1) if support[rank]]
    lower = sum(weights[rank] for rank in selected)
    # Each floored selected term loses < 1 scaled unit.  The unrestricted
    # omitted support tail is < 2^(1-depth), hence < 2^(precision+1-depth)
    # scaled units.  Use a strict integer upper endpoint.
    tail_units = 1 << max(0, precision + 1 - depth)
    upper_exclusive = lower + len(selected) + tail_units + 1
    high = upper_exclusive - 1
    total_bits = precision + 1  # one integer bit; the total Mersenne sum is < 2
    difference = lower ^ high
    common_bits = total_bits if difference == 0 else total_bits - difference.bit_length()
    prefix = format(lower, f"0{total_bits}b")[:common_bits]
    fraction = prefix[1:] if prefix else ""
    return fraction, {
        "selected_count": len(selected),
        "late_selected_count": sum(support[depth // 2 + 1 :]),
        "lower_scaled": lower,
        "upper_exclusive_scaled": upper_exclusive,
        "precision": precision,
        "certified_fraction_bit_count": len(fraction),
    }


def best_periodic_fit(bits: str, max_preperiod: int, max_period: int) -> dict[str, Any]:
    best: dict[str, Any] | None = None
    for preperiod in range(min(max_preperiod, len(bits)) + 1):
        for period in range(1, min(max_period, max(1, len(bits) - preperiod)) + 1):
            matched = preperiod + period
            while matched < len(bits) and bits[matched] == bits[
                preperiod + (matched - preperiod) % period
            ]:
                matched += 1
            row = {
                "preperiod": preperiod,
                "period": period,
                "matched_fraction_bits": matched,
                "mismatch_rank": None if matched == len(bits) else matched + 1,
                "survives_certified_prefix": matched == len(bits),
            }
            key = (matched, -preperiod, -period)
            if best is None or key > (
                best["matched_fraction_bits"],
                -best["preperiod"],
                -best["period"],
            ):
                best = row
    assert best is not None
    return best


def build_receipt(args: argparse.Namespace) -> dict[str, Any]:
    squarefree = squarefree_sieve(args.depth)
    weights = mersenne_scaled_weights(args.depth, args.precision)
    scanned = 0
    infinite_looking = 0
    char_two_violations = 0
    bounded_real_survivors: list[dict[str, Any]] = []
    best: dict[str, Any] | None = None
    period_rows: list[dict[str, int]] = []
    survivor_count = 0
    named_witnesses: dict[str, dict[str, Any]] = {}

    for preperiod in range(args.max_source_preperiod + 1):
        for period in range(1, args.max_source_period + 1):
            source_length = preperiod + period
            family_scanned = 0
            family_live = 0
            family_survivors = 0
            for word in range(1 << source_length):
                scanned += 1
                family_scanned += 1
                support = support_for_word(
                    word, preperiod, period, args.depth, squarefree
                )
                violations = verify_characteristic_two(
                    word, preperiod, period, support, args.depth
                )
                char_two_violations += violations
                bits, enclosure = certified_fraction_bits(
                    support, weights, args.depth, args.precision
                )
                fit = best_periodic_fit(bits, args.max_real_preperiod, args.max_real_period)
                row = {
                    "source_preperiod": preperiod,
                    "source_period": period,
                    "source_word_lsb_first": format(word, f"0{source_length}b")[::-1],
                    **enclosure,
                    **fit,
                }
                if preperiod == 1 and period == 1 and word == 1:
                    named_witnesses["squarefree_delta_one"] = {
                        **row,
                        "squarefree_support_mismatch_count": sum(
                            support[rank] != squarefree[rank]
                            for rank in range(1, args.depth + 1)
                        ),
                    }
                if enclosure["late_selected_count"]:
                    infinite_looking += 1
                    family_live += 1
                if fit["survives_certified_prefix"] and enclosure["late_selected_count"]:
                    survivor_count += 1
                    family_survivors += 1
                    if len(bounded_real_survivors) < args.survivor_sample_limit:
                        bounded_real_survivors.append(row)
                key = (
                    fit["matched_fraction_bits"],
                    enclosure["late_selected_count"],
                    -(preperiod + period),
                    -word,
                )
                if best is None or key > (
                    best["matched_fraction_bits"],
                    best["late_selected_count"],
                    -(best["source_preperiod"] + best["source_period"]),
                    -int(best["source_word_lsb_first"][::-1], 2),
                ):
                    if enclosure["late_selected_count"]:
                        best = row
            period_rows.append(
                {
                    "source_preperiod": preperiod,
                    "source_period": period,
                    "words_scanned": family_scanned,
                    "late_support_words": family_live,
                    "bounded_real_output_survivors": family_survivors,
                }
            )

    assert best is not None

    payload: dict[str, Any] = {
        "schema": "erdos257_characteristic_two_real_lift_scan_v1",
        "programme_target": (
            "Seek a direct rational infinite Boolean Mersenne support by lifting "
            "the complete characteristic-two periodic-output family to the real binary carry."
        ),
        "claim_boundary": (
            "The scan is exhaustive only for the declared source periods, real binary "
            "preperiods/periods, and certified finite output prefix. A survivor is not an "
            "infinite construction; a mismatch excludes only those bounded parameters."
        ),
        "parameters": {
            "depth": args.depth,
            "precision": args.precision,
            "max_source_preperiod": args.max_source_preperiod,
            "max_source_period": args.max_source_period,
            "max_real_preperiod": args.max_real_preperiod,
            "max_real_period": args.max_real_period,
        },
        "source": {
            "script": str(SCRIPT_PATH.relative_to(REPO_ROOT)),
            "script_sha256": sha256(SCRIPT_PATH),
        },
        "rigidity_theorem": (
            "For fixed characteristic-two output g, Dirichlet inversion fixes b=g*mu "
            "in F_2; reduction {0,1}->F_2 is injective, so this is the unique Boolean real lift."
        ),
        "census": {
            "source_words_scanned": scanned,
            "late_support_words": infinite_looking,
            "characteristic_two_identity_violation_count": char_two_violations,
            "bounded_real_output_survivor_count": survivor_count,
            "period_rows": period_rows,
        },
        "bounded_real_output_survivors_sample": bounded_real_survivors,
        "named_witnesses": named_witnesses,
        "best_periodic_fit": best,
        "mechanism_decision": {
            "status": (
                "bounded_real_lift_candidate_survives"
                if survivor_count
                else "bounded_period_characteristic_two_real_lifts_eliminated"
            ),
            "next_action": (
                "analyse the surviving source word with an exact all-depth identity"
                if survivor_count
                else "do not extend this bounded-period lift class without a new all-depth producer"
            ),
        },
    }
    payload["payload_sha256"] = hashlib.sha256(canonical_bytes(payload)).hexdigest()
    return payload


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=1024)
    parser.add_argument("--precision", type=int, default=1280)
    parser.add_argument("--max-source-preperiod", type=int, default=3)
    parser.add_argument("--max-source-period", type=int, default=8)
    parser.add_argument("--max-real-preperiod", type=int, default=32)
    parser.add_argument("--max-real-period", type=int, default=64)
    parser.add_argument("--survivor-sample-limit", type=int, default=12)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.precision < args.depth + 8:
        raise SystemExit("require precision >= depth + 8 for a useful tail enclosure")
    receipt = build_receipt(args)
    rendered = json.dumps(receipt, sort_keys=True, indent=2) + "\n"
    print(
        json.dumps(
            {
                "parameters": receipt["parameters"],
                "census": receipt["census"],
                "best_periodic_fit": receipt["best_periodic_fit"],
                "mechanism_decision": receipt["mechanism_decision"],
                "payload_sha256": receipt["payload_sha256"],
            },
            indent=2,
        )
    )
    if args.check:
        if not args.check.is_file() or args.check.read_text() != rendered:
            print(f"receipt drift: {args.check}")
            return 1
        print(f"CHECKED {args.check}")
        return 0
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(rendered)
    print(f"WROTE {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
