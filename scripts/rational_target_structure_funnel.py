#!/usr/bin/env python3
"""Search rational Erdős 257 targets for structured greedy-support tails.

This is a mechanism probe, not a survival audit.  It exhausts every reduced p/q
in a denominator family, selects the lowest subword-complexity support words,
quotients exact finite-prefix translations, and replays the distinct tail states
deeply.  A matched Bernoulli cohort measures whether any survivor is unusually
low-complexity, periodic, or lag-correlated.

All greedy branches use the certified integer fixed-point engine.  The output is
a canonical JSON receipt linked to this script and the engine source.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import random
import sys
from dataclasses import dataclass
from fractions import Fraction
from math import gcd
from pathlib import Path

SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_DIR = SCRIPT_PATH.parent
REPO_ROOT = SCRIPT_DIR.parents[2]
DEFAULT_RECEIPT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "rational_target_structure_funnel_receipt.json"
)
sys.path.insert(0, str(SCRIPT_DIR))

from cantor_staircase_run_length_lab import Engine  # noqa: E402


CONTROLS = ((1, 2), (1, 21), (4, 9), (1, 465), (15, 188))


@dataclass(frozen=True)
class Row:
    primary: float
    secondary: float
    p: int
    q: int
    prefix_bits: int
    fingerprint: bytes
    cutoff: int

    @property
    def target(self) -> str:
        return f"{self.p}/{self.q}"

    def key(self) -> tuple[float, float, int, int]:
        return self.primary, self.secondary, self.q, self.p


def canonical_bytes(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def pcount(word: list[int], width: int) -> int:
    seen: set[int] = set()
    mask = (1 << width) - 1
    value = 0
    for index, bit in enumerate(word):
        value = ((value << 1) | bit) & mask
        if index >= width - 1:
            seen.add(value)
    return len(seen)


def make_row(
    p: int,
    q: int,
    word: list[int],
    *,
    primary_width: int,
    secondary_width: int,
    cutoff: int,
) -> Row:
    prefix_bits = 0
    for bit in word[:cutoff]:
        prefix_bits = (prefix_bits << 1) | bit
    return Row(
        float(pcount(word, primary_width)),
        float(pcount(word, secondary_width)),
        p,
        q,
        prefix_bits,
        hashlib.blake2b(bytes(word[cutoff:]), digest_size=16).digest(),
        cutoff,
    )


def exact_remainder(row: Row) -> Fraction:
    remainder = Fraction(row.p, row.q)
    for index in range(row.cutoff):
        if (row.prefix_bits >> (row.cutoff - index - 1)) & 1:
            rank = index + 1
            remainder -= Fraction(1, (1 << rank) - 1)
    return remainder


def select_distinct(rows: list[Row], limit: int):
    buckets: dict[bytes, list[tuple[Fraction | None, Row]]] = {}
    selected: list[Row] = []
    equivalences: list[dict[str, object]] = []
    examined = 0
    for row in rows:
        examined += 1
        bucket = buckets.get(row.fingerprint)
        if bucket is None:
            buckets[row.fingerprint] = [(None, row)]
            selected.append(row)
        else:
            remainder = exact_remainder(row)
            representative = None
            for index, (known, candidate) in enumerate(bucket):
                if known is None:
                    known = exact_remainder(candidate)
                    bucket[index] = (known, candidate)
                if known == remainder:
                    representative = candidate
                    break
            if representative is None:
                bucket.append((remainder, row))
                selected.append(row)
            else:
                equivalences.append(
                    {
                        "representative": representative.target,
                        "equivalent_target": row.target,
                        "proved_common_remainder_after_rank": row.cutoff,
                    }
                )
        if len(selected) >= limit:
            break
    return selected, equivalences, examined


def enumerate_screen(args: argparse.Namespace):
    engine = Engine(args.screen_depth)
    rows: list[Row] = []
    counts = {"reduced": 0, "alive": 0, "dead": 0, "precision_failure": 0}
    for q in range(2, args.max_denominator + 1):
        for p in range(1, q):
            if gcd(p, q) != 1:
                continue
            counts["reduced"] += 1
            result = engine.run(p, q)
            status = result["status"]
            if status == "alive":
                counts["alive"] += 1
                rows.append(
                    make_row(
                        p,
                        q,
                        result["word"],
                        primary_width=8,
                        secondary_width=10,
                        cutoff=args.screen_fingerprint_cutoff,
                    )
                )
            elif status == "dead":
                counts["dead"] += 1
            else:
                counts["precision_failure"] += 1
    rows.sort(key=Row.key)
    return rows, counts


def structure_metrics(word: list[int], max_lag: int = 64) -> dict[str, object]:
    complexities = {str(width): pcount(word, width) for width in (8, 12, 16)}
    start = min(1024, len(word) // 4)
    suffix = word[start:]
    packed = 0
    for bit in suffix:
        packed = (packed << 1) | bit
    lag_rows = []
    for lag in range(1, min(max_lag, len(suffix) // 4) + 1):
        trials = len(suffix) - lag
        mask = (1 << trials) - 1
        mismatches = ((packed ^ (packed >> lag)) & mask).bit_count()
        matches = trials - mismatches
        mismatch = mismatches / trials
        z = (matches - trials / 2.0) / math.sqrt(trials / 4.0)
        lag_rows.append((mismatch, -abs(z), lag, z))
    best_periodic = min(lag_rows)
    strongest_lag = min(lag_rows, key=lambda row: row[1])
    return {
        "subword_complexity": complexities,
        "density": round(sum(word) / len(word), 12),
        "best_periodic_lag": best_periodic[2],
        "best_periodic_mismatch": round(best_periodic[0], 12),
        "strongest_lag": strongest_lag[2],
        "strongest_lag_z": round(strongest_lag[3], 12),
    }


def lag_observation(
    word: list[int], lag: int, *, start: int, end: int | None = None
) -> dict[str, object]:
    segment = word[start:end]
    trials = len(segment) - lag
    if trials <= 0:
        raise ValueError("lag confirmation segment is too short")
    packed = 0
    for bit in segment:
        packed = (packed << 1) | bit
    mask = (1 << trials) - 1
    mismatches = ((packed ^ (packed >> lag)) & mask).bit_count()
    matches = trials - mismatches
    z = (matches - trials / 2.0) / math.sqrt(trials / 4.0)
    return {
        "start_rank_zero_based": start,
        "end_rank_exclusive": start + len(segment),
        "lag": lag,
        "trials": trials,
        "matches": matches,
        "mismatches": mismatches,
        "mismatch_rate": round(mismatches / trials, 12),
        "z": round(z, 12),
    }


def replay(args: argparse.Namespace, eligible: list[Row]):
    engine = Engine(args.deep_depth)
    eligible_keys = {(row.p, row.q) for row in eligible}
    targets = eligible_keys | set(CONTROLS)
    rows: list[Row] = []
    records: list[dict[str, object]] = []
    counts = {"alive": 0, "dead": 0, "precision_failure": 0}
    for p, q in sorted(targets, key=lambda pair: (pair[1], pair[0])):
        result = engine.run(p, q)
        status = result["status"]
        if status == "PRECISION":
            counts["precision_failure"] += 1
        else:
            counts[status] += 1
        record: dict[str, object] = {
            "target": f"{p}/{q}",
            "p": p,
            "q": q,
            "status": status,
            "eligible": (p, q) in eligible_keys,
            "control": (p, q) in CONTROLS,
        }
        if status == "alive":
            word = result["word"]
            row = make_row(
                p,
                q,
                word,
                primary_width=16,
                secondary_width=12,
                cutoff=args.deep_fingerprint_cutoff,
            )
            record.update(structure_metrics(word))
            record["word_sha256"] = hashlib.sha256(bytes(word)).hexdigest()
            record["tail_fingerprint"] = row.fingerprint.hex()
            if (p, q) in eligible_keys:
                rows.append(row)
        else:
            record["death_rank"] = result["death"]
        records.append(record)
    rows.sort(key=Row.key)
    records.sort(
        key=lambda record: (
            not bool(record["eligible"]),
            int((record.get("subword_complexity") or {}).get("16", 10**9)),
            int(record["q"]),
            int(record["p"]),
        )
    )
    return rows, records, counts


def null_cohort(args: argparse.Namespace) -> list[dict[str, object]]:
    rows = []
    for index in range(args.null_size):
        rng = random.Random(args.null_seed + index)
        word = [rng.getrandbits(1) for _ in range(args.deep_depth)]
        rows.append(structure_metrics(word))
    return rows


def axis_summary(values: list[float]) -> dict[str, float]:
    ordered = sorted(values)
    return {
        "min": round(ordered[0], 12),
        "q01": round(ordered[int(0.01 * (len(ordered) - 1))], 12),
        "median": round(ordered[len(ordered) // 2], 12),
        "q99": round(ordered[int(0.99 * (len(ordered) - 1))], 12),
        "max": round(ordered[-1], 12),
        "mean": round(sum(ordered) / len(ordered), 12),
    }


def summarize_null(rows: list[dict[str, object]]) -> dict[str, object]:
    return {
        "p12": axis_summary([float(row["subword_complexity"]["12"]) for row in rows]),
        "p16": axis_summary([float(row["subword_complexity"]["16"]) for row in rows]),
        "best_periodic_mismatch": axis_summary(
            [float(row["best_periodic_mismatch"]) for row in rows]
        ),
        "max_abs_lag_z": axis_summary([abs(float(row["strongest_lag_z"])) for row in rows]),
    }


def build_receipt(args: argparse.Namespace) -> dict[str, object]:
    if args.screen_depth <= args.screen_fingerprint_cutoff:
        raise ValueError("screen-depth must exceed screen-fingerprint-cutoff")
    if args.deep_depth <= args.deep_fingerprint_cutoff:
        raise ValueError("deep-depth must exceed deep-fingerprint-cutoff")
    if args.confirm_depth <= args.deep_depth:
        raise ValueError("confirm-depth must exceed deep-depth")
    screen_rows, counts = enumerate_screen(args)
    selected, screen_equivalences, examined = select_distinct(screen_rows, args.funnel_size)
    deep_rows, records, deep_counts = replay(args, selected)
    deep_distinct, deep_equivalences, _ = select_distinct(deep_rows, len(deep_rows))
    null_rows = null_cohort(args)
    null_summary = summarize_null(null_rows)
    eligible_records = [row for row in records if row["eligible"] and row["status"] == "alive"]
    complexity_candidate = min(
        eligible_records, key=lambda row: int(row["subword_complexity"]["12"])
    )
    candidate_min_p12 = int(complexity_candidate["subword_complexity"]["12"])
    candidate_min_p16 = min(int(row["subword_complexity"]["16"]) for row in eligible_records)
    candidate_min_mismatch = min(float(row["best_periodic_mismatch"]) for row in eligible_records)
    lag_candidate = max(eligible_records, key=lambda row: abs(float(row["strongest_lag_z"])))
    candidate_max_abs_z = abs(float(lag_candidate["strongest_lag_z"]))
    exploratory_axes = []
    if candidate_min_p12 < null_summary["p12"]["min"]:
        exploratory_axes.append("subword_complexity_p12_below_matched_null_min")
    if candidate_min_p16 < null_summary["p16"]["min"]:
        exploratory_axes.append("subword_complexity_p16_below_matched_null_min")
    if candidate_min_mismatch < null_summary["best_periodic_mismatch"]["min"]:
        exploratory_axes.append("periodic_mismatch_below_matched_null_min")
    if candidate_max_abs_z > null_summary["max_abs_lag_z"]["max"]:
        exploratory_axes.append("absolute_lag_z_above_matched_null_max")

    lag = int(lag_candidate["strongest_lag"])
    initial_z = float(lag_candidate["strongest_lag_z"])
    single_cell_p = math.erfc(candidate_max_abs_z / math.sqrt(2.0))
    tested_lag_cells = len(eligible_records) * 64
    familywise_p = 1.0 - math.exp(tested_lag_cells * math.log1p(-single_cell_p))
    confirm_engine = Engine(args.confirm_depth)
    confirm_run = confirm_engine.run(int(lag_candidate["p"]), int(lag_candidate["q"]))
    if confirm_run["status"] != "alive":
        raise RuntimeError(
            f"lag candidate {lag_candidate['target']} failed confirm replay: {confirm_run['status']}"
        )
    independent_confirmation = lag_observation(
        confirm_run["word"], lag, start=args.deep_depth, end=args.confirm_depth
    )
    initial_trials = args.deep_depth - min(1024, args.deep_depth // 4) - lag
    expected_z_if_persistent = initial_z * math.sqrt(
        float(independent_confirmation["trials"]) / initial_trials
    )
    confirm_z = float(independent_confirmation["z"])
    correlation_persists = (
        initial_z * confirm_z > 0
        and abs(confirm_z) >= 3.290527
        and abs(confirm_z) >= 0.5 * abs(expected_z_if_persistent)
    )
    complexity_run = confirm_engine.run(
        int(complexity_candidate["p"]), int(complexity_candidate["q"])
    )
    if complexity_run["status"] != "alive":
        raise RuntimeError(
            f"complexity candidate {complexity_candidate['target']} failed confirm replay: "
            f"{complexity_run['status']}"
        )
    confirmation_segment = complexity_run["word"][args.deep_depth : args.confirm_depth]
    confirm_candidate_p12 = pcount(confirmation_segment, 12)
    confirm_null_p12 = []
    confirm_length = args.confirm_depth - args.deep_depth
    for index in range(args.null_size):
        rng = random.Random(args.null_seed + 10_000_000 + index)
        word = [rng.getrandbits(1) for _ in range(confirm_length)]
        confirm_null_p12.append(pcount(word, 12))
    confirm_p12_summary = axis_summary([float(value) for value in confirm_null_p12])
    complexity_persists = confirm_candidate_p12 < confirm_p12_summary["min"]
    robust_axes = []
    if correlation_persists:
        robust_axes.append("lag_correlation")
    if complexity_persists:
        robust_axes.append("low_subword_complexity")

    engine_path = SCRIPT_DIR / "cantor_staircase_run_length_lab.py"
    payload: dict[str, object] = {
        "schema": "erdos257_rational_target_structure_funnel_v1",
        "programme_target": "Solve Erdős 257; rational targets are disposable probes.",
        "claim_boundary": (
            "Finite word statistics can open or disfavor a structural mechanism; they cannot "
            "prove infinite survival, eventual periodicity, or irrationality."
        ),
        "mechanism_falsifier": (
            "A greedy tail with complexity or short-lag structure beyond the matched-random "
            "extremes opens a low-complexity/automatic analysis lane. Absence disfavors that "
            "lane in the declared exhaustive family and selected cohort."
        ),
        "parameters": {
            "max_denominator": args.max_denominator,
            "screen_depth": args.screen_depth,
            "screen_metric": "lexicographic p(8), p(10); smaller is more structured",
            "screen_fingerprint_cutoff": args.screen_fingerprint_cutoff,
            "funnel_size": args.funnel_size,
            "deep_depth": args.deep_depth,
            "deep_metric": "lexicographic p(16), p(12); smaller is more structured",
            "deep_fingerprint_cutoff": args.deep_fingerprint_cutoff,
            "null_size": args.null_size,
            "null_seed": args.null_seed,
            "confirm_depth": args.confirm_depth,
        },
        "source": {
            "script": str(SCRIPT_PATH.relative_to(REPO_ROOT)),
            "script_sha256": file_sha256(SCRIPT_PATH),
            "engine": str(engine_path.relative_to(REPO_ROOT)),
            "engine_sha256": file_sha256(engine_path),
        },
        "screen": {
            "counts": counts,
            "raw_rows_examined_for_selection": examined,
            "selected_distinct_tail_states": len(selected),
            "exact_equivalent_targets_skipped": len(screen_equivalences),
            "equivalences": screen_equivalences,
            "top": [
                {"target": row.target, "p8": int(row.primary), "p10": int(row.secondary)}
                for row in selected[:64]
            ],
        },
        "deep_replay": {
            "counts": deep_counts,
            "distinct_tail_state_count": len(deep_distinct),
            "exact_equivalent_target_count": len(deep_equivalences),
            "equivalences": deep_equivalences,
            "records": records,
        },
        "matched_bernoulli_null": null_summary,
        "observed_extremes": {
            "candidate_min_p12": candidate_min_p12,
            "candidate_min_p16": candidate_min_p16,
            "candidate_min_periodic_mismatch": round(candidate_min_mismatch, 12),
            "candidate_max_abs_lag_z": round(candidate_max_abs_z, 12),
            "exploratory_axes_against_one_null_cohort": exploratory_axes,
            "lag_multiple_testing": {
                "tested_cells": tested_lag_cells,
                "normal_approx_single_cell_p": round(single_cell_p, 12),
                "normal_approx_familywise_p": round(familywise_p, 12),
            },
            "independent_lag_confirmation": {
                "target": lag_candidate["target"],
                "selected_lag": lag,
                "initial_selected_z": round(initial_z, 12),
                "expected_new_segment_z_if_persistent": round(expected_z_if_persistent, 12),
                "new_segment": independent_confirmation,
                "persistence_threshold": (
                    "same sign, |z| >= 3.290527, and at least half the persistent-signal expectation"
                ),
                "status": "correlation_persists" if correlation_persists else "selection_spike_collapsed",
            },
            "independent_complexity_confirmation": {
                "target": complexity_candidate["target"],
                "initial_p12": candidate_min_p12,
                "new_segment_start_rank_zero_based": args.deep_depth,
                "new_segment_end_rank_exclusive": args.confirm_depth,
                "new_segment_p12": confirm_candidate_p12,
                "matched_null_p12": confirm_p12_summary,
                "persistence_rule": "candidate new-segment p12 below the minimum of the predeclared matched null cohort",
                "status": "complexity_deficit_persists" if complexity_persists else "selection_deficit_filled_in",
            },
            "robust_outlier_axes": robust_axes,
            "status": "structural_outlier_confirmed" if robust_axes else "no_robust_structural_outlier",
        },
    }
    payload["payload_sha256"] = hashlib.sha256(canonical_bytes(payload)).hexdigest()
    return payload


def print_summary(receipt: dict[str, object]) -> None:
    screen = receipt["screen"]
    observed = receipt["observed_extremes"]
    print(
        f"screen: {screen['counts']['alive']} alive / {screen['counts']['reduced']} reduced; "
        f"selected {screen['selected_distinct_tail_states']} distinct tail states"
    )
    print(
        f"deep structure verdict: {observed['status']}  axes="
        f"{observed['robust_outlier_axes']}"
    )
    print(
        f"min p12={observed['candidate_min_p12']}  min p16={observed['candidate_min_p16']}  "
        f"min mismatch={observed['candidate_min_periodic_mismatch']}  "
        f"max |lag z|={observed['candidate_max_abs_lag_z']}"
    )
    print(f"payload_sha256 {receipt['payload_sha256']}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-denominator", type=int, default=1000)
    parser.add_argument("--screen-depth", type=int, default=400)
    parser.add_argument("--screen-fingerprint-cutoff", type=int, default=256)
    parser.add_argument("--funnel-size", type=int, default=512)
    parser.add_argument("--deep-depth", type=int, default=10000)
    parser.add_argument("--deep-fingerprint-cutoff", type=int, default=512)
    parser.add_argument("--confirm-depth", type=int, default=30000)
    parser.add_argument("--null-size", type=int, default=512)
    parser.add_argument("--null-seed", type=int, default=257000)
    parser.add_argument("--write", type=Path, default=DEFAULT_RECEIPT)
    parser.add_argument("--check", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    receipt = build_receipt(args)
    print_summary(receipt)
    rendered = json.dumps(receipt, sort_keys=True, indent=2) + "\n"
    if args.check:
        if not args.check.is_file():
            print(f"missing receipt: {args.check}", file=sys.stderr)
            return 2
        if args.check.read_text() != rendered:
            print(f"receipt drift: {args.check}", file=sys.stderr)
            return 1
        print(f"CHECKED {args.check}")
        return 0
    args.write.parent.mkdir(parents=True, exist_ok=True)
    args.write.write_text(rendered)
    print(f"WROTE {args.write}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
