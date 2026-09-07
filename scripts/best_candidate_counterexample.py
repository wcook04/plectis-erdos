#!/usr/bin/env python3
"""Certified broad-target funnel for rational Erdős 257 probes.

Every greedy branch decision is certified by the integer fixed-point engine in
``cantor_staircase_run_length_lab.py``.  Floating point is used only to rank the
exact support words by

    E_D(y) = max_{8 <= n < D} (R_n(y) - log2(n)).

The screen exhausts a denominator family, then deep-replays a predeclared cohort.
Named historical targets are ineligible controls, not privileged sources.  The
canonical JSON receipt is durable and self-digesting; nothing is written to /tmp.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from dataclasses import dataclass
from math import gcd
from pathlib import Path

problem_id = "erdos_257"

SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_DIR = SCRIPT_PATH.parent
REPO_ROOT = SCRIPT_DIR.parents[2]
DEFAULT_RECEIPT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "rational_target_headroom_funnel_receipt.json"
)
sys.path.insert(0, str(SCRIPT_DIR))

from cantor_staircase_run_length_lab import Engine, run_profile  # noqa: E402


CONTROLS = (
    (1, 2, "historical_target"),
    (1, 21, "historical_target"),
    (4, 9, "historical_target"),
    (1, 465, "historical_target"),
    (1, 5, "historical_target"),
    (5, 12, "historical_target"),
    (15, 188, "prior_screen_leader"),
)


@dataclass(frozen=True)
class Score:
    excursion: float
    witness_rank: int
    p: int
    q: int
    prefix_bits: int
    fingerprint: bytes
    fingerprint_cutoff: int

    @property
    def target(self) -> str:
        return f"{self.p}/{self.q}"

    def key(self) -> tuple[float, int, int]:
        return self.excursion, self.q, self.p


def _canonical_bytes(payload: object) -> bytes:
    return (json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n").encode()


def _file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _score(
    p: int,
    q: int,
    word: list[int],
    n0: int = 8,
    fingerprint_cutoff: int = 256,
) -> Score:
    profile, _ = run_profile(word)
    best = -math.inf
    witness = n0
    for index in range(n0 - 1, len(word) - 1):
        rank = index + 1
        value = profile[index] - math.log2(rank)
        if value > best:
            best = value
            witness = rank
    cutoff = min(fingerprint_cutoff, len(word))
    prefix_bits = 0
    for bit in word[:cutoff]:
        prefix_bits = (prefix_bits << 1) | bit
    fingerprint = hashlib.blake2b(bytes(word[cutoff:]), digest_size=16).digest()
    return Score(best, witness, p, q, prefix_bits, fingerprint, cutoff)


def _score_dict(row: Score) -> dict[str, object]:
    return {
        "target": row.target,
        "p": row.p,
        "q": row.q,
        "excursion": round(row.excursion, 12),
        "witness_rank": row.witness_rank,
    }


def _exact_remainder_at_fingerprint(row: Score):
    """Exact greedy remainder after the fingerprint cutoff.

    This is evaluated only inside a fingerprint-collision bucket, so broad
    enumeration does not pay hundreds of Fraction operations per target.
    """
    from fractions import Fraction

    remainder = Fraction(row.p, row.q)
    cutoff = row.fingerprint_cutoff
    for index in range(cutoff):
        if (row.prefix_bits >> (cutoff - index - 1)) & 1:
            rank = index + 1
            remainder -= Fraction(1, (1 << rank) - 1)
    return remainder


def select_distinct_tail_states(
    rows: list[Score], limit: int
) -> tuple[list[Score], list[dict[str, object]], int]:
    """Select ranked rows modulo *proved* common-remainder equivalence.

    Matching future-word fingerprints only propose an equivalence.  Two targets
    are collapsed only when their exact rational greedy remainders agree at the
    fixed cutoff.  Equality then forces the complete future orbit to agree.
    """
    buckets: dict[bytes, list[tuple[object | None, Score]]] = {}
    selected: list[Score] = []
    equivalences: list[dict[str, object]] = []
    examined = 0
    for row in rows:
        examined += 1
        bucket = buckets.get(row.fingerprint)
        if bucket is None:
            buckets[row.fingerprint] = [(None, row)]
            selected.append(row)
        else:
            remainder = _exact_remainder_at_fingerprint(row)
            representative = None
            for index, (known_remainder, known_row) in enumerate(bucket):
                if known_remainder is None:
                    known_remainder = _exact_remainder_at_fingerprint(known_row)
                    bucket[index] = (known_remainder, known_row)
                if remainder == known_remainder:
                    representative = known_row
                    break
            if representative is None:
                bucket.append((remainder, row))
                selected.append(row)
            else:
                equivalences.append(
                    {
                        "representative": representative.target,
                        "equivalent_target": row.target,
                        "proved_common_remainder_after_rank": row.fingerprint_cutoff,
                    }
                )
        if len(selected) >= limit:
            break
    return selected, equivalences, examined


def screen(max_denominator: int, depth: int) -> tuple[list[Score], dict[str, int]]:
    engine = Engine(depth)
    rows: list[Score] = []
    counts = {"reduced": 0, "alive": 0, "dead": 0, "precision_failure": 0}
    for q in range(2, max_denominator + 1):
        for p in range(1, q):
            if gcd(p, q) != 1:
                continue
            counts["reduced"] += 1
            result = engine.run(p, q)
            if result["status"] == "alive":
                counts["alive"] += 1
                rows.append(_score(p, q, result["word"], fingerprint_cutoff=256))
            elif result["status"] == "dead":
                counts["dead"] += 1
            else:
                counts["precision_failure"] += 1
    rows.sort(key=Score.key)
    return rows, counts


def deep_replay(
    eligible: list[Score], depth: int
) -> tuple[list[Score], list[dict[str, object]], dict[str, int]]:
    engine = Engine(depth)
    eligible_keys = {(row.p, row.q) for row in eligible}
    roles = {(p, q): role for p, q, role in CONTROLS}
    targets = set(eligible_keys) | set(roles)
    rows: list[Score] = []
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
        }
        if (p, q) in roles:
            record["control_role"] = roles[(p, q)]
        if status == "alive":
            row = _score(p, q, result["word"], fingerprint_cutoff=512)
            record.update(_score_dict(row))
            record["density"] = round(sum(result["word"]) / len(result["word"]), 12)
            record["word_sha256"] = hashlib.sha256(bytes(result["word"])).hexdigest()
            record["tail_fingerprint_after_512"] = row.fingerprint.hex()
            if (p, q) in eligible_keys:
                rows.append(row)
        else:
            record["death_rank"] = result["death"]
        records.append(record)
    rows.sort(key=Score.key)
    records.sort(
        key=lambda row: (
            not bool(row["eligible"]),
            float(row.get("excursion", math.inf)),
            int(row["q"]),
            int(row["p"]),
        )
    )
    return rows, records, counts


def build_receipt(args: argparse.Namespace) -> dict[str, object]:
    if args.screen_depth <= 8 or args.deep_depth < args.screen_depth:
        raise ValueError("require 8 < screen-depth <= deep-depth")
    if args.funnel_size < args.top_k:
        raise ValueError("funnel-size must be at least top-k")

    screen_rows, screen_counts = screen(args.max_denominator, args.screen_depth)
    funnel, screen_equivalences, screen_examined = select_distinct_tail_states(
        screen_rows, args.funnel_size
    )
    deep_rows, deep_records, deep_counts = deep_replay(funnel, args.deep_depth)
    deep_distinct, deep_equivalences, _ = select_distinct_tail_states(
        deep_rows, len(deep_rows)
    )

    engine_path = SCRIPT_DIR / "cantor_staircase_run_length_lab.py"
    payload: dict[str, object] = {
        "schema": "erdos257_rational_target_headroom_funnel_v1",
        "claim_boundary": (
            "This selects disposable probes for mechanism search. Finite survival and low "
            "excursion are not an infinite-support construction or a proof of survival."
        ),
        "programme_target": "Solve Erdős Problem 257; no rational target is the objective.",
        "method": {
            "metric": "E_D(y)=max_{8<=n<D}(R_n(y)-log2(n)); smaller is safer",
            "branch_certification": (
                "integer fixed-point interval decisions; floating point only ranks exact words; "
                "unresolved exact-boundary cases are counted and excluded rather than guessed"
            ),
            "selection_policy": (
                "exhaust the declared reduced-rational family, select only by the predeclared "
                "metric modulo exact common-remainder equivalence, then deep-replay the selected "
                "cohort; historical targets are controls"
            ),
            "equivalence_rule": (
                "A matching future-word fingerprint is only a candidate. Targets are collapsed "
                "only after exact Fraction equality of their greedy remainders at the declared "
                "cutoff; equality makes the entire later greedy orbit identical."
            ),
            "tie_break": "excursion, denominator, numerator",
        },
        "parameters": {
            "max_denominator": args.max_denominator,
            "screen_depth": args.screen_depth,
            "funnel_size": args.funnel_size,
            "deep_depth": args.deep_depth,
            "top_k": args.top_k,
        },
        "source": {
            "script": str(SCRIPT_PATH.relative_to(REPO_ROOT)),
            "script_sha256": _file_sha256(SCRIPT_PATH),
            "engine": str(engine_path.relative_to(REPO_ROOT)),
            "engine_sha256": _file_sha256(engine_path),
        },
        "screen": {
            "counts": screen_counts,
            "selected_count": len(funnel),
            "raw_rows_examined_for_selection": screen_examined,
            "exact_equivalent_targets_skipped": len(screen_equivalences),
            "equivalences": screen_equivalences,
            "top": [_score_dict(row) for row in funnel[: args.top_k]],
            "selection_boundary": _score_dict(funnel[-1]) if funnel else None,
        },
        "deep_replay": {
            "counts": deep_counts,
            "eligible_alive_count": len(deep_rows),
            "distinct_tail_state_count": len(deep_distinct),
            "exact_equivalent_target_count": len(deep_equivalences),
            "equivalences": deep_equivalences,
            "top": [_score_dict(row) for row in deep_distinct[: args.top_k]],
            "records": deep_records,
        },
    }
    payload["payload_sha256"] = hashlib.sha256(_canonical_bytes(payload)).hexdigest()
    return payload


def print_summary(receipt: dict[str, object]) -> None:
    params = receipt["parameters"]
    counts = receipt["screen"]["counts"]
    print(
        f"q <= {params['max_denominator']}, D={params['screen_depth']}: "
        f"{counts['alive']} alive / {counts['reduced']} reduced targets"
    )
    print(
        f"deep replay: {params['funnel_size']} selected targets to D={params['deep_depth']}"
    )
    for rank, row in enumerate(receipt["deep_replay"]["top"][:15], start=1):
        print(
            f"{rank:>3} {row['target']:>12} E={row['excursion']:>9.6f} "
            f"witness={row['witness_rank']}"
        )
    print(f"payload_sha256 {receipt['payload_sha256']}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-denominator", type=int, default=1000)
    parser.add_argument("--screen-depth", type=int, default=400)
    parser.add_argument("--funnel-size", type=int, default=512)
    parser.add_argument("--deep-depth", type=int, default=10000)
    parser.add_argument("--top-k", type=int, default=32)
    parser.add_argument("--write", type=Path, default=DEFAULT_RECEIPT)
    parser.add_argument(
        "--check",
        type=Path,
        help="recompute and fail unless canonical output equals this receipt",
    )
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
