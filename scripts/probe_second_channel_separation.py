#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Measure the exact rational #257 second-channel predicate on a fixed range.

The checked consumer in ``Erdos249257/GreedyAchievementSet.lean`` reduces one
route to the target value ``1/2`` to the open proposition

    HalfSecondChannelSeparatedRat n

for every ``n >= 7``.  This script independently evaluates the exact rational
greedy recurrence and that predicate for a declared finite range.  It records
the complete failure set, exact least margins, branch counts, and bounded
checkpoints.  It also binds the computation to the four Lean definitions that
specify the recurrence and predicate.

The default range is ``1 <= n <= 1000``.  An empty failure set on that range
does not move the universal quantifier and does not prove that ``1/2`` belongs
to the achievement set.  The output is MEASURED evidence only.

Usage:

    python3 scripts/probe_second_channel_separation.py
    python3 scripts/probe_second_channel_separation.py --write
    python3 scripts/probe_second_channel_separation.py --check
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
SOURCE_PATH = ROOT / "Erdos249257" / "GreedyAchievementSet.lean"
OUTPUT = (
    ROOT
    / "docs"
    / "measurements"
    / "second_channel_separation_probe.json"
)

DEFAULT_MAX_RANK = 1000
OPEN_RANGE_MIN = 7
CHECKPOINT_RANKS = (1, 2, 3, 4, 5, 6, 7, 10, 20, 50, 100, 250, 500, 1000)
BRANCH_WORD_MAX_LENGTH = 8

SOURCE_FRAGMENTS = {
    "mersenneWeightRat": """def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)""",
    "greedyMersenneRemainderRat": """def greedyMersenneRemainderRat (x : ℚ) : ℕ → ℚ
  | 0 => x
  | n + 1 =>
      if mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n then
        greedyMersenneRemainderRat x n - mersenneWeightRat (n + 1)
      else
        greedyMersenneRemainderRat x n""",
    "greedyMersenneSecondChannelPhaseRat": """def greedyMersenneSecondChannelPhaseRat (n : ℕ) : ℚ :=
  (4 : ℚ) ^ n *
    (2 * greedyMersenneRemainderRat (1 / 2 : ℚ) n
      - ((1 : ℚ) / 2) ^ n)""",
    "HalfSecondChannelSeparatedRat": """def HalfSecondChannelSeparatedRat (n : ℕ) : Prop :=
  (1 / 6 : ℚ) + (37 / 56 : ℚ) * ((1 : ℚ) / 2) ^ n
    ≤ |greedyMersenneSecondChannelPhaseRat n - 1 / 3|""",
}


class SourceContractError(ValueError):
    """Raised when the Lean source no longer matches the measured model."""


def digest_text(text: str) -> str:
    """Return a labelled SHA-256 digest for UTF-8 text."""
    return "sha256:" + sha256(text.encode("utf-8")).hexdigest()


def source_contract(text: str) -> dict[str, Any]:
    """Bind the arithmetic model to the exact relevant Lean definitions."""
    rows = []
    for declaration, fragment in SOURCE_FRAGMENTS.items():
        count = text.count(fragment)
        if count != 1:
            raise SourceContractError(
                f"{declaration}: expected one exact source fragment, found {count}"
            )
        offset = text.index(fragment)
        rows.append(
            {
                "declaration": declaration,
                "line": text.count("\n", 0, offset) + 1,
                "fragment_sha256": digest_text(fragment),
            }
        )
    return {
        "source_path": str(SOURCE_PATH.relative_to(ROOT)),
        "source_sha256": digest_text(text),
        "definitions": rows,
        "model_boundary": (
            "The Python Fraction recurrence is an independent exact-arithmetic "
            "implementation of these four source definitions. Lean remains "
            "proof authority; this artifact is finite measured evidence."
        ),
    }


def rational_pair(value: Fraction) -> dict[str, int]:
    """Render one exact rational without decimal approximation."""
    return {
        "numerator": value.numerator,
        "denominator": value.denominator,
    }


def mersenne_weight(rank: int) -> Fraction:
    """Return the exact weight ``1 / (2^rank - 1)`` for positive ``rank``."""
    if rank < 1:
        raise ValueError("rank must be positive")
    return Fraction(1, (1 << rank) - 1)


def direct_phase(rank: int, remainder: Fraction) -> Fraction:
    """Evaluate the exact second-channel phase from the current remainder."""
    if rank < 0:
        raise ValueError("rank must be nonnegative")
    dyadic = 1 << rank
    return dyadic * dyadic * (2 * remainder - Fraction(1, dyadic))


def next_phase_from_branch(
    rank: int, phase: Fraction, took_weight: bool
) -> Fraction:
    """Advance ``phase`` from rank ``rank`` to ``rank + 1``.

    This is algebraically independent of ``direct_phase``:

    * skip: ``phi_(n+1) = 4 phi_n + 2^(n+1)``;
    * take: ``phi_(n+1) = 4 phi_n - 2^(n+1) - 2
      - 2/(2^(n+1)-1)``.
    """
    if rank < 0:
        raise ValueError("rank must be nonnegative")
    next_dyadic = 1 << (rank + 1)
    if not took_weight:
        return 4 * phase + next_dyadic
    return (
        4 * phase
        - next_dyadic
        - 2
        - Fraction(2, next_dyadic - 1)
    )


def separation_threshold(rank: int) -> Fraction:
    """Return ``1/6 + (37/56) 2^(-rank)`` exactly."""
    if rank < 1:
        raise ValueError("rank must be positive")
    return Fraction(1, 6) + Fraction(37, 56 * (1 << rank))


def separation_margin(rank: int, phase: Fraction) -> Fraction:
    """Return distance from the centre minus the required threshold."""
    return abs(phase - Fraction(1, 3)) - separation_threshold(rank)


def checkpoint_row(
    *,
    rank: int,
    took_weight: bool,
    remainder: Fraction,
    phase: Fraction,
    margin: Fraction,
) -> dict[str, Any]:
    """Compress a high-height exact state without serialising huge fractions."""
    return {
        "rank": rank,
        "branch": "take" if took_weight else "skip",
        "separated": margin >= 0,
        "phase_sign": (phase > 0) - (phase < 0),
        "margin_floor": margin.numerator // margin.denominator,
        "remainder_numerator_bits": remainder.numerator.bit_length(),
        "remainder_denominator_bits": remainder.denominator.bit_length(),
        "phase_numerator_bits": phase.numerator.bit_length(),
        "phase_denominator_bits": phase.denominator.bit_length(),
    }


def branch_word_coverage(
    branches: list[str], max_length: int = BRANCH_WORD_MAX_LENGTH
) -> dict[str, Any]:
    """Report every observed and missing short branch word exactly."""
    if not branches or any(branch not in {"S", "T"} for branch in branches):
        raise ValueError("branches must be a nonempty S/T sequence")
    if max_length < 1 or max_length > len(branches):
        raise ValueError("branch-word length must lie inside the sample")

    rows = []
    for length in range(1, max_length + 1):
        observed = {
            "".join(branches[start : start + length])
            for start in range(len(branches) - length + 1)
        }
        possible = {
            "".join(word) for word in product("ST", repeat=length)
        }
        missing = sorted(possible - observed)
        rows.append(
            {
                "length": length,
                "window_start_ranks": {
                    "minimum": 1,
                    "maximum": len(branches) - length + 1,
                },
                "sample_window_count": len(branches) - length + 1,
                "possible_word_count": len(possible),
                "observed_word_count": len(observed),
                "missing_word_count": len(missing),
                "missing_words": missing,
            }
        )
    return {
        "encoding": {"S": "skip", "T": "take"},
        "maximum_word_length": max_length,
        "rows": rows,
        "boundary": (
            "Complete short-word coverage is a property of this finite branch "
            "prefix only. It neither proves normality nor excludes a longer "
            "symbolic constraint."
        ),
    }


def build_measurement(
    *,
    max_rank: int = DEFAULT_MAX_RANK,
    source_text: str | None = None,
) -> dict[str, Any]:
    """Recompute the complete deterministic finite measurement."""
    if max_rank < OPEN_RANGE_MIN:
        raise ValueError(f"max_rank must be at least {OPEN_RANGE_MIN}")
    if source_text is None:
        source_text = SOURCE_PATH.read_text(encoding="utf-8")

    contract = source_contract(source_text)
    checkpoint_set = {rank for rank in CHECKPOINT_RANKS if rank <= max_rank}
    remainder = Fraction(1, 2)
    previous_phase = direct_phase(0, remainder)
    transition_check_count = 0
    failures: list[int] = []
    take_count = 0
    skip_count = 0
    minimum: tuple[Fraction, int] | None = None
    open_minimum: tuple[Fraction, int] | None = None
    checkpoints = []
    branches: list[str] = []

    for rank in range(1, max_rank + 1):
        weight = mersenne_weight(rank)
        took_weight = weight <= remainder
        if took_weight:
            remainder -= weight
            take_count += 1
            branches.append("T")
        else:
            skip_count += 1
            branches.append("S")

        phase = direct_phase(rank, remainder)
        expected = next_phase_from_branch(
            rank - 1, previous_phase, took_weight
        )
        if phase != expected:
            raise AssertionError(
                f"phase recurrence mismatch at rank {rank}"
            )
        transition_check_count += 1
        margin = separation_margin(rank, phase)
        if margin < 0:
            failures.append(rank)

        candidate = (margin, rank)
        if minimum is None or candidate < minimum:
            minimum = candidate
        if rank >= OPEN_RANGE_MIN and (
            open_minimum is None or candidate < open_minimum
        ):
            open_minimum = candidate
        if rank in checkpoint_set:
            checkpoints.append(
                checkpoint_row(
                    rank=rank,
                    took_weight=took_weight,
                    remainder=remainder,
                    phase=phase,
                    margin=margin,
                )
            )
        previous_phase = phase

    assert minimum is not None
    assert open_minimum is not None
    minimum_margin, minimum_rank = minimum
    open_margin, open_rank = open_minimum

    return {
        "schema": "erdos249257-second-channel-separation-probe/1",
        "status": "MEASURED",
        "question_id": "XQ257-second-channel-separation",
        "source_contract": contract,
        "parameters": {
            "target": rational_pair(Fraction(1, 2)),
            "checked_ranks": {"minimum": 1, "maximum": max_rank},
            "open_hypothesis_range": {
                "minimum": OPEN_RANGE_MIN,
                "maximum_checked": max_rank,
            },
            "arithmetic": "Python fractions.Fraction exact rational arithmetic",
        },
        "summary": {
            "checked_rank_count": max_rank,
            "separated_rank_count": max_rank - len(failures),
            "failure_count": len(failures),
            "failure_ranks": failures,
            "first_unchecked_rank": max_rank + 1,
            "transition_check_count": transition_check_count,
            "branch_counts": {
                "take": take_count,
                "skip": skip_count,
            },
            "minimum_margin": {
                "rank": minimum_rank,
                "value": rational_pair(minimum_margin),
            },
            "minimum_margin_on_open_hypothesis_range": {
                "rank": open_rank,
                "value": rational_pair(open_margin),
            },
        },
        "branch_word_coverage": branch_word_coverage(branches),
        "checkpoints": checkpoints,
        "limits": [
            (
                f"The complete exact failure set is reported only for "
                f"1 <= n <= {max_rank}; rank {max_rank + 1} and every later "
                "rank are unmeasured by this artifact."
            ),
            (
                "An empty finite failure set does not prove "
                "HalfSecondChannelSeparatedRat n for every n >= 7 and does "
                "not prove that 1/2 belongs to the Mersenne achievement set."
            ),
            (
                "A later failed rank would close this sufficient socket only; "
                "it would not prove universal Erdos #257."
            ),
            (
                "Checkpoint bit lengths and margin floors compress exact "
                "high-height rationals. The builder recomputes every exact "
                "predicate value before producing the failure set and minima."
            ),
            (
                "The recurrence identity is checked at every transition, but "
                "no invariant preventing a future visit to the shrinking hole "
                "is proved here."
            ),
            (
                "Every branch word of length at most seven occurs in the "
                "measured prefix. This rules out only an absent-word "
                "explanation at those lengths and on this finite range."
            ),
        ],
    }


def render_measurement(data: dict[str, Any]) -> str:
    """Return the canonical generated JSON representation."""
    return json.dumps(data, ensure_ascii=False, indent=1) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--write",
        action="store_true",
        help=f"write the default measurement to {OUTPUT.relative_to(ROOT)}",
    )
    mode.add_argument(
        "--check",
        action="store_true",
        help="fail if the generated default measurement is absent or stale",
    )
    parser.add_argument(
        "--max-rank",
        type=int,
        default=DEFAULT_MAX_RANK,
        help=(
            "finite maximum rank for stdout only; --write and --check require "
            f"the governed default {DEFAULT_MAX_RANK}"
        ),
    )
    args = parser.parse_args()
    if (args.write or args.check) and args.max_rank != DEFAULT_MAX_RANK:
        parser.error("--write and --check require the governed default max rank")

    data = build_measurement(max_rank=args.max_rank)
    rendered = render_measurement(data)
    if args.write:
        OUTPUT.parent.mkdir(parents=True, exist_ok=True)
        OUTPUT.write_text(rendered, encoding="utf-8")
        print(
            "probe_second_channel_separation: wrote "
            f"{OUTPUT.relative_to(ROOT)}"
        )
        return 0
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text(encoding="utf-8") != rendered:
            print(
                "probe_second_channel_separation: generated measurement is stale",
                file=sys.stderr,
            )
            return 1
        print("probe_second_channel_separation: current")
        return 0

    sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
