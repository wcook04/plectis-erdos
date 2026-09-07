#!/usr/bin/env python3
"""Exact finite-tree evidence for the Erdős 257 half-carry strip.

This evaluator expands every strip-admissible Boolean child.  It uses only
Python integers: bit ``n - 1`` of a word is ``a_n``, and dictionary keys are
the exact terminal carries.  A repeated carry with a different word is
treated as a collision, rather than silently coalesced.

At every odd layer the same pass detects the exact canonical boundary pair,
checks its companion carry and row-``2s`` child formulas, and records the
result in the receipt.

The generated receipt is deliberately finite evidence.  In particular, it
does not promote the observed depth interval to an induction theorem or an
infinite Boolean branch.
"""

from __future__ import annotations

problem_id = "erdos_257"

import argparse
import difflib
import hashlib
import json
from math import isqrt
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
DEFAULT_RECEIPT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/half_carry_reachability_receipt.json"
)
BASE_DEPTH = 18
DEFAULT_MAX_DEPTH = 5000


def strip_bound(n: int) -> int:
    """Return ``B_n = 2 floor(sqrt(n)) + 4`` exactly."""

    return 2 * isqrt(n) + 4


def proper_divisors(n: int) -> tuple[int, ...]:
    """Return the positive proper divisors of ``n`` in increasing order."""

    divisors: list[int] = []
    for d in range(1, isqrt(n) + 1):
        if n % d != 0:
            continue
        q = n // d
        if d < n:
            divisors.append(d)
        if q != d and q < n:
            divisors.append(q)
    return tuple(sorted(divisors))


def coefficient(word: int, divisors: tuple[int, ...]) -> int:
    """Evaluate ``sum_{d | n, d < n} a_d`` for one packed word."""

    return sum((word >> (d - 1)) & 1 for d in divisors)


def common_prefix_length(words: Any, depth: int) -> int:
    """Longest common prefix in the exponent order ``a_1, ..., a_depth``."""

    iterator = iter(words)
    first = next(iterator)
    difference = 0
    for word in iterator:
        difference |= first ^ word
    if difference == 0:
        return depth
    # Exponent order is least-significant bit first, so the first differing
    # exponent is exactly the least-significant set bit of ``difference``.
    return (difference & -difference).bit_length() - 1


def word_string(word: int, depth: int) -> str:
    """Render a packed word in mathematical order ``a_1 ... a_depth``."""

    return "".join("1" if (word >> i) & 1 else "0" for i in range(depth))


def cylinder_summary(states: dict[int, int], depth: int) -> dict[str, Any]:
    """Return and validate the canonical cylinder summary at one depth."""

    bound = strip_bound(depth)
    expected_carries = list(range(1, bound + 1))
    if sorted(states) != expected_carries:
        raise AssertionError(f"depth {depth} is not a full terminal strip")

    prefix_length = common_prefix_length(states.values(), depth)
    strings = {carry: word_string(states[carry], depth) for carry in expected_carries}
    prefix = strings[1][:prefix_length]
    suffix_width = depth - prefix_length
    suffix_values = {
        carry: int(bits[prefix_length:] or "0", 2) for carry, bits in strings.items()
    }
    endpoint = suffix_values[1] + 1
    for carry, value in suffix_values.items():
        if value != endpoint - carry:
            raise AssertionError(
                f"depth {depth} is not the claimed terminally indexed cylinder: "
                f"carry {carry}, suffix {value}, endpoint {endpoint}"
            )
    if not bound <= endpoint <= (1 << suffix_width):
        raise AssertionError(f"depth {depth} cylinder endpoint is outside its headroom")

    return {
        "bound": bound,
        "common_prefix": prefix,
        "common_prefix_length": prefix_length,
        "endpoint": endpoint,
        "suffix_encoding": "bin_L(endpoint - terminal_carry)",
        "suffix_width": suffix_width,
        "terminal_carry_range": [1, bound],
        "unique_terminal_words": len(states),
    }


def canonical_boundary_records(
    depth: int, states: dict[int, int]
) -> list[dict[str, Any]]:
    """Detect exact ``P∪{s}`` / ``P∪[s+1,2s-1]`` boundary pairs.

    The packed representation uses bit ``d - 1`` for exponent ``d``.  The
    detector is deliberately run against every complete odd layer rather
    than inferred from a cylinder summary.
    """

    if depth < 3 or depth % 2 == 0:
        return []

    s = (depth + 1) // 2
    seam_bit = 1 << (s - 1)
    tail_mask = ((1 << depth) - 1) & ~((1 << s) - 1)
    carry_by_word = {word: carry for carry, word in states.items()}
    feedback_divisors = proper_divisors(2 * s)
    out: list[dict[str, Any]] = []

    for delta, left_word in sorted(states.items()):
        if left_word & seam_bit == 0 or left_word & tail_mask:
            continue

        stem_word = left_word & ~seam_bit
        right_word = stem_word | tail_mask
        companion_carry = carry_by_word.get(right_word)
        if companion_carry is None:
            continue
        if companion_carry != delta + 1:
            raise AssertionError(
                "canonical boundary companion violates pre-feedback gauge: "
                f"s={s}, delta={delta}, companion={companion_carry}"
            )

        lower_feedback_coefficient = coefficient(stem_word, feedback_divisors)
        left_feedback_coefficient = coefficient(left_word, feedback_divisors)
        right_feedback_coefficient = coefficient(right_word, feedback_divisors)
        if left_feedback_coefficient != lower_feedback_coefficient + 1:
            raise AssertionError(
                f"canonical left feedback coefficient changed at s={s}"
            )
        if right_feedback_coefficient != lower_feedback_coefficient:
            raise AssertionError(
                f"canonical right feedback coefficient changed at s={s}"
            )

        hole = 2 * delta - lower_feedback_coefficient
        child_carries = {
            "left_bit_0": 2 * delta - left_feedback_coefficient,
            "left_bit_1": 2 * delta - left_feedback_coefficient - 1,
            "right_bit_0": 2 * companion_carry - right_feedback_coefficient,
            "right_bit_1": 2 * companion_carry - right_feedback_coefficient - 1,
        }
        expected_child_carries = {
            "left_bit_0": hole - 1,
            "left_bit_1": hole - 2,
            "right_bit_0": hole + 2,
            "right_bit_1": hole + 1,
        }
        if child_carries != expected_child_carries:
            raise AssertionError(
                "canonical row-2s child formula changed: "
                f"s={s}, actual={child_carries}, expected={expected_child_carries}"
            )

        out.append(
            {
                "P": [
                    d for d in range(2, s) if stem_word & (1 << (d - 1))
                ],
                "companion_carry": companion_carry,
                "delta": delta,
                "depth": depth,
                "hole": hole,
                "lower_feedback_coefficient": lower_feedback_coefficient,
                "row_2s_child_carries": child_carries,
                "s": s,
                "terminal_bound_at_feedback": strip_bound(2 * s),
            }
        )

    return out


def canonical_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def attach_payload_hash(payload: dict[str, Any]) -> dict[str, Any]:
    encoded = json.dumps(payload, separators=(",", ":"), sort_keys=True).encode()
    return {**payload, "receipt_payload_sha256": hashlib.sha256(encoded).hexdigest()}


def update_tree_trace(trace: Any, depth: int, states: dict[int, int]) -> None:
    """Bind one complete depth layer into a platform-stable binary digest."""

    byte_width = (depth + 7) // 8
    trace.update(depth.to_bytes(8, "big"))
    trace.update(len(states).to_bytes(8, "big"))
    for carry, word in sorted(states.items()):
        trace.update(carry.to_bytes(8, "big"))
        trace.update(word.to_bytes(byte_width, "little"))


def evaluate(max_depth: int) -> dict[str, Any]:
    if max_depth < BASE_DEPTH:
        raise ValueError(f"max_depth must be at least {BASE_DEPTH}")

    # At depth one, a_1 = 0 and K_1 = 1.
    states: dict[int, int] = {1: 0}
    depth13: dict[int, int] | None = None
    depth14: dict[int, int] | None = None
    depth18: dict[int, int] | None = None
    collision_count = 0
    full_strip_depths: list[int] = []
    full_unique_after_base = True
    noncommon_coefficient_depths: list[int] = []
    maximum_common_prefix_lag = 0
    candidate_child_count = 0
    admissible_child_count = 0
    enumerated_terminal_state_count = len(states)
    tree_trace = hashlib.sha256()
    boundary_records: list[dict[str, Any]] = []
    update_tree_trace(tree_trace, 1, states)

    for n in range(2, max_depth + 1):
        divisors = proper_divisors(n)
        next_states: dict[int, int] = {}
        coefficients_seen: set[int] = set()
        new_bit_mask = 1 << (n - 1)

        for parent_carry, word in states.items():
            proper_coefficient = coefficient(word, divisors)
            coefficients_seen.add(proper_coefficient)
            for new_bit in (0, 1):
                candidate_child_count += 1
                child_carry = 2 * parent_carry - proper_coefficient - new_bit
                if not 1 <= child_carry <= strip_bound(n):
                    continue
                admissible_child_count += 1
                child_word = word | (new_bit_mask if new_bit else 0)
                previous = next_states.get(child_carry)
                if previous is not None and previous != child_word:
                    collision_count += 1
                    raise AssertionError(
                        f"distinct admissible words collide at depth {n}, carry {child_carry}"
                    )
                next_states[child_carry] = child_word

        if not next_states:
            raise AssertionError(f"admissible tree is empty at depth {n}")
        states = next_states
        enumerated_terminal_state_count += len(states)
        update_tree_trace(tree_trace, n, states)
        boundary_records.extend(canonical_boundary_records(n, states))

        carries = sorted(states)
        bound = strip_bound(n)
        full_strip = carries == list(range(1, bound + 1))
        if full_strip:
            full_strip_depths.append(n)
        if n >= BASE_DEPTH and not full_strip:
            full_unique_after_base = False
            missing = sorted(set(range(1, bound + 1)) - set(carries))
            raise AssertionError(f"terminal strip fails at depth {n}; missing {missing}")
        if n >= BASE_DEPTH and len(coefficients_seen) != 1:
            noncommon_coefficient_depths.append(n)

        prefix_length = common_prefix_length(states.values(), n)
        maximum_common_prefix_lag = max(maximum_common_prefix_lag, n - prefix_length)

        if n == 13:
            depth13 = states.copy()
        elif n == 14:
            depth14 = states.copy()
        elif n == BASE_DEPTH:
            depth18 = states.copy()

    assert depth13 is not None and depth14 is not None and depth18 is not None

    base_cylinder = cylinder_summary(depth18, BASE_DEPTH)
    expected_base = {
        "bound": 12,
        "common_prefix": "0110011000000",
        "common_prefix_length": 13,
        "endpoint": 17,
        "suffix_width": 5,
        "terminal_carry_range": [1, 12],
        "unique_terminal_words": 12,
    }
    for field, expected in expected_base.items():
        actual = base_cylinder[field]
        if actual != expected:
            raise AssertionError(
                f"depth-18 cylinder regression at {field}: expected {expected!r}, got {actual!r}"
            )

    depth13_cylinder = cylinder_summary(depth13, 13)
    expected_depth13 = {
        "bound": 10,
        "common_prefix": "011001",
        "common_prefix_length": 6,
        "endpoint": 66,
        "suffix_width": 7,
    }
    for field, expected in expected_depth13.items():
        actual = depth13_cylinder[field]
        if actual != expected:
            raise AssertionError(
                f"depth-13 seam regression at {field}: expected {expected!r}, got {actual!r}"
            )

    missing_at_14 = sorted(set(range(1, strip_bound(14) + 1)) - set(depth14))
    if missing_at_14 != [3] or len(depth14) != 9:
        raise AssertionError(
            f"depth-14 negative regression changed: states={len(depth14)}, missing={missing_at_14}"
        )
    seam_delta = depth13_cylinder["endpoint"] - (1 << (depth13_cylinder["suffix_width"] - 1))
    lower_fixed_coefficient = 1
    missing_carry = 2 * seam_delta - lower_fixed_coefficient
    if (seam_delta, lower_fixed_coefficient, missing_carry) != (2, 1, 3):
        raise AssertionError("depth-14 seam identity changed")

    terminal_cylinder = cylinder_summary(states, max_depth)
    terminal_prefix = terminal_cylinder.pop("common_prefix")
    terminal_cylinder["common_prefix_sha256"] = hashlib.sha256(
        terminal_prefix.encode("ascii")
    ).hexdigest()
    terminal_cylinder["common_prefix_selected_count"] = terminal_prefix.count("1")
    terminal_cylinder["terminal_carry_one_selected_count"] = (
        terminal_prefix.count("1") + (terminal_cylinder["endpoint"] - 1).bit_count()
    )
    full_runs: list[list[int]] = []
    for depth in full_strip_depths:
        if not full_runs or depth != full_runs[-1][1] + 1:
            full_runs.append([depth, depth])
        else:
            full_runs[-1][1] = depth
    if [BASE_DEPTH, max_depth] not in full_runs:
        raise AssertionError("the full-strip run from depth 18 was not recorded")

    expected_boundary_records = [
        {"P": [], "delta": 2, "hole": 4, "lower_feedback_coefficient": 0, "s": 2},
        {"P": [2], "delta": 2, "hole": 3, "lower_feedback_coefficient": 1, "s": 3},
        {
            "P": [2, 3, 6],
            "delta": 2,
            "hole": 3,
            "lower_feedback_coefficient": 1,
            "s": 7,
        },
    ]
    boundary_record_projection = [
        {
            key: record[key]
            for key in ("P", "delta", "hole", "lower_feedback_coefficient", "s")
        }
        for record in boundary_records
        if record["s"] <= DEFAULT_MAX_DEPTH // 2
    ]
    if boundary_record_projection != expected_boundary_records:
        raise AssertionError(
            "canonical boundary scan changed: "
            f"expected={expected_boundary_records}, actual={boundary_record_projection}"
        )

    post_base_start_s = (BASE_DEPTH + 2) // 2
    post_base_records = [
        record for record in boundary_records if record["s"] >= post_base_start_s
    ]
    post_base_inside_strip = [
        record
        for record in post_base_records
        if 1 <= record["hole"] <= record["terminal_bound_at_feedback"]
    ]
    if post_base_inside_strip:
        first = post_base_inside_strip[0]
        raise AssertionError(
            "post-base canonical seam has an in-strip hole: "
            f"s={first['s']}, P={first['P']}, delta={first['delta']}, "
            f"c={first['lower_feedback_coefficient']}, hole={first['hole']}"
        )

    payload: dict[str, Any] = {
        "schema": "erdos257_half_carry_reachability_exact_finite_v2",
        "status": "pass_exact_finite_computation_not_asymptotic_proof",
        "parameters": {
            "base_depth": BASE_DEPTH,
            "max_depth": max_depth,
            "recurrence": "K_1=1; K_n=2*K_(n-1)-sum_{d|n}a_d; a_1=0",
            "strip": "1 <= K_n <= 2*floor(sqrt(n))+4 for every enumerated prefix",
        },
        "method": {
            "arithmetic": "exact Python integers",
            "enumeration": "complete two-child expansion of every admissible word",
            "terminal_state_policy": "distinct words at one carry are a hard collision failure",
        },
        "negative_regression": {
            "depth": 14,
            "depth_13_cylinder": depth13_cylinder,
            "lower_fixed_coefficient": lower_fixed_coefficient,
            "missing_carry": missing_carry,
            "seam_delta": seam_delta,
            "terminal_bound": strip_bound(14),
            "terminal_carries": sorted(depth14),
            "unique_terminal_words": len(depth14),
        },
        "canonical_boundary_scan": {
            "complete_pair_scan_through_s": (max_depth + 1) // 2,
            "exact_records": boundary_records,
            "post_base_in_strip_hole_count": len(post_base_inside_strip),
            "post_base_pair_count": len(post_base_records),
            "post_base_start_s": post_base_start_s,
            "record_count": len(boundary_records),
        },
        "depth_18_base_cylinder": base_cylinder,
        "verified_tree": {
            "admissible_child_count": admissible_child_count,
            "candidate_child_count": candidate_child_count,
            "collision_count": collision_count,
            "complete_enumeration_through_depth": max_depth,
            "enumerated_terminal_state_count": enumerated_terminal_state_count,
            "exact_tree_trace_sha256": tree_trace.hexdigest(),
            "full_strip_depth_runs": full_runs,
            "full_unique_terminal_strip_range": [BASE_DEPTH, max_depth],
            "full_unique_terminal_strip_verified": full_unique_after_base,
            "maximum_common_prefix_lag": maximum_common_prefix_lag,
            "noncommon_proper_coefficient_depths_from_18": noncommon_coefficient_depths,
        },
        "terminal_depth": {"depth": max_depth, **terminal_cylinder},
        "nonclaims": [
            "No statement beyond max_depth is proved.",
            "Full terminal coverage is not itself a uniform induction theorem.",
            "The finite tree does not prove HalfCarryEvenSeamEscape or HalfCarryFullStripReachability.",
            "Long common ancestry is finite evidence, not a reverse-rigidity proof.",
            "Absence of a post-base canonical boundary pair is finite evidence only.",
            "No infinite support, exact value 1/2, or decision of Erdos #257 is certified here.",
        ],
    }
    return attach_payload_hash(payload)


def write_receipt(receipt: dict[str, Any], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(canonical_json(receipt), encoding="utf-8")


def check_receipt(receipt: dict[str, Any], path: Path) -> None:
    expected = canonical_json(receipt)
    try:
        actual = path.read_text(encoding="utf-8")
    except FileNotFoundError as error:
        raise SystemExit(f"receipt missing: {path}") from error
    if actual != expected:
        diff = "".join(
            difflib.unified_diff(
                actual.splitlines(keepends=True),
                expected.splitlines(keepends=True),
                fromfile=str(path),
                tofile="fresh exact evaluation",
            )
        )
        raise SystemExit(f"receipt mismatch:\n{diff}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-depth", type=int, default=DEFAULT_MAX_DEPTH)
    action = parser.add_mutually_exclusive_group()
    action.add_argument(
        "--write",
        nargs="?",
        const=DEFAULT_RECEIPT,
        type=Path,
        metavar="PATH",
        help="write the stable receipt (default: repo state path)",
    )
    action.add_argument(
        "--check",
        nargs="?",
        const=DEFAULT_RECEIPT,
        type=Path,
        metavar="PATH",
        help="compare exact output with a saved receipt (default: repo state path)",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    receipt = evaluate(args.max_depth)
    if args.write is not None:
        write_receipt(receipt, args.write)
        print(
            f"WROTE {args.write} depth={args.max_depth} "
            f"sha256={receipt['receipt_payload_sha256']}"
        )
    elif args.check is not None:
        check_receipt(receipt, args.check)
        print(
            f"PASS depth={args.max_depth} receipt={args.check} "
            f"sha256={receipt['receipt_payload_sha256']}"
        )
    else:
        print(canonical_json(receipt), end="")


if __name__ == "__main__":
    main()
