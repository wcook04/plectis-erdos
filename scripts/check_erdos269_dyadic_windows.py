#!/usr/bin/env python3
"""Exact dyadic-window certificate engine for Erdős #269.

The computation uses integers only.  It constructs the actual compressed
`{2,3,5}` dyadic block bases and digits, composes local windows, and asks
whether the canonical least-positive residue escapes the proved quadratic
carry bound.  A successful finite scan is regression evidence for the exact
Lean consumer, never a cofinal theorem.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from bisect import bisect_left, bisect_right
from math import gcd
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
)


PRIMES = (2, 3, 5)
OTHERS = {2: (3, 5), 3: (2, 5), 5: (2, 3)}
PACKET_CERTIFICATES = (
    (1, 1, 2, 4, 60, 47, 13, 9),
    (7, 1, 3, 6, 360, 289, 137, 95),
    (16, 1, 4, 9, 10_800, 8_735, 640, 352),
)
SCRIPT_PATH = Path(__file__).resolve()
SOURCE_REF = str(SCRIPT_PATH.relative_to(REPO_ROOT))
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "DyadicWindowComputationalLab.md"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "ResidueEscape.lean"
)
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse"
    / "erdos269_dyadic_window_receipt.json"
)


def pair_count_lt(target: int, xs: list[int], ys: list[int]) -> int:
    """Count pairs `(x,y)` from increasing power lists with `x*y < target`."""

    j = len(ys) - 1
    while j >= 0 and ys[j] >= target:
        j -= 1
    answer = 0
    for x in xs:
        if x >= target or j < 0:
            break
        while j >= 0 and x * ys[j] >= target:
            j -= 1
        if j < 0:
            break
        answer += j + 1
    return answer


def build_dyadic_blocks(max_a: int) -> list[tuple[int, int, int]]:
    """Return `(block_base, block_digit, ending_jump_index)` for `1 <= a <= max_a`."""

    if max_a < 1:
        raise ValueError("max_a must be positive")
    limit = 1 << (max_a + 1)
    powers: dict[int, list[int]] = {}
    for prime in PRIMES:
        values = [1]
        while values[-1] * prime <= limit:
            values.append(values[-1] * prime)
        powers[prime] = values

    block_counts: dict[int, list[int]] = {}
    cumulative_counts: dict[int, list[int]] = {}
    for prime in PRIMES:
        other_left, other_right = OTHERS[prime]
        widths = [0] * len(powers[prime])
        cumulative = [0] * len(powers[prime])
        for exponent in range(1, len(powers[prime])):
            widths[exponent] = pair_count_lt(
                powers[prime][exponent],
                powers[other_left],
                powers[other_right],
            )
            cumulative[exponent] = cumulative[exponent - 1] + widths[exponent]
        block_counts[prime] = widths
        cumulative_counts[prime] = cumulative

    jumps: list[tuple[int, int, int]] = []
    for prime in PRIMES:
        for exponent, value in enumerate(powers[prime][1:], start=1):
            if value < limit:
                jumps.append((value, prime, exponent))
    jumps.sort()
    jump_values = [value for value, _, _ in jumps]

    blocks: list[tuple[int, int, int]] = []
    for a in range(1, max_a + 1):
        lower = 1 << a
        upper = 1 << (a + 1)
        left = bisect_right(jump_values, lower)
        right = bisect_left(jump_values, upper)
        internal = jumps[left:right]
        internal_channels = [prime for _, prime, _ in internal]
        if len(internal_channels) > 2 or len(set(internal_channels)) != len(
            internal_channels
        ):
            raise AssertionError(("dyadic internal-channel uniqueness", a, internal))

        block_base = 2
        for _, prime, _ in internal:
            block_base *= prime
        if block_base not in (2, 6, 10, 30):
            raise AssertionError(("unexpected block base", a, block_base))

        block_digit = block_counts[2][a + 1]
        suffix_base = 1
        for _, prime, exponent in reversed(internal):
            strip_count = (
                cumulative_counts[prime][exponent] - cumulative_counts[2][a]
            )
            block_digit += (prime - 1) * suffix_base * strip_count
            suffix_base *= prime
        blocks.append((block_base, block_digit, right))
    return blocks


def least_positive_residue(value: int, modulus: int) -> int:
    if modulus <= 0:
        raise ValueError("modulus must be positive")
    residue = value % modulus
    return modulus if residue == 0 else residue


def short_bound(denominator: int, jump_index: int) -> int:
    return denominator * (
        jump_index * jump_index + 10 * jump_index + 27
    ) // 9


def window(
    blocks: list[tuple[int, int, int]], a: int, length: int
) -> tuple[int, int, int]:
    if a < 1 or length < 1 or a + length - 1 > len(blocks):
        raise ValueError("window is outside the constructed block range")
    base, forcing = 1, 0
    for index in range(a - 1, a + length - 1):
        block_base, block_digit, _ = blocks[index]
        base *= block_base
        forcing = block_base * forcing + block_digit
    ending_index = blocks[a + length - 2][2]
    return base, forcing, ending_index


def certificate(
    blocks: list[tuple[int, int, int]], denominator: int, a: int, length: int
) -> dict[str, int | bool | None]:
    base, forcing, ending_index = window(blocks, a, length)
    bound = short_bound(denominator, ending_index)
    residue = least_positive_residue(-denominator * forcing, base)
    last_block_base, last_block_digit, _ = blocks[a + length - 2]
    return {
        "denominator": denominator,
        "dyadic_start": a,
        "length": length,
        "ending_jump_index": ending_index,
        "window_base": base,
        "window_forcing": forcing,
        "last_block_base": last_block_base,
        "last_block_digit": last_block_digit,
        "least_positive_residue": residue,
        "short_bound": bound,
        "base_clears_bound": base > bound,
        "residue_escapes": residue > bound,
        "consumer_fires": base > bound and residue > bound,
    }


def assert_packet_certificates(blocks: list[tuple[int, int, int]]) -> None:
    for expected in PACKET_CERTIFICATES:
        denominator, a, length, ending, base, forcing, residue, bound = expected
        actual = certificate(blocks, denominator, a, length)
        observed = (
            actual["ending_jump_index"],
            actual["window_base"],
            actual["window_forcing"],
            actual["least_positive_residue"],
            actual["short_bound"],
        )
        if observed != (ending, base, forcing, residue, bound):
            raise AssertionError((expected, observed))


def scan(
    blocks: list[tuple[int, int, int]],
    min_denominator: int,
    max_denominator: int,
    start_min: int,
    start_max: int,
    max_length: int,
    residue_delay_threshold: int,
) -> dict[str, object]:
    failures: list[tuple[int, int]] = []
    tested_pairs = 0
    largest_minimal_length = 0
    first_worst: dict[str, int | bool | None] | None = None
    length_histogram: dict[int, int] = {}
    residue_delay_histogram: dict[int, int] = {}
    largest_residue_delay = 0
    first_largest_residue_delay_case: dict[str, object] | None = None
    largest_residue_delay_cases: list[dict[str, object]] = []
    delay_threshold_violations: list[dict[str, object]] = []
    base_never_clears_count = 0
    residue_never_escapes_count = 0
    for denominator in range(min_denominator, max_denominator + 1):
        if gcd(denominator, 30) != 1:
            continue
        for a in range(start_min, start_max + 1):
            tested_pairs += 1
            first_base_clear_length: int | None = None
            trajectory: list[dict[str, int | bool | None]] = []
            for length in range(1, max_length + 1):
                current = certificate(blocks, denominator, a, length)
                if trajectory:
                    previous = trajectory[-1]
                    unwrapped = (
                        current["last_block_base"]
                        * previous["least_positive_residue"]
                        - denominator * current["last_block_digit"]
                    )
                    modulus = current["window_base"]
                    current["residue_transition_lift"] = (
                        current["least_positive_residue"] - unwrapped
                    ) // modulus
                else:
                    current["residue_transition_lift"] = None
                trajectory.append(current)
                if current["base_clears_bound"] and first_base_clear_length is None:
                    first_base_clear_length = length
                if current["consumer_fires"]:
                    length_histogram[length] = length_histogram.get(length, 0) + 1
                    assert first_base_clear_length is not None
                    residue_delay = length - first_base_clear_length
                    residue_delay_histogram[residue_delay] = (
                        residue_delay_histogram.get(residue_delay, 0) + 1
                    )
                    if residue_delay > largest_residue_delay:
                        largest_residue_delay = residue_delay
                        delay_case = {
                            **current,
                            "first_base_clear_length": first_base_clear_length,
                            "residue_delay": residue_delay,
                            "post_clear_trajectory": trajectory[
                                first_base_clear_length - 1 :
                            ],
                        }
                        first_largest_residue_delay_case = delay_case
                        largest_residue_delay_cases = [delay_case]
                    elif residue_delay == largest_residue_delay:
                        largest_residue_delay_cases.append(
                            {
                                **current,
                                "first_base_clear_length": first_base_clear_length,
                                "residue_delay": residue_delay,
                                "post_clear_trajectory": trajectory[
                                    first_base_clear_length - 1 :
                                ],
                            }
                        )
                    if residue_delay > residue_delay_threshold:
                        delay_threshold_violations.append(
                            {
                                **current,
                                "first_base_clear_length": first_base_clear_length,
                                "residue_delay": residue_delay,
                            }
                        )
                    if length > largest_minimal_length:
                        largest_minimal_length = length
                        first_worst = current
                    break
            else:
                failures.append((denominator, a))
                if first_base_clear_length is None:
                    base_never_clears_count += 1
                else:
                    residue_never_escapes_count += 1
    return {
        "tested_pairs": tested_pairs,
        "failure_count": len(failures),
        "first_failures": failures[:20],
        "largest_minimal_length": largest_minimal_length,
        "first_worst_case": first_worst,
        "base_never_clears_count": base_never_clears_count,
        "residue_never_escapes_count": residue_never_escapes_count,
        "residue_delay_threshold": residue_delay_threshold,
        "largest_residue_delay": largest_residue_delay,
        "first_largest_residue_delay_case": first_largest_residue_delay_case,
        "largest_residue_delay_case_count": len(largest_residue_delay_cases),
        "largest_residue_delay_cases": largest_residue_delay_cases[:100],
        "delay_threshold_violation_count": len(delay_threshold_violations),
        "first_delay_threshold_violations": delay_threshold_violations[:20],
        "minimal_length_histogram": {
            str(length): count for length, count in sorted(length_histogram.items())
        },
        "residue_delay_histogram": {
            str(delay): count
            for delay, count in sorted(residue_delay_histogram.items())
        },
    }


def emit_result(result: dict[str, object], output: Path | None, check: bool) -> int:
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


def compact_existing_receipt(path: Path, job_ref: str | None) -> dict[str, object]:
    payload = path.read_bytes()
    source_receipt = json.loads(payload)
    scan_result = source_receipt["scan"]
    return {
        "schema": "erdos269-dyadic-window-compact-result/1",
        "compaction_boundary": (
            "Exact terminal result compacted without rerunning the computation; "
            "the retained counterexamples suffice to falsify the tested constant, "
            "while omitted non-witness rows were finite support only."
        ),
        "detached_job_ref": job_ref,
        "source_receipt": {
            "original_path": str(path),
            "byte_length": len(payload),
            "sha256": hashlib.sha256(payload).hexdigest(),
        },
        "parameters": source_receipt["parameters"],
        "scan": {
            key: scan_result[key]
            for key in (
                "tested_pairs",
                "failure_count",
                "largest_minimal_length",
                "base_never_clears_count",
                "residue_never_escapes_count",
                "residue_delay_threshold",
                "largest_residue_delay",
                "largest_residue_delay_case_count",
                "largest_residue_delay_cases",
                "delay_threshold_violation_count",
                "first_delay_threshold_violations",
                "residue_delay_histogram",
            )
        },
        "experiment_contract": source_receipt["experiment_contract"],
        "computation_source": source_receipt["source"],
        "compactor_source": source_record(REPO_ROOT, SOURCE_REF),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-denominator", type=int, default=1)
    parser.add_argument("--max-denominator", type=int, default=200)
    parser.add_argument("--start-min", type=int, default=20)
    parser.add_argument("--start-max", type=int, default=120)
    parser.add_argument("--max-length", type=int, default=18)
    parser.add_argument("--residue-delay-threshold", type=int, default=8)
    parser.add_argument("--assert-packet", action="store_true")
    parser.add_argument("--output", type=Path)
    parser.add_argument(
        "--compact-existing",
        type=Path,
        help="compact one completed full receipt without rerunning its scan",
    )
    parser.add_argument(
        "--job-ref",
        help="detached command-future id that produced --compact-existing",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="compare the deterministic result with --output",
    )
    args = parser.parse_args()
    if args.compact_existing is not None:
        if args.output is None:
            parser.error("--compact-existing requires --output")
        result = compact_existing_receipt(args.compact_existing, args.job_ref)
        return emit_result(result, args.output, args.check)
    if args.min_denominator < 1 or args.max_denominator < args.min_denominator:
        parser.error("invalid denominator interval")
    if args.start_min < 1 or args.start_max < args.start_min:
        parser.error("invalid dyadic start interval")
    if args.max_length < 1:
        parser.error("--max-length must be positive")
    if args.residue_delay_threshold < 0:
        parser.error("--residue-delay-threshold must be nonnegative")
    if args.check and args.output is None:
        parser.error("--check requires --output")

    blocks = build_dyadic_blocks(args.start_max + args.max_length)
    if args.assert_packet:
        assert_packet_certificates(blocks)
    scan_result = scan(
        blocks,
        args.min_denominator,
        args.max_denominator,
        args.start_min,
        args.start_max,
        args.max_length,
        args.residue_delay_threshold,
    )
    if scan_result["delay_threshold_violation_count"]:
        result_status = "finite_counterexample"
        result_summary = (
            f"The scan found {scan_result['delay_threshold_violation_count']} "
            f"exact counterexamples to residue delay <= "
            f"{args.residue_delay_threshold}; the first displayed witnesses "
            "falsify that bounded-delay mechanism."
        )
    elif scan_result["failure_count"]:
        result_status = "mixed"
        result_summary = (
            f"The scan left {scan_result['failure_count']} denominator/start "
            f"pairs unresolved through length {args.max_length}; no finite "
            "counterexample to eventual escape is claimed."
        )
    else:
        result_status = "finite_support"
        result_summary = (
            f"All {scan_result['tested_pairs']} denominator/start pairs fire "
            f"by length {scan_result['largest_minimal_length']}; the largest "
            f"observed post-base-clear residue delay is "
            f"{scan_result['largest_residue_delay']}."
        )
    result = {
        "schema": "erdos269-dyadic-window-exact-check/1",
        "claim_ceiling": "finite_exact_consumer_experiment_not_cofinal_escape",
        "parameters": {
            "min_denominator": args.min_denominator,
            "max_denominator": args.max_denominator,
            "start_min": args.start_min,
            "start_max": args.start_max,
            "max_length": args.max_length,
            "residue_delay_threshold": args.residue_delay_threshold,
        },
        "packet_regressions_checked": args.assert_packet,
        "block_base_alphabet": [2, 6, 10, 30],
        "scan": scan_result,
        "experiment_contract": build_experiment_contract(
            problem_id="erdos_269",
            target_statement=(
                "Prove irrationality for the running-LCM series generated "
                "by the prime support {2,3,5}."
            ),
            claim_ceiling=(
                "Finite denominator/start scans do not prove the universal "
                "denominator and cofinal-anchor quantifiers."
            ),
            hypothesis_id="uniform_post_clear_residue_delay",
            hypothesis_statement=(
                f"After the window base first exceeds the short carry bound, "
                f"the canonical residue escapes within "
                f"{args.residue_delay_threshold} additional dyadic blocks."
            ),
            probe_id="denominator_adaptive_residue_delay_scan",
            probe_question=(
                "Is the hard part only deterministic base growth, or can the "
                "actual residue remain trapped for increasingly many blocks "
                "after the base already clears the analytic bound?"
            ),
            computation=(
                "Construct the exact {2,3,5} compressed block bases and "
                "digits, scan coprime denominators and dyadic anchors, and "
                "measure minimal firing length minus first base-clear length."
            ),
            falsifier=(
                f"Any exact pair with residue delay greater than "
                f"{args.residue_delay_threshold}."
            ),
            stop_condition=(
                "At the first bounded-delay counterexample, retire that "
                "constant and study the witness genealogy; if delays remain "
                "bounded, formulate the corresponding universal residue-chain "
                "lemma rather than treating a larger rectangle as proof."
            ),
            survival_consequence=(
                "A universal bounded-delay theorem plus elementary block-base "
                "growth would produce denominator-adaptive escaping windows "
                "cofinally and fire the Lean irrationality consumer."
            ),
            falsification_consequence=(
                "An exact delay violation eliminates the proposed uniform "
                "constant and exposes a concrete long-lived residue trap for "
                "the next structural probe."
            ),
            consumer_ref=CONSUMER_REF,
            analysis_refs=[ANALYSIS_REF],
            source_refs=[SOURCE_REF],
            result_status=result_status,
            result_summary=result_summary,
        ),
        "source": source_record(REPO_ROOT, SOURCE_REF),
    }
    emitted = emit_result(result, args.output, args.check)
    if emitted != 0:
        return emitted
    return 0 if result["scan"]["failure_count"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
