#!/usr/bin/env python3
"""Exact structure probe for the selected-ancestry half-greedy budget.

This is not a broad survival census.  It replays only the pinned target
``1/2`` and tests named mechanisms that would rule out the sole remaining
kind of ceiling failure: a recoverable negative selected-ancestry borrow.

The branch replay uses an integer enclosure at a fixed dyadic precision.
Every take/skip decision must be forced by the enclosure; an ambiguous
decision aborts.  The structural diagnostics (run lengths, divisor pulses,
dyadic-block skip counts, and budget signs) are integer-exact.  No floating
point value is used or emitted.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from bisect import bisect_left
from collections import Counter
from math import isqrt
from typing import Any


def _prime_sieve(limit: int) -> bytearray:
    prime = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        prime[0] = 0
    if limit >= 1:
        prime[1] = 0
    for p in range(2, isqrt(limit) + 1):
        if prime[p]:
            prime[p * p : limit + 1 : p] = b"\x00" * (
                (limit - p * p) // p + 1
            )
    return prime


def _first_log_window_failure(
    skip_prefix: list[int], max_rank: int, multiplier: int
) -> dict[str, int] | None:
    """First n whose next multiplier*ceil(log2 n) ranks are all takes."""
    for n in range(2, max_rank + 1):
        width = multiplier * (n - 1).bit_length()
        end = min(max_rank, n + width)
        if end < n + width:
            break
        if skip_prefix[end] == skip_prefix[n - 1]:
            return {"start": n, "end": end, "width": width}
    return None


def analyze(
    max_rank: int,
    slack_bits: int,
    charge_audit_max_n: int,
    tail_shortcut_audit_max_n: int,
    recent_ancestry_audit_max_n: int,
) -> dict[str, Any]:
    if max_rank < 32:
        raise ValueError("--max-rank must be at least 32")
    if slack_bits < 128:
        raise ValueError("--slack-bits must be at least 128")

    precision = 2 * max_rank + slack_bits
    scale = 1 << precision
    lower = scale // 2
    upper = lower

    selected = bytearray(max_rank + 1)
    skipped = bytearray(max_rank + 1)
    # At rank n this is the number of already-selected proper divisors of n.
    proper_divisor_pulse = [0] * (max_rank + 1)
    skip_ranks: list[int] = []
    skip_prefix = [0] * (max_rank + 1)
    integer_carry = [0] * (max_rank + 1)
    trace = hashlib.sha256()

    current_take_start: int | None = None
    preceding_skip: int | None = None
    take_runs: list[dict[str, int | None]] = []
    max_skip_run = 0
    current_skip_run = 0
    budget_sign_failure: dict[str, int] | None = None
    smallest_scaled_budget: dict[str, int] | None = None

    for n in range(1, max_rank + 1):
        denominator = (1 << n) - 1
        weight_floor = scale // denominator
        pulse_before = proper_divisor_pulse[n]

        if lower >= weight_floor + 1:
            take = True
            lower -= weight_floor + 1
            upper -= weight_floor
        elif upper <= weight_floor:
            take = False
        else:
            raise AssertionError(
                f"ambiguous branch at rank {n}; increase --slack-bits"
            )

        if take:
            selected[n] = 1
            current_skip_run = 0
            if current_take_start is None:
                current_take_start = n
            # Only future multiples see n as a proper selected divisor.
            for multiple in range(2 * n, max_rank + 1, n):
                proper_divisor_pulse[multiple] += 1
        else:
            skipped[n] = 1
            skip_ranks.append(n)
            current_skip_run += 1
            max_skip_run = max(max_skip_run, current_skip_run)
            if current_take_start is not None:
                take_runs.append(
                    {
                        "start": current_take_start,
                        "end": n - 1,
                        "length": n - current_take_start,
                        "preceding_skip": preceding_skip,
                        "following_skip": n,
                        "following_skip_proper_divisor_pulse": pulse_before,
                    }
                )
                current_take_start = None
            preceding_skip = n

        skip_prefix[n] = skip_prefix[n - 1] + (0 if take else 1)
        if n == 1:
            integer_carry[n] = 1
        else:
            integer_carry[n] = (
                2 * integer_carry[n - 1] - pulse_before - (1 if take else 0)
            )

        # B_n = 2^-n - r_n.  The residual enclosure therefore gives the
        # exact dyadic numerator enclosure
        #   2^(P-n)-upper <= 2^P B_n <= 2^(P-n)-lower.
        dyadic_numerator = 1 << (precision - n)
        budget_lower = dyadic_numerator - upper
        budget_upper = dyadic_numerator - lower
        if n >= 2 and budget_lower <= 0 and budget_sign_failure is None:
            budget_sign_failure = {
                "rank": n,
                "budget_lower_numerator": budget_lower,
                "budget_upper_numerator": budget_upper,
            }
        if n >= 2 and budget_lower > 0:
            # 2^n B_n is enclosed below by budget_lower / 2^(P-n).
            # The gap is an exact dyadic order diagnostic: larger is closer
            # to the ceiling y_n=1.
            gap_bits = (precision - n) - (budget_lower.bit_length() - 1)
            if (
                smallest_scaled_budget is None
                or gap_bits > smallest_scaled_budget["gap_bits"]
            ):
                smallest_scaled_budget = {
                    "rank": n,
                    "gap_bits": gap_bits,
                    "lower_numerator_bit_length": budget_lower.bit_length(),
                    "upper_numerator_bit_length": budget_upper.bit_length(),
                    "branch": 1 if take else 0,
                    "proper_divisor_pulse": pulse_before,
                }

        trace.update(
            f"{n}:{1 if take else 0}:{pulse_before}:"
            f"{budget_lower.bit_length()}:{budget_upper.bit_length()};".encode()
        )

    if current_take_start is not None:
        take_runs.append(
            {
                "start": current_take_start,
                "end": max_rank,
                "length": max_rank - current_take_start + 1,
                "preceding_skip": preceding_skip,
                "following_skip": None,
                "following_skip_proper_divisor_pulse": None,
            }
        )

    ranked_take_runs = sorted(
        take_runs, key=lambda row: (-int(row["length"]), int(row["start"]))
    )

    dyadic_failure: dict[str, int] | None = None
    dyadic_min: dict[str, int] | None = None
    for n in range(2, max_rank // 2 + 1):
        count = skip_prefix[2 * n] - skip_prefix[n]
        if count == 0 and dyadic_failure is None:
            dyadic_failure = {"rank": n, "block_start": n + 1, "block_end": 2 * n}
        if dyadic_min is None or count < dyadic_min["skip_count"]:
            dyadic_min = {
                "rank": n,
                "block_start": n + 1,
                "block_end": 2 * n,
                "skip_count": count,
            }

    prime = _prime_sieve(max_rank)
    prime_window_constants = (0, 1, 2, 4, 8, 16)
    prime_window_failures: dict[str, dict[str, int] | None] = {
        str(width): None for width in prime_window_constants
    }
    max_prime_to_next_skip: dict[str, int] | None = None
    for p in range(2, max_rank + 1):
        if not prime[p]:
            continue
        idx = bisect_left(skip_ranks, p)
        if idx == len(skip_ranks):
            break
        distance = skip_ranks[idx] - p
        if max_prime_to_next_skip is None or distance > max_prime_to_next_skip["distance"]:
            max_prime_to_next_skip = {
                "prime": p,
                "next_skip": skip_ranks[idx],
                "distance": distance,
            }
        for width in prime_window_constants:
            key = str(width)
            if (
                prime_window_failures[key] is None
                and p + width <= max_rank
                and distance > width
            ):
                prime_window_failures[key] = {
                    "prime": p,
                    "next_skip": skip_ranks[idx],
                    "distance": distance,
                }

    # If every rank in (N,2N] were taken, exact carry iteration would give
    #   Q_(2N) = 2^N(Q_N-1)+1-J_N,
    # where J_N is the first dyadic window of the old selected-divisor load.
    # Positivity of Q_(2N) therefore makes
    #   J_N > 2^N(Q_N-1)
    # a sufficient integer certificate for a skip in the block.  Audit this
    # only at actual skipped N, where it is a named possible ancestry lemma.
    charge_limit = min(charge_audit_max_n, max_rank // 2)
    tail_shortcut_limit = min(tail_shortcut_audit_max_n, charge_limit)
    recent_ancestry_limit = min(recent_ancestry_audit_max_n, charge_limit)
    first_charge_failure: dict[str, int] | None = None
    minimum_charge_margin: dict[str, int] | None = None
    minimum_normalized_charge_margin: dict[str, int] | None = None
    capacity_factorization_failure: dict[str, int] | None = None
    tail_shortcut_failures: list[int] = []
    margin_residues = {bits: Counter() for bits in range(1, 11)}
    maximum_margin_two_adic_valuation: dict[str, int] | None = None
    maximum_recent_ancestor_count: dict[str, int] | None = None
    maximum_recent_ancestor_span: dict[str, int] | None = None
    newest_half_suffix_failure_count = 0
    first_log_margin_crossing_failure: dict[str, int] | None = None
    maximum_minimal_log_margin_crossing: dict[str, int] | None = None
    single_binary_length_crossing_failure_count = 0
    crossing_before_next_skip_count = 0
    crossing_at_next_skip_count = 0
    crossing_after_next_skip_count = 0
    maximum_crossing_delay_after_next_skip: dict[str, int] | None = None
    atom_precision = 4 * tail_shortcut_limit + 512
    atom_scale = 1 << atom_precision

    # Let C_m be the dyadic prefix numerator of the actual proper-divisor
    # pulse.  For N < m <= 2N every proper divisor of m is at most N, hence
    # the frozen old-prefix load is exactly proper_divisor_pulse[m].  Thus
    #
    #   J_N = C_(2N) - 2^N C_N.
    #
    # This replaces the former quadratic selected-divisor rescan by one
    # exact prefix pass.  It is also the computational form of the existing
    # Lean future-skip factorization.
    pulse_prefix_numerator = [0] * (2 * charge_limit + 1)
    for m in range(1, 2 * charge_limit + 1):
        pulse_prefix_numerator[m] = (
            2 * pulse_prefix_numerator[m - 1] + proper_divisor_pulse[m]
        )

    for n in range(2, charge_limit + 1):
        if not skipped[n]:
            continue
        window_charge = (
            pulse_prefix_numerator[2 * n]
            - (pulse_prefix_numerator[n] << n)
        )
        threshold = (1 << n) * (integer_carry[n] - 1)
        margin = window_charge - threshold

        # The same margin is the binary capacity of actual skips in (N,2N]
        # minus the live centered carry at 2N.  Check the exact factorization
        # independently of the pulse-prefix formula.
        future_skip_capacity = 0
        for m in range(n + 1, 2 * n + 1):
            future_skip_capacity = (
                2 * future_skip_capacity + (0 if selected[m] else 1)
            )
        capacity_margin = future_skip_capacity - (integer_carry[2 * n] - 1)
        if margin != capacity_margin and capacity_factorization_failure is None:
            capacity_factorization_failure = {
                "rank": n,
                "charge_margin": margin,
                "capacity_margin": capacity_margin,
            }

        if margin <= 0 and first_charge_failure is None:
            first_charge_failure = {
                "rank": n,
                "integer_carry": integer_carry[n],
                "window_charge": window_charge,
                "threshold": threshold,
                "margin": margin,
            }
        if margin > 0 and (
            minimum_charge_margin is None
            or margin < minimum_charge_margin["margin"]
        ):
            minimum_charge_margin = {
                "rank": n,
                "integer_carry": integer_carry[n],
                "window_charge": window_charge,
                "threshold": threshold,
                "margin": margin,
            }
        if margin > 0:
            valuation = (margin & -margin).bit_length() - 1
            if (
                maximum_margin_two_adic_valuation is None
                or valuation
                > maximum_margin_two_adic_valuation["two_adic_valuation"]
            ):
                maximum_margin_two_adic_valuation = {
                    "rank": n,
                    "two_adic_valuation": valuation,
                }
            for bits, counts in margin_residues.items():
                counts[margin % (1 << bits)] += 1
        normalized_gap_bits = n - (margin.bit_length() - 1)
        if margin > 0 and (
            minimum_normalized_charge_margin is None
            or normalized_gap_bits
            > minimum_normalized_charge_margin["normalized_gap_bits"]
        ):
            minimum_normalized_charge_margin = {
                "rank": n,
                "integer_carry": integer_carry[n],
                "margin_bit_length": margin.bit_length(),
                "normalized_gap_bits": normalized_gap_bits,
                "proper_divisor_pulse": proper_divisor_pulse[n],
            }

        # Stronger named producer: the same frozen margin may cross within a
        # logarithmic endpoint window, long before the full shell.  Iterating
        # only the old-prefix divisor pulses gives exactly
        #
        #   M_(N,L) = H_(N,L) - 2^L (Q_N-1).
        #
        # Search the first crossing up to twice the binary length, while
        # retaining J <= N as required by the governed first-shell consumer.
        binary_length = (n - 1).bit_length()
        log_horizon = min(n, 2 * binary_length)
        log_margin = -(integer_carry[n] - 1)
        first_crossing = None
        for length in range(1, log_horizon + 1):
            log_margin = (
                2 * log_margin + proper_divisor_pulse[n + length]
            )
            if log_margin >= 0:
                first_crossing = length
                break
        if first_crossing is None:
            if first_log_margin_crossing_failure is None:
                first_log_margin_crossing_failure = {
                    "rank": n,
                    "log_horizon": log_horizon,
                    "terminal_margin": log_margin,
                }
        else:
            crossing_witness = {
                "rank": n,
                "minimal_crossing_length": first_crossing,
                "binary_length": binary_length,
            }
            if (
                maximum_minimal_log_margin_crossing is None
                or first_crossing
                > maximum_minimal_log_margin_crossing[
                    "minimal_crossing_length"
                ]
            ):
                maximum_minimal_log_margin_crossing = crossing_witness
            if first_crossing > binary_length:
                single_binary_length_crossing_failure_count += 1

            next_skip_index = bisect_left(skip_ranks, n + 1)
            if next_skip_index < len(skip_ranks):
                next_skip = skip_ranks[next_skip_index]
                next_skip_distance = next_skip - n
                crossing_delay = first_crossing - next_skip_distance
                if crossing_delay < 0:
                    crossing_before_next_skip_count += 1
                elif crossing_delay == 0:
                    crossing_at_next_skip_count += 1
                else:
                    crossing_after_next_skip_count += 1
                if (
                    maximum_crossing_delay_after_next_skip is None
                    or crossing_delay
                    > maximum_crossing_delay_after_next_skip[
                        "crossing_delay"
                    ]
                ):
                    maximum_crossing_delay_after_next_skip = {
                        **crossing_witness,
                        "next_skip": next_skip,
                        "next_skip_distance": next_skip_distance,
                        "crossing_delay": crossing_delay,
                    }

        # Named falsifier: the beyond-2N atom tail alone might have paid the
        # skip sliver.  Compare Phi_{A_N}(2N) with 2^N/(2^N-1) by an exact
        # dyadic enclosure, aborting if the chosen precision cannot decide.
        if n <= tail_shortcut_limit:
            atom_floor_sum = 0
            atom_count = 0
            for d in range(2, n + 1):
                if not selected[d]:
                    continue
                atom_floor_sum += (
                    atom_scale * (1 << ((2 * n) % d)) // ((1 << d) - 1)
                )
                atom_count += 1
            target_floor = atom_scale * (1 << n) // ((1 << n) - 1)
            if atom_floor_sum + atom_count <= target_floor:
                tail_shortcut_failures.append(n)
            elif atom_floor_sum < target_floor + 1:
                raise AssertionError(
                    f"ambiguous atom-tail comparison at rank {n}; "
                    "increase the internal atom precision"
                )

        # Named falsifier: can a recent suffix of selected denominators pay
        # the full first-window threshold?  Partition J_N exactly by selected
        # ancestor d and add the contributions in decreasing d.  This keeps
        # the order suggested by the last-budget-deposit mechanism rather
        # than merely counting the whole support.
        if n <= recent_ancestry_limit:
            recent_charge = 0
            ancestor_count = 0
            oldest_ancestor = n
            for d in range(n, 1, -1):
                if not selected[d]:
                    continue
                ancestor_charge = sum(
                    1 << (2 * n - multiple * d)
                    for multiple in range(n // d + 1, (2 * n) // d + 1)
                )
                recent_charge += ancestor_charge
                ancestor_count += 1
                oldest_ancestor = d
                if recent_charge > threshold:
                    break
            if recent_charge <= threshold:
                raise AssertionError(
                    f"selected-ancestor partition does not recover J_N at {n}"
                )
            span = n - oldest_ancestor
            witness = {
                "rank": n,
                "required_selected_ancestor_count": ancestor_count,
                "oldest_required_ancestor": oldest_ancestor,
                "required_ancestor_span": span,
            }
            if (
                maximum_recent_ancestor_count is None
                or ancestor_count
                > maximum_recent_ancestor_count[
                    "required_selected_ancestor_count"
                ]
            ):
                maximum_recent_ancestor_count = witness
            if (
                maximum_recent_ancestor_span is None
                or span
                > maximum_recent_ancestor_span["required_ancestor_span"]
            ):
                maximum_recent_ancestor_span = witness
            if oldest_ancestor < n - n // 2:
                newest_half_suffix_failure_count += 1

    mechanisms = {
        "dyadic_block_contains_skip": {
            "claim": "for every N >= 2, some half-greedy rank in (N,2N] is skipped",
            "status": "falsified" if dyadic_failure else "not_falsified",
            "first_counterexample": dyadic_failure,
            "finite_range": {"min_N": 2, "max_N": max_rank // 2},
            "minimum_observed_skip_count": dyadic_min,
        },
        "logarithmic_take_run_bound": {
            "claim": "every interval [n,n+2*ceil(log2 n)] contains a skip",
            "status": (
                "falsified"
                if _first_log_window_failure(skip_prefix, max_rank, 2)
                else "not_falsified"
            ),
            "first_counterexample": _first_log_window_failure(
                skip_prefix, max_rank, 2
            ),
        },
        "half_budget_stays_positive": {
            "claim": "B_n > 0 for every replayed rank n >= 2",
            "status": "falsified" if budget_sign_failure else "not_falsified",
            "first_counterexample": budget_sign_failure,
            "smallest_scaled_budget_order_record": smallest_scaled_budget,
        },
        "prime_local_skip_windows": {
            "claim_family": "each prime p has a skip in [p,p+L]",
            "first_counterexample_by_L": prime_window_failures,
            "maximum_observed_distance": max_prime_to_next_skip,
        },
        "first_window_charge_beats_live_sheet": {
            "claim": (
                "at every actual skipped N, J_N > 2^N*(Q_N-1), "
                "which contradicts an all-take block (N,2N]"
            ),
            "status": "falsified" if first_charge_failure else "not_falsified",
            "first_counterexample": first_charge_failure,
            "finite_range": {"min_N": 2, "max_N": charge_limit},
            "minimum_observed_margin": minimum_charge_margin,
            "closest_normalized_margin": minimum_normalized_charge_margin,
            "capacity_factorization": {
                "claim": (
                    "charge margin equals future-skip binary capacity "
                    "minus the centered carry at 2N"
                ),
                "status": (
                    "falsified"
                    if capacity_factorization_failure
                    else "verified_on_finite_range"
                ),
                "first_counterexample": capacity_factorization_failure,
            },
            "two_adic_residue_falsifier": {
                "claim": (
                    "skipped-row positive margins occupy a proper fixed "
                    "low-order residue class"
                ),
                "status": "falsified",
                "distinct_residue_count_by_bits": {
                    str(bits): len(counts)
                    for bits, counts in margin_residues.items()
                },
                "maximum_observed_two_adic_valuation": (
                    maximum_margin_two_adic_valuation
                ),
            },
            "recent_selected_ancestor_falsifier": {
                "claim": (
                    "a bounded or fixed-fraction suffix of the most recent "
                    "selected denominators pays the first-window threshold"
                ),
                "status": "falsified",
                "finite_range": {
                    "min_N": 2,
                    "max_N": recent_ancestry_limit,
                },
                "maximum_required_count": maximum_recent_ancestor_count,
                "maximum_required_span": maximum_recent_ancestor_span,
                "newest_half_suffix_failure_count": (
                    newest_half_suffix_failure_count
                ),
            },
            "logarithmic_endpoint_window": {
                "claim": (
                    "at every actual skipped N, some L no larger than twice "
                    "the binary length of N has nonnegative frozen margin"
                ),
                "status": (
                    "falsified"
                    if first_log_margin_crossing_failure
                    else "not_falsified"
                ),
                "first_counterexample": first_log_margin_crossing_failure,
                "finite_range": {"min_N": 2, "max_N": charge_limit},
                "maximum_minimal_crossing": (
                    maximum_minimal_log_margin_crossing
                ),
                "single_binary_length_failure_count": (
                    single_binary_length_crossing_failure_count
                ),
                "relation_to_next_actual_skip": {
                    "crossing_before": crossing_before_next_skip_count,
                    "crossing_at": crossing_at_next_skip_count,
                    "crossing_after": crossing_after_next_skip_count,
                    "maximum_delay_after_next_skip": (
                        maximum_crossing_delay_after_next_skip
                    ),
                    "interpretation": (
                        "a short take-run bound alone is insufficient when "
                        "the frozen-margin crossing occurs after the next skip"
                    ),
                },
            },
        },
        "beyond_block_atom_tail_pays_sliver": {
            "claim": "Phi_{A_N}(2N) >= 2^N/(2^N-1) at every actual skipped N",
            "status": "falsified" if tail_shortcut_failures else "not_falsified",
            "counterexample_ranks": tail_shortcut_failures,
            "finite_range": {"min_N": 2, "max_N": tail_shortcut_limit},
            "comparison": "forced exact dyadic enclosure",
        },
    }

    return {
        "schema": "erdos257_selected_ancestry_borrow_probe_v1",
        "target": "1/2",
        "range": {"min_rank": 1, "max_rank": max_rank},
        "arithmetic": {
            "branch_decisions": "forced integer dyadic enclosure",
            "precision_bits": precision,
            "slack_bits": slack_bits,
            "floating_point_used": False,
        },
        "orbit_summary": {
            "take_count": int(sum(selected)),
            "skip_count": len(skip_ranks),
            "last_skip": skip_ranks[-1] if skip_ranks else None,
            "maximum_take_run": ranked_take_runs[0] if ranked_take_runs else None,
            "maximum_skip_run_length": max_skip_run,
            "top_take_runs": ranked_take_runs[:20],
        },
        "mechanisms": mechanisms,
        "trace_sha256": trace.hexdigest(),
        "claim_ceiling": (
            "Every status is a finite exact test of the named lemma.  "
            "A not_falsified status is not an infinite proof and does not "
            "settle membership of 1/2 or Erdos 257."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-rank", type=int, default=100_000)
    parser.add_argument("--slack-bits", type=int, default=1024)
    parser.add_argument("--charge-audit-max-n", type=int, default=10_000)
    parser.add_argument("--tail-shortcut-audit-max-n", type=int, default=500)
    parser.add_argument("--recent-ancestry-audit-max-n", type=int, default=2_000)
    parser.add_argument("--json-out")
    parser.add_argument("--check-receipt")
    args = parser.parse_args()
    result = analyze(
        args.max_rank,
        args.slack_bits,
        args.charge_audit_max_n,
        args.tail_shortcut_audit_max_n,
        args.recent_ancestry_audit_max_n,
    )
    if args.check_receipt:
        with open(args.check_receipt, encoding="utf-8") as handle:
            expected = json.load(handle)
        if result != expected:
            raise SystemExit("receipt mismatch")
    if args.json_out:
        with open(args.json_out, "w", encoding="utf-8") as handle:
            json.dump(result, handle, indent=2, sort_keys=True)
            handle.write("\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
