#!/usr/bin/env python3
"""Exact ride-manifold audit of the compressed 1/465 corridor cylinder.

Verifies, through --horizon, in one exact single pass:
  1. full endpoint coverage and uniqueness (compressed invariants);
  2. the ancestry gate prefix_length >= rank // 2 at every rank;
  3. the exact truncated sigma-doubling law
     delta_{j+1} - sigma_{j+1}
     = 2 (delta_j - sigma_j) inside every recorded non-extraction run,
     with the J-th boundary term accounted exactly.  The echo at each ride
     is evaluated online from exactly the prefix frozen on that ride;
  4. run statistics: maximum run length and entry deviations.

No finite horizon is promoted to an all-depth statement.
"""

from __future__ import annotations

import argparse

DENOMINATOR = 465


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--horizon", type=int, default=200_000)
    parser.add_argument("--sigma-depth", type=int, default=140)
    parser.add_argument("--min-verified-run", type=int, default=8)
    args = parser.parse_args()
    n_max = args.horizon
    j_depth = args.sigma_depth
    scale = 1 << j_depth

    target_bits = [0] * (n_max + j_depth + 2)
    remainder = 1
    for rank in range(1, n_max + j_depth + 2):
        remainder *= 2
        target_bits[rank], remainder = divmod(remainder, DENOMINATOR)

    proper_counts = bytearray(n_max + j_depth + 2)
    prefix_len = 0
    suffix_width = 0
    endpoint = 0
    runs: list[tuple[int, int, int, int]] = []
    run_start: int | None = None
    run_length = 0
    run_entry_scaled_e = 0
    previous_run_rank: int | None = None
    previous_scaled_e = 0
    checked = 0
    failures: list[tuple[int, int]] = []

    def close_run(end_rank: int) -> None:
        nonlocal run_start, run_length, run_entry_scaled_e
        if run_start is not None:
            runs.append(
                (run_start, end_rank, run_length, run_entry_scaled_e)
            )
        run_start = None
        run_length = 0
        run_entry_scaled_e = 0

    for rank in range(1, n_max + 1):
        assert prefix_len >= rank // 2, f"ancestry gate failed at {rank}"
        correction = target_bits[rank] - proper_counts[rank]
        ceiling = rank // 20
        enlarged = 2 * endpoint + correction
        lower = enlarged - ceiling
        upper = enlarged
        assert 0 <= lower <= upper < (1 << (suffix_width + 1)), (
            f"interval failure at {rank}"
        )
        remain = (lower ^ upper).bit_length() if lower != upper else 0
        extracted = suffix_width + 1 - remain
        common = upper >> remain if extracted else 0
        for offset in range(extracted):
            bit = (common >> (extracted - offset - 1)) & 1
            prefix_len += 1
            if bit:
                for multiple in range(
                    2 * prefix_len, n_max + j_depth + 1, prefix_len
                ):
                    if proper_counts[multiple] == 255:
                        raise OverflowError("byte counter overflow")
                    proper_counts[multiple] += 1
        suffix_width = remain
        endpoint = upper & ((1 << remain) - 1) if remain else 0
        current_delta = (
            endpoint - (1 << (suffix_width - 1)) if suffix_width else None
        )

        if extracted == 0 and current_delta is not None:
            echo = 0
            for k in range(1, j_depth + 1):
                echo += (proper_counts[rank + k] - target_bits[rank + k]) << (
                    j_depth - k
                )
            scaled_e = current_delta * scale - echo

            if previous_run_rank == rank - 1:
                boundary = (
                    proper_counts[previous_run_rank + j_depth + 1]
                    - target_bits[previous_run_rank + j_depth + 1]
                )
                checked += 1
                if scaled_e != 2 * previous_scaled_e - boundary:
                    failures.append((previous_run_rank, rank))
            else:
                close_run(rank - 1)
                run_start = rank
                run_entry_scaled_e = scaled_e

            run_length += 1
            previous_run_rank = rank
            previous_scaled_e = scaled_e
        else:
            close_run(rank - 1)
            previous_run_rank = None

    close_run(n_max)
    runs.sort(key=lambda run: run[2], reverse=True)
    verified_entries = [
        entry / scale
        for _, _, length, entry in runs
        if length >= args.min_verified_run
    ]

    max_load = max(
        abs(proper_counts[r] - target_bits[r]) for r in range(1, n_max + 1)
    )
    print(
        {
            "horizon": n_max,
            "final": {
                "prefix_length": prefix_len,
                "suffix_width": suffix_width,
                "endpoint": endpoint,
                "ceiling": n_max // 20,
            },
            "runs_total": len(runs),
            "max_run_length": runs[0][2] if runs else 0,
            "max_run_window": [runs[0][0], runs[0][1]] if runs else None,
            "doubling_checks_exact": checked,
            "doubling_failures": len(failures),
            "long_run_entry_deviations_range": (
                [min(verified_entries), max(verified_entries)]
                if verified_entries
                else None
            ),
            "max_abs_load_deviation": max_load,
            "status": "exact finite verification, not an all-depth theorem",
        }
    )
    if failures:
        raise SystemExit(f"sigma-doubling failures: {failures[:5]}")


if __name__ == "__main__":
    main()
