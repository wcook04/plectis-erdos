#!/usr/bin/env python3
"""Structure probes for the rational half-greedy orbit (target 1/2).

Exact fixed-precision replay of the greedy orbit toward 1/2 over the
positive Mersenne weights, in the style of ``check_twenty_one_greedy.py``:
an integer enclosure ``[lower, upper]`` of the residual at precision
``2 * ranks + slack`` bits, branch decisions only when the enclosure is
unambiguous, hard failure otherwise.  No floating point decides anything.

Probes collected (all exact):

* skip ranks, skip gaps, DOUBLE-skip ranks (c,c+1 both skipped) and the
  gap law between consecutive double-skips -- the corpus's unconditional
  two-consecutive-skips producer needs cofinally many of these;
* take-run / skip-run maxima by window;
* the exact skip-margin ``w_n - residual`` and take-margin at every rank,
  binned by bit length (razor-edge statistics);
* reset/deviation sign structure: deviation w = rem - 2^floor?  Not used
  here; instead the direct residual-to-tail slack
  ``T_n - residual`` (positive slack = alive) with its minimum by window.

Finite evidence only; decides nothing at infinity.
"""

from __future__ import annotations

import argparse
import json


def run(ranks: int, slack_bits: int = 1024) -> dict:
    precision = 2 * ranks + slack_bits
    scale = 1 << precision
    lower = scale // 2
    upper = lower  # 1/2 is exact at this precision
    tail_upper_num = scale  # upper bound for T_n scaled: sum_{j>n} 2^P/(2^j-1)
    # exact tail enclosure: maintain T_lower/T_upper as integers via
    # T_n = sum_{j>n} 1/(2^j-1) < 2^{-n} * (1 + 2^{-n})  (two-channel bound)
    # We track exact rational-ish integer enclosures instead:
    #   scaled tail upper: 2^P * T_n <= 2^{P-n} + 2^{P-2n-1} + ... use closed form:
    #   T_n = sum_{j>n} 1/(2^j-1) = sum_{j>n} 2^{-j} + eps_j, eps_j < 2/4^j
    #   => T_n < 2^{-n} + 2^{-2n}  (since sum_{j>n}2^{-j}=2^{-n}, sum eps < 2/(3*4^n))
    #   => T_n < 2^{-n} + 2^{-2n}  safe for n>=1.
    skip_ranks: list[int] = []
    double_skip_ranks: list[int] = []
    take_run_max = 0
    skip_run_max = 0
    cur_take = 0
    cur_skip = 0
    min_slack_by_window: list[tuple[int, int, int]] = []  # (window_hi, rank, bits)
    window_edges = []
    lo = 1
    width = 64
    while lo <= ranks:
        hi = min(ranks, lo + width - 1)
        window_edges.append((lo, hi))
        lo = hi + 1
        width *= 2
    wi = 0
    best_rank = None
    best_slack_bits = None
    margin_hist: dict[int, int] = {}
    win_stats: dict[int, dict] = {}
    selected = 0
    ambiguous = 0

    for n in range(1, ranks + 1):
        wf = (1 << precision) // ((1 << n) - 1)
        if lower >= wf + 1:
            sel = True
            lower -= wf + 1
            upper -= wf
            margin = lower  # post-take residual lower
        elif upper <= wf:
            sel = False
            skip_ranks.append(n)
            if n >= 2 and skip_ranks and len(skip_ranks) >= 2 \
                    and skip_ranks[-2] == n - 1:
                double_skip_ranks.append(n - 1)
            margin = wf - upper  # distance below the skipped weight
        else:
            raise AssertionError(f"ambiguous half branch at rank {n}")
        ambiguous += 0
        if sel:
            selected += 1
            cur_take += 1
            cur_skip = 0
            if cur_take > take_run_max:
                take_run_max = cur_take
        else:
            cur_take = 0
            cur_skip += 1
            if cur_skip > skip_run_max:
                skip_run_max = cur_skip
        bl = margin.bit_length() if margin > 0 else 0
        key = bl if bl <= 96 else 97
        margin_hist[key] = margin_hist.get(key, 0) + 1

        # slack: T_n - residual > 0 keeps the orbit alive at rank n
        # scaled: 2^P * (T_n - upper/scale) > 0  iff  tail_cap > upper
        tail_cap = (1 << (precision - n)) + (1 << (precision - 2 * n)) \
            if 2 * n <= precision else 1
        slack = tail_cap - upper
        if slack <= 0:
            raise AssertionError(
                f"fatal state at rank {n}: residual exceeds tail bound")

        # wall coordinate: sigma_n = 2^n * (T_n - r_n) >= 0, the signed
        # distance of the scaled residual z_n = 2^n r_n below the scaled
        # tail limit (~1).  Fatality is sigma < 0; membership needs
        # cofinally small positive sigma OR bounded z returns.
        shift = precision - n
        z_rel_hi = (upper >> (shift - 63)) / float(1 << 63)
        sig_rel = ((tail_cap - upper) >> (shift - 63)) / float(1 << 63)
        while wi < len(window_edges) and n > window_edges[wi][1]:
            wi += 1
        if wi < len(window_edges):
            key = window_edges[wi][1]
            st = win_stats.get(key)
            if st is None:
                st = win_stats[key] = {
                    "lo": window_edges[wi][0], "hi": key,
                    "sig_min": 9e9, "sig_max": -9e9, "sig_sum": 0.0,
                    "z_min": 9e9, "z_max": -9e9, "count": 0,
                }
            st["count"] += 1
            st["sig_sum"] += sig_rel
            if sig_rel < st["sig_min"]:
                st["sig_min"] = sig_rel
            if sig_rel > st["sig_max"]:
                st["sig_max"] = sig_rel
            if z_rel_hi > st["z_max"]:
                st["z_max"] = z_rel_hi
            if z_rel_hi < st["z_min"]:
                st["z_min"] = z_rel_hi

    # double-skip gap law
    ds_gaps = [b - a for a, b in zip(double_skip_ranks,
                                     double_skip_ranks[1:])]
    max_ds_gap_by_decade: dict[int, int] = {}
    for a, b in zip(double_skip_ranks, double_skip_ranks[1:]):
        dec = 10 ** len(str(a))
        g = b - a
        if g > max_ds_gap_by_decade.get(dec, -1):
            max_ds_gap_by_decade[dec] = g
    skip_gaps = [b - a for a, b in zip(skip_ranks, skip_ranks[1:])]
    max_skip_gap_by_decade: dict[int, int] = {}
    for a, b in zip(skip_ranks, skip_ranks[1:]):
        dec = 10 ** len(str(a))
        g = b - a
        if g > max_skip_gap_by_decade.get(dec, -1):
            max_skip_gap_by_decade[dec] = g
    return {
        "ranks": ranks,
        "selected": selected,
        "skip_count": len(skip_ranks),
        "last_skip_rank": skip_ranks[-1] if skip_ranks else None,
        "max_skip_gap": max(skip_gaps, default=0),
        "max_skip_gap_by_decade": {str(k): v for k, v in
                                   sorted(max_skip_gap_by_decade.items())},
        "double_skip_count": len(double_skip_ranks),
        "double_skip_last": double_skip_ranks[-1] if double_skip_ranks
        else None,
        "double_skip_max_gap": max(ds_gaps, default=0),
        "double_skip_gap_by_decade": {str(k): v for k, v in
                                      sorted(max_ds_gap_by_decade.items())},
        "max_take_run": take_run_max,
        "max_skip_run": skip_run_max,
        "windows": [
            {
                "lo": st["lo"], "hi": hi,
                "sigma_min": round(st["sig_min"], 9),
                "sigma_max": round(st["sig_max"], 9),
                "sigma_mean": round(st["sig_sum"] / st["count"], 9),
                "z_max": round(st["z_max"], 9),
                "z_min": round(st["z_min"], 9),
            }
            for hi, st in sorted(win_stats.items())
        ][1:],
        "small_margin_frac_bits_le_40": round(sum(
            c for k, c in margin_hist.items() if 0 < k <= 40) / ranks, 9),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ranks", type=int, default=100_000)
    ap.add_argument("--json-out", type=str)
    args = ap.parse_args()
    result = run(args.ranks)
    text = json.dumps(result, indent=1, sort_keys=True)
    print(text)
    if args.json_out:
        with open(args.json_out, "w") as fh:
            fh.write(text)


if __name__ == "__main__":
    main()
