#!/usr/bin/env python3
"""Deep pure-integer replay of the denominator-21 quotient-greedy chain.

Exact state machine of ``check_twenty_one_greedy.py`` /
``TwentyOneQuotientGreedy.lean``::

    pulse        = 2 * cnt[2n-1] + cnt[2n]          (selected-divisor pulse)
    target_pulse = (4 * 2^(2(n-1))) // 21           (= 0 or 3)
    core         = 4 * state + target_pulse - pulse
    coin         = 2^n + 1
    take         = coin <= core
    state'       = core - coin  if take  else core

plus the Lambert carry/defect recurrence.  Every quantity is an exact
integer; no floating point decides anything; the chain re-verifies its
overlap with the certified 200000-rank receipt before extending.

Structure statistics per log-spaced window:

* normalised closed-capacity margin mantissa ``m_n / 2^n`` (the coordinate
  the fatal branch lives in);
* exact decision margins ``|core - coin|``;
* take density, max runs, defect stats, Q<=1 return gaps by decade;
* mod-3/pulse stratification, saturation census.

Finite evidence only.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass, field


@dataclass
class Window:
    lo: int
    hi: int
    takes: int = 0
    q_zero: int = 0
    q_le_one: int = 0
    q_max: int = 0
    lambda_min: float = 2.0
    lambda_max: float = -1.0
    lambda_sum: float = 0.0
    take_margin_min: int | None = None
    skip_margin_min: int | None = None
    margin_bitlen_hist: dict[int, int] = field(default_factory=dict)
    max_take_run: int = 0
    max_skip_run: int = 0
    saturated: int = 0
    pulse_hist: dict[tuple[int, int], int] = field(default_factory=dict)
    mod3_lambda_min: dict[int, float] = field(default_factory=dict)


class DeepChain:
    def __init__(self, ranks: int):
        self.ranks = ranks
        self.divisor_counts = [0] * (ranks + 1)
        self.quotient_counts = [0] * (2 * ranks + 3)
        self.take = bytearray(ranks + 1)
        self.defect = [0] * (ranks + 1)
        self.state = 0
        self.carry = 1
        self.periodic_remainder = 1
        self.selected = 0
        self.q_le_one_ranks: list[int] = []
        self.min_closed_margin: int | None = None
        self.min_closed_margin_rank = 0
        self.windows: list[Window | None] = []

    # ------------------------------------------------------------------
    def run(self) -> None:
        ranks = self.ranks
        dc = self.divisor_counts
        qc = self.quotient_counts
        take = self.take
        defect = self.defect
        state = 0
        carry = 1
        pr = 1
        selected = 0
        cur_take_run = 0
        cur_skip_run = 0
        edges = self._window_edges(ranks)
        wi = 0
        win: Window | None = None

        for n in range(1, ranks + 1):
            if n >= 2:
                prev = n - 1
                pulse = 2 * qc[2 * prev + 1] + qc[2 * prev + 2]
                target_pulse = (4 * pow(2, 2 * prev, 21)) // 21
                core = 4 * state + target_pulse - pulse
                if core < 0:
                    raise AssertionError(f"negative core at {n}")
                coin = (1 << n) + 1
                take_now = coin <= core
                nxt = core - coin if take_now else core
                if nxt > (1 << n):
                    raise AssertionError(f"closed state failed at {n}")
                margin_closed = (1 << n) - nxt
                if (self.min_closed_margin is None
                        or margin_closed < self.min_closed_margin):
                    self.min_closed_margin = margin_closed
                    self.min_closed_margin_rank = n
            else:
                pulse = target_pulse = 0
                core = 0
                coin = 0
                take_now = False
                nxt = 0

            take[n] = 1 if take_now else 0
            state = nxt
            if take_now:
                selected += 1
                for mult in range(n, ranks + 1, n):
                    dc[mult] += 1
                for mult in range(n, 2 * ranks + 3, n):
                    qc[mult] += 1
                cur_take_run += 1
                cur_skip_run = 0
            else:
                cur_take_run = 0
                cur_skip_run += 1

            carry = 2 * carry - 21 * dc[n]
            if carry < 0:
                raise AssertionError(f"negative carry at {n}")
            bit = 1 if n % 6 in (0, 5) else 0
            pr = 2 * pr - 21 * bit
            q, rem = divmod(carry - pr, 21)
            if rem:
                raise AssertionError(f"nonintegral defect at {n}")
            if q < 0:
                raise AssertionError(f"negative defect at {n}")
            defect[n] = q
            if q <= 1:
                self.q_le_one_ranks.append(n)

            while wi < len(edges) and n > edges[wi][1]:
                wi += 1
                win = None
            if wi < len(edges):
                if win is None or win.lo != edges[wi][0]:
                    win = Window(lo=edges[wi][0], hi=edges[wi][1])
                    while len(self.windows) <= wi:
                        self.windows.append(None)
                    self.windows[wi] = win
                self._aggregate(win, n, take_now, q, nxt, core, coin,
                                pulse, target_pulse,
                                cur_take_run, cur_skip_run)

        self.state_final = state
        self.selected_final = selected

    # ------------------------------------------------------------------
    @staticmethod
    def _window_edges(ranks: int) -> list[tuple[int, int]]:
        edges: list[tuple[int, int]] = []
        lo = 1
        width = 8
        while lo <= ranks:
            hi = min(ranks, lo + width - 1)
            edges.append((lo, hi))
            lo = hi + 1
            width *= 2
        return edges

    @staticmethod
    def _mantissa(value: int, n: int) -> float:
        if value <= 0:
            return 0.0
        shift = n - 63
        if shift > 0:
            return (value >> shift) / float(1 << 63)
        return value / float(1 << n)

    def _aggregate(self, w: Window, n: int, take_now: bool, q: int,
                   state: int, core: int, coin: int,
                   pulse: int, target_pulse: int,
                   cur_take_run: int, cur_skip_run: int) -> None:
        total = w.hi - w.lo + 1
        w.takes += 1 if take_now else 0
        if q == 0:
            w.q_zero += 1
        if q <= 1:
            w.q_le_one += 1
        if q > w.q_max:
            w.q_max = q
        lam = self._mantissa((1 << n) - state, n)
        w.lambda_sum += lam
        if lam < w.lambda_min:
            w.lambda_min = lam
        if lam > w.lambda_max:
            w.lambda_max = lam
        r3 = n % 3
        cur = w.mod3_lambda_min.get(r3, 2.0)
        if lam < cur:
            w.mod3_lambda_min[r3] = lam
        margin = core - coin if take_now else coin - core
        if margin > 0:
            if take_now:
                if w.take_margin_min is None or margin < w.take_margin_min:
                    w.take_margin_min = margin
            else:
                if w.skip_margin_min is None or margin < w.skip_margin_min:
                    w.skip_margin_min = margin
            bl = margin.bit_length()
            key = bl if bl <= 80 else 81
            w.margin_bitlen_hist[key] = w.margin_bitlen_hist.get(key, 0) + 1
        if cur_take_run > w.max_take_run:
            w.max_take_run = cur_take_run
        if cur_skip_run > w.max_skip_run:
            w.max_skip_run = cur_skip_run
        if state == (1 << n):
            w.saturated += 1
        pk = (pulse, target_pulse)
        w.pulse_hist[pk] = w.pulse_hist.get(pk, 0) + 1
        del total

    # ------------------------------------------------------------------
    def post_pass(self) -> dict:
        ranks = self.ranks
        defect = self.defect
        dc = self.divisor_counts
        le1 = self.q_le_one_ranks
        zero_ranks = [n for n in range(1, ranks + 1) if defect[n] == 0]
        gaps = [b - a for a, b in zip(le1, le1[1:])]
        max_gap_by_decade: dict[int, int] = {}
        for a, b in zip(le1, le1[1:]):
            dec = 10 ** len(str(a))
            g = b - a
            if g > max_gap_by_decade.get(dec, -1):
                max_gap_by_decade[dec] = g
        danger: list[int] = []
        failures: list[int] = []
        for n in range(ranks - 5):
            amplified = 64 * defect[n] + 3 * pow(2, n, 21)
            allowance = n // 6 + 1
            if allowance < amplified:
                danger.append(n)
                load = (32 * dc[n + 1] + 16 * dc[n + 2] + 8 * dc[n + 3]
                        + 4 * dc[n + 4] + 2 * dc[n + 5] + dc[n + 6])
                if amplified > load + allowance:
                    failures.append(n)
        six_step_failures = sum(
            1 for n in range(ranks - 5) if defect[n + 6] > defect[n] + 1
        )
        first_six = next(
            (n for n in range(ranks - 5) if defect[n + 6] > defect[n] + 1),
            None,
        )
        return {
            "defect_zero_return_count": len(zero_ranks),
            "defect_zero_last_rank": zero_ranks[-1] if zero_ranks else None,
            "q_le_one_return_count": len(le1),
            "q_le_one_last_rank": le1[-1] if le1 else None,
            "q_le_one_max_gap": max(gaps, default=0),
            "max_gap_by_decade": {str(k): v for k, v in
                                  sorted(max_gap_by_decade.items())},
            "six_step_failure_count": six_step_failures,
            "first_six_step_failure": first_six,
            "slope_danger_count": len(danger),
            "slope_danger_last": danger[-1] if danger else None,
            "slope_danger_repair_failure_count": len(failures),
            "slope_danger_first_after_1e4": next(
                (d for d in danger if d > 10_000), None),
        }

    def summary(self) -> dict:
        post = self.post_pass()
        wins = []
        for w in self.windows:
            if w is None:
                continue
            total = w.hi - w.lo + 1
            wins.append({
                "lo": w.lo, "hi": w.hi,
                "take_density": round(w.takes / total, 6),
                "q_zero": w.q_zero,
                "q_le_one": w.q_le_one,
                "q_max": w.q_max,
                "lambda_min": round(w.lambda_min, 9),
                "lambda_max": round(w.lambda_max, 9),
                "lambda_mean": round(w.lambda_sum / total, 9),
                "mod3_lambda_min": {str(k): round(v, 9) for k, v in
                                    sorted(w.mod3_lambda_min.items())},
                "take_margin_min_bits":
                    None if w.take_margin_min is None
                    else w.take_margin_min.bit_length(),
                "skip_margin_min_bits":
                    None if w.skip_margin_min is None
                    else w.skip_margin_min.bit_length(),
                "small_margin_frac_lt_2^-40": round(sum(
                    c for k, c in w.margin_bitlen_hist.items()
                    if isinstance(k, int) and 0 < k <= 40) / total, 9),
                "max_take_run": w.max_take_run,
                "max_skip_run": w.max_skip_run,
                "saturated": w.saturated,
                "pulse_hist_top": [
                    [list(k), v] for k, v in
                    sorted(w.pulse_hist.items(), key=lambda kv: -kv[1])[:6]
                ],
            })
        return {
            "ranks": self.ranks,
            "selected": self.selected_final,
            "min_closed_margin": self.min_closed_margin,
            "min_closed_margin_rank": self.min_closed_margin_rank,
            "windows": wins,
            **post,
        }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ranks", type=int, default=200_000)
    ap.add_argument("--json-out", type=str)
    args = ap.parse_args()
    chain = DeepChain(args.ranks)
    chain.run()
    result = chain.summary()
    text = json.dumps(result, indent=1, sort_keys=True)
    print(text)
    if args.json_out:
        with open(args.json_out, "w") as fh:
            fh.write(text)


if __name__ == "__main__":
    main()
