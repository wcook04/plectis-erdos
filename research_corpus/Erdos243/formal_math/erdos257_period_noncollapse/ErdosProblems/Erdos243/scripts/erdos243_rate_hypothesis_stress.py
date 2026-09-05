#!/usr/bin/env python3
"""Erdos #243: how long can a real rational orbit IMITATE a counterexample?

Experiments 1-5 of the wave-1 computational lab all measure unconditional orbit
statistics.  None of them touches the actual hypothesis of #243, which in
Koizumi coordinates is normalised vanishing E_n/C_n -> 0.  This script measures
it directly, by finding the longest stretch on which a genuine rational orbit
sits inside the counterexample regime.

For a threshold theta, define a THETA-WINDOW to be a maximal run of consecutive
indices n with

        0 < |E_n| / C_n <= theta.

The strict inequality E_n != 0 matters: once E_n = 0 the orbit is on the exact
Sylvester tail, where E/C = 0 forever, so windows containing a zero are
vacuous.  A counterexample to #243 is, eventually, an INFINITE theta-window for
every theta > 0.  The longest theta-window realised by an actual rational is
therefore a direct measure of how expensive the hypothesis is.

The same is done for the corpus's sharper regime -- the slow-negative-part
band (-E_n)_+ <= (1 - delta) log2 log2 C_n, which is Lean-closed -- and for the
one-sided band E_n >= 0 (no negative part at all).

Search space: an exhaustive small-seed sweep over (C_0, D_0), pre-filtered to
seeds whose first step already lies in the band (which is where every long
window must start or be reachable from), plus random large-q sampling.

Examples
--------
    ./repo-python .../erdos243_rate_hypothesis_stress.py --quick
    ./repo-python .../erdos243_rate_hypothesis_stress.py --c0-max 140 \
        --d0-max 90000 --samples 200000 --out r.json
"""

from __future__ import annotations

import argparse
import json
import math
import random
import sys
import time
from collections import Counter
from math import gcd
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from erdos243_orbit_engine import TERMINATED, centre, run_orbit  # noqa: E402

THETAS = (0.5, 0.25, 0.125, 0.0625, 0.03125, 0.015625)


def band_windows(C, E, pred):
    """Longest run of consecutive n with E_n != 0 and pred(E_n, C_n)."""
    best = 0
    best_span = None
    cur = 0
    start = 0
    for n in range(len(E)):
        if E[n] != 0 and pred(E[n], C[n]):
            if cur == 0:
                start = n
            cur += 1
            if cur > best:
                best = cur
                best_span = (start, n)
        else:
            cur = 0
    return best, best_span


class Stress:
    def __init__(self):
        self.theta_best = {t: (0, None) for t in THETAS}
        self.theta_hist = {t: Counter() for t in THETAS}
        self.slow_best = (0, None)
        self.slow_hist = Counter()
        self.nonneg_best = (0, None)
        self.nonneg_hist = Counter()
        self.orbits = 0
        self.total_steps = 0
        self.in_band = {t: 0 for t in THETAS}
        self.nonzero_steps = 0

    def ingest(self, C0, D0, orb, label):
        C, E = orb["C"], orb["E"]
        self.orbits += 1
        self.total_steps += len(E)
        for n in range(len(E)):
            if E[n] == 0:
                continue
            self.nonzero_steps += 1
            r = abs(E[n]) / C[n]
            for t in THETAS:
                if r <= t:
                    self.in_band[t] += 1
        for t in THETAS:
            L, span = band_windows(C, E, lambda e, c, t=t: abs(e) <= t * c)
            self.theta_hist[t][L] += 1
            if L > self.theta_best[t][0]:
                self.theta_best[t] = (L, {
                    "C0": C0, "D0": D0, "source": label, "span": span,
                    "C": C[span[0]:span[1] + 1] if span else [],
                    "E": E[span[0]:span[1] + 1] if span else [],
                    "status": orb["status"], "steps": orb["steps"]})
        L, span = band_windows(
            C, E, lambda e, c: (-e if e < 0 else 0) <= math.log2(math.log2(max(4, c))))
        self.slow_hist[L] += 1
        if L > self.slow_best[0]:
            self.slow_best = (L, {"C0": C0, "D0": D0, "source": label, "span": span,
                                  "C": C[span[0]:span[1] + 1] if span else [],
                                  "E": E[span[0]:span[1] + 1] if span else [],
                                  "status": orb["status"], "steps": orb["steps"]})
        L, span = band_windows(C, E, lambda e, c: e > 0)
        self.nonneg_hist[L] += 1
        if L > self.nonneg_best[0]:
            self.nonneg_best = (L, {"C0": C0, "D0": D0, "source": label,
                                    "span": span,
                                    "C": C[span[0]:span[1] + 1] if span else [],
                                    "E": E[span[0]:span[1] + 1] if span else [],
                                    "status": orb["status"], "steps": orb["steps"]})

    def report(self):
        return {
            "orbits_searched": self.orbits,
            "steps_searched": self.total_steps,
            "nonzero_steps": self.nonzero_steps,
            "iid_uniform_model": "if E_n were uniform on [-C_n/2, C_n/2) and independent, "
                                 "P(|E_n|/C_n <= theta) = 2 theta and the longest window "
                                 "over S nonzero steps is about log S / log(1/(2 theta))",
            "theta_windows": {
                str(t): {
                    "longest_window": self.theta_best[t][0],
                    "empirical_step_probability": (self.in_band[t] / self.nonzero_steps
                                                   if self.nonzero_steps else None),
                    "iid_model_step_probability": 2 * t,
                    "empirical_over_model": ((self.in_band[t] / self.nonzero_steps) / (2 * t)
                                             if self.nonzero_steps else None),
                    "iid_model_predicted_longest_window": (
                        math.log(max(2, self.nonzero_steps)) / math.log(1.0 / (2 * t))
                        if t < 0.5 else None),
                    "witness": self.theta_best[t][1],
                    "window_length_histogram": dict(sorted(self.theta_hist[t].items())),
                } for t in THETAS},
            "slow_negative_band_window": {
                "definition": "(-E_n)_+ <= log2 log2 max(4, C_n) and E_n != 0 "
                              "(the delta -> 0 edge of the Lean-closed regime)",
                "longest_window": self.slow_best[0],
                "witness": self.slow_best[1],
                "window_length_histogram": dict(sorted(self.slow_hist.items())),
            },
            "strictly_positive_band_window": {
                "definition": "E_n > 0 (no negative part at all); C is strictly decreasing "
                              "on such a window, so its length is trivially bounded by "
                              "log_2 C at the start",
                "longest_window": self.nonneg_best[0],
                "witness": self.nonneg_best[1],
                "window_length_histogram": dict(sorted(self.nonneg_hist.items())),
            },
        }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--c0-max", type=int, default=140)
    ap.add_argument("--d0-max", type=int, default=90000)
    ap.add_argument("--prefilter-theta", type=float, default=0.25,
                    help="only seeds whose first step already satisfies "
                         "|E_0| <= theta*C_0 are run in the exhaustive sweep")
    ap.add_argument("--samples", type=int, default=200000)
    ap.add_argument("--sample-qbits", type=int, default=48)
    ap.add_argument("--step-cap", type=int, default=400)
    ap.add_argument("--exact-bits", type=int, default=8000)
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()
    if args.quick:
        args.c0_max = 50
        args.d0_max = 6000
        args.samples = 8000

    t0 = time.perf_counter()
    sweep = Stress()
    seen = 0
    for C0 in range(2, args.c0_max + 1):
        lim = int(args.prefilter_theta * C0)
        for D0 in range(C0 + 1, args.d0_max + 1):
            r = centre(D0 % C0, C0)
            if abs(r) > lim:
                continue
            if gcd(C0, D0) != 1:
                continue
            seen += 1
            orb = run_orbit(C0, D0, height_cap=max(10 ** 9, 10 ** 5 * C0),
                            step_cap=args.step_cap, exact_bits=args.exact_bits,
                            lean=True)
            sweep.ingest(C0, D0, orb, "exhaustive_seed_sweep")
    t_sweep = time.perf_counter() - t0

    t0 = time.perf_counter()
    samp = Stress()
    rng = random.Random(243243)
    lo, hi = 1 << (args.sample_qbits - 1), 1 << args.sample_qbits
    for _ in range(args.samples):
        q = rng.randrange(lo, hi)
        p = rng.randrange(1, q)
        g = gcd(p, q)
        p //= g
        q //= g
        orb = run_orbit(p, q, height_cap=max(10 ** 9, 10 ** 5 * p),
                        step_cap=args.step_cap, exact_bits=args.exact_bits,
                        lean=True)
        samp.ingest(p, q, orb, "random_large_q")
    t_samp = time.perf_counter() - t0

    payload = {
        "probe_id": "erdos243_rate_hypothesis_stress",
        "quick": args.quick,
        "options": vars(args),
        "why": "Erdos #243's hypothesis is exactly normalised vanishing E_n/C_n -> 0; "
               "a counterexample is an eventually-infinite theta-window for every "
               "theta > 0.  The longest theta-window a genuine rational realises is a "
               "direct measure of how much the hypothesis costs, and it is the number "
               "that says whether a proof should be LOCAL (short windows are already "
               "impossible past a computable length) or ASYMPTOTIC.",
        "exhaustive_seed_sweep": {
            "C0_max": args.c0_max, "D0_max": args.d0_max,
            "prefilter_theta": args.prefilter_theta,
            "seeds_run": seen, **sweep.report()},
        "random_large_q": {"q_bits": args.sample_qbits, **samp.report()},
        "timings": {"sweep_seconds": t_sweep, "sample_seconds": t_samp},
    }
    text = json.dumps(payload, indent=1, ensure_ascii=False, default=str)
    if args.out:
        Path(args.out).write_text(text + "\n")
        print(f"wrote {args.out} ({len(text)} bytes) in {t_sweep + t_samp:.1f}s")
    else:
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
