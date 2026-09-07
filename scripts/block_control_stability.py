#!/usr/bin/env python3
"""Is the section-45 block control a NULL, or one draw from a lottery?

WHY THIS EXISTS (the analysis it is bound to)
---------------------------------------------
Cross-index T39b. Section 60 screened the SOCKET census and found its controls were
zero-runs carrying no arithmetic. That correction does NOT transfer here: the block
clause is `tau_A(N+j) = tau_A(j) + 1`, and a zero at `N+j` would need `tau_A(j) = -1`,
so zeros get no free pass. Section 45's control was therefore left UNAUDITED, and its
*"worse than chance"* reading stands as MEASURED-IN-RANGE with no screen behind it.

THE STRUCTURE THE CLAUSE ACTUALLY HAS (read off `shifted_block_census.py`, not guessed)
---------------------------------------------------------------------------------------
`max_block` tests `tau[N+j] == tau[j] + 1` for `j = 1..K`, and `control_census` shuffles
the WHOLE array `1..M` and reruns the same census. So in the control the values at the
SMALL indices `j = 1..K` are themselves shuffled, and

    the run at every `N` is tested against ONE FIXED WORD  w = (tau'(1), ..., tau'(K)),

drawn once per seed. The per-`N` success probability is `prod_j P(tau' = w_j + 1)`, which
depends on which values the shuffle happened to deposit at positions `1..K`. In
particular `K >= 1` requires `tau'(N+1) = tau'(1) + 1`, so the entire cascade is
conditioned on the single realised value `tau'(1)`.

**A statistic conditioned on one lottery draw is not a null.** That is the hypothesis.

WHY THE OBVIOUS MARGINAL PREDICTOR FAILED (recorded, so it is not retried)
--------------------------------------------------------------------------
`p = sum_v P(tau=v) P(tau=v+1)` gives `p = 1/6` for BOTH `powers2` (`tau = v_2 + 1`) and
`lacunary` (`tau = v_3 + 1`), hence one predicted `K ~ log_6(5x10^5) = 7.3` for both,
against recorded controls of 3 and 10. It also predicts `powers2 > lacunary` (since
`P(tau'=2)` is `1/4` versus `2/9`), and the recording is the other way round. That model
averages over the head word; the point of this probe is that the head word must not be
averaged over.

PREDICTIONS, RECORDED BEFORE THE RUN
------------------------------------
P1  **Instability.** Across seeds the control max `K` for `lacunary` spans a range of at
    least 5. If the control is a lottery, one recorded value cannot be a baseline.
P2  **The head value explains it.** Conditioning the control max `K` on the realised
    `tau'(1)` collapses most of that spread: runs with the modal `tau'(1)` are long, runs
    with a rare `tau'(1)` are short.
P3  **Discrimination -- the screen must not dissolve everything.** `naturals` (`tau = d`,
    a diffuse marginal with no dominant value) must stay small, max `K <= 2` on every
    seed, matching its recorded control of 1. If a screen flattens every cohort it is
    measuring nothing.

FALSIFIER, stated before the run: if EVERY cohort's control max `K` is stable across
seeds (full range <= 1), the control is a legitimate null, section 45's reading survives
untouched, and T39b closes as a clean bill. That is a real possible outcome and would
vindicate section 45.

WHAT THIS CANNOT DO: it cannot touch the REAL values. For `naturals`, `powers2` and
`lacunary` the real max `K` is fixed by algebra in the census's own docstring (`d(N+1)=2`
forces `N+1` prime and consecutive squares are impossible, so `K=2` at `N=2` only;
`v_2+1` forces `K=1`; and for `v_3+1`, `j=1,2` would need `3 || N+1` and `3 || N+2` at
once). Those are theorems. A control comparison against a proven value decides nothing
either way.

Bound directions, per the standing infrastructure rule:
  analysis -> here : CertificateSocketCollapse.md section 45 (the reading under audit)
                     section 60 + T39/T39b (the outcome-screen rule and this residual)
  here -> analysis : CertificateSocketCollapse.md section 61, receipt under state/
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import random
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]


def _load_census():
    """Import the census module so the cohort conventions are ITS conventions."""
    spec = importlib.util.spec_from_file_location(
        "sbc", HERE / "shifted_block_census.py"
    )
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def max_block(tau, N, M, cap):
    K = 0
    while K < cap and N + K + 1 <= M:
        j = K + 1
        if tau[N + j] != tau[j] + 1:
            break
        K += 1
    return K


def census_max(tau, M, nmax, cap):
    best = 0
    for N in range(1, nmax + 1):
        K = max_block(tau, N, M, cap)
        if K > best:
            best = K
    return best


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--M", type=int, default=1000000)
    ap.add_argument("--nmax", type=int, default=500000)
    ap.add_argument("--cap", type=int, default=64)
    ap.add_argument("--seeds", type=int, default=16)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    M, nmax, cap = args.M, args.nmax, args.cap
    sbc = _load_census()
    spf = sbc.sieve_smallest_prime_factor(M)

    recorded = json.loads(
        (REPO / "state/formal_math/erdos257_period_noncollapse"
                "/shifted_block_census_receipt.json").read_text()
    )["cohorts"]

    report = {"M": M, "nmax": nmax, "cap": cap, "seeds": args.seeds, "cohorts": {}}
    for kind in sorted(recorded):
        tau = sbc.build_tau(kind, M, spf)
        pool = tau[1:M + 1]
        perm_runs, iid_runs, heads = [], [], []
        vals = list(pool)
        for s in range(args.seeds):
            rng = random.Random(90000 + s)
            sh = vals[:]
            rng.shuffle(sh)
            sh = [0] + sh
            perm_runs.append(census_max(sh, M, nmax, cap))
            heads.append(sh[1])
            idd = [0] + [rng.choice(vals) for _ in range(M)]
            iid_runs.append(census_max(idd, M, nmax, cap))

        by_head = {}
        for h, k in zip(heads, perm_runs):
            by_head.setdefault(h, []).append(k)

        report["cohorts"][kind] = {
            "recorded_control_max_K": recorded[kind]["control_max_K"],
            "recorded_real_max_K": recorded[kind]["max_K"],
            "perm_control_runs": perm_runs,
            "perm_min": min(perm_runs), "perm_max": max(perm_runs),
            "perm_range": max(perm_runs) - min(perm_runs),
            "iid_control_runs": iid_runs,
            "iid_min": min(iid_runs), "iid_max": max(iid_runs),
            "head_values": heads,
            "maxK_by_head_value": {str(h): sorted(v) for h, v in sorted(by_head.items())},
        }

    C = report["cohorts"]
    report["P1_instability"] = C["lacunary"]["perm_range"] >= 5
    report["P3_naturals_stays_small"] = C["naturals"]["perm_max"] <= 2
    report["falsifier_survived"] = any(c["perm_range"] > 1 for c in C.values())

    out = args.out or str(
        REPO / "state/formal_math/erdos257_period_noncollapse"
               "/block_control_stability_receipt.json"
    )
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    blob = json.dumps(report, indent=2, sort_keys=True)
    Path(out).write_text(blob)

    print(f"M={M} nmax={nmax} seeds={args.seeds}")
    print(f"{'cohort':>10} {'real':>5} {'recorded':>9} {'perm min..max':>15} {'range':>6} {'iid min..max':>14}")
    for k, c in report["cohorts"].items():
        print(f"{k:>10} {c['recorded_real_max_K']:>5} {c['recorded_control_max_K']:>9} "
              f"{str(c['perm_min'])+'..'+str(c['perm_max']):>15} {c['perm_range']:>6} "
              f"{str(c['iid_min'])+'..'+str(c['iid_max']):>14}")
    print(f"P1 lacunary range >= 5      = {report['P1_instability']}")
    print(f"P3 naturals stays <= 2      = {report['P3_naturals_stays_small']}")
    print(f"falsifier survived (some range > 1) = {report['falsifier_survived']}")
    print(f"wrote {out} sha256={hashlib.sha256(blob.encode()).hexdigest()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
