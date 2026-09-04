#!/usr/bin/env python3
"""Erdos 68: predecessor-gap certificate scan via the Q-recursion.

Producer `cofinal_tailfree_predecessor_gap_threshold` (priority 1) asks for
cofinally many m with the pure integer inequality

        ((m+2)m! - 2) v_m  <=  m^2 (m! - 1) u_m,

equivalently  eta_m := 1 - {Q_m}  >=  tau_m := 1/m + 2/m^2 + 1/(m(m!-1)),
where Q_m = (m-1)! * sum_{n=2}^{m-1} 1/(n!-1).  Lean proves cofinally many such
certificates imply irrationality of S = sum_{n>=2} 1/(n!-1).

`PredecessorGapThresholdLab.md` evaluated this for m = 3..210 in exact rational
arithmetic and reported the cost barrier: den(Q_m) grows like prod(n!-1).

This probe removes that barrier.  From the definition,

        Q_{m+1} = m Q_m + 1 + 1/(m! - 1),

so the fractional part obeys

        theta_{m+1} = { m theta_m + delta_m },     delta_m = 1/(m! - 1),

and the scan never forms den(Q_m) at all.  The only cost is precision: each step
inflates the error by a factor m, so a start error of 10^-D at m0 becomes
10^-D * M!/m0! at M.  Choosing D > log10(M!) + margin keeps the scan sound, and
the realised error bound is printed and asserted against tau_M.

Start value is exact: Q_{m0} is built as a Fraction and converted at full working
precision, so no floating-point logarithm or approximation enters the seed.

This measures the fire rate.  It does not prove cofinality, and Erdos 68 remains
open.
"""
from __future__ import annotations

import argparse
import json
import math
import pathlib
import sys
from fractions import Fraction

from mpmath import mp


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--start", type=int, default=30, help="exact-seed index m0")
    ap.add_argument("--max-m", type=int, default=12000)
    ap.add_argument("--margin-digits", type=int, default=400)
    ap.add_argument("--receipt", type=str, default=None)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    m0, M = args.start, args.max_m
    log10_fact_M = math.lgamma(M + 1) / math.log(10)
    mp.dps = int(log10_fact_M) + args.margin_digits

    # exact seed
    q = Fraction(0)
    for n in range(2, m0):
        q += Fraction(1, math.factorial(n) - 1)
    q *= math.factorial(m0 - 1)
    frac = q - int(q)
    theta = mp.mpf(frac.numerator) / mp.mpf(frac.denominator)

    fires = 0
    failures = []
    err = mp.mpf(10) ** (-mp.dps + 20)
    fact = mp.mpf(math.factorial(m0))
    for m in range(m0, M + 1):
        eta = 1 - theta
        tau = mp.mpf(1) / m + mp.mpf(2) / (m * m) + mp.mpf(1) / (m * (fact - 1))
        if eta >= tau:
            fires += 1
        else:
            failures.append({"m": m, "eta": float(eta), "tau": float(tau)})
        theta = m * theta + mp.mpf(1) / (fact - 1)
        theta = theta - mp.floor(theta)
        err = err * m
        fact = fact * (m + 1)

    checked = M - m0 + 1
    expected = sum(1.0 / m for m in range(m0, M + 1))
    sound = err < mp.mpf(1) / (1000 * M)

    receipt = {
        "problem_id": "erdos_68",
        "probe": "erdos68_predecessor_gap_recursion_scan",
        "producer": "cofinal_tailfree_predecessor_gap_threshold (priority 1)",
        "builds_on": "PredecessorGapThresholdLab.md, which reached m <= 210 "
                     "in exact rational arithmetic",
        "method": "theta_{m+1} = {m theta_m + 1/(m!-1)}: never forms den(Q_m)",
        "range": [m0, M], "checked": checked,
        "working_dps": mp.dps,
        "final_error_bound": mp.nstr(err, 6),
        "soundness_threshold": mp.nstr(mp.mpf(1) / (1000 * M), 6),
        "precision_sound": bool(sound),
        "fires": fires, "failure_count": len(failures), "failures": failures,
        "fire_rate": fires / checked,
        "expected_failures_uniform": expected,
        "observed_over_expected": len(failures) / expected if expected else None,
        "claim_boundary": "measures the fire rate over a finite range; does not prove "
                          "cofinality. Erdos 68 remains open.",
        "status": "pass" if sound else "fail",
    }
    if args.receipt:
        p = pathlib.Path(args.receipt)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    if args.json:
        print(json.dumps(receipt, indent=2, sort_keys=True))
    else:
        print(f"range m = {m0}..{M}  ({checked} certificates); working dps {mp.dps}")
        print(f"error bound {mp.nstr(err, 4)} vs soundness threshold "
              f"{mp.nstr(mp.mpf(1)/(1000*M), 4)}  -> "
              f"{'SOUND' if sound else 'PRECISION TOO LOW'}")
        print(f"fires {fires}  failures {len(failures)}  fire rate {fires/checked:.6f}")
        print(f"expected failures under uniformity {expected:.2f}; "
              f"observed/expected {len(failures)/expected:.3f}")
        print("failures:", [(f["m"], f"{f['eta']:.3e}") for f in failures])
        print(f"status : {receipt['status']}")
    return 0 if sound else 1


if __name__ == "__main__":
    sys.exit(main())
