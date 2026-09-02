#!/usr/bin/env python3
"""Does Erdos #68's predecessor-gap certificate actually fire?

Upstream analytic state
-----------------------
`cofinal_tailfree_predecessor_gap_threshold` is one of the few producers in the
corpus stated as a pure integer inequality, and Lean proves that cofinally many
certificates imply irrationality outright:

    for every cutoff B there is m > B with  ((m+2)m! - 2) v_m  <=  m^2 (m!-1) u_m,

where Q_m = (m-1)! * sum_(n=2)^(m-1) 1/(n!-1), v_m = den(Q_m), and
u_m = (floor(Q_m)+1) v_m - num(Q_m).  Lean also proves 1 <= u_m <= v_m and the
exact equivalence with  1 + 1/(m!-1) + 2/m <= m u_m / v_m.

Reading the definition, u_m / v_m = floor(Q_m) + 1 - Q_m = 1 - {Q_m}, so the
certificate fires exactly when

    {Q_m}  <=  1 - 1/m - 2/m^2 - 1/(m (m!-1)).

That is a statement about the fractional part of an explicit rational.  It has
never been evaluated: the packet records no computational coverage for it.

Probe
-----
Compute Q_m exactly as a rational for m in range, evaluate the literal integer
inequality (not the reduced form), and measure how often it fires.

Predeclared falsifier
---------------------
If {Q_m} were uniform the certificate would fail with probability about 1/m, so
failures should be rare and thin out.  A failure rate that does not decay, or
failures that cluster, is the interesting outcome: it would mean {Q_m} is pushed
against 1 by arithmetic and the producer is genuinely hard rather than generic.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import factorial
from pathlib import Path


def run(max_m: int, min_m: int = 3) -> dict:
    prefix = Fraction(0)          # sum_(n=2)^(m-1) 1/(n!-1)
    rows = []
    fires = 0
    failures = []
    expected_failures = 0.0
    for m in range(3, max_m + 1):
        prefix += Fraction(1, factorial(m - 1) - 1)   # adds n = m-1
        if m < min_m:
            continue
        Q = factorial(m - 1) * prefix
        v = Q.denominator
        num = Q.numerator
        u = (Q.numerator // Q.denominator + 1) * v - num
        assert 1 <= u <= v, (m, u, v)
        fac = factorial(m)
        lhs = ((m + 2) * fac - 2) * v
        rhs = m * m * (fac - 1) * u
        fired = lhs <= rhs
        fires += fired
        expected_failures += 1.0 / m
        frac_q = float(Fraction(num % v, v)) if v else 0.0
        if not fired:
            failures.append({"m": m, "frac_Q": round(frac_q, 9),
                             "threshold": round(1 - 1 / m - 2 / (m * m), 9)})
        rows.append({"m": m, "fired": bool(fired), "frac_Q": round(frac_q, 6)})
    tested = len(rows)
    return {
        "probe_id": "erdos68_predecessor_gap_threshold",
        "m_range": [min_m, max_m],
        "tested": tested,
        "certificates_fired": fires,
        "fire_rate": round(fires / tested, 6) if tested else None,
        "failures": failures,
        "failure_count": len(failures),
        "expected_failures_if_uniform": round(expected_failures, 3),
        "largest_m_with_failure": max((f["m"] for f in failures), default=None),
        "largest_m_tested": max_m,
        "failure_count_vs_uniform_ratio": (
            round(len(failures) / expected_failures, 4) if expected_failures else None
        ),
        "reading": (
            "failure count matches the uniform prediction, so {Q_m} shows no arithmetic "
            "bias against the certificate: the producer's event is generic and the "
            "missing input is equidistribution of {Q_m}, not a new mechanism"
            if expected_failures and 0.5 <= len(failures) / expected_failures <= 2.0 else
            "failure count departs from the uniform prediction; {Q_m} carries a bias"
        ),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-m", type=int, default=180)
    ap.add_argument("--min-m", type=int, default=3)
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()
    payload = run(args.max_m, args.min_m)
    if args.out:
        Path(args.out).write_text(json.dumps(payload, indent=1) + "\n")
    compact = {k: v for k, v in payload.items() if k != "rows"}
    print(json.dumps(compact, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
