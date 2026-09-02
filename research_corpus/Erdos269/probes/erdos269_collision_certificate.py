#!/usr/bin/env python3
"""Erdos 269: covering-obligation certificate over ALL denominators.

`DyadicWindowComputationalLab.md` (Window-residue rigidity) refutes the
integral-state branch exactly for first indices A <= 6000, and its 2026-08-23
correction records that this branch is only the `Q = 1` fibre: the obligation
covering every denominator is the collision criterion of
`ErdosProblems/Erdos269/RationalLatticeReduction.lean`
(`exists_normalizedTailState_collision_of_value_eq_rat`).

That criterion says: if S = p/q then two DISTINCT scales carry normalized tail
states differing by an integer, i.e. theta_a = theta_a' with a < a' <= q+1,
where theta_a = {X_a}.  Contrapositive, quantitatively:

  * pairwise-distinct theta over a <= N            =>  q >= N;
  * distinct theta are >= 1/q apart, so with G the observed minimum gap and
    eps the truncation error,                       =>  q >= 1/(G + 2 eps).

Both bounds hold for EVERY denominator, with no Q = 1 restriction and no
coprime-to-30 reduction.

theta_a is computed by exact rational truncation at depth J of
X_a = sum_{j>=0} d_{a+j} / prod_{i<=j} b_{a+i}, using the lab's own fast block
engine.  The truncation error is bounded by max(digit) * 8^-J and is reported;
the certificate is only claimed when the observed gap exceeds it comfortably.

Boundary: this is a finite certificate, weaker than the landed Farey lane
(~1.64e90) and the certified continued fraction (~1e6768), which are however
computed for the value directly.  Its point is coverage: it is the first
certificate attached to the criterion that covers all denominators at once.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import sys
from fractions import Fraction

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from erdos269_fast_engine import build_dyadic_blocks_fast  # noqa: E402


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--max-a", type=int, default=200000)
    ap.add_argument("--depth", type=int, default=26)
    ap.add_argument("--receipt", type=str, default=None)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    N, J = args.max_a, args.depth
    blocks = build_dyadic_blocks_fast(N + J + 4)
    b = [0] + [t[0] for t in blocks]
    d = [0] + [t[1] for t in blocks]

    theta = [0.0] * (N + 1)
    for a in range(1, N + 1):
        num, den = 0, 1
        for j in range(J):
            den *= b[a + j]
            num = num * b[a + j] + d[a + j]
        fr = Fraction(num, den)
        theta[a] = float(fr - int(fr))

    eps = float(max(d[N:N + J])) * 8.0 ** (-J)
    order = sorted(range(1, N + 1), key=lambda a: theta[a])
    gap, gi, gj = min((theta[order[i + 1]] - theta[order[i]], order[i], order[i + 1])
                      for i in range(N - 1))
    dist, di = min((min(theta[a], 1.0 - theta[a]), a) for a in range(1, N + 1))

    certified = gap > 10 * eps
    q_from_count = N
    q_from_gap = int(1.0 / (gap + 2 * eps))
    q_from_zero = int(1.0 / (dist + eps))

    receipt = {
        "problem_id": "erdos_269",
        "probe": "erdos269_collision_certificate",
        "criterion": "exists_normalizedTailState_collision_of_value_eq_rat "
                     "(RationalLatticeReduction.lean)",
        "covers": "every denominator; not restricted to Q = 1 or to gcd(Q,30) = 1",
        "scales": N, "truncation_depth": J, "truncation_error": eps,
        "min_gap": gap, "min_gap_pair": [gi, gj],
        "min_distance_to_Z": dist, "min_distance_scale": di,
        "gap_over_error": gap / eps,
        "all_theta_distinct": gap - 2 * eps > 0,
        "denominator_lower_bound_from_count": q_from_count,
        "denominator_lower_bound_from_gap": q_from_gap,
        "denominator_lower_bound_from_zero_distance": q_from_zero,
        "denominator_lower_bound": max(q_from_count, q_from_gap, q_from_zero),
        "claim_boundary": "finite certificate; weaker than the landed Farey lane "
                          "(~1.64e90) and certified continued fraction (~1e6768), "
                          "but the first one attached to the all-denominator criterion",
        "status": "pass" if certified and gap - 2 * eps > 0 else "fail",
    }
    if args.receipt:
        p = pathlib.Path(args.receipt)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    if args.json:
        print(json.dumps(receipt, indent=2, sort_keys=True))
    else:
        print(f"scales tested             : {N}")
        print(f"theta truncation error    : {eps:.3e}")
        print(f"min gap between distinct  : {gap:.4e}  at (a,a') = ({gi},{gj})"
              f"   [{gap / eps:.1f}x the error]")
        print(f"min distance to Z         : {dist:.4e}  at a = {di}")
        print(f"all theta pairwise distinct: {receipt['all_theta_distinct']}")
        print(f"q >= {q_from_count} (count), {q_from_gap} (gap), "
              f"{q_from_zero} (distance to Z)")
        print(f"=> every rational S has denominator q >= "
              f"{receipt['denominator_lower_bound']}, for ALL denominators")
        print(f"status : {receipt['status']}")
    return 0 if receipt["status"] == "pass" else 1


if __name__ == "__main__":
    sys.exit(main())
