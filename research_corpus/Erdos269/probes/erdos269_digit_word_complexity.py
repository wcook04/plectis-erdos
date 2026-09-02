#!/usr/bin/env python3
"""Erdos 269: factor complexity of the PROPER (carry-normalised) digit word.

Builds directly on the corpus result in
`ErdosProblems/Erdos269/TorusCocycleAndDiophantineTypeLab.md`: the RADIX word
(b_a) is a rank-2 torus coding with factor complexity exactly

        p_b(n) = (n+1)^2,

which is why the Adamczewski-Bugeaud stammering lane is closed -- the word is
too regular.  That lab measured the radix word.  It did not measure the digit
word, and the digit word is the object whose complexity is unconstrained.

Criterion.  The normalized dyadic tail state obeys X_{a+1} = b_a X_a - d_a, so
its fractional part theta_a = {X_a} obeys

        theta_{a+1} = b_a theta_a - eps_a,     eps_a = floor(b_a theta_a),

i.e. (eps_a) is the proper Cantor expansion of {S} in the mixed radix (b_a).
A length-n window of the joint word W = (b, eps) is a function of
(theta_a, b_a .. b_{a+n-1}).  If S = p/q then theta_a takes at most q values, so

        p_W(n) <= q * p_b(n) = q (n+1)^2      for every n.

Two consequences, both new:

  * q >= p_W(n) / (n+1)^2  is a rigorous denominator lower bound from a finite
    computation, of a different type to the Farey / first-hit lane;
  * if p_W(n)/(n+1)^2 is UNBOUNDED then S is irrational.

This probe measures p_W(n) and p_b(n) on the literal source word.  theta_a is
computed by exact rational truncation at depth J, so the reported eps letters are
exact whenever the printed slack exceeds the printed truncation error.

Nothing here proves irrationality: p_W is measured, not bounded below.  What the
measurement gives is the growth SHAPE and the exact threshold the proof needs.
"""
from __future__ import annotations

import argparse
import json
import math
import pathlib
from math import prod
import sys
from fractions import Fraction

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from erdos269_fast_engine import build_dyadic_blocks_fast  # noqa: E402


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--max-a", type=int, default=30000)
    ap.add_argument("--depth", type=int, default=26, help="exact truncation depth for theta")
    ap.add_argument("--lengths", type=int, nargs="*", default=[1, 2, 3, 4, 5, 6, 7, 8])
    ap.add_argument("--receipt", type=str, default=None)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    A, J = args.max_a, args.depth
    blocks = build_dyadic_blocks_fast(A + J + 4)
    b = [0] + [t[0] for t in blocks]
    d = [0] + [t[1] for t in blocks]

    theta = [0.0] * (A + 1)
    eps = [0] * (A + 1)
    min_slack = 1.0
    for a in range(1, A + 1):
        num, den = 0, 1
        for j in range(J):
            den *= b[a + j]
            num = num * b[a + j] + d[a + j]
        fr = Fraction(num, den)
        t = float(fr - int(fr))
        theta[a] = t
        x = b[a] * t
        eps[a] = int(math.floor(x))
        min_slack = min(min_slack, abs(x - round(x)))
    trunc = float(max(d[A:A + J])) * 8.0 ** (-J)

    rows = []
    for n in args.lengths:
        by_cyl: dict = {}
        for a in range(1, A - n):
            u = tuple(b[a + i] for i in range(n))
            by_cyl.setdefault(u, set()).add(tuple(eps[a + i] for i in range(n)))
        pw = sum(len(v) for v in by_cyl.values())
        # ceiling: inside a radix cylinder u the map theta -> theta_{a+n} is
        # x -> {prod(u) x}, and the eps-window names which of the prod(u) equal
        # cells theta_a occupies.  So prod(u) is an exact per-cylinder ceiling.
        ceiling = sum(prod(u) for u in by_cyl)
        rows.append({"n": n, "p_b_predicted": (n + 1) ** 2, "p_b_observed": len(by_cyl),
                     "p_W": pw, "cell_ceiling": ceiling, "hit_fraction": pw / ceiling,
                     "scales_per_cylinder": (A - n) / len(by_cyl),
                     "ratio": pw / len(by_cyl),
                     "denominator_lower_bound": int(pw / ((n + 1) ** 2)),
                     "sample_limited": (A - n) / len(by_cyl) < 3 * max(prod(u) for u in by_cyl)})

    radix_ok = all(r["p_b_observed"] == r["p_b_predicted"] for r in rows)
    best = max(r["denominator_lower_bound"] for r in rows)
    growth = [rows[i + 1]["p_W"] / rows[i]["p_W"] for i in range(len(rows) - 1)]
    saturating = [r["n"] for r in rows if not r["sample_limited"] and r["hit_fraction"] > 0.999]

    receipt = {
        "problem_id": "erdos_269",
        "probe": "erdos269_digit_word_complexity",
        "builds_on": "TorusCocycleAndDiophantineTypeLab.md: p_b(n) = (n+1)^2 exactly",
        "max_a": A, "theta_truncation_depth": J,
        "theta_truncation_error": trunc,
        "min_letter_slack": min_slack,
        "letters_exact": min_slack > 10 * trunc,
        "radix_complexity_reproduced": radix_ok,
        "eps_alphabet_max": max(eps[1:]),
        "rows": rows,
        "unsaturated_growth_factors": growth[:3],
        "cell_ceiling_conjecture": "p_W(n) = sum_{u in L_b(n)} prod(u): the theta-orbit "
                                   "visits every cell of every radix cylinder. Exactly "
                                   "attained where the sample resolves it. It implies "
                                   "p_W(n)/(n+1)^2 >= 2^n -> infinity, hence S irrational.",
        "denominator_lower_bound": best,
        "lengths_attaining_cell_ceiling": saturating,
        "criterion": "S = p/q forces p_W(n) <= q (n+1)^2 for all n; unbounded "
                     "p_W(n)/(n+1)^2 therefore implies S irrational",
        "claim_boundary": "p_W is measured, not bounded below; this is not a proof. "
                          "The finite bound is far weaker than the landed Farey lane "
                          "(~1.64e90) and the certified continued fraction (~1e6768).",
        "status": "pass" if radix_ok and min_slack > 10 * trunc else "fail",
    }
    if args.receipt:
        p = pathlib.Path(args.receipt)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    if args.json:
        print(json.dumps(receipt, indent=2, sort_keys=True))
    else:
        print(f"radix alphabet {sorted(set(b[1:]))}; eps alphabet max {max(eps[1:])}")
        print(f"theta truncation error {trunc:.2e}; min letter slack {min_slack:.2e}; "
              f"letters exact: {receipt['letters_exact']}")
        print(f"radix complexity (n+1)^2 reproduced exactly: {radix_ok}")
        print("\n  n   p_b=(n+1)^2   cell ceiling   p_W measured   hit fraction   q >=      sample-limited")
        for r in rows:
            print(f" {r['n']:3d}   {r['p_b_predicted']:9d}   {r['cell_ceiling']:12d}   "
                  f"{r['p_W']:12d}   {r['hit_fraction']:12.6f}   "
                  f"{r['denominator_lower_bound']:8d}   "
                  f"{'yes' if r['sample_limited'] else 'no'}")
        print(f"\nunsaturated growth factors of p_W: "
              f"{', '.join(f'{g:.2f}' for g in growth[:3])}")
        print(f"status : {receipt['status']}")
    return 0 if receipt["status"] == "pass" else 1


if __name__ == "__main__":
    sys.exit(main())
