#!/usr/bin/env python3
"""Exhaustive death census for every rational with a fixed denominator.

WHAT THIS DECIDES
-----------------
`notes/HoleGenericity.md` gives the measure model: the conditional death hazard
of the forced greedy is ``rho_n = gamma_n / T_{n-1} ~ (1/3) 2^-n``, summable,
so a uniform real survives forever with probability ``1/E = 0.6224``.

Applied to rationals that model says Erdos 257 is FALSE, because
`SupportWordStructureLab.md` section 4g proves that for ``q`` a non-Mersenne
prime NO ``p/q`` is a finite sum of ``1/(2^a - 1)``.  So for such ``q``:

    p/q survives the greedy forever   <=>   p/q has an INFINITE support A
                                            with sum_{a in A} 1/(2^a-1) = p/q
                                      <=>   p/q is a counterexample to 257.

Therefore, for a single non-Mersenne prime ``q``, the census below is a
complete decision procedure for "does denominator ``q`` contain a
counterexample, up to depth D":

    every p dies by depth D   =>   no counterexample has denominator q
                                   (a one-way result for that denominator)
    some p survives to depth D =>  that p is a named counterexample CANDIDATE

and the survival curve ``S_q(D)`` decides between the two hypotheses:

    S_q(D) -> positive limit  =>  the measure model holds for rationals,
                                  survivors are counterexample candidates
    S_q(D) -> 0               =>  rationals carry an arithmetic hazard the
                                  measure model cannot see; that excess IS the
                                  mechanism behind Erdos 257, and its RATE is
                                  the quantity a proof must reproduce

This is a census, not a sample: every residue is run, so there is no sampling
noise and no repeated-target confound (which is exactly the defect in a random
p/q ensemble when q is small -- only ~qE distinct targets exist).

Bound directions:
  analysis -> here : notes/HoleGenericity.md ; SupportWordStructureLab.md 4g
  here -> analysis : notes/RationalDeathCensus.md, receipt under state/
"""

from __future__ import annotations

import argparse
import hashlib
import json
from math import gcd
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]


def build_tables(P: int):
    """Z[n] <= 2^P z_n < Z[n]+1 ; TT[n] <= 2^P T_n < TT[n] + (P-n) + 2."""
    one = 1 << P
    Z = [0] * (P + 2)
    for n in range(1, P + 1):
        Z[n] = one // ((1 << n) - 1)
    TT = [0] * (P + 2)
    s = 0
    for n in range(P, -1, -1):
        TT[n] = s
        if n >= 1:
            s += Z[n]
    return Z, TT


def run_target(R0: int, err0: int, depth: int, P: int, Z, TT):
    """Certified forced greedy; see late_hazard_profile.py for the enclosures."""
    R, err = R0, err0
    taken = 0
    for n in range(1, depth + 1):
        zn = Z[n]
        if R >= zn + 1:
            R = R - zn - 1
            err += 1
            taken += 1
            if R + err < 1:
                return ("terminated", n, taken)
            continue
        if R + err < zn:
            if R > TT[n] + (P - n) + 2:
                return ("dead", n, taken)
            if R + err <= TT[n]:
                continue
            return ("indeterminate_death", n, taken)
        return ("indeterminate_take", n, taken)
    return ("alive", depth, taken)


def census(q: int, depth: int, P: int, Z, TT):
    ceiling = TT[0]  # floor(2^P E)
    pmax = (q * ceiling) >> P
    death_rank = {}
    counts = {"alive": 0, "dead": 0, "terminated": 0,
              "indeterminate_take": 0, "indeterminate_death": 0}
    survivor_density = []
    survivors = []
    for p in range(1, pmax + 1):
        if gcd(p, q) != 1:
            continue
        status, rank, taken = run_target((p << P) // q, 1, depth, P, Z, TT)
        counts[status] += 1
        if status == "dead":
            death_rank[rank] = death_rank.get(rank, 0) + 1
        elif status == "alive":
            survivor_density.append(taken / depth)
            if len(survivors) < 40:
                survivors.append(p)
    total = sum(counts.values())
    # S_q(D') = fraction not yet dead by depth D'
    curve = []
    dead_so_far = 0
    for d in range(1, depth + 1):
        dead_so_far += death_rank.get(d, 0)
        curve.append(round((total - dead_so_far) / total, 8))
    return {
        "q": q,
        "targets": total,
        "counts": counts,
        "death_rank_histogram": {str(k): v for k, v in sorted(death_rank.items())},
        "deepest_death": max(death_rank) if death_rank else None,
        "survival_curve": curve,
        "survival_final": curve[-1] if curve else None,
        "mean_survivor_support_density": (
            sum(survivor_density) / len(survivor_density) if survivor_density else None
        ),
        "example_survivor_numerators": survivors,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--q", default="1009,2003,4001")
    ap.add_argument("--depth", type=int, default=400)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    depth = args.depth
    P = 3 * depth + 160
    Z, TT = build_tables(P)

    E_over = TT[0] / float(1 << P)
    report = {"depth": depth, "bits": P, "E_lower_bound": E_over,
              "null_survival_1_over_E": 1.0 / E_over, "denominators": []}
    for qs in args.q.split(","):
        q = int(qs)
        row = census(q, depth, P, Z, TT)
        report["denominators"].append(row)
        c = row["counts"]
        print(
            f"q={q:>7} targets={row['targets']:>6} "
            f"alive={c['alive']:>6} dead={c['dead']:>6} term={c['terminated']} "
            f"indet(take/death)={c['indeterminate_take']}/{c['indeterminate_death']} "
            f"S_q({depth})={row['survival_final']:.4f} "
            f"deepest_death={row['deepest_death']} "
            f"mean_supp_density={row['mean_survivor_support_density']}"
        )

    out = args.out or str(
        REPO / "state/formal_math/erdos257_period_noncollapse/rational_death_census_receipt.json"
    )
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    blob = json.dumps(report, indent=2, sort_keys=True)
    Path(out).write_text(blob)
    print(f"null survival 1/E = {1.0/E_over:.6f}")
    print(f"wrote {out} sha256={hashlib.sha256(blob.encode()).hexdigest()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
