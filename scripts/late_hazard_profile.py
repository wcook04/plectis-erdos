#!/usr/bin/env python3
"""Late-depth death hazard of the forced greedy: rationals versus reals.

WHY THIS EXISTS (the analysis it is bound to)
---------------------------------------------
`formal_math/erdos257_hole_geometry/notes/HoleGenericity.md` establishes the
measure model: death at rank ``n`` happens iff the rescaled remainder lands in
one hole of width ``h_n ~ (1/3) 2^-n``, so the conditional hazard is summable
and the survivor set has measure ``1``, i.e. a uniform real survives forever
with probability ``1/E = 0.6224`` (``E`` = Erdos-Borwein).

That model, applied to a RATIONAL target, says Erdos 257 is false.  A rational
``p/q`` whose greedy never dies has an infinite support ``A`` with
``sum_{a in A} 1/(2^a - 1) = p/q``.  And for ``q`` a non-Mersenne prime,
`SupportWordStructureLab.md` section 4g proves NO finite representation exists,
so survival forces the support to be infinite.  A 62% survival rate among such
rationals would be a 62% counterexample rate.

So exactly one of these is true, and no measurement in either programme
decides which:

  (H1)  the hazard really is summable for rationals too, and the counterexample
        lane is live -- deep search is then the right use of compute;
  (H2)  rational targets carry a HEAVIER late hazard than reals, invisible to
        the hole-width model, and that excess IS the arithmetic mechanism
        behind Erdos 257.

DESIGN (what makes it discriminating)
-------------------------------------
Three cohorts differing in nothing but the arithmetic of the target:

  real      uniform dyadic of ``P`` bits           -- the null, where the
                                                      measure model is exact
  large_q   ``p/q`` with ``q ~ 2^160``             -- lattice far finer than any
                                                      hole; must track the null
  small_q   ``p/q`` with ``q ~ 10^3``              -- lattice coarse enough that
                                                      arithmetic bites early

Under (H1) the three empirical hazards agree at every depth and all three go
silent past depth ~25 (expected deaths beyond that are < 1 per 10^5 targets).
Under (H2) ``small_q`` shows deaths at depths where the null predicts none.

FALSIFIER, stated before the run: if ``small_q`` records zero deaths beyond the
depth at which the null's expected count drops below 1, this probe does not
support (H2) and the counterexample lane stays live.

CERTIFICATION
-------------
Every take/skip/death decision is certified by integer enclosures at ``P``
bits; an undecidable comparison is reported as ``indeterminate`` and never
silently resolved.  Terminating targets are separated from live ones
(cross-index trap 5: terminating targets must not contaminate ensemble
statistics).

Bound directions, per the standing infrastructure rule:
  analysis -> here : notes/HoleGenericity.md (hole width, measure model)
                     SupportWordStructureLab.md section 4g (no finite rep)
  here -> analysis : notes/LateHazardProfile.md, receipt under state/
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]


# ---------------------------------------------------------------- tables


def build_tables(P: int):
    """Z[n] = floor(2^P / (2^n - 1)); TT[n] = sum_{k=n+1..P} Z[k].

    Enclosures, used everywhere below:
        Z[n]  <= 2^P z_n  <  Z[n] + 1
        TT[n] <= 2^P T_n  <  TT[n] + (P - n) + 2
    the ``+2`` covering the whole tail beyond rank P.
    """
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


# ---------------------------------------------------------------- engine


def run_target(R0: int, err0: int, depth: int, P: int, Z, TT):
    """Certified forced greedy.

    State: the true remainder r satisfies  R * 2^-P <= r <= (R + err) * 2^-P.

    Returns (status, rank, support) with status in
    {alive, dead, terminated, indeterminate}.
    """
    R, err = R0, err0
    support = []
    for n in range(1, depth + 1):
        zn = Z[n]
        if R >= zn + 1:  # r >= R 2^-P >= (Z[n]+1) 2^-P > z_n
            R = R - zn - 1  # r - z_n in [R - Z[n] - 1, R + err - Z[n]] 2^-P
            err += 1
            support.append(n)
            if R + err < 1:  # r < 2^-P : the representation has closed
                return ("terminated", n, support)
            continue
        if R + err < zn:  # r <= (R+err) 2^-P < Z[n] 2^-P <= z_n
            hi_T = TT[n] + (P - n) + 2
            if R > hi_T:  # r > T_n and r < z_n : the fatal gap
                return ("dead", n, support)
            if R + err <= TT[n]:  # r <= T_n : survivable skip
                continue
            # undecidable DEATH test: r sits inside the enclosure of T_n.
            # This is the interesting failure -- never pool it with a take.
            return ("indeterminate_death", n, support)
        return ("indeterminate_take", n, support)
    return ("alive", depth, support)


# ---------------------------------------------------------------- cohorts


def sample_start(kind: str, P: int, TT, rng: random.Random):
    """Return (R0, err0, label) for one target of the given cohort."""
    ceiling = TT[0]  # 2^P * E, rounded down
    if kind == "real":
        return rng.randrange(1, ceiling), 0, None
    m = int(kind.split("_")[1])  # cohort "q_<m>" means q ~ 2^m
    q = rng.randrange(1 << (m - 1), 1 << m)
    hi = (q * ceiling) >> P
    if hi < 1:
        hi = 1
    p = rng.randrange(1, hi + 1)
    return (p << P) // q, 1, q


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--targets", type=int, default=60000)
    ap.add_argument("--depth", type=int, default=70)
    ap.add_argument("--seed", type=int, default=20260822)
    ap.add_argument("--qbits", default="6,10,14,18,24,40,160")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    depth = args.depth
    P = 3 * depth + 160
    Z, TT = build_tables(P)
    rng = random.Random(args.seed)

    cohorts = ("real",) + tuple(
        f"q_{int(m)}" for m in args.qbits.split(",") if m.strip()
    )
    stats = {
        c: {
            "deaths": [0] * (depth + 2),
            "at_risk": [0] * (depth + 2),
            "alive": 0,
            "dead": 0,
            "terminated": 0,
            "indeterminate_take": 0,
            "indeterminate_death": 0,
            "support_frac": [],
        }
        for c in cohorts
    }

    for kind in cohorts:
        st = stats[kind]
        for _ in range(args.targets):
            R0, err0, _q = sample_start(kind, P, TT, rng)
            status, rank, support = run_target(R0, err0, depth, P, Z, TT)
            # every target was at risk at ranks 1..rank
            for n in range(1, rank + 1):
                st["at_risk"][n] += 1
            if status == "dead":
                st["deaths"][rank] += 1
                st["dead"] += 1
            elif status == "alive":
                st["alive"] += 1
                st["support_frac"].append(len(support) / depth)
            elif status == "terminated":
                st["terminated"] += 1
            else:
                st[status] += 1

    # ---- hazard profile, and the null it is being tested against
    report = {"targets_per_cohort": args.targets, "depth": depth, "bits": P,
              "seed": args.seed, "cohorts": {}}
    # The decisive comparison is each q-cohort against the "real" null at the
    # SAME rank.  log2(q) is the lattice scale of the target; the question is
    # whether the excess sits in a window near that scale (transient -> H1) or
    # persists for all deeper ranks (heavy tail -> H2).
    for kind in cohorts:
        st = stats[kind]
        rows = []
        for n in range(1, depth + 1):
            ar, d = st["at_risk"][n], st["deaths"][n]
            if ar == 0:
                continue
            rows.append({
                "rank": n,
                "at_risk": ar,
                "deaths": d,
                "hazard": d / ar,
                "null_hazard": (1.0 / 3.0) * 2.0 ** (-n),
                "null_expected": ar * (1.0 / 3.0) * 2.0 ** (-n),
            })
        sf = st["support_frac"]
        report["cohorts"][kind] = {
            "alive": st["alive"],
            "dead": st["dead"],
            "terminated": st["terminated"],
            "indeterminate_take": st["indeterminate_take"],
            "indeterminate_death": st["indeterminate_death"],
            "survival_fraction": st["alive"] / max(1, args.targets - st["terminated"]),
            "mean_support_density": (sum(sf) / len(sf)) if sf else None,
            "deepest_death": max((r["rank"] for r in rows if r["deaths"]), default=None),
            "deaths_beyond_null_silence": sum(
                r["deaths"] for r in rows if r["null_expected"] < 1.0
            ),
            "log2q": (None if kind == "real" else int(kind.split("_")[1])),
            "deaths_at_or_past": {
                str(k): sum(r["deaths"] for r in rows if r["rank"] >= k)
                for k in (6, 8, 10, 12, 15, 20, 25, 30)
            },
            "null_silence_rank": next(
                (r["rank"] for r in rows if r["null_expected"] < 1.0), None
            ),
            "hazard_rows": rows,
        }

    out = args.out or str(
        REPO / "state/formal_math/erdos257_period_noncollapse/late_hazard_profile_receipt.json"
    )
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    blob = json.dumps(report, indent=2, sort_keys=True)
    Path(out).write_text(blob)
    digest = hashlib.sha256(blob.encode()).hexdigest()

    print(f"P={P} bits  depth={depth}  targets/cohort={args.targets}")
    for kind in cohorts:
        c = report["cohorts"][kind]
        print(
            f"{kind:>8}: survive={c['survival_fraction']:.4f} "
            f"dead={c['dead']} term={c['terminated']} "
            f"indet(take/death)={c['indeterminate_take']}/{c['indeterminate_death']} "
            f"deepest_death={c['deepest_death']} "
            f"null_silent_from={c['null_silence_rank']} "
            f"d>=8={c['deaths_at_or_past']['8']} d>=12={c['deaths_at_or_past']['12']} "
            f"d>=20={c['deaths_at_or_past']['20']} d>=30={c['deaths_at_or_past']['30']}"
        )
    print(f"wrote {out} sha256={digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
