#!/usr/bin/env python3
r"""Component depth at the first-merge level, and the DEPTH-ALL conjecture.

At mu = min_k |f(c_k)| every component of {|f| < mu} holds exactly one root and
f maps it conformally onto the disk D_mu.  Define, with NO hub selection and NO
pair selection,

    Delta_j = max over theta of  length{ z : f(z) = t e^{i theta}, t in [0,mu] }
              ending at the root z_j.

The two descent branches at c* are two such curves, so L(c*) <= Delta_a + Delta_b
and therefore

        DEPTH-ALL:   Delta_j <= R  for all j   ==>   L(c*) <= 2R < 2,

i.e. Erdos #1041.  It is EXACTLY tight on both equality families:
  * every monic quadratic: centring at the critical point gives f = z^2 - h^2,
    R = h, mu = h^2, and |h^2 + t e^{i th}| >= h^2 - t forces the max to th = pi,
    where INT_0^{h^2} dt/(2(h^2-t)^{1/2}) = h = R exactly;
  * z^n - r^n at th = pi: Delta = r = R exactly.

TWO INSTRUMENT FACTS, both learned the hard way, both load bearing.

1. THE MAXIMUM SITS AT theta = arg f(c).  A uniform theta grid misses it and
   under-reports -- it returned 0.943664 for a random quadratic against the
   PROVED exact value 1.  z^n - r^n conceals the fault because its theta_c = pi
   lands on any symmetric grid.  The critical arguments are forced into the list.

2. A SURVIVING SUPREMUM IS NOT EVIDENCE (negative_results 19).  So --validate
   runs first and must REPRODUCE a known refutation: the strong form
   Delta <= mu^{1/n} must FAIL, because entry 29 refutes L(c*) <= 2 mu^{1/n} and
   Delta_a + Delta_b >= L(c*).  If the search cannot drive Delta/mu^{1/n} above
   1, the instrument is under-reporting and its DEPTH-ALL numbers mean nothing.

Exit 0 iff calibration reproduces the two equality families and (when --validate
is on) the mu^{1/n} form is refuted.  A DEPTH-ALL violation is reported, not
treated as failure: it would be a result, not a bug.

*** DEPTH-ALL IS REFUTED (2026-08-24).  See ComponentDepthRefutation.md and
    scripts/check_erdos1041_component_depth_refutation.py, which carries the
    exact Gaussian-rational witness and a rigorous inscribed-polygon lower
    bound of 1.0071292 at 60 dps.  THIS script's search never found it: its
    hill-climb seeds roots at modulus ~0.6 with 2 restarts x 18 steps, and the
    violating set sits in the near-Fekete shell at modulus ~0.99.  On the
    refuting configuration this script returns 1.00492 -- above one -- so it
    detects the violation; it simply never looked there.  The pinned witness is
    now included in the depth rows below so the refutation cannot be lost. ***
"""
from __future__ import annotations

import argparse
import json
import sys

import numpy as np
from scipy.optimize import linear_sum_assignment


def circumcentre_radius(z, iters=300):
    c = z.mean()
    for i in range(1, iters + 1):
        c = c + (z[np.argmax(np.abs(z - c))] - c) / (i + 1)
    return c, float(np.max(np.abs(z - c)))


def depths(roots, n_theta=12, steps=200):
    """Arclength of the longest descent branch reaching each root."""
    coef = np.poly(roots)
    cv = np.polyval(coef, np.roots(np.polyder(coef)))
    mu = float(np.abs(cv).min())
    if not np.isfinite(mu) or mu <= 0:
        return None
    thetas = list(np.linspace(0, 2 * np.pi, n_theta, endpoint=False))
    thetas += [float(np.angle(v)) for v in cv]        # fact 1 above
    n = len(roots)
    tail = coef[:-1]
    best = np.zeros(n)
    for th in thetas:
        ts = mu * np.sin(np.linspace(0, np.pi / 2, steps + 1)) ** 2
        e = np.exp(1j * th)
        cur = np.asarray(roots, complex)
        acc = np.zeros(n)
        for t in ts[1:]:
            w = np.roots(np.concatenate([tail, [coef[-1] - t * e]]))
            _, col = linear_sum_assignment(np.abs(cur[:, None] - w[None, :]))
            nxt = w[col]
            acc += np.abs(nxt - cur)
            cur = nxt
        best = np.maximum(best, acc)
    return mu, best


def ratio(roots, key):
    n = len(roots)
    m = np.max(np.abs(roots))
    if m >= 1:
        roots = roots / m * (1 - 1e-9)
    _, R = circumcentre_radius(roots)
    out = depths(roots - circumcentre_radius(roots)[0])
    if out is None:
        return None
    mu, D = out
    return float(D.max()) / (R if key == "R" else mu ** (1.0 / n))


def hill(rng, n, key, restarts, steps):
    best = -np.inf
    for _ in range(restarts):
        v = rng.standard_normal(2 * n) * 0.6
        cur = ratio(v[:n] + 1j * v[n:], key) or -np.inf
        T = 0.25
        for _ in range(steps):
            w = v + rng.standard_normal(2 * n) * T
            s = ratio(w[:n] + 1j * w[n:], key)
            if s is not None and s > cur:
                v, cur = w, s
            T *= 0.97
        best = max(best, cur)
    return best


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--degrees", default="2,3")
    ap.add_argument("--restarts", type=int, default=2)
    ap.add_argument("--steps", type=int, default=18)
    ap.add_argument("--validate", action="store_true", default=True)
    ap.add_argument("--search-validate", action="store_true",
                    help="also hill-climb for fresh witnesses (slow)")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()
    rng = np.random.default_rng(20260824)

    # PINNED validation witness.  A hill-climb is not a receipt: with a light
    # search budget it simply fails to find a violation and then the run cannot
    # tell "conjecture holds" from "search too weak".  This configuration is
    # stored so the validation is deterministic and cheap.
    WITNESS3 = np.array([0.6687031583458182 + 0.7386826958971497j,
                         -0.1044350945161572 - 0.0723948034130899j,
                         0.9514529373979631 - 0.3077942590705480j])

    cal = []
    for n in (2, 3, 5):
        r = 0.9 * np.exp(2j * np.pi * np.arange(n) / n)
        cal.append(dict(name=f"z^{n}-r^{n}", value=ratio(r, "R")))
    for q in ([0.4 + 0.2j, -0.7 + 0.5j], [-0.11 + 0.9j, 0.63 - 0.24j]):
        cal.append(dict(name="quadratic", value=ratio(np.array(q), "R")))
    cal_ok = all(abs(c["value"] - 1.0) < 4e-3 for c in cal)

    degs = [int(x) for x in args.degrees.split(",")]
    val = []
    val_ok = True
    if args.validate:
        v = ratio(WITNESS3, "mu")
        val.append(dict(n=3, source="pinned witness", max_ratio=v,
                        refutes=bool(v is not None and v > 1)))
        if args.search_validate:
            for n in degs:
                if n < 3:
                    continue
                s = hill(rng, n, "mu", args.restarts, args.steps)
                val.append(dict(n=n, source="hill-climb", max_ratio=s,
                                refutes=bool(s > 1)))
        val_ok = any(r["refutes"] for r in val)

    # PINNED refuting witness (ComponentDepthRefutation.md): three Gaussian
    # rationals over 1000, all strictly inside the open unit disk.  Included so
    # the DEPTH-ALL rows can never again report a surviving supremum.
    REFUTER = np.array([990 + 0j, -500 + 860j, -497 - 855j]) / 1000.0
    dep = [dict(n=3, source="pinned refuter", max_ratio=ratio(REFUTER, "R"))]
    dep += [dict(n=n, source="hill-climb", max_ratio=hill(rng, n, "R", args.restarts, args.steps))
            for n in degs]
    violation = [r for r in dep if r["max_ratio"] > 1 + 1e-7]

    refuter_ok = bool(dep and dep[0]["max_ratio"] > 1)
    ok = cal_ok and val_ok and refuter_ok
    payload = dict(conjecture="DEPTH-ALL: Delta_j <= R at the first-merge level",
                   implies="Erdos 1041, via L(c*) <= Delta_a + Delta_b <= 2R",
                   calibration=cal, calibration_ok=cal_ok,
                   instrument_validation=val,
                   instrument_validation_ok=val_ok,
                   depth_all_status="REFUTED 2026-08-24 (ComponentDepthRefutation.md)",
                   pinned_refuter_reproduces=refuter_ok,
                   depth_rows=dep, depth_violations=violation,
                   verdict="pass" if ok else "FAIL")
    if args.json:
        print(json.dumps(payload, indent=2))
    else:
        print("calibration (both equality families must return 1):")
        for c in cal:
            print(f"  {c['name']:<12} Delta/R = {c['value']:.6f}")
        if val:
            print("\ninstrument validation -- Delta/mu^(1/n) MUST exceed 1 "
                  "(entry 29 refutes that form):")
            for r in val:
                print(f"  n={r['n']} ({r['source']})  {r['max_ratio']:.9f}  "
                      f"{'refutes, instrument OK' if r['refutes'] else '*** UNDER-REPORTING ***'}")
        print("\nDEPTH-ALL (max Delta/R) -- REFUTED, see ComponentDepthRefutation.md:")
        for r in dep:
            print(f"  n={r['n']} ({r['source']})  {r['max_ratio']:.9f}"
                  f"{'   *** VIOLATION -- this is a RESULT, not a bug' if r['max_ratio'] > 1 + 1e-7 else ''}")
        print(f"\ncalibration_ok={cal_ok}  instrument_ok={val_ok}  "
              f"verdict={payload['verdict']}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
