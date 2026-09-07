#!/usr/bin/env python3
"""Receipt for ClaimLRefutation.md.

CLAIM L (CapacityGeodesicConjecture.md section 8.1): at the tie-free
minimum-critical hub c*, the two merging roots are the two roots nearest c*.

This receipt refutes it with three stored witnesses, at degrees 6, 10 (tie
guard 1.001) and 8 (tie guard 1.05).  For each witness it independently
re-derives:

  - the critical points, mu, and the tie separation |f(c_2)|/|f(c_1)|;
  - the merging set, by upward branch continuation from every root along the
    ray of f(c*), at three shrink levels 1e-10, 1e-13, 1e-15: a merging root's
    endpoint distance to c* must fall at the saddle square-root rate, a
    non-merging root's must stabilise at a macroscopic distance;
  - the distance ranking, the violation (a non-merging root strictly nearer
    than a merging one), and the merging-pair metric floor (d_a+d_b)/(2 rho).

The witnesses were produced by the signed-gap instrument this directory asked
for ("build a proxy with a gradient", CapacityGeodesicConjecture.md 8.1):

    gap = ( min_{k not in S} d_k - max_{k in S} d_k ) / rho ,

minimised by stochastic descent under the tie guard.  The flat violation-ratio
objective used by the earlier sweeps is exactly 1 on the entire good set and
cannot see these configurations; the corpus's own guarded retests (guard 1.05)
reported no violation for that reason.

All numbers are float; margins are 10^2 - 10^3 times the classifier
resolution.  No exact rational witness is claimed.  Erdos #1041, conjecture
(C), and the merging-pair metric floor are all untouched: the floor HOLDS with
room on every witness here.
"""
from __future__ import annotations

import sys

import numpy as np

WITNESSES = [
    {
        "tag": "n6_guard_1.001",
        "guard": 1.001,
        "expect_merging": [0, 5],
        "expect_nearest": [1, 5],
        "roots": [
            -0.418061007027225 + 0.145188938149130j,
            -0.760526041191082 - 0.362574362009888j,
            +0.599253933335387 - 0.495546704186076j,
            +0.440992539575592 + 0.524570170458065j,
            -0.123715490723356 + 0.896283673641519j,
            -0.315096094350564 - 0.603503072810813j,
        ],
    },
    {
        "tag": "n10_guard_1.001",
        "guard": 1.001,
        "expect_merging": [0, 6],
        "expect_nearest": [1, 6],
        "roots": [
            +0.052878685180527 - 0.142894330812531j,
            +0.111516279272361 + 0.358717288963099j,
            -0.365614732054346 - 0.313728405548909j,
            -0.618684870010829 - 0.199301323376298j,
            +0.754326245967916 + 0.495004861236271j,
            +0.182577311732940 - 0.556851089481010j,
            -0.315283899625988 + 0.266132802616856j,
            +0.455859768539069 - 0.848925370094565j,
            +0.726339753707012 - 0.283648402903496j,
            -0.202502685840246 + 0.616265604107458j,
        ],
    },
    {
        "tag": "n8_guard_1.05",
        "guard": 1.05,
        "expect_merging": None,   # derived; the violation is what is asserted
        "expect_nearest": None,
        "roots": [
            +0.539310219510419 + 0.648770173004504j,
            -0.514658316201808 - 0.280715242892567j,
            +0.177921492835576 + 0.120448048404419j,
            +0.059722098546505 + 0.687400899472367j,
            +0.274483477095894 + 0.500640325710409j,
            -0.710530067446438 - 0.549934797153521j,
            -0.771899303672085 - 0.003058987995671j,
            -0.481086796980426 - 0.602137896758784j,
        ],
    },
]

SHRINKS = (1e-10, 1e-13, 1e-15)


def analyse(roots: np.ndarray):
    n = len(roots)
    c = np.poly(roots)
    dc = np.polyder(c)
    cps = np.roots(dc)
    vals = np.polyval(c, cps)
    keep = np.abs(vals) > 1e-14
    cps, vals = cps[keep], vals[keep]
    av = np.abs(vals)
    order = np.argsort(av)
    i0 = int(order[0])
    cstar, vstar, mu = complex(cps[i0]), complex(vals[i0]), float(av[i0])
    critsep = float(av[order[1]] / mu)

    def climb(dl, n_steps=2500):
        ray = vstar / mu
        u = np.linspace(1.0, 0.0, n_steps + 1)
        sv = mu * (1.0 - dl - (1.0 - dl) * u**2)
        z = roots.copy()
        for s in sv[1:]:
            tgt = s * ray
            for _ in range(60):
                d = np.polyval(dc, z)
                bad = np.abs(d) < 1e-300
                corr = np.where(
                    bad, 0.0, (np.polyval(c, z) - tgt) / np.where(bad, 1.0, d)
                )
                z = z - corr
                if np.max(np.abs(corr)) < 1e-15:
                    break
        return np.abs(z - cstar)

    dists = [climb(dl) for dl in SHRINKS]
    S = [j for j in range(n) if dists[-1][j] < 1e-6]
    stable_nonmerging = all(
        dists[-1][j] > 1e-2 and abs(dists[0][j] - dists[-1][j]) < 1e-6
        for j in range(n)
        if j not in S
    )
    d = np.abs(roots - cstar)
    rho = mu ** (1.0 / n)
    nearest = sorted(np.argsort(d)[:2].tolist())
    inside = max(d[j] for j in S)
    outside = min(d[j] for j in range(n) if j not in S)
    return {
        "mu": mu,
        "critsep": critsep,
        "S": sorted(S),
        "nearest": nearest,
        "d": d,
        "gap": (outside - inside) / rho,
        "floor": sum(sorted(d[j] for j in S)[:2]) / (2 * rho),
        "converged": stable_nonmerging and len(S) == 2,
    }


def main() -> int:
    print("check_erdos1041_claim_l_refutation")
    gates = {}
    floors = []
    for w in WITNESSES:
        roots = np.asarray(w["roots"], dtype=complex)
        r = analyse(roots)
        tag = w["tag"]
        print(f"  {tag}")
        print(f"    mu {r['mu']:.12f}  critsep {r['critsep']:.6f}  "
              f"(guard {w['guard']})")
        print(f"    merging {r['S']}  nearest {r['nearest']}  "
              f"gap {r['gap']:+.6f}  floor {r['floor']:.6f}")
        ok = (
            r["critsep"] >= w["guard"] - 1e-9
            and r["converged"]
            and r["S"] != r["nearest"]
            and r["gap"] < -0.02
        )
        if w["expect_merging"] is not None:
            ok &= r["S"] == w["expect_merging"]
            ok &= r["nearest"] == w["expect_nearest"]
        gates[tag] = ok
        floors.append(r["floor"])
    gates["metric_floor_intact_on_all_witnesses"] = all(f < 1.0 for f in floors)
    print()
    for key, val in gates.items():
        print(f"  {key}={val}")
    ok = all(gates.values())
    print(f"\nverdict {'pass' if ok else 'FAIL'}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
