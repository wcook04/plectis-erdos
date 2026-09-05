#!/usr/bin/env python3
"""Replay for CentroidVarianceChordChart.md.

Exact components (integer / Fraction arithmetic, no floating point):
  * section 4 refutation of  D <= Var^{n(n-1)/2}  and  mu <= Var^{n/2}
    for 6 <= n <= 40, via the integer inequality
        n^{n(n-3)/2} > (n-1)^{(n-1)(n-2)/2},
    together with the exact rational Var, D and mu^{n-1} for f_n = z^n - z;
  * the same quantities at 3 <= n <= 5, where the inequality is the other way;
  * the Corollary 3 sharp configuration z ((z)^{n-1} - rho^{n-1}) with
    rho^2 = n/(2n-1): centroid 0, Var = (n-1)/(2n-1), 1 - Var = rho^2 = r_(2)^2,
    every root of modulus rho < 1;
  * the even-degree diameter chord of z^n - r^n.

Sampled components (floating point, falsification evidence only):
  * Proposition 1 envelope |f(z)|^{2/n} <= |z-c|^2 + Var;
  * Theorem 2: (2.1) implies the segment stays in {|f| < 1};
  * Theorem 4: max Phi_ij < 1 implies the segment stays in {|f| < 1},
    and (2.1) implies max Phi_ij < 1 (the hierarchy);
  * Corollary 3: Var < (n-1)/(2n-1) implies r_(2)^2 + Var < 1.

Universal authority is the analytic proof in CentroidVarianceChordChart.md;
the sampled parts of this script are falsification evidence only.

Run from the repository root:
  ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_centroid_variance_chord_chart.py
"""
from __future__ import annotations

import cmath
import json
import math
import random
from fractions import Fraction


# --------------------------------------------------------------- exact part


def section4_certificate(nmax: int = 40):
    """f_n(z) = z^n - z.  Exact Var, D, mu^{n-1} and the integer ratio."""
    rows = []
    for n in range(3, nmax + 1):
        A = n * (n - 3) // 2                 # exponent of n
        B = (n - 1) * (n - 2) // 2           # exponent of n-1
        lhs = n ** A
        rhs = (n - 1) ** B
        var = Fraction(n - 1, n)
        disc_over_nn = Fraction((n - 1) ** (n - 1), n ** n)   # = mu^{n-1}
        # D / Var^{n(n-1)/2} recomputed independently from Var and D
        p = n * (n - 1) // 2
        ratio = disc_over_nn / (var ** p)
        assert ratio == Fraction(lhs, rhs), (n, ratio, Fraction(lhs, rhs))
        rows.append(
            dict(
                n=n,
                Var=str(var),
                disc_over_n_pow_n=str(disc_over_nn),
                mu_pow_n_minus_1=str(disc_over_nn),
                ratio_num_exponent=[n, A],
                ratio_den_exponent=[n - 1, B],
                ratio_gt_one=bool(lhs > rhs),
                ratio_float=float(ratio),
                mu_over_var_pow_half_n_float=float(ratio) ** (1.0 / (n - 1)),
            )
        )
    fails_from_6 = [r["n"] for r in rows if r["n"] >= 6 and not r["ratio_gt_one"]]
    holds_below_6 = [r["n"] for r in rows if r["n"] < 6 and r["ratio_gt_one"]]
    return dict(
        rows=rows,
        refutation_holds_for_all_n_ge_6=(fails_from_6 == []),
        no_refutation_below_6=(holds_below_6 == []),
        n6_certificate={"6^9": 6 ** 9, "5^10": 5 ** 10,
                        "strict": 6 ** 9 > 5 ** 10,
                        "ratio": str(Fraction(6 ** 9, 5 ** 10))},
        limit_of_mu_over_var_pow_half_n=math.sqrt(math.e),
    )


def corollary3_sharp_configuration(nmax: int = 30):
    """One root at the centroid, n-1 on a regular (n-1)-gon of radius rho,
    rho^2 = n/(2n-1).  Exact rational check of Var, 1 - Var and r_(2)."""
    rows = []
    for n in range(3, nmax + 1):
        rho2 = Fraction(n, 2 * n - 1)
        var = Fraction(n - 1, n) * rho2          # (n-1) rho^2 / n
        assert var == Fraction(n - 1, 2 * n - 1)
        rows.append(
            dict(
                n=n,
                rho_squared=str(rho2),
                Var=str(var),
                var_threshold=str(Fraction(n - 1, 2 * n - 1)),
                var_equals_threshold=(var == Fraction(n - 1, 2 * n - 1)),
                one_minus_var=str(1 - var),
                r2_squared=str(rho2),
                condition_2_2_is_equality=(1 - var == rho2),
                all_roots_inside_open_disc=(rho2 < 1),
            )
        )
    return dict(
        rows=rows,
        every_row_is_exact_boundary=all(
            r["var_equals_threshold"] and r["condition_2_2_is_equality"]
            and r["all_roots_inside_open_disc"] for r in rows),
    )


def cubic_chord_lemma():
    """Lemma 6: on the chord of z^3 - r^3 the scaled modulus squared is
    P(m) = m^3 + (3/4)m^2 - (45/16)m + 81/64 with m = 3(t-1/2)^2 in [0, 3/4];
    P is decreasing there, P(0) = 81/64 and P(3/4) = 0.  Exact rationals."""
    def P(m):
        return m ** 3 + Fraction(3, 4) * m ** 2 - Fraction(45, 16) * m + Fraction(81, 64)

    grid = [Fraction(3 * k, 4 * 200) for k in range(201)]
    vals = [P(m) for m in grid]
    decreasing = all(vals[k] > vals[k + 1] for k in range(len(vals) - 1))
    # derivative 3m^2 + (3/2)m - 45/16 has its positive root at m = 3/4
    dP34 = 3 * Fraction(3, 4) ** 2 + Fraction(3, 2) * Fraction(3, 4) - Fraction(45, 16)
    return dict(
        P_at_0=str(P(Fraction(0))),
        P_at_three_quarters=str(P(Fraction(3, 4))),
        endpoints_are_roots=(P(Fraction(3, 4)) == 0),
        max_is_81_over_64=(P(Fraction(0)) == Fraction(81, 64)),
        derivative_vanishes_at_three_quarters=(dP34 == 0),
        decreasing_on_grid=decreasing,
        critical_radius_cubed=str(Fraction(8, 9)),
        critical_variance_float=(8 / 9) ** (2 / 3),
    )


def even_degree_diameter_chord(nmax: int = 20):
    """For even n and 0 < r < 1 the chord [-r, r] of z^n - r^n satisfies
    |f| = r^n - z^n in [0, r^n] subset [0, 1).  Exact rational spot checks."""
    checks = []
    ok = True
    for n in range(4, nmax + 1, 2):
        for r in (Fraction(9, 10), Fraction(99, 100), Fraction(999, 1000)):
            worst = Fraction(0)
            for k in range(0, 41):
                z = -r + 2 * r * Fraction(k, 40)
                val = r ** n - z ** n          # equals |f(z)| on the chord
                assert val >= 0
                worst = max(worst, val)
            ok = ok and worst < 1 and worst == r ** n
            checks.append(dict(n=n, r=str(r), max_abs_f=str(worst),
                               below_one=bool(worst < 1)))
    return dict(checks=checks, all_below_one=ok)


# ------------------------------------------------------------- sampled part


def poly_abs(z: complex, a) -> float:
    v = 1.0
    for x in a:
        v *= abs(z - x)
    return v


def phi_max(i: int, j: int, a, m: int = 1200) -> float:
    di = [abs(a[i] - x) for x in a]
    dj = [abs(a[j] - x) for x in a]
    best = 0.0
    for s in range(m + 1):
        t = s / m
        p = 1.0
        for u, v in zip(di, dj):
            p *= t * u + (1 - t) * v
        best = max(best, p)
    return best


def seg_max(p: complex, q: complex, a, m: int = 1200) -> float:
    best = 0.0
    for s in range(m + 1):
        t = s / m
        best = max(best, poly_abs(p + t * (q - p), a))
    return best


def sample(rng: random.Random, trials: int = 900):
    env_fail = 0
    thm2_fail = 0
    thm4_fail = 0
    hierarchy_fail = 0
    cor3_fail = 0
    cor3_fires = 0
    thm2_fires = 0
    thm4_fires = 0
    total = 0
    for _ in range(trials):
        n = rng.randint(2, 9)
        a = [math.sqrt(rng.random()) * 0.999 * cmath.exp(2j * math.pi * rng.random())
             for _ in range(n)]
        c = sum(a) / n
        var = sum(abs(x - c) ** 2 for x in a) / n
        total += 1

        for _ in range(4):
            z = complex(rng.uniform(-2, 2), rng.uniform(-2, 2))
            if poly_abs(z, a) ** (2.0 / n) > abs(z - c) ** 2 + var + 1e-12:
                env_fail += 1

        order = sorted(range(n), key=lambda k: abs(a[k] - c))
        i, j = order[0], order[1]
        di, dj = abs(a[i] - c), abs(a[j] - c)
        if max(di, dj) ** 2 + var < 1.0:
            thm2_fires += 1
            if seg_max(a[i], a[j], a) >= 1.0:
                thm2_fail += 1
            if phi_max(i, j, a) >= 1.0:
                hierarchy_fail += 1
        if var < (n - 1) / (2 * n - 1):
            cor3_fires += 1
            if abs(a[order[1]] - c) ** 2 + var >= 1.0:
                cor3_fail += 1
        for p in range(n):
            for q in range(p + 1, n):
                if phi_max(p, q, a) < 1.0:
                    thm4_fires += 1
                    if seg_max(a[p], a[q], a) >= 1.0:
                        thm4_fail += 1
    return dict(
        configurations=total,
        envelope_failures=env_fail,
        theorem2_fires=thm2_fires, theorem2_failures=thm2_fail,
        theorem4_fires=thm4_fires, theorem4_failures=thm4_fail,
        hierarchy_failures=hierarchy_fail,
        corollary3_fires=cor3_fires, corollary3_failures=cor3_fail,
    )


def main() -> None:
    rng = random.Random(20260905)
    report = {
        "status": "pass",
        "source_note": "CentroidVarianceChordChart.md",
        "section4_refutation": section4_certificate(40),
        "corollary3_sharp_configuration": corollary3_sharp_configuration(30),
        "cubic_chord_lemma": cubic_chord_lemma(),
        "even_degree_diameter_chord": even_degree_diameter_chord(20),
        "sampled": sample(rng, 900),
        "evidence_class": "exact_integer_and_rational_certificates_plus_floating_point_falsification",
        "universal_authority": "CentroidVarianceChordChart.md",
        "claim_boundary": (
            "proves a sufficient chord condition and the regime Var < (n-1)/(2n-1); "
            "refutes D <= Var^{n(n-1)/2} and mu <= Var^{n/2} for n >= 6; "
            "unrestricted Erdos 1041 stays open and no counterexample to it is claimed"
        ),
    }
    s4 = report["section4_refutation"]
    assert s4["refutation_holds_for_all_n_ge_6"]
    assert s4["no_refutation_below_6"]
    assert s4["n6_certificate"]["strict"]
    assert report["corollary3_sharp_configuration"]["every_row_is_exact_boundary"]
    assert report["even_degree_diameter_chord"]["all_below_one"]
    cl = report["cubic_chord_lemma"]
    assert cl["endpoints_are_roots"] and cl["max_is_81_over_64"]
    assert cl["derivative_vanishes_at_three_quarters"] and cl["decreasing_on_grid"]
    sm = report["sampled"]
    for key in ("envelope_failures", "theorem2_failures", "theorem4_failures",
                "hierarchy_failures", "corollary3_failures"):
        assert sm[key] == 0, (key, sm[key])
    assert sm["theorem2_fires"] > 0 and sm["theorem4_fires"] > 0
    print(json.dumps(report))


if __name__ == "__main__":
    main()
