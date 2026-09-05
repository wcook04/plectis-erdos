#!/usr/bin/env python3
"""Replay for TranslatedNonAdjacentTrinomial.md.

Exact rational certificates for the coprime quintic of section 8 (factorisation,
Rouche margin 863/76800, sigma^2 = 121/125, and the bounds (8.4) and (8.5) by
rational squaring), plus finite floating-point falsification of the moment
localisation, the spoke envelope, the quantitative second-nearest-root bound,
the balanced-weight dual formula, and the non-firing of the coefficient
certificate on the stored centroid-hub counterexample.

Universal authority is the analytic proof in TranslatedNonAdjacentTrinomial.md;
this script is falsification evidence only.

Run from the repository root:
  ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_translated_trinomial.py
"""
from __future__ import annotations

import cmath
import json
import math
import random
from fractions import Fraction


# ------------------------------------------------------------------ utilities


def eval_desc(desc, z: complex) -> complex:
    acc = 0j
    for c in desc:
        acc = acc * z + c
    return acc


def poly_roots(desc):
    """Durand-Kerner on a monic descending coefficient list."""
    n = len(desc) - 1
    lead = desc[0]
    c = [v / lead for v in desc]
    z = [(0.4 + 0.9j) ** i * (1 + 0.13 * i) for i in range(n)]
    for _ in range(800):
        worst = 0.0
        for i in range(n):
            p = 0j
            for a in c:
                p = p * z[i] + a
            d = 1 + 0j
            for j in range(n):
                if j != i:
                    d *= (z[i] - z[j])
            if d == 0:
                continue
            dz = p / d
            z[i] -= dz
            worst = max(worst, abs(dz))
        if worst < 1e-14:
            break
    return z


def dkm(k: int, m: int) -> float:
    """max_{[0,1]} |t^k - t^m|, formula (7.7)."""
    lo, hi = min(k, m), max(k, m)
    return (hi - lo) / hi * (lo / hi) ** (lo / (hi - lo))


# ---------------------------------------------------------------- exact part


def exact_coprime_quintic() -> dict:
    """Section 8, entirely in exact rational arithmetic."""
    # g(w) = w^5 - (461/525) w^3 - 64/525 factors as
    # (w - 1)(5 w + 4)(105 w^3 + 21 w^2 - 4 w + 16) / 525.
    def mul(p, q):
        out = [Fraction(0)] * (len(p) + len(q) - 1)
        for i, u in enumerate(p):
            for j, v in enumerate(q):
                out[i + j] += u * v
        return out

    lin1 = [Fraction(-1), Fraction(1)]                 # w - 1
    lin2 = [Fraction(4), Fraction(5)]                  # 5 w + 4
    cub = [Fraction(16), Fraction(-4), Fraction(21), Fraction(105)]
    prod = mul(mul(lin1, lin2), cub)
    prod = [c / 525 for c in prod]
    target = [Fraction(-64, 525), Fraction(0), Fraction(0),
              Fraction(-461, 525), Fraction(0), Fraction(1)]
    assert prod == target, (prod, target)

    # Rouche margin on |w| = 3/4, equation (8.2).
    three_quarters = Fraction(3, 4)
    margin = (Fraction(461, 525) * three_quarters ** 3
              - three_quarters ** 5 - Fraction(64, 525))
    assert margin == Fraction(863, 76800), margin
    assert margin > 0

    # Exactly three roots of g lie in |w| < 3/4; the other two are 1 and -4/5.
    # All five lie in the closed disc of centre 1/10 and radius 9/10.
    assert abs(Fraction(1) - Fraction(1, 10)) == Fraction(9, 10)
    assert abs(Fraction(-4, 5) - Fraction(1, 10)) == Fraction(9, 10)
    assert three_quarters + Fraction(1, 10) < Fraction(9, 10)

    # Translation and scaling, equation (8.3).
    s = Fraction(11, 10)
    h = Fraction(-11, 100)
    # z = s (w - 1/10) and z - h = s w, so F(z) = s^5 g(w).
    assert s * (Fraction(1) - Fraction(1, 10)) - h == s * 1
    R = s * Fraction(9, 10)
    assert R == Fraction(99, 100)
    H = abs(h)
    assert H == Fraction(11, 100)
    sigma_sq = R * R - H * H
    assert sigma_sq == Fraction(121, 125), sigma_sq

    # The largest root displacement from h exceeds one, so no theorem that
    # requires every translated displacement to lie in the unit disc applies.
    biggest = s * Fraction(1)
    assert biggest == Fraction(11, 10)
    assert biggest > 1

    # (8.4): length <= 2 sigma = 22 / (5 sqrt 5) < 2, by rational squaring.
    length_sq = 4 * sigma_sq
    assert length_sq == Fraction(484, 125)
    assert length_sq < 4
    # (8.5): sigma^5 = (121/125)^{5/2} < 1 because 121 < 125.
    assert sigma_sq < 1

    length = 2 * math.sqrt(float(sigma_sq))
    envelope = float(sigma_sq) ** 2.5
    assert abs(length - 1.9677398201) < 1e-9, length
    assert abs(envelope - 0.9219097186) < 1e-9, envelope

    # Exponents 5 and 3 are coprime and m = n - 2, the third-moment branch.
    assert math.gcd(5, 3) == 1
    assert 3 == 5 - 2

    # Float confirmation that h is the centroid and the selection is real.
    desc = [1 + 0j, 0j, -461 / 525 * float(s) ** 2 + 0j, 0j, 0j,
            -64 / 525 * float(s) ** 5 + 0j]
    ws = poly_roots(desc)
    assert abs(sum(ws)) < 1e-9
    zs = [w + float(h) for w in ws]
    assert max(abs(z) for z in zs) <= float(R) + 1e-9
    sigma = math.sqrt(float(sigma_sq))
    close = sorted(abs(w) for w in ws)
    assert close[1] <= sigma + 1e-9, close
    # Spoke envelope (1.2) along both selected arms.
    picked = sorted(ws, key=abs)[:2]
    for w in picked:
        for step in range(0, 61):
            t = step / 60.0
            assert abs(eval_desc(desc, t * w)) <= sigma ** 5 * (1 - t ** 5) + 1e-9

    return {
        "rouche_margin": str(margin),
        "sigma_squared": str(sigma_sq),
        "R": str(R),
        "H": str(H),
        "max_displacement_from_h": str(biggest),
        "length_bound": length,
        "envelope_bound": envelope,
        "second_centroid_distance": close[1],
    }


# --------------------------------------------------- sampled trinomial family


def sample_translated_trinomials(rng: random.Random, trials: int) -> dict:
    localisation_failures = 0
    spoke_failures = 0
    moment_failures = 0
    star_failures = 0
    r2_bound_failures = 0
    constant_failures = 0
    worst_ratio = 0.0
    checked = 0
    for _ in range(trials):
        n = rng.randint(4, 14)
        m = rng.randint(1, n - 2)
        A = complex(rng.uniform(-2, 2), rng.uniform(-2, 2))
        C = complex(rng.uniform(-2, 2), rng.uniform(-2, 2))
        desc = [0j] * (n + 1)
        desc[0] = 1 + 0j
        desc[n - m] = A
        desc[n] = C
        ws = poly_roots(desc)
        if max(abs(eval_desc(desc, w)) for w in ws) > 1e-7:
            continue
        checked += 1

        # h is the centroid because the w^{n-1} coefficient vanishes.
        if abs(sum(ws)) > 1e-7:
            moment_failures += 1
        S2 = sum(w ** 2 for w in ws)
        S3 = sum(w ** 3 for w in ws)
        if m <= n - 3:
            if abs(S2) > 1e-6:
                moment_failures += 1
        else:
            if abs(S3) > 1e-6:
                moment_failures += 1

        # Arbitrary enclosing disc centred at h + xi.
        xi = complex(rng.uniform(-1, 1), rng.uniform(-1, 1))
        R = max(abs(w - xi) for w in ws)
        H = abs(xi)
        sigma_sq = R * R - H * H
        if sigma_sq < 0:
            sigma_sq = 0.0
        sigma = math.sqrt(sigma_sq)
        radii = sorted(abs(w) for w in ws)

        # Theorem 2: two listed roots inside the centroid disc of radius sigma.
        if radii[1] > sigma * (1 + 1e-9) + 1e-12:
            localisation_failures += 1
        if sigma > 0:
            worst_ratio = max(worst_ratio, radii[1] / sigma)

        # (3.4): the constant term obeys the same scale bound.
        if abs(C) > sigma ** n + 1e-9:
            constant_failures += 1

        # (3.6): both selected spokes stay under sigma^n (1 - t^n).
        for w in sorted(ws, key=abs)[:2]:
            for step in range(0, 31):
                t = step / 30.0
                if abs(eval_desc(desc, t * w)) > sigma ** n * (1 - t ** n) + 1e-7:
                    spoke_failures += 1
                    break

        # Theorem 3: the star count when the second moment vanishes.
        if m <= n - 3 and sigma > 0:
            count = sum(1 for w in ws if abs(w) <= sigma * (1 + 1e-12))
            if count <= n * (R + H) / (4 * R + 2 * H) - 1e-9:
                star_failures += 1
            if count < n // 4 + 1:
                star_failures += 1

        # Theorem 4: the quantitative second-nearest-root bound.
        if H > 1e-12:
            theta = cmath.phase(-xi)
            M2 = (cmath.exp(-2j * theta) * S2).real
            M3 = (cmath.exp(-3j * theta) * S3).real
            D0 = 2 * H * (R - H) / (n - 1)
            D2 = max(0.0, 3 * (R - H) ** 2 - (n - 1) * sigma_sq - M2) / (n - 1)
            D3 = math.sqrt(2 * H * max(0.0, M3) / (3 * (n - 1)))
            bound = sigma_sq + min(D0, D2, D3)
            if radii[1] ** 2 > bound + 1e-7:
                r2_bound_failures += 1
            # (5.9): the sharp unconditional comparison.
            if radii[1] > n / math.sqrt(n * n - 1) * R + 1e-7:
                r2_bound_failures += 1
    return {
        "polynomials": checked,
        "localisation_failures": localisation_failures,
        "spoke_failures": spoke_failures,
        "moment_identity_failures": moment_failures,
        "star_count_failures": star_failures,
        "r2_bound_failures": r2_bound_failures,
        "constant_bound_failures": constant_failures,
        "max_r2_over_sigma": worst_ratio,
    }


def sample_sharp_configuration(rng: random.Random) -> dict:
    """(5.10): the odd-n configuration attaining n R / sqrt(n^2 - 1)."""
    checked = 0
    worst = 0.0
    for n in range(3, 22, 2):
        d = n * n - 1
        base = complex(-1.0 / d, math.sqrt(1 - 1.0 / (d * d)))
        pts = [complex(1.0, 0.0)]
        pts += [base] * ((n - 1) // 2)
        pts += [base.conjugate()] * ((n - 1) // 2)
        assert len(pts) == n
        assert max(abs(abs(p) - 1) for p in pts) < 1e-12
        h = sum(pts) / n
        assert abs(h - 1.0 / (n + 1)) < 1e-12, (n, h)
        radii = sorted(abs(p - h) for p in pts)
        target = n / math.sqrt(n * n - 1)
        assert abs(radii[1] - target) < 1e-12, (n, radii[1], target)
        worst = max(worst, radii[1])
        checked += 1
    return {"odd_degrees": checked, "largest_attained_r2": worst}


def sample_balanced_dual(rng: random.Random, trials: int) -> dict:
    """Theorem 5: rho_*^2 as a primal minimum and as a balanced-weight maximum."""
    gaps = 0
    worst_gap = 0.0
    checked = 0
    for _ in range(trials):
        n = rng.randint(4, 7)
        pts = [complex(rng.uniform(-1, 1), rng.uniform(-1, 1)) for _ in range(n)]
        c = sum(pts) / n
        ws = [p - c for p in pts]

        def envelope(p: float, q: float) -> float:
            return max(abs(w) ** 2 - 2 * (p * w.real + q * w.imag) for w in ws)

        # Primal: the minimum of the piecewise-affine envelope is a linear
        # programme in (tau, p, q); enumerate its vertices exactly.
        primal = None
        for i in range(n):
            for j in range(i + 1, n):
                for l in range(j + 1, n):
                    rows = [[1.0, 2 * ws[t].real, 2 * ws[t].imag,
                             abs(ws[t]) ** 2] for t in (i, j, l)]
                    ok = True
                    for col in range(3):
                        piv = max(range(col, 3), key=lambda t: abs(rows[t][col]))
                        if abs(rows[piv][col]) < 1e-12:
                            ok = False
                            break
                        rows[col], rows[piv] = rows[piv], rows[col]
                        for t in range(3):
                            if t != col:
                                fac = rows[t][col] / rows[col][col]
                                for cc in range(col, 4):
                                    rows[t][cc] -= fac * rows[col][cc]
                    if not ok:
                        continue
                    tau, pp, qq = (rows[t][3] / rows[t][t] for t in range(3))
                    if envelope(pp, qq) <= tau + 1e-9:
                        if primal is None or tau < primal:
                            primal = tau
        if primal is None:
            continue

        # Dual: balanced probability vectors supported on at most three points.
        dual = 0.0
        for i in range(n):
            if abs(ws[i]) < 1e-14:
                dual = max(dual, 0.0)
            for j in range(i + 1, n):
                den = abs(ws[i]) + abs(ws[j])
                if den < 1e-14:
                    continue
                p = abs(ws[j]) / den
                if abs(p * ws[i] + (1 - p) * ws[j]) < 1e-9:
                    dual = max(dual, p * abs(ws[i]) ** 2
                               + (1 - p) * abs(ws[j]) ** 2)
                for l in range(j + 1, n):
                    a, b, d = ws[i], ws[j], ws[l]
                    det = ((a.real - d.real) * (b.imag - d.imag)
                           - (b.real - d.real) * (a.imag - d.imag))
                    if abs(det) < 1e-12:
                        continue
                    pa = (-d.real * (b.imag - d.imag)
                          + d.imag * (b.real - d.real)) / det
                    pb = ((a.real - d.real) * -d.imag
                          + d.real * (a.imag - d.imag)) / det
                    pd = 1 - pa - pb
                    if min(pa, pb, pd) < -1e-12:
                        continue
                    dual = max(dual, pa * abs(a) ** 2 + pb * abs(b) ** 2
                               + pd * abs(d) ** 2)
        checked += 1
        # The uniform balanced vector is always admissible, giving (2.1).
        uniform = sum(abs(w) ** 2 for w in ws) / n
        if uniform > dual + 1e-7 or uniform > primal + 1e-7:
            gaps += 1
        gap = abs(primal - dual)
        worst_gap = max(worst_gap, gap)
        if gap > 1e-5:
            gaps += 1
    return {"configurations": checked, "duality_gaps": gaps,
            "worst_primal_dual_gap": worst_gap}


# ------------------------------------- centroid-hub counterexample, section 10


def centroid_hub_certificate_does_not_fire() -> dict:
    """The stored exact quintic must not be promoted by the budget (7.8)."""
    params = [Fraction(0), Fraction(5, 8), Fraction(7, 2),
              Fraction(-11, 3), Fraction(-5, 7)]
    r = Fraction(99999, 100000)
    pts = [(r * (1 - s * s) / (1 + s * s), r * (2 * s) / (1 + s * s))
           for s in params]
    n = 5
    hx = sum(p[0] for p in pts) / n
    hy = sum(p[1] for p in pts) / n
    ws = [(p[0] - hx, p[1] - hy) for p in pts]

    def cmul(a, b):
        return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])

    coeffs = [(Fraction(1), Fraction(0))]
    for w in ws:
        nxt = [[Fraction(0), Fraction(0)] for _ in range(len(coeffs) + 1)]
        for i, c in enumerate(coeffs):
            nxt[i][0] += c[0]
            nxt[i][1] += c[1]
            prod = cmul(c, w)
            nxt[i + 1][0] -= prod[0]
            nxt[i + 1][1] -= prod[1]
        coeffs = [tuple(x) for x in nxt]
    b = {n - i: coeffs[i] for i in range(n + 1)}
    assert b[4] == (Fraction(0), Fraction(0)), b[4]

    H_sq = hx * hx + hy * hy
    H = math.sqrt(float(H_sq))
    R = float(r)
    sigma_sq = float(r * r - H_sq)
    S2 = (Fraction(0), Fraction(0))
    S3 = (Fraction(0), Fraction(0))
    for w in ws:
        w2 = cmul(w, w)
        w3 = cmul(w2, w)
        S2 = (S2[0] + w2[0], S2[1] + w2[1])
        S3 = (S3[0] + w3[0], S3[1] + w3[1])
    hbar = (hx, -hy)
    hbar2 = cmul(hbar, hbar)
    hbar3 = cmul(hbar2, hbar)
    M2 = float(cmul(hbar2, S2)[0] / H_sq)
    H_times_M3 = float(cmul(hbar3, S3)[0] / H_sq)

    D0 = 2 * H * (R - H) / (n - 1)
    D2 = max(0.0, 3 * (R - H) ** 2 - (n - 1) * sigma_sq - M2) / (n - 1)
    D3 = math.sqrt(max(0.0, 2 * H_times_M3) / (3 * (n - 1)))
    U = math.sqrt(sigma_sq + min(D0, D2, D3))

    radii = sorted(math.hypot(float(w[0]), float(w[1])) for w in ws)
    assert radii[1] <= U + 1e-12, (radii[1], U)

    mag = {k: math.hypot(float(b[k][0]), float(b[k][1])) for k in (0, 1, 2, 3)}
    budgets = {}
    for pivot in (1, 2, 3):
        total = U ** n + sum(mag[k] * U ** k * dkm(k, pivot)
                             for k in (1, 2, 3) if k != pivot)
        budgets[pivot] = total
        assert total > 1, (pivot, total)
    assert abs(budgets[1] - 1.16927981) < 1e-7
    assert abs(budgets[2] - 1.05490983) < 1e-7
    assert abs(budgets[3] - 1.06166219) < 1e-7
    return {
        "U": U,
        "second_centroid_distance": radii[1],
        "budgets": budgets,
        "certificate_fires": False,
        "evidence_class": "float_diagnostic_over_exact_rational_configuration",
    }


def main() -> None:
    rng = random.Random(20260905)
    report = {
        "status": "pass",
        "source_note": "TranslatedNonAdjacentTrinomial.md",
        "return_batch_id": "erdos1041_20260905_eight_return_stream_01",
        "exact_coprime_quintic": exact_coprime_quintic(),
        "sampled_translated_trinomials": sample_translated_trinomials(rng, 900),
        "sharp_configuration": sample_sharp_configuration(rng),
        "balanced_dual": sample_balanced_dual(rng, 120),
        "centroid_hub_non_firing": centroid_hub_certificate_does_not_fire(),
        "evidence_class": "exact_rational_certificates_plus_floating_point_falsification",
        "universal_authority": "TranslatedNonAdjacentTrinomial.md",
        "claim_boundary": "n >= 4 and 1 <= m <= n-2 only; translated adjacent m = n-1 and unrestricted Erdos 1041 stay open",
    }
    s = report["sampled_translated_trinomials"]
    for key in ("localisation_failures", "spoke_failures",
                "moment_identity_failures", "star_count_failures",
                "r2_bound_failures", "constant_bound_failures"):
        assert s[key] == 0, (key, s[key])
    assert report["balanced_dual"]["duality_gaps"] == 0
    print(json.dumps(report))


if __name__ == "__main__":
    main()
