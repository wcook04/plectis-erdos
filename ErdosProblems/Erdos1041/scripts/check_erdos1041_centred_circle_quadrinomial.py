#!/usr/bin/env python3
"""Replay for CentredCircleQuadrinomialConnector.md.

Exact rational certificates for the sextic tail defeat (41), the guardrail
sextic spoke amplitude 4/5, and the arc threshold 3-sqrt(5) < 1, plus finite
floating-point falsification of the paired-quadrinomial alternative and of the
polar-derivative Schur certificate.  Universal authority is the analytic proof
in CentredCircleQuadrinomialConnector.md; this script is falsification
evidence only.

Run from the repository root:
  ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_centred_circle_quadrinomial.py
"""
from __future__ import annotations

import cmath
import json
import math
import random
from fractions import Fraction

TOL = 1e-9


# ---------------------------------------------------------------- exact part


def exact_sextic_tail_defeat() -> dict:
    """Section 8: every lower Abel tail of F exceeds one, exactly.

    F(z) = z^6 + (5/2) r^2 z^4 + (5/2) r^4 z^2 + r^6 with r = 99/100.
    In the corpus quotient variable w = z^2 the polynomial is
    G(w) = w^3 + (5/2) r^2 w^2 + (5/2) r^4 w + r^6, so m = 3, r = 2, s = 1 and
    the recorded tetranomial tail is t = c + b w^s with c = r^6, b = (5/2) r^4.
    """
    r = Fraction(99, 100)
    r2, r4, r6 = r ** 2, r ** 4, r ** 6

    # The normalised quotient q(w) = w^3 + (5/2) w^2 + (5/2) w + 1 factors as
    # (w + 1)(w^2 + (3/2) w + 1); both factors have unimodular roots.
    lin = [Fraction(1), Fraction(1)]                    # w + 1
    quad = [Fraction(1), Fraction(3, 2), Fraction(1)]   # w^2 + (3/2) w + 1
    prod = [Fraction(0)] * 4
    for i, u in enumerate(lin):
        for j, v in enumerate(quad):
            prod[i + j] += u * v
    assert prod == [Fraction(1), Fraction(5, 2), Fraction(5, 2), Fraction(1)], prod

    # Root of w + 1 is -1, modulus 1.  Roots of the quadratic are
    # -3/4 +- i sqrt(7)/4, with |w|^2 = 9/16 + 7/16 = 1 exactly.
    assert Fraction(9, 16) + Fraction(7, 16) == 1
    # Their product is the constant term 1, confirming both lie on |w| = 1.
    assert quad[2] == 1

    # Every quotient root of the scaled G has modulus r^2 < 1, so every root of
    # F has modulus r < 1 and F is admissible for the corpus tetranomial family.
    assert r2 < 1

    # |t| = r^6 |1 + (5/2) w| >= r^6 (5/2 - 1) = (3/2) r^6 at every root.
    margin = Fraction(3, 2) * r6 - 1
    assert margin == Fraction(824440448203, 2000000000000), margin
    assert margin > 0

    # The proved coefficient-only budget |b| + |c| <= 1 fails here, so no
    # recorded tetranomial theorem is contradicted.
    coeff_budget = Fraction(5, 2) * r4 + r6
    assert coeff_budget > 1, coeff_budget

    return {
        "r": str(r),
        "tail_lower_bound_minus_one": str(margin),
        "coefficient_only_budget_value": str(coeff_budget),
        "coefficient_only_budget_holds": False,
    }


def exact_arc_threshold() -> dict:
    """Section 7: 8 sin^2(pi/10) = 3 - sqrt(5) < 1, by rational squaring."""
    # 3 - sqrt(5) < 1 iff 2 < sqrt(5) iff 4 < 5.
    assert Fraction(2) ** 2 < Fraction(5)
    # s = sin(pi/10) satisfies 4 s^2 + 2 s - 1 = 0, hence 8 s^2 = 2 - 4 s
    # = 2 - (sqrt(5) - 1) = 3 - sqrt(5).
    s = math.sin(math.pi / 10)
    assert abs(4 * s * s + 2 * s - 1) < 1e-15, s
    assert abs(8 * s * s - (3 - math.sqrt(5))) < 1e-15
    # The arc bound is also below the radial threshold one.
    assert 3 - math.sqrt(5) < 1
    return {"arc_sup_bound": "3 - sqrt(5)", "decimal": 3 - math.sqrt(5)}


def exact_guardrail_sextic() -> dict:
    """Section 8: the stored guardrail sextic gets a provably safe spoke pair.

    p(z) = z^6 + (1/5) z^4 - (1/5) z^2 - 1 is the r = 1 member of the corpus
    guardrail family in AbelControlPolygon.lean section 5.  Here omega = -1,
    a = -1/5, k = 2, n = 6.
    """
    omega = Fraction(-1)
    a = Fraction(-1, 5)

    # q(w) = w^3 + (1/5) w^2 - (1/5) w - 1 = (w - 1)(w^2 + (6/5) w + 1).
    lin = [Fraction(-1), Fraction(1)]
    quad = [Fraction(1), Fraction(6, 5), Fraction(1)]
    prod = [Fraction(0)] * 4
    for i, u in enumerate(lin):
        for j, v in enumerate(quad):
            prod[i + j] += u * v
    assert prod == [Fraction(-1), Fraction(-1, 5), Fraction(1, 5), Fraction(1)], prod

    # The four roots with zeta^2 = -3/5 +- (4/5) i.  |zeta^2|^2 = 1 exactly.
    wr, wi = Fraction(-3, 5), Fraction(4, 5)
    assert wr * wr + wi * wi == 1
    # |omega + a zeta^2|^2 = |(-22 -+ 4 i)/25|^2 = 500/625 = 4/5.
    sr = omega + a * wr
    si = a * wi
    amp = sr * sr + si * si
    assert amp == Fraction(4, 5), amp
    assert amp < 1

    # The prescribed spoke to the root 1 fails: |omega + a| = 6/5 > 1, and the
    # exact midpoint value p(1/2) = -327/320 leaves the unit lemniscate.
    bad = abs(omega + a)
    assert bad == Fraction(6, 5)
    half = Fraction(1, 2)
    pmid = half ** 6 + Fraction(1, 5) * half ** 4 - Fraction(1, 5) * half ** 2 - 1
    assert pmid == Fraction(-327, 320), pmid
    assert abs(pmid) > 1

    # Quantitative bound (42): defect d = 1 - 2/sqrt(5).
    defect = 1 - 2 / math.sqrt(5)
    assert defect > 0
    return {
        "safe_spoke_amplitude_sq": str(amp),
        "failed_spoke_amplitude": str(bad),
        "midpoint_value": str(pmid),
        "defect": defect,
    }


# ------------------------------------------------------- sampled quadrinomial


def psi_samples(n: int, k: int, alpha: complex, grid: int):
    """Continuous phase Psi(theta) = n theta - 2 arg(1 + alpha e^{i k theta})."""
    out = []
    run = None
    prev = 0.0
    for i in range(grid + 1):
        t = 2 * math.pi * i / grid
        ang = cmath.phase(1 + alpha * cmath.exp(1j * k * t))
        if run is None:
            run = ang
        else:
            d = ang - prev
            while d > math.pi:
                d -= 2 * math.pi
            while d < -math.pi:
                d += 2 * math.pi
            run += d
        prev = ang
        out.append((t, n * t - 2 * run))
    return out


def signed_crossings(samples, lam: float):
    lo = min(p[1] for p in samples)
    hi = max(p[1] for p in samples)
    found = []
    m = math.floor((lo - lam) / (2 * math.pi)) - 1
    while lam + 2 * math.pi * m <= hi + 2 * math.pi:
        level = lam + 2 * math.pi * m
        for i in range(len(samples) - 1):
            a = samples[i][1] - level
            b = samples[i + 1][1] - level
            if a * b < 0:
                t0, t1 = samples[i][0], samples[i + 1][0]
                theta = t0 + (t1 - t0) * (-a) / (b - a)
                found.append((theta, 1 if b > a else -1))
        m += 1
    return found


def quadrinomial_coeffs(n: int, k: int, a: complex, omega: complex):
    """Descending coefficients of z^n + omega conj(a) z^{n-k} + a z^k + omega."""
    desc = [0j] * (n + 1)
    desc[0] = 1 + 0j
    desc[k] += omega * a.conjugate()
    desc[n - k] += a
    desc[n] += omega
    return desc


def eval_desc(desc, z: complex) -> complex:
    acc = 0j
    for c in desc:
        acc = acc * z + c
    return acc


def newton_refine(desc, z: complex) -> complex:
    n = len(desc) - 1
    dv = [desc[i] * (n - i) for i in range(n)]
    for _ in range(60):
        p = eval_desc(desc, z)
        d = eval_desc(dv, z)
        if d == 0:
            break
        step = p / d
        z -= step
        if abs(step) < 1e-15:
            break
    return z


def sample_quadrinomial_alternative(rng: random.Random, trials: int) -> dict:
    """Every accepted unit-circle paired quadrinomial takes one branch."""
    accepted = 0
    exceptional = 0
    violations = 0
    negcount_mismatch = 0
    for _ in range(trials):
        n = rng.randint(4, 12)
        k = rng.randint(1, (n - 1) // 2)
        if rng.random() < 0.6:
            top = 3.0 if n == 3 * k else min(2.0, math.sqrt(n / k))
            if top <= 1.001:
                continue
            amp = rng.uniform(1.001, top)
        else:
            amp = rng.uniform(0.01, 0.999)
        alpha = amp * cmath.exp(1j * rng.uniform(0, 2 * math.pi))
        samples = psi_samples(n, k, alpha, 8000)
        lam = rng.uniform(0, 2 * math.pi)
        crossings = signed_crossings(samples, lam)
        if len(crossings) != n:
            continue

        omega = -cmath.exp(1j * lam)
        a = alpha * omega
        desc = quadrinomial_coeffs(n, k, a, omega)
        refined = []
        ok = True
        for theta, sign in crossings:
            zeta = newton_refine(desc, cmath.exp(1j * theta))
            if abs(abs(zeta) - 1) > 1e-9 or abs(eval_desc(desc, zeta)) > 1e-9:
                ok = False
                break
            refined.append((cmath.phase(zeta) % (2 * math.pi), sign, zeta))
        if not ok:
            continue
        accepted += 1

        # Lemma 2 amplitude constraint away from the exceptional exponent.
        if n != 3 * k:
            assert amp ** 2 <= n / k + 1e-6, (n, k, amp)
            assert amp <= 2 + 1e-6, (n, k, amp)

        # Winding count (27): exactly k negatively oriented crossings when A > 1.
        neg = sum(1 for _, s, _ in refined if s < 0)
        if amp > 1 and neg != k:
            negcount_mismatch += 1

        good = [z for _, _, z in refined
                if abs(omega + a * z ** k) <= 1 + 1e-9]
        if len(good) >= 2:
            # Radial certificate: verify (3) along both selected spokes.
            for zeta in good[:2]:
                for step in range(0, 41):
                    t = step / 40.0
                    assert abs(eval_desc(desc, t * zeta)) <= 1 - t ** n + 1e-8, \
                        (n, k, t)
            continue

        exceptional += 1
        # Only the n = 3k, A > sqrt(3) branch may reach here.
        if not (n == 3 * k and amp > math.sqrt(3) - 1e-9):
            violations += 1
            continue
        # Arc certificate (5): two consecutive roots within 2 pi / (5 k) whose
        # joining arc has sup |p| < 3 - sqrt(5).
        angles = sorted(t for t, _, _ in refined)
        best = None
        for i in range(len(angles)):
            j = (i + 1) % len(angles)
            gap = (angles[j] - angles[i]) % (2 * math.pi)
            if best is None or gap < best[0]:
                best = (gap, angles[i])
        gap, start = best
        assert gap < 2 * math.pi / (5 * k) + 1e-6, (n, k, amp, gap)
        for step in range(0, 61):
            z = cmath.exp(1j * (start + gap * step / 60.0))
            assert abs(eval_desc(desc, z)) < 3 - math.sqrt(5) + 1e-7, \
                (n, k, amp, step)
    return {
        "accepted": accepted,
        "exceptional_branch": exceptional,
        "alternative_violations": violations,
        "negative_crossing_count_mismatch": negcount_mismatch,
    }


def sample_exceptional_arc(rng: random.Random, trials: int) -> dict:
    """Direct generator for the n = 3k, A > sqrt(3) exceptional family.

    Any three unit-circle points w_1, w_2, w_3 give a paired cubic
    q(w) = w^3 + omega conj(a) w^2 + a w + omega with omega = -w_1 w_2 w_3 and
    a = e_2, because conj(e_2) = e_1 / e_3 when the points are unimodular.
    Lifting through w = z^k produces the exceptional degree n = 3k members.
    """
    built = 0
    for _ in range(trials):
        k = rng.randint(2, 6)
        n = 3 * k
        while True:
            ws = [cmath.exp(2j * math.pi * rng.random()) for _ in range(3)]
            if abs(sum(ws)) > math.sqrt(3):
                break
        e1 = sum(ws)
        e2 = ws[0] * ws[1] + ws[0] * ws[2] + ws[1] * ws[2]
        e3 = ws[0] * ws[1] * ws[2]
        omega = -e3
        a = e2
        assert abs(omega * a.conjugate() - (-e1)) < 1e-9
        amp = abs(a)
        assert amp > math.sqrt(3) - 1e-12
        desc = quadrinomial_coeffs(n, k, a, omega)
        built += 1

        # The three quotient roots lie in an open semicircle of length D < 4 pi/5.
        angs = sorted(cmath.phase(w) % (2 * math.pi) for w in ws)
        gaps = [(angs[(i + 1) % 3] - angs[i]) % (2 * math.pi) for i in range(3)]
        span = 2 * math.pi - max(gaps)
        assert span < 4 * math.pi / 5 + 1e-9, (span, amp)

        # Shortest consecutive separation and its arc certificate (5), (38).
        delta = min(g for g in gaps if g <= span + 1e-12)
        assert delta < 2 * math.pi / 5 + 1e-9, delta
        start = angs[gaps.index(delta)]
        top = 0.0
        for step in range(0, 81):
            z = cmath.exp(1j * (start + delta * step / 80.0) / k)
            top = max(top, abs(eval_desc(desc, z)))
        assert top < 3 - math.sqrt(5) + 1e-9, (n, k, amp, top)
        assert delta / k < 2 * math.pi / (5 * k) + 1e-9
        assert delta / k < 2.0

        # No two-tail alternative is asserted here: the branch exists exactly
        # because the radial selector may fail at every root.
    return {"exceptional_instances": built,
            "arc_sup_bound": 3 - math.sqrt(5)}


# ------------------------------------------------------------ Schur certificate


def poly_from_roots(roots):
    coeffs = [1 + 0j]
    for r in roots:
        nxt = [0j] * (len(coeffs) + 1)
        for i, c in enumerate(coeffs):
            nxt[i] += c
            nxt[i + 1] -= c * r
        coeffs = nxt
    return coeffs  # descending powers


def poly_roots(desc):
    n = len(desc) - 1
    lead = desc[0]
    c = [v / lead for v in desc]
    z = [(0.4 + 0.9j) ** i * (1 + 0.13 * i) for i in range(n)]
    for _ in range(600):
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


def sample_schur_certificate(rng: random.Random, trials: int) -> dict:
    """Theorem 3 (46) and the composed inequalities (50) and (51)."""
    strict_failures = 0
    composition_failures = 0
    worst_sigma = 0.0
    checked = 0
    for _ in range(trials):
        n = rng.randint(2, 9)
        roots = [rng.random() ** 0.4 * cmath.exp(2j * math.pi * rng.random())
                 for _ in range(n)]
        f = poly_from_roots(roots)
        m = n - 1
        if m == 0:
            continue
        deriv = [f[i] * (n - i) for i in range(n)]
        crit = poly_roots(deriv)
        checked += 1

        vals = []
        prods = []
        for c in crit:
            fv = 0j
            for a in f:
                fv = fv * c + a
            pr = 1.0
            for d in crit:
                pr *= abs(1 - d.conjugate() * c)
            vals.append(abs(fv))
            prods.append(pr)
            if abs(fv) >= pr + 1e-9:
                strict_failures += 1
            if pr > 0:
                worst_sigma = max(worst_sigma, abs(fv) / pr)

        # Taylor coefficients of g = (q#)^{1/m}.
        depth = 24
        logc = [0j] * (depth + 1)
        for nu in range(1, depth + 1):
            logc[nu] = -sum(d.conjugate() ** nu for d in crit) / (m * nu)
        b = [0j] * (depth + 1)
        b[0] = 1 + 0j
        for nu in range(1, depth + 1):
            acc = 0j
            for j in range(1, nu + 1):
                acc += j * logc[j] * b[nu - j]
            b[nu] = acc / nu
        defect = sum((2 * nu - 1) * abs(b[nu]) ** 2 for nu in range(1, depth + 1))

        mean_crit = 0.0
        extra = 0.0
        for fv, pr in zip(vals, prods):
            gsq = pr ** (2.0 / m)
            mean_crit += fv ** (2.0 / m)
            sig = fv / pr if pr > 0 else 0.0
            extra += (1 - sig ** (2.0 / m)) * gsq
        mean_crit /= m
        extra /= m
        if mean_crit + defect + extra > 1 + 1e-7:
            composition_failures += 1
        centroid = abs(sum(roots) / n)
        if mean_crit + centroid ** 2 + extra > 1 + 1e-7:
            composition_failures += 1
    return {
        "polynomials": checked,
        "strict_46_failures": strict_failures,
        "composition_50_51_failures": composition_failures,
        "max_sampled_sigma_modulus": worst_sigma,
    }


def main() -> None:
    rng = random.Random(20260905)
    report = {
        "status": "pass",
        "source_note": "CentredCircleQuadrinomialConnector.md",
        "return_batch_id": "erdos1041_20260905_eight_return_stream_01",
        "exact_sextic_tail_defeat": exact_sextic_tail_defeat(),
        "exact_arc_threshold": exact_arc_threshold(),
        "exact_guardrail_sextic": exact_guardrail_sextic(),
        "sampled_alternative": sample_quadrinomial_alternative(rng, 900),
        "sampled_exceptional_arc": sample_exceptional_arc(rng, 400),
        "sampled_schur_certificate": sample_schur_certificate(rng, 220),
        "evidence_class": "exact_rational_certificates_plus_floating_point_falsification",
        "universal_authority": "CentredCircleQuadrinomialConnector.md",
        "claim_boundary": "centred-circle quadrinomials only; unrestricted Erdos 1041 stays open",
    }
    assert report["sampled_alternative"]["alternative_violations"] == 0
    assert report["sampled_alternative"]["negative_crossing_count_mismatch"] == 0
    assert report["sampled_schur_certificate"]["strict_46_failures"] == 0
    assert report["sampled_schur_certificate"]["composition_50_51_failures"] == 0
    assert report["sampled_schur_certificate"]["max_sampled_sigma_modulus"] < 1
    print(json.dumps(report))


if __name__ == "__main__":
    main()
