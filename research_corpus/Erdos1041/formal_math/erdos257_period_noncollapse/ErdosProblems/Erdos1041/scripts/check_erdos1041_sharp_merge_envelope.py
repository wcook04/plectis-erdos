#!/usr/bin/env python3
"""Replay for SharpSymmetricMergeEnvelope.md.

Six gates.  The algebraic gate is exact rational arithmetic.  The closed-form,
sharpness, fibre-defect, scale and corpus-consistency gates are deterministic
floating point at a disclosed tolerance.  Nothing here proves Erdos 1041, and
the metric consumers of the envelope are untouched.
"""
import cmath
import json
import math
import random
from fractions import Fraction


# ---------------------------------------------------------------- exact algebra

def _g(nn, xx):
    return xx * xx / (nn * xx - 1)


def _gprime(nn, xx):
    return (nn * xx * xx - 2 * xx) / (nn * xx - 1) ** 2


def exact_algebraic_identities():
    """Fraction-exact checks of (3.6), (3.10), (4.8)<->(4.3) and (9.1)."""
    failures = []
    checks = 0

    # (3.6)  g(x)-g(y)-g'(y)(x-y) = (x-y)^2/((nx-1)(ny-1)^2),  g(x)=x^2/(nx-1).
    for n in (3, 5, 8, 20):
        for xn, xd in ((1, 2), (3, 7), (5, 4), (9, 8)):
            for yn, yd in ((2, 5), (1, 2), (7, 3)):
                x = Fraction(xn, xd)
                y = Fraction(yn, yd)
                if n * x <= 1 or n * y <= 1:
                    continue
                lhs = _g(n, x) - _g(n, y) - _gprime(n, y) * (x - y)
                rhs = (x - y) ** 2 / ((n * x - 1) * (n * y - 1) ** 2)
                checks += 1
                if lhs != rhs:
                    failures.append(("3.6", n, str(x), str(y)))

    # (3.10)  (k-N p^2)^2 - 4 m^2 p^2 = (1-p^2)(k^2-N^2 p^2),  k=n-m, N=n+m.
    for n in (3, 4, 9, 20, 31):
        for m in range(1, n):
            k, N = n - m, n + m
            for pn, pd in ((1, 10), (3, 100), (7, 25), (1, 3)):
                p = Fraction(pn, pd)
                checks += 1
                if (k - N * p * p) ** 2 - 4 * m * m * p * p != (1 - p * p) * (k * k - N * N * p * p):
                    failures.append(("3.10", n, m, str(p)))

    # Poisson denominator positivity is exactly the capacity gap p < k/N.
    for n, m in ((4, 2), (9, 5), (20, 18)):
        k, N = n - m, n + m
        p0 = Fraction(k, N)
        for p in (p0 * Fraction(1, 2), p0 * Fraction(99, 100), p0, p0 * Fraction(101, 100)):
            checks += 1
            positive = (k - N * p * p) > 2 * m * p
            if positive != (p < p0):
                failures.append(("poisson_positivity", n, m, str(p)))

    # (4.8) n(1-py)(y-p) = m y (1-p^2)  <->  (4.3) y^2 - (k+N p^2)/(n p) y + 1 = 0,
    # as an exact polynomial identity in y (no root extraction needed).
    for n in (3, 5, 12, 40):
        for m in (1, 2, 3, n - 1):
            if not 1 <= m < n:
                continue
            k, N = n - m, n + m
            for p in (Fraction(1, 10), Fraction(3, 40), Fraction(1, 7)):
                for y in (Fraction(2), Fraction(5, 3), Fraction(11, 4)):
                    lhs = n * (1 - p * y) * (y - p) - m * y * (1 - p * p)
                    rhs = -n * p * (y * y - Fraction(k + N * p * p, 1) / (n * p) * y + 1)
                    checks += 1
                    if lhs != rhs:
                        failures.append(("4.8", n, m, str(p), str(y)))

    # (9.1) exact non-negative defect identity, and its agreement with the
    # tangent-line remainder (3.6)/(3.7) of the other return.
    fibres = {
        2: [(Fraction(1, 2), Fraction(3, 5))],
        3: [(Fraction(1, 2), Fraction(3, 5), Fraction(7, 4))],
        4: [(Fraction(1, 3), Fraction(2, 5), Fraction(9, 8), Fraction(5, 2))],
        5: [(Fraction(1, 4), Fraction(1, 2), Fraction(1, 1), Fraction(3, 2), Fraction(8, 3))],
    }
    for n in (7, 13):
        for m, rows in fibres.items():
            for qs in rows:
                ys = [(q + 1) / n for q in qs]
                sq = sum(qs)
                pp = sum(ys)
                direct = sum(_g(n, y) for y in ys) - pp * pp / (n * pp - m)
                pairwise = sum(
                    (qs[i] - qs[j]) ** 2 / (qs[i] * qs[j])
                    for i in range(m) for j in range(i + 1, m)
                ) / (n * n * sq)
                harmonic = (sum(1 / q for q in qs) - Fraction(m * m, 1) / sq) / (n * n)
                ybar = pp / m
                tangent = sum(
                    (y - ybar) ** 2 / ((n * y - 1) * (n * ybar - 1) ** 2) for y in ys
                )
                checks += 3
                if direct != pairwise:
                    failures.append(("9.1_pairwise", n, m))
                if direct != harmonic:
                    failures.append(("9.1_harmonic", n, m))
                if direct != tangent:
                    failures.append(("9.1_vs_3.7", n, m))
                if direct <= 0:
                    failures.append(("9.1_sign", n, m))

    # Equality of the two remainder forms when the fibre is constant: defect 0.
    for n in (7, 13):
        for m in (2, 3, 4):
            qs = [Fraction(3, 4)] * m
            ys = [(q + 1) / n for q in qs]
            pp = sum(ys)
            checks += 1
            if sum(_g(n, y) for y in ys) - pp * pp / (n * pp - m) != 0:
                failures.append(("9.1_zero", n, m))

    return {"pass": not failures, "exact_checks": checks, "failures": failures[:8]}


# --------------------------------------------------------------- envelope forms

def envelope_root(n, k, p):
    """Larger root Y>1 of Y^2 - (k+N p^2)/(n p) Y + 1 = 0."""
    N = 2 * n - k
    a = (k + N * p * p) / (n * p)
    return (a + math.sqrt(a * a - 4)) / 2


def log_envelope(n, k, p):
    """log F_{n,k}(p) = (n/m) log Y + log(1-pY) - log(Y-p)."""
    m = n - k
    y = envelope_root(n, k, p)
    return (n / m) * math.log(y) + math.log1p(-p * y) - math.log(y - p)


def envelope_integral(n, k, p, panels=4096):
    """Psi_{n,k}(p) by composite Simpson after u = (k/N) cos(psi)."""
    m = n - k
    p0 = k / (2 * n - k)
    psi0 = math.acos(min(1.0, max(-1.0, p / p0)))

    def integrand(psi):
        c = math.cos(psi)
        s = math.sin(psi)
        return s * s / (c * math.sqrt(1 - p0 * p0 * c * c))

    h = psi0 / panels
    total = integrand(0.0) + integrand(psi0)
    for i in range(1, panels):
        total += (4 if i % 2 else 2) * integrand(i * h)
    return (k / m) * total * h / 3


ENVELOPE_ROWS = [
    (4, 2, 0.1), (9, 4, 0.04), (20, 2, 0.03),          # the three rows of r06 §9
    (3, 2, 0.2), (3, 1, 0.05), (5, 4, 0.5), (5, 2, 0.1),
    (6, 3, 0.3), (7, 1, 0.02), (8, 6, 0.55), (12, 5, 0.25),
    (30, 3, 0.008), (50, 49, 0.9), (9, 7, 0.4), (10, 4, 0.02),
]


def closed_form_gate(tolerance=1e-9):
    rows = []
    worst = 0.0
    for n, k, p in ENVELOPE_ROWS:
        p0 = k / (2 * n - k)
        assert 0 < p < p0, (n, k, p)
        psi = envelope_integral(n, k, p)
        lf = log_envelope(n, k, p)
        worst = max(worst, abs(psi - lf))
        rows.append({"n": n, "k": k, "p": p, "psi": psi, "log_F": lf, "abs_gap": abs(psi - lf)})
    return {"pass": worst <= tolerance, "tolerance": tolerance,
            "worst_abs_gap": worst, "rows": len(rows), "sample": rows[:3]}


# ------------------------------------------------------------ polynomial sharpness

def sharpness_gate(tolerance=1e-11):
    """f = z^k (z^m - 1): the exterior model reproduces the true critical modulus."""
    rows = []
    worst_value = 0.0
    worst_stationary = 0.0
    worst_quadratic = 0.0
    for n, k in ((3, 1), (5, 2), (6, 3), (8, 2), (9, 7), (10, 4), (12, 4)):
        m = n - k
        p0 = k / (2 * n - k)
        # true nonzero critical modulus of f, from f' = z^(k-1)(n z^m - k)
        beta_direct = min(
            abs(zc) ** k * abs(zc ** m - 1)
            for zc in ((k / n) ** (1 / m) * cmath.exp(2j * math.pi * j / m) for j in range(m))
        )
        beta_formula = (m / n) * (k / n) ** (k / m)
        worst_value = max(worst_value, abs(beta_direct - beta_formula))
        for p in (0.02, 0.1, 0.5 * p0, 0.9 * p0):
            if not 0 < p < p0:
                continue
            f_val = math.exp(log_envelope(n, k, p))
            t = beta_formula / f_val
            y = envelope_root(n, k, p)
            worst_quadratic = max(
                worst_quadratic, abs(y * y - (k + (2 * n - k) * p * p) / (n * p) * y + 1))
            zc = y ** (1 / m)
            assert zc > 1.0, (n, k, p, zc)

            def w(zeta):
                return t * zeta ** n * (1 - p * zeta ** m) / (zeta ** m - p)

            # W'(zeta_c) = 0 by central difference on the analytic model
            step = 1e-6
            deriv = (w(complex(zc + step, 0)) - w(complex(zc - step, 0))) / (2 * step)
            scale = abs(w(complex(zc, 0))) / zc
            worst_stationary = max(worst_stationary, abs(deriv) / scale)
            worst_value = max(worst_value, abs(abs(w(complex(zc, 0))) - beta_formula))
            rows.append({"n": n, "k": k, "p": p, "t": t, "beta": beta_formula,
                         "F": f_val, "zeta_c": zc})
    return {"pass": worst_value <= tolerance and worst_quadratic <= tolerance
                    and worst_stationary <= 1e-6,
            "tolerance": tolerance,
            "worst_abs_critical_value_gap": worst_value,
            "worst_quadratic_residual": worst_quadratic,
            "worst_relative_stationarity_residual": worst_stationary,
            "rows": len(rows)}


# ------------------------------------------------------------------ fibre defect

def blaschke_derivative_modulus(zeros, zeta):
    return sum((1 - abs(a) ** 2) / abs(zeta - a) ** 2 for a in zeros)


def blaschke_value(zeros, zeta):
    out = 1 + 0j
    for a in zeros:
        out *= (zeta - a) / (1 - a.conjugate() * zeta)
    return out


def _poly_from_roots(roots):
    coeffs = [1 + 0j]
    for r in roots:
        new = [0j] * (len(coeffs) + 1)
        for i, c in enumerate(coeffs):
            new[i] += c
            new[i + 1] -= c * r
        coeffs = new
    return coeffs


def _poly_eval(coeffs, z):
    out = 0j
    for c in coeffs:
        out = out * z + c
    return out


def fibre_roots(zeros, w):
    """Solve B(zeta) = w on the unit circle by Durand-Kerner."""
    m = len(zeros)
    num = _poly_from_roots(zeros)
    den = _poly_from_roots([1 / a.conjugate() for a in zeros])
    lead = 1.0
    for a in zeros:
        lead *= -a.conjugate()
    den = [c * lead for c in den]
    poly = [a - w * b for a, b in zip(num, den)]
    guesses = [cmath.exp(2j * math.pi * (j + 0.37) / m) for j in range(m)]
    for _ in range(200):
        moved = 0.0
        for i in range(m):
            denom = poly[0]
            for j in range(m):
                if j != i:
                    denom *= guesses[i] - guesses[j]
            if denom == 0:
                continue
            delta = _poly_eval(poly, guesses[i]) / denom
            guesses[i] -= delta
            moved = max(moved, abs(delta))
        if moved < 1e-15:
            break
    return [g / abs(g) for g in guesses]


def _j_value(n, m, p):
    k = n - m
    N = n + m
    return (1 + m * math.sqrt(1 - p * p) / math.sqrt(k * k - N * N * p * p)) / n


def _curvilinear_area(n, zeros, samples=2048):
    total = 0.0
    for i in range(samples):
        zeta = cmath.exp(2j * math.pi * i / samples)
        total += 1 / (n - blaschke_derivative_modulus(zeros, zeta))
    return total / samples


def _fibre_area_and_defect(n, zeros, samples=512):
    m = len(zeros)
    b0 = blaschke_value(zeros, 0j)
    p = abs(b0)
    area = 0.0
    defect = 0.0
    worst_fibre_identity = 0.0
    for i in range(samples):
        w = cmath.exp(2j * math.pi * i / samples)
        pts = fibre_roots(zeros, w)
        ys = [1 / blaschke_derivative_modulus(zeros, z) for z in pts]
        poisson = (1 - p * p) / abs(w - b0) ** 2
        worst_fibre_identity = max(worst_fibre_identity, abs(sum(ys) - poisson))
        area += sum(y * y / (n * y - 1) for y in ys)
        qs = [n * y - 1 for y in ys]
        sq = sum(qs)
        defect += sum(
            (qs[a] - qs[b]) ** 2 / (qs[a] * qs[b])
            for a in range(m) for b in range(a + 1, m)
        ) / (n * n * sq)
    return area / samples, defect / samples, worst_fibre_identity, p


def fibre_defect_gate(seed=20260905, trials=6):
    rng = random.Random(seed)
    worst_negative_defect = 0.0
    worst_area_mismatch = 0.0
    worst_identity = 0.0
    worst_defect_formula = 0.0
    worst_symmetric_defect = 0.0
    instances = 0
    for n, m in ((5, 2), (7, 3), (9, 3), (11, 4), (8, 2)):
        cap = (n / m) * 0.55
        rmax = (cap - 1) / (cap + 1)
        for _ in range(trials):
            zeros = [
                rng.uniform(0.05, rmax) * cmath.exp(2j * math.pi * rng.random())
                for _ in range(m)
            ]
            if max(
                blaschke_derivative_modulus(zeros, cmath.exp(2j * math.pi * i / 512))
                for i in range(512)
            ) >= n - 1e-6:
                continue
            theta_area = _curvilinear_area(n, zeros)
            fib_area, pair_defect, ident, p = _fibre_area_and_defect(n, zeros)
            j = _j_value(n, m, p)
            worst_area_mismatch = max(worst_area_mismatch, abs(theta_area - fib_area))
            worst_identity = max(worst_identity, ident)
            worst_negative_defect = min(worst_negative_defect, fib_area - j)
            worst_defect_formula = max(worst_defect_formula, abs((fib_area - j) - pair_defect))
            instances += 1
        # symmetric model B_p(z) = (z^m - p)/(1 - p z^m): zero defect
        for p_root in (0.2, 0.4):
            zeros = [p_root * cmath.exp(2j * math.pi * j / m) for j in range(m)]
            if max(
                blaschke_derivative_modulus(zeros, cmath.exp(2j * math.pi * i / 512))
                for i in range(512)
            ) >= n - 1e-6:
                continue
            fib_area, _, _, p = _fibre_area_and_defect(n, zeros)
            worst_symmetric_defect = max(worst_symmetric_defect, abs(fib_area - _j_value(n, m, p)))
            instances += 1
    return {"pass": worst_negative_defect >= -1e-9 and worst_area_mismatch <= 1e-9
                    and worst_identity <= 1e-9 and worst_defect_formula <= 1e-9
                    and worst_symmetric_defect <= 1e-9,
            "instances": instances,
            "worst_negative_defect": worst_negative_defect,
            "worst_theta_vs_fibre_area_gap": worst_area_mismatch,
            "worst_fibre_identity_residual": worst_identity,
            "worst_defect_formula_residual": worst_defect_formula,
            "worst_symmetric_model_defect": worst_symmetric_defect,
            "evidence_class": "deterministic_floating_falsifier_search_not_proof"}


# ------------------------------------------------------------------ scales gate

def corpus_log_radial_ceiling(n, r):
    """log M_n(r) of CapacitySaturationBridge.md (10), the spectator-drop ceiling."""
    a = ((n - 1) + (n + 1) * r * r) / (n * r)
    root = (a + math.sqrt(a * a - 4)) / 2
    return n * math.log(root) + math.log1p(-r * root) - math.log(root - r)


def scales_gate():
    """Log-domain comparisons; F itself overflows the double range at large n."""
    worst_corollary = -math.inf
    worst_vs_corpus = -math.inf
    strict_improvements = 0
    comparisons = 0
    for n, k, p in ENVELOPE_ROWS:
        m = n - k
        p0 = k / (2 * n - k)
        log_f = log_envelope(n, k, p)
        worst_corollary = max(worst_corollary, log_f - (k / m) * math.log(p0 / p))
        r = p ** (1 / m)
        if r < (n - 1) / (n + 1):
            corpus = corpus_log_radial_ceiling(n, r)
            worst_vs_corpus = max(worst_vs_corpus, log_f - corpus)
            comparisons += 1
            if m >= 2 and log_f < corpus - 1e-9:
                strict_improvements += 1
    # p -> 0 scale (4.12) and saturation cusp (4.13) against corpus (17)
    worst_small_p = 0.0
    cusp_ratio_errors = {}
    for n, k in ((4, 2), (9, 4), (20, 2), (30, 3)):
        m = n - k
        log_asym = math.log(m) + (k / m) * math.log(k) - (n / m) * math.log(n)
        for p in (1e-8, 1e-10, 1e-12):
            gap = log_envelope(n, k, p) - (log_asym - (k / m) * math.log(p))
            worst_small_p = max(worst_small_p, abs(gap))
        coefficient = math.sqrt(2) / 3 * (n * n - m * m) / (math.sqrt(n) * m ** 1.5)
        p0 = k / (2 * n - k)
        for eps in (1e-2, 1e-3, 1e-4, 1e-5):
            ratio = log_envelope(n, k, p0 * (1 - eps)) / (coefficient * eps ** 1.5)
            key = f"eps_{eps:g}"
            cusp_ratio_errors[key] = max(cusp_ratio_errors.get(key, 0.0), abs(ratio - 1))
    # the cusp remainder is O(eps^(5/2)), so the relative error must fall like eps.
    # Below eps = 1e-6 the closed form loses the comparison to cancellation, not
    # to the expansion, so the decade ladder stops there.
    ladder = [cusp_ratio_errors[f"eps_{e:g}"] for e in (1e-2, 1e-3, 1e-4, 1e-5)]
    cusp_decays = (max(ladder) <= 5e-3
                   and all(a > 5 * b for a, b in zip(ladder, ladder[1:])))
    # m = 1: the new envelope IS the corpus radial ceiling, exactly.
    worst_m1 = 0.0
    for n in (3, 5, 12, 40):
        for p in (0.02, 0.1, 0.3):
            if p < (n - 1) / (n + 1):
                worst_m1 = max(worst_m1, abs(
                    log_envelope(n, n - 1, p) - corpus_log_radial_ceiling(n, p)))
    return {"pass": worst_corollary <= 1e-9 and worst_vs_corpus <= 1e-9
                    and worst_small_p <= 1e-6 and cusp_decays and worst_m1 <= 1e-9,
            "worst_corollary_log_excess": worst_corollary,
            "worst_log_excess_over_corpus_radial_ceiling": worst_vs_corpus,
            "strict_improvements_over_corpus_ceiling": strict_improvements,
            "comparisons": comparisons,
            "worst_small_p_log_gap": worst_small_p,
            "cusp_ratio_errors": cusp_ratio_errors,
            "cusp_relative_error_decays_like_epsilon": cusp_decays,
            "worst_m_equals_one_identification": worst_m1}


# ------------------------------------------------------------- corpus agreement

def corpus_consistency_gate():
    """LastLobeCapacityLaw.md and the r06 §9 exact cubic merge level."""
    # A single hanging lobe of multiplicity m merges at p = p0^m: at or before
    # capacity saturation, with equality exactly when m = 1.
    lobe = []
    lobe_ok = True
    for n in (3, 5, 8, 17):
        for m in range(1, n):
            p0 = Fraction(n - m, n + m)
            p_merge = p0 ** m
            residual = envelope_integral(n, n - m, float(p_merge))
            lobe.append({"n": n, "m": m, "p_merge": float(p_merge), "p0": float(p0),
                         "residual_envelope": residual})
            if m == 1:
                lobe_ok &= p_merge == p0 and residual < 1e-9
            else:
                lobe_ok &= p_merge < p0 and residual > 1e-9
    m1_saturates = all(
        envelope_integral(n, n - 1, float(Fraction(n - 1, n + 1)) * (1 - 1e-12)) < 1e-6
        for n in (3, 5, 8, 17)
    )

    # r06 §9 cubic row: exact next merge level of (z^2-1/25)(z-1) in Q(sqrt 7).
    # Critical points 1/3 +- 2 sqrt(7)/15; the outer one carries the merge.
    def q7_mul(a, b):
        return (a[0] * b[0] + 7 * a[1] * b[1], a[0] * b[1] + a[1] * b[0])

    c = (Fraction(1, 3), Fraction(2, 15))              # 1/3 + (2/15) sqrt 7
    c2 = q7_mul(c, c)
    left = (c2[0] - Fraction(1, 25), c2[1])
    right = (c[0] - 1, c[1])
    value = q7_mul(left, right)
    claim = (Fraction(32, 675), Fraction(112, 3375))
    exact_merge = (value[0] == -claim[0] and value[1] == -claim[1])
    numeric = abs(float(value[0]) + float(value[1]) * math.sqrt(7))

    return {"pass": lobe_ok and m1_saturates and exact_merge,
            "last_lobe_rows": len(lobe),
            "last_lobe_merges_at_or_before_saturation": lobe_ok,
            "m_equals_one_merges_exactly_at_saturation": m1_saturates,
            "r06_cubic_exact_merge_level_matches": exact_merge,
            "r06_cubic_merge_level": numeric}


def main():
    algebra = exact_algebraic_identities()
    closed = closed_form_gate()
    sharp = sharpness_gate()
    fibre = fibre_defect_gate()
    scales = scales_gate()
    corpus = corpus_consistency_gate()
    ok = all(part["pass"] for part in (algebra, closed, sharp, fibre, scales, corpus))
    print(json.dumps({
        "schema": "erdos1041_sharp_merge_envelope_receipt_v1",
        "status": "pass" if ok else "fail",
        "exact_algebraic_identities": algebra,
        "closed_form_identification": closed,
        "polynomial_sharpness": sharp,
        "fibre_defect_non_negativity": fibre,
        "scales_and_corollaries": scales,
        "corpus_consistency": corpus,
        "universal_authority": "SharpSymmetricMergeEnvelope.md",
        "claim_boundary": (
            "Gate one is exact rational arithmetic; the rest is deterministic floating "
            "point at the disclosed tolerances. The envelope theorem is proved in the "
            "note, not by this script. Erdos 1041 remains open."
        ),
    }))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
