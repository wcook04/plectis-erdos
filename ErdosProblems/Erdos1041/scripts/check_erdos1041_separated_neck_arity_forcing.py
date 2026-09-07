#!/usr/bin/env python3
"""Replay for SeparatedNeckArityForcing.md.

Six arms.  IDENTITY, SCHEDULE and CLOSURE are exact rational certificates and
carry proof authority for the statements they certify; CLOSURE reruns the
certified pipeline of check_erdos1041_low_critical_potential_closure.py with the
neck arity bound added to k_lower and nothing else changed, and it also checks
that the unpatched pipeline does NOT reach 1/5.  TRIANGLE, CRITICAL and LEMMA
are finite floating-point falsification arms with no universal authority: the
analytic proofs in the note supply the quantifiers.

Standard library only.
"""
import argparse
import cmath
import json
import math
import random
from fractions import Fraction as F
from math import isqrt

DEN = 10 ** 30


def sqrt_enclosure(fr, digits=40):
    """Rational lo <= sqrt(fr) < hi, certified by squaring."""
    assert fr >= 0
    scale = 10 ** digits
    m = isqrt(fr.numerator * scale * scale * fr.denominator)
    lo = F(m, scale * fr.denominator)
    hi = F(m + 1, scale * fr.denominator)
    assert lo * lo <= fr < hi * hi
    return lo, hi


def exp_enclosure(x, terms=60):
    """Rational lo <= exp(x) <= hi for a positive rational x."""
    total, term = F(1), F(1)
    for j in range(1, terms + 1):
        term = term * x / j
        total += term
    tail = term * x / (terms + 1) / (1 - x / (terms + 1))
    return total, total + tail


# ---------------------------------------------------------------- arm IDENTITY

def arm_identity():
    """rho_* = sqrt(1-e^{-4}), s_* = sqrt(tanh 1), and 2 s_*/(1+s_*^2) = rho_*.

    With E = e^2 the identity is a rational identity: s_*^2 = (E-1)/(E+1), so
        (2 s_*/(1+s_*^2))^2 = 4 s_*^2 / (1+s_*^2)^2
                            = 4 (E-1)/(E+1) * ((E+1)/(2E))^2
                            = (E^2-1)/E^2 = 1 - e^{-4} = rho_*^2 ,
    for EVERY value of E, hence in particular for E = e^2.  It is verified below
    at a list of exact rational E, which certifies the rational identity.
    Also log(1/(1-rho_*^2)) = 4 exactly, which is the whole content of the
    threshold: Theorem C' plus Area <= pi gives length^2 <= 4 at rho = rho_*.
    """
    rows = []
    for E in (F(2), F(7, 3), F(739, 100), F(1000003, 135914), F(10 ** 6, 7)):
        s2 = (E - 1) / (E + 1)
        lhs = 4 * s2 / (1 + s2) ** 2
        rhs = (E * E - 1) / (E * E)
        assert lhs == rhs, (E, lhs, rhs)
        rows.append(str(E))
    e2_lo, e2_hi = exp_enclosure(F(2))
    tanh1_lo = (e2_lo - 1) / (e2_lo + 1)
    tanh1_hi = (e2_hi - 1) / (e2_hi + 1)
    assert F(76159, 100000) < tanh1_lo and tanh1_hi < F(76160, 100000)
    e4_lo, e4_hi = exp_enclosure(F(4))
    rho2_lo, rho2_hi = 1 - 1 / e4_lo, 1 - 1 / e4_hi
    assert F(9816, 10000) < rho2_lo and rho2_hi < F(9817, 10000)
    rlo, _ = sqrt_enclosure(rho2_lo)
    assert rlo > F(99, 100), "rho_* must exceed the 0.99 quoted in the brief"
    return {
        "rational_identity_checked_at_E": rows,
        "tanh1_enclosure": [float(tanh1_lo), float(tanh1_hi)],
        "rho_star_sq_enclosure": [float(rho2_lo), float(rho2_hi)],
        "rho_star_lower": float(rlo),
        "rho_star_exceeds_0_99": True,
    }


# ---------------------------------------------------------------- arm SCHEDULE

def neck_constants(kmax=16):
    """Certified rational LOWER bounds for N_k = m_k s_*^{k-1}.

    s_*^2 = tanh 1 = (E-1)/(E+1) with E = e^2;  g(s_*) = (1-s_*^2)/s_*;
    G_k = (k-1) g(s_*);  m_k = (sqrt(G_k^2+4)-G_k)/2, decreasing in G_k.
    Directed rounding: tanh1 from below, s_* from below, g(s_*) from above,
    G_k from above, m_k from below, and the power s_*^{k-1} from below.
    """
    e2_lo, e2_hi = exp_enclosure(F(2))
    tau_lo = (e2_lo - 1) / (e2_lo + 1)
    tau_hi = (e2_hi - 1) / (e2_hi + 1)
    s_lo, _ = sqrt_enclosure(tau_lo)
    g_hi = (1 - tau_lo) / s_lo                      # (1 - tau)/s >= g(s_*)
    assert g_hi > (1 - tau_hi) / s_lo - F(1, 10 ** 20)
    out = {}
    pw = F(1)
    for k in range(2, kmax + 1):
        pw = pw * s_lo if k > 2 else s_lo           # <= s_*^{k-1}
        pw = F(int(pw * DEN), DEN)
        G = g_hi * (k - 1)
        r_lo, _ = sqrt_enclosure(G * G + 4)
        m_lo = (r_lo - G) / 2                       # <= m_k
        out[k] = F(int(m_lo * pw * DEN), DEN)
    return out


def arm_schedule():
    """The certified neck table and the integer arity schedule it forces."""
    N = neck_constants()
    rows, prev = {}, None
    for k, v in N.items():
        assert v > 0
        if prev is not None:
            assert v < prev, "N_k must be strictly decreasing"
        prev = v
        rows[k] = {"N_k_lower": float(v), "X_k_upper": -math.log(float(v))}
    # exact rational statements quoted in the note
    assert N[2] > F(76159, 100000)          # N_2 = tanh 1
    assert N[3] > F(5814, 10000)
    assert N[4] > F(4459, 10000)
    assert N[5] > F(344, 1000)
    assert N[6] > F(2672, 10000)
    assert N[7] > F(2091, 10000)
    assert N[8] > F(1647, 10000)
    # two-root window corollary: t > v/tanh(1) is impossible under failure
    assert F(1, 1) / N[2] < F(13131, 10000)
    return {"table": rows, "two_root_window_ratio_upper": float(1 / N[2])}


# ------------------------------------------------------ floating helper tools

def rho(a, b):
    return abs((a - b) / (1 - b.conjugate() * a))


def blaschke_crit(ws):
    """Critical points of the finite Blaschke product with zeros ws, via
    Durand-Kerner on the numerator of B'/B (degree 2k-2)."""
    k = len(ws)

    def polymul(p, q):
        r = [0j] * (len(p) + len(q) - 1)
        for i, a in enumerate(p):
            for j, b in enumerate(q):
                r[i + j] += a * b
        return r

    coeffs = [0j]
    for j in range(k):
        term = [1 + 0j]
        for l in range(k):
            if l == j:
                continue
            term = polymul(term, [-ws[l], 1 + 0j])
            term = polymul(term, [1 + 0j, -ws[l].conjugate()])
        w = 1 - abs(ws[j]) ** 2
        if len(term) > len(coeffs):
            coeffs = coeffs + [0j] * (len(term) - len(coeffs))
        for i, c in enumerate(term):
            coeffs[i] += w * c
    while len(coeffs) > 1 and abs(coeffs[-1]) < 1e-14:
        coeffs.pop()
    deg = len(coeffs) - 1
    if deg < 1:
        return []
    lead = coeffs[-1]
    mono = [c / lead for c in coeffs]

    def ev(z):
        acc = 0j
        for c in reversed(mono):
            acc = acc * z + c
        return acc

    roots = [(0.4 + 0.9j) ** i for i in range(deg)]
    for _ in range(400):
        new = []
        for i, r in enumerate(roots):
            d = 1 + 0j
            for j, s in enumerate(roots):
                if i != j:
                    d *= (r - s)
            new.append(r - ev(r) / d if abs(d) > 1e-300 else r)
        if max(abs(a - b) for a, b in zip(new, roots)) < 1e-15:
            roots = new
            break
        roots = new
    return [r for r in roots if abs(r) < 1 - 1e-9]


# ---------------------------------------------------------------- arm TRIANGLE

def arm_triangle(trials=200000, seed=20260905):
    """Mobius triangle inequality rho(a,b) <= (rho(a,c)+rho(c,b))/(1+product).

    Classical (Garnett, Bounded Analytic Functions, Ch. I); falsification only.
    """
    rnd = random.Random(seed)
    worst = 0.0
    for _ in range(trials):
        pts = []
        while len(pts) < 3:
            z = complex(rnd.uniform(-1, 1), rnd.uniform(-1, 1))
            if abs(z) < 1:
                pts.append(z)
        a, b, c = pts
        r1, r2 = rho(a, c), rho(c, b)
        worst = max(worst, rho(a, b) - (r1 + r2) / (1 + r1 * r2))
    assert worst <= 1e-12, worst
    return {"trials": trials, "max_violation": worst}


# ---------------------------------------------------------------- arm CRITICAL

def arm_critical(trials=400, seed=7):
    """At a critical point c of B, moved to 0, sum_j (1-|v_j|^2)/v_j = 0."""
    rnd = random.Random(seed)
    worst = 0.0
    checked = 0
    for _ in range(trials):
        k = rnd.randint(2, 6)
        ws = []
        while len(ws) < k:
            z = complex(rnd.uniform(-.95, .95), rnd.uniform(-.95, .95))
            if abs(z) < .95:
                ws.append(z)
        for c in blaschke_crit(ws):
            vs = [(w - c) / (1 - c.conjugate() * w) for w in ws]
            if min(abs(v) for v in vs) < 1e-6:
                continue
            s = sum((1 - abs(v) ** 2) / v for v in vs)
            worst = max(worst, abs(s))
            checked += 1
    assert worst < 1e-6, worst
    return {"critical_points_checked": checked, "max_identity_residual": worst}


# ------------------------------------------------------------------- arm LEMMA

def arm_lemma(trials=6000, seed=11):
    """On rho_*-separated zero sets, m >= m_k and |B(c)| >= N_k."""
    N = {k: float(v) for k, v in neck_constants().items()}
    tau = math.tanh(1.0)
    s = math.sqrt(tau)
    gs = (1 - tau) / s
    m_k = {k: (math.sqrt(((k - 1) * gs) ** 2 + 4) - (k - 1) * gs) / 2
           for k in range(2, 9)}
    rho_star = math.sqrt(1 - math.exp(-4.0))
    rnd = random.Random(seed)
    seen = {k: 0 for k in range(2, 6)}
    worst_m = {k: 10.0 for k in range(2, 6)}
    worst_B = {k: 10.0 for k in range(2, 6)}
    for _ in range(trials):
        k = rnd.randint(2, 5)
        # bias towards the separated regime: radii near the circle, spread angles
        base = rnd.uniform(0, 2 * math.pi)
        ws = []
        for j in range(k):
            t = base + 2 * math.pi * j / k + rnd.gauss(0, 0.9 / k)
            u = 1 - 10 ** rnd.uniform(-7, -1.6)
            ws.append(complex(u * math.cos(t), u * math.sin(t)))
        if min(rho(ws[i], ws[j]) for i in range(k) for j in range(i + 1, k)) < rho_star:
            continue
        seen[k] += 1
        for c in blaschke_crit(ws):
            ds = [rho(c, w) for w in ws]
            m = min(ds)
            prod = 1.0
            for d in ds:
                prod *= d
            worst_m[k] = min(worst_m[k], m - m_k[k])
            worst_B[k] = min(worst_B[k], prod - N[k])
    for k in seen:
        if seen[k]:
            assert worst_m[k] > -1e-9, (k, worst_m[k])
            assert worst_B[k] > -1e-9, (k, worst_B[k])
    return {"separated_samples": seen,
            "min_slack_m_minus_m_k": {k: (None if v > 9 else v) for k, v in worst_m.items()},
            "min_slack_B_minus_N_k": {k: (None if v > 9 else v) for k, v in worst_B.items()}}


# ----------------------------------------------------------------- arm CLOSURE

def arm_closure():
    """Run the certified LowCriticalPotentialClosure pipeline with the neck
    arity bound added to k_lower, and nothing else changed.

    Exact rational certificate.  Quick mode (step 1/100, nine grid points).
    """
    import importlib.util
    import os
    here = os.path.dirname(os.path.abspath(__file__))
    src = os.path.join(here, "check_erdos1041_low_critical_potential_closure.py")
    spec = importlib.util.spec_from_file_location("lcpc", src)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)

    N = neck_constants(kmax=260)
    cache = {}

    def neck_k(x):
        """Certified arity lower bound; monotone in x, so flooring x onto a
        fixed grid keeps it a lower bound and makes it cacheable."""
        if x <= 0:
            return F(2)
        xg = F((x.numerator * 10 ** 6) // x.denominator, 10 ** 6)
        if xg <= 0:
            return F(2)
        hit = cache.get(xg)
        if hit is None:
            e_lo = m.exp_lower(xg)
            k = 2
            while k + 1 < len(N) + 2 and k in N and N[k] * e_lo > 1:
                k += 1
            hit = F(min(k, m.K_CAP))
            cache[xg] = hit
        return hit

    base_k_lower = m.k_lower

    def patched(x, a):
        return max(base_k_lower(x, a), neck_k(x))

    m.k_lower = patched
    res = m.certify_all_degree(F(1, 100), 8)
    X = res["X_cert"]
    assert F(1, 5) * m.exp_upper(X) <= 1, "mu = 1/5 not certified"
    m.k_lower = base_k_lower
    base = m.certify_all_degree(F(1, 100), 8)
    Xb = base["X_cert"]
    assert not (F(1, 5) * m.exp_upper(Xb) <= 1), "baseline should stop at 197/1000"
    assert X < Xb
    return {"X_cert_with_neck": float(X), "X_cert_baseline": float(Xb),
            "gain": float(Xb - X), "mu_certified": "1/5",
            "mu_certified_baseline": "197/1000",
            "worst_initial_area": float(res["worst_alpha"])}


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--part", default="all",
                   choices=["all", "identity", "schedule", "triangle",
                            "critical", "lemma", "closure"])
    a = p.parse_args()
    out = {"status": "pass", "target": "erdos1041",
           "note": "formal_math/erdos257_period_noncollapse/ErdosProblems/"
                   "Erdos1041/SeparatedNeckArityForcing.md"}
    if a.part in ("all", "identity"):
        out["identity"] = arm_identity()
    if a.part in ("all", "schedule"):
        out["schedule"] = arm_schedule()
    if a.part in ("all", "triangle"):
        out["triangle"] = arm_triangle()
    if a.part in ("all", "critical"):
        out["critical"] = arm_critical()
    if a.part in ("all", "lemma"):
        out["lemma"] = arm_lemma()
    if a.part in ("all", "closure"):
        out["closure"] = arm_closure()
    out["evidence_class"] = {
        "identity": "exact_rational_certificate",
        "schedule": "exact_rational_certificate",
        "triangle": "floating_point_falsification_only",
        "critical": "floating_point_falsification_only",
        "lemma": "floating_point_falsification_only",
        "closure": "exact_rational_certificate",
    }
    out["universal_authority"] = "SeparatedNeckArityForcing.md"
    print(json.dumps(out))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
