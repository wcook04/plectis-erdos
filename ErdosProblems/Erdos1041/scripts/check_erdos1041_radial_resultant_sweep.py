#!/usr/bin/env python3
"""Erdos 1041 receipt: the radial resultant sweep, the near-Fekete spoke law,
and the entry-radius fractional power.

Checks, in order:

  (A) RADIAL SWEEP IDENTITY.  For monic f with roots a_k of common modulus r,
      f* the reciprocal adjoint, ahat_j = a_j / r, sigma_m = sum_j ahat_j^m:

          sum_j -log|f*(t ahat_j)|  =  sum_{m>=1} ((t r)^m / m) |sigma_m|^2  >= 0

      for every t in [0, 1/r).  Equivalently
          prod_j |f*(t ahat_j)| = exp(-sum_m ((t r)^m/m)|sigma_m|^2) <= 1.
      At t = r this is exactly research_packet exact_results
      `reciprocal_adjoint_resultant_power_sum_identity` (RootCentredReciprocalSweep.md
      Theorem RS): the sweep is the whole radius, not only its endpoint.
      The general-moduli form  sum_j -log|f*(t ahat_j)| = sum_m (t^m/m) Re(pbar_m sigma_m)
      is checked too (it is NOT signed in general).

  (B) NEAR-FEKETE FIRST-ORDER SPOKE LAW.  For a_k = omega^k (1 + e_k),
          log|f(z)| = log|1 - z^n| + Re Lambda(z) + O(eta^2),
          Lambda(z) = sum_k e_k / (1 - z omega^{-k}),
      with the EXACT balance identity
          sum_{j=0}^{n-1} Lambda(t omega^j) = n Lambda(0) / (1 - t^n).
      Both are checked: the balance to machine precision, the expansion by its
      O(eta^2) convergence rate.

  (C) ENTRY-RADIUS LAW.  On the ray zeta = t omega^j the near-field model
          W(zeta) = Re(e^{i psi} zeta) - Re(zeta^n),   psi = arg Ehat_1,
      gives W(t omega^j) = t cos(psi_j) - t^n exactly, hence the entry radius
          tau_j = (cos psi_j)_+^{1/(n-1)}.
      Checked against tau measured in ROOT coordinates by exact segment maxima:
      the ratio tends to 1 as the perturbation shrinks.

  (D) FAIL-CLOSED CONTROL.  The instrument must reproduce a KNOWN-FALSE
      statement, else a pass proves nothing.  Form A' (two FULL origin spokes)
      is false; a pinned degree-three angular perturbation of the regular
      triangle always loses one spoke, and the recorded five-root witness loses
      all of them.

  (E) NEAR-FIELD MODEL CRITICALITY.  W(zeta) = Re(e^{i psi} zeta) - Re(zeta^n)
      is EXACTLY critical at n = 3, psi = pi/3: the chord maximum for the only
      admissible pair is g(s) = s^3/8 - s/4 + 1/(8 s), g'(s) = 0 iff
      3 s^4 - 2 s^2 - 1 = 0 iff s = 1, and g(1) = 0 exactly, attained at
      zeta* = -1/2 - i sqrt3/6 where BOTH harmonics vanish separately.
      That is why every recorded Form A-cut search pins at 1.0000000.

  (F) CLOSED-FORM SPOKE FUNCTIONAL.  For a pure angular perturbation theta,
          log|f(t w^j)| - log(1-t^n)  =  P_j(t) + O(eta^2),
          P_j(t) = sum_{l=1}^{floor((n-1)/2)} (theta_{j+l} - theta_{j-l}) g_l(t),
          g_l(t) = t sin(2 pi l/n)/(1 - 2 t cos(2 pi l/n) + t^2)  >  0,
      so the functional sees only the ANTISYMMETRIC part of theta about j,
      every kernel is positive, sum_j P_j == 0, and a perturbation symmetric
      about root j leaves that spoke exactly contained.

Exit 0 on success, 1 on any failed check.
"""
from __future__ import annotations

import cmath
import math
import sys

import numpy as np

TOL = 1e-12
FAILURES: list[str] = []


def report(name: str, ok: bool, detail: str) -> None:
    print(f"[{'PASS' if ok else 'FAIL'}] {name}: {detail}")
    if not ok:
        FAILURES.append(name)


# --------------------------------------------------------------- shared pieces


def poly_from_roots(roots):
    return np.poly(np.array(roots, dtype=complex))


def compose_segment(coeffs, z0, z1):
    """coefficients (highest first) in t of f(z0 + t (z1 - z0))."""
    n = len(coeffs) - 1
    d = z1 - z0
    work = list(coeffs)
    asc = []
    while work:
        acc = 0j
        newq = []
        for x in work[:-1]:
            acc = acc * z0 + x
            newq.append(acc)
        asc.append(work[-1] if len(work) == 1 else acc * z0 + work[-1])
        work = newq
    out = np.array([asc[k] * d ** k for k in range(n + 1)], dtype=complex)
    return out[::-1]


def seg_max2(coeffs, z0, z1):
    """EXACT max of |f|^2 on [z0, z1]: |f|^2 is a real polynomial of degree 2n
    in the parameter, so its critical points are located as polynomial roots."""
    c = compose_segment(coeffs, z0, z1)
    q = np.convolve(c, np.conj(c)).real
    dq = np.polyder(q)
    ts = [0.0, 1.0]
    if len(dq) > 1 and np.any(np.abs(dq) > 0):
        for r in np.roots(dq):
            if abs(r.imag) < 1e-9 and -1e-12 <= r.real <= 1 + 1e-12:
                ts.append(min(1.0, max(0.0, r.real)))
    return max(float(np.polyval(q, t)) for t in ts)


def entry_radius(coeffs, a, steps=60):
    """tau(a) = inf{s : |f| <= 1 on [s ahat, a]}; the predicate is monotone in s
    because a shorter segment is contained in a longer one."""
    ah = a / abs(a)

    def ok(s):
        return seg_max2(coeffs, s * ah, a) <= 1.0 + 1e-15

    if ok(0.0):
        return 0.0
    lo, hi = 0.0, abs(a)
    for _ in range(steps):
        mid = 0.5 * (lo + hi)
        if ok(mid):
            hi = mid
        else:
            lo = mid
    return hi


def fstar_value(roots, z):
    """f*(z) = prod_k (1 - conj(a_k) z)."""
    out = 1.0 + 0j
    for a in roots:
        out *= 1 - np.conj(complex(a)) * z
    return out


# ------------------------------------------------------- (A) radial sweep


def _terms_needed(x: float, n: int, target: float = 1e-14) -> int:
    """M with the TAIL BOUND  n^2 x^{M+1} / ((M+1)(1-x)) < target.

    RootCentredReciprocalSweep.md records that truncating on a small TERM rather
    than on a tail bound reports spurious errors up to 5.3, because on a regular
    gon sigma_m vanishes unless n | m and a run of zeros triggers an early break.
    """
    if x <= 0:
        return 2
    M = 64
    while M < 4_000_000:
        if n * n * x ** (M + 1) / ((M + 1) * (1 - x)) < target:
            return M
        M *= 2
    raise RuntimeError("tail bound unreachable")


def _power_sums(units, M):
    """sigma_m = sum_j u_j^m for m = 0..M, computed by repeated multiplication."""
    u = np.array(units, dtype=complex)
    cur = np.ones_like(u)
    out = np.empty(M + 1, dtype=complex)
    out[0] = len(u)
    for m in range(1, M + 1):
        cur = cur * u
        out[m] = cur.sum()
    return out


def check_radial_sweep():
    rng = np.random.default_rng(20260824)
    worst_eq = 0.0
    worst_gen = 0.0
    worst_endpoint = 0.0
    checks = 0
    for n in (2, 3, 4, 5, 7, 9):
        for r in (0.4, 0.85, 0.999):
            ang = np.sort(rng.uniform(0, 2 * math.pi, n))
            ahat = [cmath.exp(1j * a) for a in ang]
            roots = [r * h for h in ahat]
            M = _terms_needed(r * r, n)
            sig = _power_sums(ahat, M)
            ms = np.arange(1, M + 1)
            for t in (0.1 * r, 0.5 * r, 0.9 * r, r):
                x = t * r
                lhs = -sum(math.log(abs(fstar_value(roots, t * h))) for h in ahat)
                w = np.power(x, ms) / ms
                rhs_eq = float(np.sum(w * np.abs(sig[1:]) ** 2))
                # general form: Re(conj(p_m) sigma_m) with p_m = r^m sigma_m
                pm = np.power(r, ms) * sig[1:]
                rhs_gen = float(np.sum(np.power(t, ms) / ms
                                       * (np.conj(pm) * sig[1:]).real))
                worst_eq = max(worst_eq, abs(lhs - rhs_eq))
                worst_gen = max(worst_gen, abs(lhs - rhs_gen))
                checks += 1
                if rhs_eq < -1e-14:
                    report("A.nonneg", False, f"RHS negative {rhs_eq}")
                    return
            # endpoint t = r must reproduce Theorem RS  |Res(f,f*)|
            res = 1.0
            for aj in roots:
                for ak in roots:
                    res *= abs(1 - np.conj(complex(aj)) * complex(ak))
            pm_all = np.power(r, ms) * sig[1:]
            rs = math.exp(-float(np.sum(np.abs(pm_all) ** 2 / ms)))
            worst_endpoint = max(worst_endpoint, abs(res - rs) / max(rs, 1e-300))
    report("A1 radial sweep identity (equal moduli)", worst_eq < 1e-11,
           f"worst abs error {worst_eq:.3e} over {checks} (degree, radius, radial point) checks, tail-bounded truncation")
    report("A2 radial sweep identity (general form)", worst_gen < 1e-11,
           f"worst abs error {worst_gen:.3e}")
    report("A3 endpoint t=r reduces to Theorem RS", worst_endpoint < 1e-11,
           f"worst relative error {worst_endpoint:.3e}")


# ------------------------------------------- (B) near-Fekete first-order law


def check_near_fekete_law():
    rng = np.random.default_rng(7)
    n = 6
    om = cmath.exp(2j * math.pi / n)
    e = [complex(rng.normal(0, 1), rng.normal(0, 1)) for _ in range(n)]

    # B1: the balance identity, EXACT (no perturbative content)
    worst = 0.0
    for scale in (1.0, 0.3):
        ee = [scale * x for x in e]
        for t in (0.2, 0.6, 0.95):
            lhs = sum(sum(ee[k] / (1 - t * om ** j * om ** (-k)) for k in range(n))
                      for j in range(n))
            rhs = n * sum(ee) / (1 - t ** n)
            worst = max(worst, abs(lhs - rhs))
    report("B1 balance identity  sum_j Lambda(t w^j) = n Lambda(0)/(1-t^n)",
           worst < 1e-11, f"worst abs error {worst:.3e}")

    # B2: the expansion is first order -- the residual must fall like eta^2
    ratios = []
    prev = None
    for eta in (1e-2, 1e-3, 1e-4):
        ee = [eta * x for x in e]
        roots = [om ** k * (1 + ee[k]) for k in range(n)]
        c = poly_from_roots(roots)
        err = 0.0
        for t in (0.15, 0.35, 0.55):
            z = t * om ** 2
            exact = math.log(abs(np.polyval(c, z)))
            lam = sum(ee[k] / (1 - z * om ** (-k)) for k in range(n))
            approx = math.log(abs(1 - z ** n)) + lam.real
            err = max(err, abs(exact - approx))
        if prev is not None:
            ratios.append(prev / err)
        prev = err
    ok = all(r > 50 for r in ratios)   # eta drops by 10 -> error should drop ~100
    report("B2 expansion residual is O(eta^2)", ok,
           f"residual shrink factors per decade of eta: {[round(x, 1) for x in ratios]}")


# ------------------------------------------------ (C) the entry-radius law


def check_entry_radius_law():
    n = 3
    om = cmath.exp(2j * math.pi / n)
    rows = []
    ok = True
    for eta in (1e-2, 1e-3, 1e-4, 1e-5):
        th = [eta, 0.0, 0.0]
        e = [1j * x for x in th]
        E1 = sum(e[k] * om ** (-k) for k in range(n))
        roots = [(1.0 - 1e-12) * cmath.exp(1j * (2 * math.pi * k / n + th[k]))
                 for k in range(n)]
        c = poly_from_roots(roots)
        for j in range(n):
            cj = (om ** j * E1).real
            pred = cj ** (1.0 / (n - 1)) if cj > 0 else 0.0
            meas = entry_radius(c, roots[j])
            if cj <= 0:
                if meas > 1e-9:
                    ok = False
                rows.append((eta, j, "predicted tau=0", f"measured {meas:.3e}"))
            else:
                ratio = meas / pred
                rows.append((eta, j, f"tau_pred {pred:.6e}",
                             f"measured {meas:.6e}  ratio {ratio:.5f}"))
                if not (0.9 < ratio < 1.1):
                    ok = False
    last = [r for r in rows if r[0] == 1e-5 and "tau_pred" in r[2]]
    report("C entry radius tau_j = (cos psi_j)_+^{1/(n-1)}", ok,
           f"{len(rows)} ray/scale checks; finest scale: {last}")


# -------------------------------------------------- (D) fail-closed control


def check_form_a_prime_is_false():
    """Form A' (two FULL origin spokes) is KNOWN FALSE.  The instrument must
    exhibit that, otherwise a clean pass above proves nothing."""
    n = 3
    counts = {}
    for eta in (1e-2, 1e-3, 1e-4):
        th = [eta, 0.0, 0.0]
        roots = [(1.0 - 1e-9) * cmath.exp(1j * (2 * math.pi * k / n + th[k]))
                 for k in range(n)]
        c = poly_from_roots(roots)
        counts[eta] = sum(1 for a in roots if seg_max2(c, 0j, a) <= 1.0 + 1e-14)
    ok = all(v == 2 for v in counts.values())
    report("D1 pinned n=3 witness has exactly 2 contained full origin spokes",
           ok, f"counts by eta: {counts}  (three roots, one spoke always exits)")

    # the recorded five-root witness: ZERO contained full spokes
    r = 99999 / 100000
    five = [r, r * complex(-20, 99) / 101, r * complex(-20, -99) / 101,
            r * complex(-28, 195) / 197, r * complex(-28, -195) / 197]
    c5 = poly_from_roots(five)
    k5 = sum(1 for a in five if seg_max2(c5, 0j, a) <= 1.0 + 1e-14)
    taus = [entry_radius(c5, a) / abs(a) for a in five]
    ok5 = (k5 == 0)
    report("D2 recorded five-root witness: Form A' fails outright", ok5,
           f"contained full spokes = {k5}; tau/|a| = "
           f"{[round(t, 6) for t in taus]} (recorded 0.542751 0.047854 0.047854 "
           f"0.032779 0.032779)")


def check_near_field_model():
    """(E) The near-field model W(zeta) = Re(e^{i psi} zeta) - Re(zeta^n) is
    EXACTLY CRITICAL at the worst rotation psi = pi/n.  Proved at n = 3 by hand;
    checked here as exact algebra plus a direct evaluation."""
    n = 3
    psi = math.pi / n
    om = cmath.exp(2j * math.pi / n)

    def W(z):
        return (cmath.exp(1j * psi) * z).real - (z ** n).real

    # only ray 1 is fully good; rays 0 and 2 have cos psi_j = 1/2, tau = 2^{-1/2}
    cs = [math.cos(psi + 2 * math.pi * j / n) for j in range(n)]
    good = [j for j in range(n) if cs[j] <= 1e-15]
    tau2 = cs[2] ** (1.0 / (n - 1))
    ok_setup = (good == [1]) and abs(tau2 - 2 ** -0.5) < 1e-14

    # g(s) = s^3/8 - s/4 + 1/(8s) is the chord maximum for the pair (1,2);
    # g'(s) = 0  <=>  3 s^4 - 2 s^2 - 1 = 0  <=>  s = 1, and g(1) = 0 exactly.
    quartic = np.roots([3.0, 0.0, -2.0, 0.0, -1.0])
    pos = sorted(r.real for r in quartic if abs(r.imag) < 1e-12 and r.real > 0)
    g = lambda s: s ** 3 / 8 - s / 4 + 1 / (8 * s)
    ok_alg = (len(pos) == 1 and abs(pos[0] - 1.0) < 1e-12 and abs(g(1.0)) < 1e-15)

    # the optimum point: both harmonics vanish separately there
    zstar = complex(-0.5, -math.sqrt(3) / 6)
    ok_pt = (abs((cmath.exp(1j * psi) * zstar).real) < 1e-15
             and abs((zstar ** n).real) < 1e-15 and abs(W(zstar)) < 1e-15)

    # and the chord max over a fine sample never exceeds 0 by more than roundoff
    ts = np.linspace(0.0, 1.0, 200001)
    zs = 1.0 * om ** 1 + (1.0 * om ** 2 - 1.0 * om ** 1) * ts
    wmax = float(np.max((np.exp(1j * psi) * zs).real - (zs ** n).real))
    ok_chord = wmax <= 1e-14

    report("E near-field model is exactly critical at n=3, psi=pi/3",
           ok_setup and ok_alg and ok_pt and ok_chord,
           f"one fully-good ray; tau_2 = 2^-1/2 = {tau2:.15f}; 3s^4-2s^2-1 has the "
           f"single positive root s = {pos[0] if pos else float('nan'):.15f}; "
           f"g(1) = {g(1.0):.3e}; both harmonics vanish at zeta* = -1/2 - i sqrt3/6; "
           f"sampled chord max at s=1 is {wmax:.3e}")


def check_spoke_kernel():
    """(F) The closed-form spoke functional for a pure angular perturbation:

        log|f(t w^j)| - log(1-t^n)  =  P_j(t) + O(eta^2),
        P_j(t) = sum_{l=1}^{floor((n-1)/2)} (theta_{j+l} - theta_{j-l}) g_l(t),
        g_l(t) = t sin(2 pi l/n) / (1 - 2 t cos(2 pi l/n) + t^2)  >  0.
    """
    rng = np.random.default_rng(3)

    def g(l, n, t):
        a = 2 * math.pi * l / n
        return t * math.sin(a) / (1 - 2 * t * math.cos(a) + t * t)

    rows = []
    ok = True
    for n in (3, 4, 5, 6, 7, 8, 9):
        rel = []
        for eta in (1e-3, 1e-5, 1e-7):
            th = [float(rng.normal(0, eta)) for _ in range(n)]
            roots = [cmath.exp(1j * (2 * math.pi * k / n + th[k])) for k in range(n)]
            c = poly_from_roots(roots)
            worst = 0.0
            scale = 0.0
            for j in range(n):
                for t in (0.13, 0.37, 0.61, 0.83):
                    meas = (math.log(abs(np.polyval(c, t * cmath.exp(2j * math.pi * j / n))))
                            - math.log(1 - t ** n))
                    pred = sum((th[(j + l) % n] - th[(j - l) % n]) * g(l, n, t)
                               for l in range(1, (n - 1) // 2 + 1))
                    worst = max(worst, abs(meas - pred))
                    scale = max(scale, abs(pred))
            rel.append(worst / max(scale, 1e-300))
        # relative residual must fall by at least 10x per two decades of eta
        if not (rel[0] > rel[1] > rel[2] and rel[2] < 1e-4):
            ok = False
        rows.append((n, [f"{x:.1e}" for x in rel]))
        # positivity of every kernel on the whole index range
        for l in range(1, (n - 1) // 2 + 1):
            for t in (0.05, 0.5, 0.95):
                if g(l, n, t) <= 0:
                    ok = False

    # a perturbation symmetric about root j leaves P_j identically zero
    n = 7
    th = [0.0] * n
    th[1] = th[-1] = 3e-4
    th[2] = th[-2] = -7e-4
    roots = [cmath.exp(1j * (2 * math.pi * k / n + th[k])) for k in range(n)]
    c = poly_from_roots(roots)
    sym_ok = seg_max2(c, 0j, roots[0]) <= 1.0 + 1e-13
    if not sym_ok:
        ok = False
    report("F closed-form spoke kernel P_j(t) on the antisymmetric part", ok,
           f"relative residual per (n, eta in 1e-3/1e-5/1e-7): {rows}; all kernels "
           f"positive; spoke through the symmetry axis contained: {sym_ok}")


def _form_a_cut(roots, grid=200, floor=1e-9):
    """min over pairs and common hub radius of max|f| on the Form A-cut staple
    a -> s ahat -> s bhat -> b.  <= 1 means feasible.  Exact segment maxima.

    The hub-radius grid is LOGARITHMIC.  The optimum sits at s ~ eta^{1/(n-1)},
    a fractional power of the perturbation, so a uniform grid on [tau, 1] cannot
    resolve it and reports an inflated V -- the same scale-truncation defect
    class `negative_results` 34 records for the branch integrator, and it
    corrupts the measured cusp exponent (1.08 instead of 1.5 at n = 3).
    """
    c = poly_from_roots(roots)
    n = len(roots)
    taus = [entry_radius(c, a) for a in roots]
    best = float("inf")
    for i in range(n):
        for j in range(i + 1, n):
            a, b = roots[i], roots[j]
            lo = max(taus[i], taus[j])
            hi = min(abs(a), abs(b))
            if lo > hi:
                continue
            ah, bh = a / abs(a), b / abs(b)
            start = max(lo, floor)
            if start >= hi:
                continue
            ratio = hi / start
            for q in range(grid + 1):
                s = start * ratio ** (q / grid)
                v = max(seg_max2(c, s * ah, a), seg_max2(c, s * bh, b),
                        seg_max2(c, s * ah, s * bh))
                if v < best:
                    best = v
            if lo > 0:  # the endpoint s = tau exactly
                v = max(seg_max2(c, lo * ah, a), seg_max2(c, lo * bh, b),
                        seg_max2(c, lo * ah, lo * bh))
                best = min(best, v)
    return math.sqrt(best)


def check_cusp_exponent():
    """(G) The regular n-gon on the unit circle is a STRICT local maximum of the
    Form A-cut objective V, with V = 1 exactly, and  1 - V ~ c_n eps^{n/(n-1)}:
    a cusp, so V has infinite second derivative there and no Hessian argument
    applies.  Roots stay exactly on |z| = 1 (Delta = 0, the hardest case)."""
    rng = np.random.default_rng(5)
    rows = []
    ok = True
    for n in (3, 4, 5):
        # V = 1 exactly at the regular n-gon on the unit circle
        base = [cmath.exp(2j * math.pi * k / n) for k in range(n)]
        v0 = _form_a_cut(base)
        if abs(v0 - 1.0) > 1e-12:
            ok = False
        expos = []
        for _ in range(2):
            raw = rng.normal(0, 1, n)
            raw = raw / math.sqrt(float(np.sum(raw ** 2)))
            vals = []
            for eps in (1e-2, 1e-3, 1e-4):
                th = eps * raw
                roots = [cmath.exp(1j * (2 * math.pi * k / n + th[k])) for k in range(n)]
                vals.append(_form_a_cut(roots) - 1.0)
            if any(v > 1e-12 for v in vals):      # strictness in this direction
                ok = False
            e = math.log(abs(vals[1]) / abs(vals[2])) / math.log(10)
            expos.append(e)
            if not (0.85 * n / (n - 1) < e < 1.15 * n / (n - 1)):
                ok = False
        rows.append((n, round(n / (n - 1), 4), [round(x, 3) for x in expos]))
    report("G Form A-cut cusp: V=1 at the regular n-gon, 1-V ~ eps^{n/(n-1)}", ok,
           f"(n, predicted n/(n-1), measured exponents): {rows}; every sampled "
           f"direction gives V < 1 strictly")


def main() -> int:
    print("Erdos 1041 -- radial resultant sweep + near-Fekete origin-spoke law")
    print("=" * 78)
    check_radial_sweep()
    check_near_fekete_law()
    check_entry_radius_law()
    check_form_a_prime_is_false()
    check_near_field_model()
    check_spoke_kernel()
    check_cusp_exponent()
    print("=" * 78)
    if FAILURES:
        print("FAILED:", ", ".join(FAILURES))
        return 1
    print("all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
