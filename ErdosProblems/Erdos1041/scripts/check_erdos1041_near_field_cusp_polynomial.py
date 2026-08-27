#!/usr/bin/env python3
"""Erdos #1041: the near-field cusp constant kappa_n is governed by ONE polynomial.

NearFeketeCuspLaw.md reduces the near-Fekete behaviour of `min_c L(c)/(2R)` to a
renormalised near-field excess `kappa_n(phi)`, computed on the model
`g_phi(zeta) = zeta^n + n e^{i phi} zeta`.  NearFeketeCuspPositivityProof.md
proves `kappa_3 > 0` from an algebraic graph special to `n = 3`, and records:

    "Lemma 1 is special to n = 3 ... no such form is available above degree three."

PROVENANCE: kappa_n > 0 at every degree and every ray direction is ALREADY a
theorem in this directory -- MonotoneTurningProof.md, BridgeIdentityProof.md and
ConeBoundMonotoneFunctional.md, all landed 2026-08-24.  This receipt was written
without opening those three files (research_packet.json does not carry them among
its 51 exact results), so the bound Phi in G11/G12 is a SECOND derivation of their
C_n - B_n, agreeing to 7 digits, not a new one.  What is not duplicated is the
normal form itself, the geometric-mean form of omega, and the two instrument
defects pinned in G8/G9.

This receipt validates a reduction that IS available at every degree.  Put the
hub at `w = 1` and absorb the ray direction into the level set; the model
collapses to

    Ghat(w) = w^n - n w + (n-1) = (w-1)^2 q(w),  q(w) = sum_{j<=n-2} (n-1-j) w^j

with the descent branches the two arcs of `Ghat(w) in rho e^{-i n nu}`,
`rho >= 0`, leaving the double root `w = 1`.  Writing `v := Ghat(w)^{1/n}` (so
`v` runs along a straight ray) and `w = w(v)`:

    omega(s) := |dw/dv| = s^{n-1}/|w^{n-1}-1| = n |Ghat|^{(n-1)/n} / |Ghat'|
    ex       = 1 + int_0^oo (omega - 1) ds          (a RADIAL DEFICIT)
    kappa_n  = 2 - ex_+ - ex_-

and the exact identity, which is an equality rather than an estimate and needs
no monotonicity hypothesis (Lemma 2 of NearFeketeCuspPositivityProof.md needs
`P` monotone; that hypothesis does hold here -- `Re w' > 0` was checked along
every branch below -- but the identity does not require it):

    ex = 1 - cos(alpha) + int_0^oo (Im w')^2 / (|w'| + Re w') ds ,

since |w'| - Re w' = (Im w')^2/(|w'| + Re w') exactly, and int (Re w' - 1) ds
= -cos(alpha) exactly because w(v) - v vanishes at infinity and equals 1 at the
hub.  Also exact, and the reason the extremal family is the constant function:

    omega = (GM of distances to the n roots of Ghat
             / GM of distances to the n-1 critical points of Ghat)^(n-1),

so omega == 1 identically for Ghat = w^n, which is the descent of z^n - lambda.

Gates (each FAILS loudly, none is a bare supremum):

  G1  kappa_n from Ghat reproduces the four recorded constants of
      NearFeketeCuspLaw.md (n = 3,4,5,6) to 1e-6.
  G2  the two n = 3 per-branch excesses reproduce the recorded
      ex_1 = 1.2350942613 and ex_2 = 0.156884427 to 1e-6.
  G3  the exact identity agrees with the direct radial-deficit integral to 1e-7.
  G4  the MEASURED exit directions at the binding ray direction are the closed
      forms alpha_+ = -pi(n-2)/(n(n-1)) and alpha_- = pi/(n-1) (adjacent pair).
  G5  the closed form  T(n) = 2 cos(pi/n) cos(pi/(n(n-1)))  reproduces the
      "target" row of NearFeketeCuspPositivityProof.md section 4 to 1e-4.
      T is min over ray direction of max over the n-1 hubs of cos g_1 + cos g_2;
      this PROVES a row that file records only as a measurement.
  G6  kappa_n > 0 at every tested degree, and the two-resolution spread is at
      least 100x below the reported margin (instrument guard, negative_results
      entry 43: never report a value whose grid error is the size of the claim).
  G7  saddle-connection guard: the distance from each traced branch to the OTHER
      critical points eta_k = exp(2 pi i k/(n-1)), k != 0, stays above 0.05 (a
      collision there is the kappa = -inf direction: a real bifurcation, not a bug).

The remaining gates support a PROOF SKELETON for kappa_n > 0 at every degree.
Two further exact facts (both proved, see NearFieldCuspPolynomial.md section 6):

    int_0^oo Im w' ds = sin(alpha)          [from int (1 - w') dv = e^{-i alpha}]
    D := ex - (1 - cos alpha) = int |tan(beta/2)| * |Im w'| ds,   beta := arg w'

so if Im w' keeps ONE SIGN then int |Im w'| ds = |sin alpha| and

    D <= |sin alpha| * sup_Gamma |tan(beta/2)| .

Numerically sup|tan(beta/2)| is attained AT THE HUB, where beta has the exact
analytic value beta(0) = (n/2 - 1) alpha, giving the closed-form lower bound

    kappa_n >= Phi(n, psi) := sum_pm [ cos a_pm - sin|a_pm| tan((n-2)|a_pm|/4) ].

  G8  Im w' is single-signed, tested truncation-free as int|Im w'| = |int Im w'|
      to 1e-9, plus a convergence check against the exact |sin alpha|.
      MEASUREMENT BOUNDARY, and it bit: reading alpha off the traced endpoint
      instead of using its closed form injects an error ~ S^{1-n}, which is the
      SIZE of Im w' in the far field, and manufactured a resolution-independent
      "sign flip" over the last 30% of the trace at n = 3, 4, 5.  alpha is now
      the exact ray direction; the endpoint angle is only G4's check.
  G9  sup |beta| over the branch equals |beta(0)| = (n/2-1)|alpha| to 1e-4.
      MEASUREMENT BOUNDARY, and it bit: |w'| underflows near the hub (|w'| ~
      1e-54 at n = 10), Re w' cancels to 1e-69, and a naive sup reads exactly
      pi/2 at EVERY degree -- a clean-looking constant that is pure roundoff.
      The sup is therefore taken only where |w - 1| > 1e-7, and beta(0) is
      supplied by its analytic limit, not by the float.
  G10 the mechanism: S := Ghat Ghat''/Ghat'^2 = ((n-1)/n) w^{n-2} q(w)/p(w)^2
      has Im S of constant sign = sign(alpha) along Gamma, with S(1) = 1/2 and
      S(infinity) = (n-1)/n both REAL.  Since d arg(Ghat')/d rho = Im(S)/rho,
      that sign condition is exactly the monotone turning that forces G9.
  G11 Phi(n, psi) > 0 for every degree 3..200 across the whole hub window
      |psi - pi/n| <= pi/(n(n-1)); the minimum over all of that is 0.385986,
      attained at n = 3.
  G12 the bound dominates the measurement: D <= |sin alpha| tan(|beta(0)|/2)
      on every branch, and Phi(n) <= kappa_n on every traced row.

Nothing here proves Erdos #1041.  (SIGN) -- gate G10 -- is measured HERE, but it
is not an open corpus gate: it is the same statement as the monotone turning with
constant sign that MonotoneTurningProof.md proves at every degree and
ConeBoundMonotoneFunctional.md proves again and extends to every ray direction.
So the chain

    G10  ==>  G9  ==>  kappa_n >= Phi(n) > 0 at every degree

is a second route to a landed theorem, and Phi is that theorem's own C_n - B_n.
Proved by ordinary mathematics and not duplicated: the normal form, the
radial-deficit reading, omega as a ratio of geometric means, and the closed form
in G5.  Proposition 5's stronger reading -- that phi = 0 is argmin_phi kappa_n --
is WITHDRAWN per RayDirectionScopeLimit.md section 4.
"""
from __future__ import annotations

import json
import math
import sys

import numpy as np

TOL_RECORDED = 1e-6
# The residual gap between the two forms is the direct form's OMITTED quadratic
# tail int_S^oo (|w'| - Re w') ds ~ S^{4-2n}/(2n-4): 5.6e-8 at n = 3, S = 3000,
# and negligible above.  Measured worst gap 1.4e-7.  The identity form is the
# accurate one; this tolerance sizes the cruder comparison, not the claim.
TOL_IDENTITY = 1e-6
TOL_TARGET = 1e-4
SADDLE_FLOOR = 0.05
SPREAD_RATIO = 100.0

# NearFeketeCuspLaw.md section 4, "Measured limits at phi = 0".
RECORDED_KAPPA = {3: 0.60802134, 4: 1.0301197, 5: 1.2585783, 6: 1.3989124}
# NearFeketeCuspPositivityProof.md section 1, table of graph-derived constants.
RECORDED_EX_N3 = {"long": 1.2350942613, "short": 0.156884427}
# NearFeketeCuspPositivityProof.md section 4, "target" row.
RECORDED_TARGET = {3: 0.8660, 4: 1.3660, 5: 1.5981, 6: 1.7226,
                   8: 1.8449, 10: 1.9010, 12: 1.9313}


def _q(n: int, w: complex) -> complex:
    r = 0.0 + 0j
    for j in range(n - 2, -1, -1):
        r = r * w + (n - 1 - j)
    return r


def _dq(n: int, w: complex) -> complex:
    r = 0.0 + 0j
    for j in range(n - 2, 0, -1):
        r = r * w + j * (n - 1 - j)
    return r


def _solve(n: int, target: complex, guess: complex, root_sqrt: complex) -> complex:
    """Solve Ghat(w) = target. Near the hub solve the square-root-resolved
    equation Psi(xi) = xi sqrt(q(1+xi)) = root_sqrt, whose root is SIMPLE, so
    Newton stays quadratic where plain Newton would crawl on a double root."""
    w = guess
    for _ in range(80):
        xi = w - 1.0
        if abs(xi) < 0.30:
            qq = _q(n, w)
            sq = np.sqrt(qq)
            fun = xi * sq - root_sqrt
            der = sq + xi * _dq(n, w) / (2 * sq)
        else:
            fun = w ** n - n * w + (n - 1) - target
            der = n * (w ** (n - 1) - 1.0)
        if der == 0:
            break
        step = fun / der
        w = w - step
        if abs(step) < 1e-15 * max(1.0, abs(w)):
            break
    return w


def trace(n: int, nu: float, sign: int, s_max: float, npts: int, s_min: float = 1e-14):
    """One descent branch, parametrised by s = |v| = |Ghat|^{1/n} on a log mesh.

    sign selects which of the two arcs leaves the hub (the two square roots).
    The mesh is geometric because the branch crosses many decades of |w-1|
    inside a vanishing range of s -- negative_results entry 33's class.
    """
    alpha_seed = -nu if sign > 0 else (2 * math.pi / n - nu)
    lg = np.linspace(math.log(s_min), math.log(s_max), npts)
    s = np.exp(lg)
    w = np.empty(npts, dtype=complex)
    cur = 1.0 + np.exp(1j * n * alpha_seed / 2.0) * s_min ** (n / 2.0) / np.sqrt(n * (n - 1) / 2.0)
    for k in range(npts):
        tgt = (s[k] * np.exp(1j * alpha_seed)) ** n
        rst = np.exp(1j * n * alpha_seed / 2.0) * s[k] ** (n / 2.0)
        cur = _solve(n, tgt, cur, rst)
        w[k] = cur
    return s, lg, w


def _simpson_log(vals: np.ndarray, lg: np.ndarray) -> float:
    m = len(lg) - 1
    if m % 2:
        vals, lg, m = vals[:-1], lg[:-1], m - 1
    h = (lg[-1] - lg[0]) / m
    tot = vals[0] + vals[-1] + 4 * np.sum(vals[1:-1:2]) + 2 * np.sum(vals[2:-2:2])
    return float(tot * h / 3)


def branch(n: int, nu: float, sign: int, s_max: float | None = None, npts: int = 8001) -> dict:
    if s_max is None:
        s_max = 3000.0 if n == 3 else (300.0 if n == 4 else (80.0 if n <= 6 else 30.0))
    s, lg, w = trace(n, nu, sign, s_max, npts)
    # alpha is EXACT (it is the ray direction the branch was traced along).
    # Do NOT read it off the endpoint: w(S) = v + h with h = O(S^{2-n}), so
    # arg(w(S)) carries an error ~ S^{1-n} -- which is exactly the size of
    # Im w' out there (1e-7 at n = 3, S = 3000).  Using the measured angle put
    # a spurious sign flip into Im w' over the last 30% of the trace at n = 3,4,5,
    # resolution-independent and therefore easy to mistake for a real feature.
    # The measured endpoint angle is kept only as the convergence check in G4.
    alpha = -nu if sign > 0 else (2 * math.pi / n - nu)
    alpha_measured = float(np.angle(w[-1]))
    v = s * np.exp(1j * alpha)
    # Saddle guard is about the OTHER critical points of Ghat.  w = 1 is itself
    # a critical point (it is the hub), so |w^{n-1}-1| -> 0 at the start of every
    # trace by construction; guarding on that would fire on the hub, not on a
    # collision.  Guard on the distance to eta_k = exp(2 pi i k/(n-1)), k != 0.
    etas = np.exp(2j * np.pi * np.arange(1, n - 1) / (n - 1)) if n >= 3 else np.array([])
    if etas.size:
        saddle_gap = float(np.min(np.abs(w[:, None] - etas[None, :])))
    else:
        saddle_gap = float("inf")
    wp = v ** (n - 1) / (w ** (n - 1) - 1.0)            # w'(v)
    om = np.abs(wp)
    # Tail-corrected direct form.  int_S^oo (omega-1) ds = int_S^oo Re h' ds
    # + O(S^{3-2n}) = S - Re(e^{-i alpha} w(S)) + O(S^{3-2n}); without this the
    # direct form carries an O(S^{2-n}) truncation (3e-4 at n=3, S=3000) that
    # the identity form does not, and the two would appear to disagree.
    tail = s[-1] - float((w[-1] * np.exp(-1j * alpha)).real)
    ex_direct = 1.0 + _simpson_log((om - 1.0) * s, lg) + tail
    den = om + wp.real
    quad = np.where(om > 1e-13, wp.imag ** 2 / np.where(den > 0, den, 1.0), 0.0)
    quad = np.where(den > 0, quad, 0.0)
    ex_identity = 1.0 - math.cos(alpha) + _simpson_log(quad * s, lg)

    # --- proof-skeleton quantities -------------------------------------------
    # Everything angular is read only OUTSIDE the underflow shell |w-1| <= 1e-7.
    # Inside it |w'| is below 1e-13 (far below at high degree) and Re w' has
    # cancelled entirely; a sup taken there reports exactly pi/2 at every degree,
    # which looks like a theorem and is roundoff.  See gate G9.
    live = np.abs(w - 1.0) > 1e-7
    beta = np.angle(wp)
    beta_hub_analytic = (n / 2.0 - 1.0) * alpha           # analytic limit at the hub
    sup_beta = float(np.max(np.abs(beta[live]))) if live.any() else 0.0
    # Single-sign test, free of far-field truncation: if Im w' keeps one sign
    # then int|Im w'| and |int Im w'| agree EXACTLY on any mesh.  Comparing
    # int|Im w'| against |sin alpha| instead would only measure the tail
    # (7.7e-4 at n = 3, S = 3000, since Im w' ~ s^{1-n}).
    int_abs_im = _simpson_log(np.abs(wp.imag) * s, lg)
    int_signed_im = abs(_simpson_log(wp.imag * s, lg))
    # S = Ghat Ghat''/Ghat'^2, the turning mechanism; S(1)=1/2, S(oo)=(n-1)/n.
    p_w = np.zeros_like(w)
    for _ in range(n - 1):
        p_w = p_w * w + 1.0                               # p = 1+w+...+w^{n-2}
    q_w = np.zeros_like(w)
    for j in range(n - 2, -1, -1):
        q_w = q_w * w + (n - 1 - j)
    S = ((n - 1) / n) * w ** (n - 2) * q_w / p_w ** 2
    ims = S.imag[live]
    sig = math.copysign(1.0, alpha)
    frac_right_sign = float(np.mean(sig * ims >= -1e-13)) if ims.size else 1.0

    return {
        "alpha": alpha,
        "alpha_measured": alpha_measured,
        "s_max": float(s[-1]),
        "ex_direct": ex_direct,
        "ex_identity": ex_identity,
        "deficit": ex_identity - (1.0 - math.cos(alpha)),
        "max_omega": float(om.max()),
        "min_saddle": saddle_gap,
        "sup_beta": sup_beta,
        "beta_hub_analytic": beta_hub_analytic,
        "int_abs_im_wprime": int_abs_im,
        "int_signed_im_wprime": int_signed_im,
        "abs_sin_alpha": abs(math.sin(alpha)),
        "sin_alpha_truncation_gap": abs(int_abs_im - abs(math.sin(alpha))),
        "imS_fraction_right_sign": frac_right_sign,
        "S_at_hub": float(S[live][0].real) if live.any() else float("nan"),
        "S_at_infinity": float(S[-1].real),
        "bound_D": abs(math.sin(alpha)) * math.tan(abs(beta_hub_analytic) / 2.0),
    }


def kappa(n: int, nu: float, npts: int = 8001) -> dict:
    a = branch(n, nu, +1, npts=npts)
    b = branch(n, nu, -1, npts=npts)
    return {
        "plus": a,
        "minus": b,
        "kappa_direct": 2.0 - a["ex_direct"] - b["ex_direct"],
        "kappa_identity": 2.0 - a["ex_identity"] - b["ex_identity"],
        "T_measured": math.cos(a["alpha"]) + math.cos(b["alpha"]),
    }


def binding_nu(n: int) -> float:
    """The ray direction that minimises the max over the n-1 hubs.

    The n-1 hubs sit at exit-angle offsets spaced 2 pi/(n(n-1)) which tile
    [0, 2 pi/n); T(psi) = 2 cos(pi/n) cos(psi - pi/n) peaks at psi = pi/n, so
    the worst ray direction is the symmetric straddle at distance pi/(n(n-1)).
    That is phi = 0 in NearFeketeCuspLaw.md's parametrisation.
    """
    return math.pi / n - math.pi / (n * (n - 1))


def target_closed_form(n: int) -> float:
    return 2 * math.cos(math.pi / n) * math.cos(math.pi / (n * (n - 1)))


def phi_term(n: int, x: float) -> float:
    """cos a - sin|a| tan((n-2)|a|/4): the per-branch closed-form lower bound."""
    a = abs(x)
    return math.cos(a) - math.sin(a) * math.tan((n - 2) * a / 4.0)


def phi_bound(n: int, psi: float) -> float:
    """Phi(n, psi): closed-form lower bound for kappa at a hub with offset psi."""
    return phi_term(n, psi) + phi_term(n, 2 * math.pi / n - psi)


def main() -> int:
    failures: list[str] = []
    report: dict = {"schema": "erdos1041_near_field_cusp_polynomial/1", "gates": {}}

    # ---- G5 first: closed form for the recorded "target" row (pure arithmetic).
    tgt_rows = []
    for n, rec in RECORDED_TARGET.items():
        got = target_closed_form(n)
        ok = abs(got - rec) <= TOL_TARGET
        tgt_rows.append({"n": n, "closed_form": got, "recorded": rec, "ok": ok})
        if not ok:
            failures.append(f"G5 target n={n}: closed form {got:.6f} vs recorded {rec}")
    report["gates"]["G5_target_closed_form"] = {
        "formula": "T(n) = 2 cos(pi/n) cos(pi/(n(n-1)))",
        "rows": tgt_rows,
        "verdict": "pass" if all(r["ok"] for r in tgt_rows) else "fail",
    }

    # ---- G1/G2/G3/G4/G6/G7 on the traced model.
    rows = []
    prev_kappa = None
    monotone = True
    for n in (3, 4, 5, 6, 7, 8, 10, 12):
        nu = binding_nu(n)
        fine = kappa(n, nu, npts=8001)
        coarse = kappa(n, nu, npts=2001)
        spread = abs(fine["kappa_identity"] - coarse["kappa_identity"])
        kap = fine["kappa_identity"]

        alpha_plus_cf = -math.pi * (n - 2) / (n * (n - 1))
        alpha_minus_cf = math.pi / (n - 1)
        # The endpoint angle converges to the closed form only at rate S^{1-n}
        # (w(S) = v + O(S^{2-n})), so the tolerance is sized by that, not flat.
        for side, want in (("plus", alpha_plus_cf), ("minus", alpha_minus_cf)):
            r4 = fine[side]
            tol4 = 20.0 * r4["s_max"] ** (1 - n) + 1e-12
            if abs(r4["alpha_measured"] - want) > tol4:
                failures.append(
                    f"G4 exit direction n={n} {side}: measured"
                    f" {r4['alpha_measured']:.12f} vs closed form {want:.12f}"
                    f" (tol {tol4:.2e})")

        for side in ("plus", "minus"):
            r = fine[side]
            d = abs(r["ex_direct"] - r["ex_identity"])
            if d > TOL_IDENTITY:
                failures.append(f"G3 identity n={n} {side}: gap {d:.3e}")
            if r["min_saddle"] < SADDLE_FLOOR:
                failures.append(
                    f"G7 saddle guard n={n} {side}: dist to other crit pts ="
                    f" {r['min_saddle']:.3e}")
            # G8: Im w' single-signed. Truncation-free form: int|Im w'| = |int Im w'|.
            g8 = abs(r["int_abs_im_wprime"] - r["int_signed_im_wprime"])
            if g8 > 1e-9:
                failures.append(
                    f"G8 single sign n={n} {side}: int|Im w'| ="
                    f" {r['int_abs_im_wprime']:.9f} but |int Im w'| ="
                    f" {r['int_signed_im_wprime']:.9f}")
            # Convergence check on the same quantity against its exact value; the
            # residual here is the far-field tail, sized S^{2-n}, not a sign defect.
            if r["sin_alpha_truncation_gap"] > 1e-3:
                failures.append(
                    f"G8 tail n={n} {side}: int|Im w'| = {r['int_abs_im_wprime']:.6f}"
                    f" vs |sin a| = {r['abs_sin_alpha']:.6f}")
            # G9: sup|beta| equals the analytic hub value.
            g9 = abs(r["sup_beta"] - abs(r["beta_hub_analytic"]))
            if g9 > 1e-4:
                failures.append(
                    f"G9 sup beta n={n} {side}: {r['sup_beta']:.6f} vs"
                    f" |beta(0)| = {abs(r['beta_hub_analytic']):.6f}")
            # G10: Im S single-signed with the sign of alpha; S real at both ends.
            if r["imS_fraction_right_sign"] < 1.0 - 1e-12:
                failures.append(
                    f"G10 Im S sign n={n} {side}: only"
                    f" {r['imS_fraction_right_sign']:.6f} of samples have sign(alpha)")
            if abs(r["S_at_hub"] - 0.5) > 1e-3 or abs(r["S_at_infinity"] - (n - 1) / n) > 1e-3:
                failures.append(
                    f"G10 S endpoints n={n} {side}: S(1) = {r['S_at_hub']:.6f}"
                    f" (want 0.5), S(oo) = {r['S_at_infinity']:.6f}"
                    f" (want {(n - 1) / n:.6f})")
            # G12: the closed-form bound dominates the measured deficit.
            if r["deficit"] > r["bound_D"] + 1e-9:
                failures.append(
                    f"G12 bound n={n} {side}: D = {r['deficit']:.6f} >"
                    f" |sin a| tan(|beta(0)|/2) = {r['bound_D']:.6f}")

        phi = phi_bound(n, nu)
        if phi > kap + 1e-9:
            failures.append(f"G12 Phi n={n}: Phi = {phi:.6f} > kappa = {kap:.6f}")
        if phi <= 0:
            failures.append(f"G11 Phi n={n}: {phi:.6f} <= 0")

        if kap <= 0:
            failures.append(f"G6 kappa n={n}: {kap:.6f} <= 0")
        if spread * SPREAD_RATIO > kap:
            failures.append(
                f"G6 resolution guard n={n}: spread {spread:.3e} not <"
                f" kappa/{SPREAD_RATIO:g} = {kap / SPREAD_RATIO:.3e}")
        if prev_kappa is not None and kap <= prev_kappa:
            monotone = False
        prev_kappa = kap

        if n in RECORDED_KAPPA:
            rec = RECORDED_KAPPA[n]
            if abs(kap - rec) > TOL_RECORDED:
                failures.append(f"G1 kappa n={n}: {kap:.9f} vs recorded {rec}")

        rows.append({
            "n": n,
            "nu_binding": nu,
            "alpha_plus": fine["plus"]["alpha"],
            "alpha_minus": fine["minus"]["alpha"],
            "ex_plus": fine["plus"]["ex_identity"],
            "ex_minus": fine["minus"]["ex_identity"],
            "kappa": kap,
            "kappa_recorded": RECORDED_KAPPA.get(n),
            "T_measured": fine["T_measured"],
            "T_closed_form": target_closed_form(n),
            "deficit_sum": fine["plus"]["deficit"] + fine["minus"]["deficit"],
            "max_omega": max(fine["plus"]["max_omega"], fine["minus"]["max_omega"]),
            "min_saddle": min(fine["plus"]["min_saddle"], fine["minus"]["min_saddle"]),
            "two_resolution_spread": spread,
            "phi_lower_bound": phi_bound(n, nu),
            "sup_beta_over_hub_value": [
                fine["plus"]["sup_beta"] / abs(fine["plus"]["beta_hub_analytic"]),
                fine["minus"]["sup_beta"] / abs(fine["minus"]["beta_hub_analytic"]),
            ],
        })

    # ---- G11: the closed-form bound over the whole hub window, every degree.
    window_min = float("inf")
    window_arg = None
    for n in range(3, 201):
        lo = math.pi / n - math.pi / (n * (n - 1))
        hi = math.pi / n + math.pi / (n * (n - 1))
        for k in range(201):
            psi = lo + (hi - lo) * k / 200
            val = phi_bound(n, psi)
            if val < window_min:
                window_min, window_arg = val, (n, psi)
    if window_min <= 0:
        failures.append(f"G11 window: min Phi = {window_min:.6f} <= 0 at {window_arg}")
    report["gates"]["G11_phi_positive_over_window"] = {
        "degrees_scanned": "3..200",
        "window": "|psi - pi/n| <= pi/(n(n-1))",
        "min_Phi": window_min,
        "attained_at_degree": window_arg[0] if window_arg else None,
        "note": ("Phi is the closed-form consequence of G10; its minimum over every "
                 "degree and the whole window is attained at n = 3, where the "
                 "independent NearFeketeCuspPositivityProof.md argument gives the "
                 "weaker lower bound 0.211899."),
    }

    # G2: n = 3 per-branch excesses.
    n3 = rows[0]
    long_side, short_side = max(n3["ex_plus"], n3["ex_minus"]), min(n3["ex_plus"], n3["ex_minus"])
    for label, got in (("long", long_side), ("short", short_side)):
        rec = RECORDED_EX_N3[label]
        if abs(got - rec) > TOL_RECORDED:
            failures.append(f"G2 n=3 {label} branch: {got:.10f} vs recorded {rec}")
    report["gates"]["G2_n3_per_branch"] = {
        "long": long_side, "long_recorded": RECORDED_EX_N3["long"],
        "short": short_side, "short_recorded": RECORDED_EX_N3["short"],
    }

    report["rows"] = rows
    report["kappa_monotone_in_degree"] = monotone
    report["max_omega_over_all_rows"] = max(r["max_omega"] for r in rows)
    report["verdict"] = "pass" if not failures else "fail"
    report["failures"] = failures
    report["claim_boundary"] = (
        "PROVED in the companion source note, not by this checker: the all-degree "
        "normal form, radial-deficit identity, and closed form for the far-field "
        "target T. CHECKED here only as finite numerical and symbolic evidence: "
        "G1--G12, including the sign sweep and degrees 3..200 for Phi. PROVED in "
        "separate ordinary-proof sources: limit-model kappa_n(phi) > 0 for every "
        "degree and direction. The phi=0 calculation concerns T, not argmin kappa. "
        "NOT proved here: universal monotonicity in degree, finite-perturbation "
        "remainder control, the degenerate h'(0)=0 case, or Erdos #1041."
    )

    print(json.dumps(report, indent=2, default=float))
    if failures:
        print("\nFAILURES:", file=sys.stderr)
        for f in failures:
            print("  " + f, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
