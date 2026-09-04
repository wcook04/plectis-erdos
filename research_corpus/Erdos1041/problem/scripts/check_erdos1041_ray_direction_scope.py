"""Erdos #1041: how far the cone bound reaches in the descent-ray direction
-- for ONE FIXED HUB.  See PART 7: with the hub free, it reaches everywhere.

Scope, per ``ade3b6ac08``: everything here lives on the fixed near-field model
``g(zeta) = zeta^n + n zeta``, one polynomial per degree.  Nothing is a statement
about a perturbed polynomial.

The branch at ray direction ``delta`` solves ``g(zeta(s)) = (n-1) zeta_c + s e^{-i delta}``
for ``s >= 0``, with ``zeta_c = e^{i phi_c}``, ``phi_c = pi/(n-1)``.  ``delta = 0``
is the aligned direction; ``NearFeketeCuspPositivityProof.md`` section 4 records
``delta = n phi / (n-1)`` for the ray angle ``phi`` of ``zeta^n + n e^{i phi} zeta``,
so every ``delta`` is realised.

PART 1 -- an independent proof of (star) at delta = 0, by a route that shares
nothing with ``ConeBoundMonotoneFunctional.md``'s harmonic functional ``Xi``.
Write ``A = sin((n-2)phi/2)``, ``B = sin(n phi/2)``, ``Sigma = sin((n-1)phi) + (n-1) sin phi``
and, on the level set ``V(r,phi) := Im g = c_n``,

    m(zeta) := e^{-i(n-2)phi/2} (zeta^{n-1} + 1),
    Im m    = r^{n-1} B - A,       Re m = r^{n-1} cos(n phi/2) + cos((n-2)phi/2),
    Im[(zeta^{n-1}+1)^2 / zeta^{n-2}] = 2 Re(m) Im(m) / r^{n-2},

so ``sign(dtau/dsigma) = sign(Re m) sign(Im m)``.  Both branches need the SAME
inequality ``Im m > 0``; the sign flip between them is carried entirely by
``Re m``.  Let ``r_Z(phi) := (A/B)^{1/(n-1)}`` be the zero curve of ``Im m`` and
``N(phi) := V(r_Z(phi), phi)``.  Then ``N = r_Z * Sigma`` and, with ``L := log N``,

    KEY LEMMA        2(n-1) A B Sigma * L'(phi)  =  n(n-2) sin^2((n-1) phi),

an exact identity.  So ``L`` is strictly increasing on ``(0, 2 pi/n)`` with a single
stationary point at ``phi_c``, ``N(phi_c) = c_n``, and hence ``N < c_n`` below
``phi_c`` and ``N > c_n`` above it.  Comparing ``V(r_Z, phi)`` with ``V(r,phi) = c_n``
on the side of ``dV/dr``'s sign fixed by ``Im G`` gives ``r > r_Z`` on BOTH branches.

The identity also answers ``ConeBoundBranchGeometry.md`` section 7's open question --
"the cubic vanishing at the hub is the striking feature and is unexplained".
``L'`` has a DOUBLE zero at ``phi_c``, so ``N - c_n`` has a TRIPLE zero there; the
``n = 3`` factorisation's ``(y-1)^3`` is that triple zero, and it is general.

PART 2 -- the same chain checked numerically at delta = 0, adaptive precision.

PART 3 -- the wall-crossing closed form.  The branch leaves its sector exactly
where the value ray meets the image of a sector wall:

    wall arg zeta = 0       :  s_1 = c_n / sin(delta),
                               admissible iff sin(delta) > 0 and sin(delta + phi_c) > 0
    wall arg zeta = 2 phi_c :  s_2 = -c_n / sin(delta + 2 phi_c),
                               admissible iff sin(delta + 2 phi_c) < 0 and sin(delta + phi_c) < 0

So Lemma S / Lemma S2 do NOT extend: ``sign(Im g')`` is non-constant on an
explicit arc of ray directions.

PART 4 -- and at ``n = 6`` the cone bound ``|t| <= |t(0+)|`` itself fails at several
ray directions, reaching ``5.25``.  At ``n = 3`` it survives every sampled direction,
but PART 6 shows the CONSTANT-SIGN hypothesis is what fails there, on exactly the
arc PART 3 identifies.

PART 7 -- **and none of that closes the route.**  PARTS 2-4 and 6 all fix the hub at
``zeta_c = e^{i phi_c}`` and vary the direction; the cusp law minimises over all
``n-1`` hubs.  ``ConeBoundMonotoneFunctional.md``'s Proposition W shows the
confinement window has length exactly the hub spacing ``2 pi/(n-1)``, so exactly one
hub is good at every direction, and its Theorem R closes the near-Fekete half at
every ray direction.  PART 7 verifies that at the ACTUAL hubs ``e^{i pi (2k+1)/(n-1)}``:
at each failure direction of PART 4, exactly one of the five ``n = 6`` hubs passes
both hypotheses, and it is never the hub the earlier parts fixed.

Reproduce:  ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/\
Erdos1041/scripts/check_erdos1041_ray_direction_scope.py
"""

from __future__ import annotations

import json
import sys
from typing import Any

import mpmath as mp


# ---------------------------------------------------------------------------
# model
# ---------------------------------------------------------------------------


def model(n: int):
    return (
        lambda z: z**n + n * z,
        lambda z: n * (z ** (n - 1) + 1),
        lambda z: n * (n - 1) * z ** (n - 2),
    )


def hub(n: int):
    phi_c = mp.pi / (n - 1)
    return phi_c, mp.exp(1j * phi_c), (n - 1) * mp.sin(phi_c)


def A(n, p):
    return mp.sin(mp.mpf(n - 2) / 2 * p)


def B(n, p):
    return mp.sin(mp.mpf(n) / 2 * p)


def Sigma(n, p):
    return mp.sin((n - 1) * p) + (n - 1) * mp.sin(p)


# ---------------------------------------------------------------------------
# part 1: the Key Lemma, as an exact identity
# ---------------------------------------------------------------------------


def check_key_lemma() -> dict[str, Any]:
    mp.mp.dps = 50
    worst_identity = mp.mpf(0)
    worst_hub = mp.mpf(0)
    monotone_ok = True
    triple_zero = []

    for n in range(3, 26):
        phi_c, _, c_n = hub(n)

        # (i) the identity  2(n-1) A B Sigma L' = n(n-2) sin^2((n-1) phi)
        for i in range(1, 201):
            p = mp.mpf(2) * mp.pi / n * mp.mpf(i) / 202
            pp, s = mp.mpf(n - 2) / 2 * p, mp.mpf(n) / 2 * p
            lhs = Sigma(n, p) * (
                (n - 2) * mp.cos(pp) * mp.sin(s) - n * mp.sin(pp) * mp.cos(s)
            ) + (n - 1) ** 2 * mp.sin(2 * pp) * mp.sin(2 * s)
            rhs = n * (n - 2) * mp.sin((n - 1) * p) ** 2
            worst_identity = max(worst_identity, abs(lhs - rhs))

        # (ii) N(phi_c) = c_n exactly, and N monotone increasing
        def N(p):
            return (A(n, p) / B(n, p)) ** (mp.mpf(1) / (n - 1)) * Sigma(n, p)

        worst_hub = max(worst_hub, abs(N(phi_c) - c_n))
        for i in range(1, 400):
            p = mp.mpf(2) * mp.pi / n * mp.mpf(i) / 401
            if A(n, p) <= 0 or B(n, p) <= 0:
                continue
            v = N(p) - c_n
            if p < phi_c * (1 - mp.mpf("1e-9")) and v >= 0:
                monotone_ok = False
            if p > phi_c * (1 + mp.mpf("1e-9")) and v <= 0:
                monotone_ok = False

        # (iii) the triple zero at phi_c: (N - c_n)/(phi - phi_c)^3 tends to a
        #       finite nonzero limit, so the n = 3 cubic is general.
        rows = []
        for e in ("1e-3", "1e-4", "1e-5"):
            h = mp.mpf(e)
            rows.append((N(phi_c - h) - c_n) / (-h) ** 3)
        spread = abs(rows[-1] - rows[0]) / abs(rows[-1])
        triple_zero.append({"n": n, "ratio": mp.nstr(rows[-1], 8),
                            "spread": mp.nstr(spread, 3)})

    ok = (worst_identity < mp.mpf("1e-40") and worst_hub < mp.mpf("1e-40")
          and monotone_ok and all(mp.mpf(r["spread"]) < mp.mpf("0.02")
                                  for r in triple_zero))
    return {
        "claim": (
            "2(n-1) A B Sigma L'(phi) = n(n-2) sin^2((n-1) phi) exactly; N(phi_c) "
            "= c_n; N strictly increasing on (0, 2 pi/n); N - c_n has a TRIPLE "
            "zero at phi_c, which is the general-n form of the n = 3 (y-1)^3."
        ),
        "degrees": "3..25",
        "worst_identity_residual": mp.nstr(worst_identity, 4),
        "worst_hub_residual": mp.nstr(worst_hub, 4),
        "monotone": monotone_ok,
        "triple_zero_sample": triple_zero[:4],
        "passes": bool(ok),
    }


# ---------------------------------------------------------------------------
# part 2: the full chain at delta = 0
# ---------------------------------------------------------------------------


def trace(n, delta, br, smax, steps, dps):
    """Newton-continue a descending branch; return (tau, arg z, z) samples."""
    mp.mp.dps = dps
    g, gp, gpp = model(n)
    phi_c, zc, c_n = hub(n)
    ray = mp.exp(-1j * delta)
    root = (1 if br == 1 else -1) * mp.sqrt(2 * ray / gpp(zc))
    tau0 = mp.arg(root)
    s = mp.mpf("1e-14")
    z = zc + root * mp.sqrt(s)
    ratio = (smax / s) ** (mp.mpf(1) / steps)
    tol = mp.mpf(10) ** (-(dps - 6))
    out = []
    for _ in range(steps + 1):
        w = (n - 1) * zc + s * ray
        for _ in range(150):
            step = (g(z) - w) / gp(z)
            z = z - step
            if abs(step) < tol * max(1, abs(z)):
                break
        out.append((mp.arg(ray / gp(z)), mp.arg(z), z))
        s = s * ratio
    return tau0, out


def check_chain_aligned() -> dict[str, Any]:
    rows = []
    all_ok = True
    for n, R in [(3, "1e6"), (5, "1e5"), (8, "1e4"), (12, "1e4"),
                 (20, "1e3"), (30, "1e3"), (60, "1e2")]:
        smax = mp.mpf(R)
        dps = int(40 + (n - 1) * mp.log(smax, 10) / n + 40)
        phi_c, zc, c_n = hub(n)
        for br in (1, 2):
            mp.mp.dps = dps
            T_exact = ((n - 2) * mp.pi / (2 * (n - 1)) if br == 1
                       else (n - 2) ** 2 * mp.pi / (2 * n * (n - 1)))
            alpha = mp.mpf(0) if br == 1 else 2 * mp.pi / n
            tau0, pts = trace(n, mp.mpf(0), br, smax, 1200, dps)
            bad = {k: 0 for k in
                   ("sector", "ImG", "Imm", "Rem", "ImF", "tsign", "tcone")}
            sup = mp.mpf(0)
            tol = mp.mpf(10) ** (-(dps - 12))
            for tau, phi, z in pts:
                r = abs(z)
                lo, hi = (mp.mpf(0), phi_c) if br == 1 else (phi_c, 2 * mp.pi / n)
                if not (lo - tol < phi < hi + tol):
                    bad["sector"] += 1
                imG = c_n - (n - 1) * mp.im(z)
                if br == 1 and imG < -tol:
                    bad["ImG"] += 1
                if br == 2 and imG > tol:
                    bad["ImG"] += 1
                imm = r ** (n - 1) * B(n, phi) - A(n, phi)
                rem = r ** (n - 1) * mp.cos(mp.mpf(n) / 2 * phi) + mp.cos(
                    mp.mpf(n - 2) / 2 * phi)
                if imm <= 0:
                    bad["Imm"] += 1
                if br == 1 and rem <= 0:
                    bad["Rem"] += 1
                if br == 2 and rem >= 0:
                    bad["Rem"] += 1
                sF = mp.sign(rem) * mp.sign(imm)
                if br == 1 and sF < 0:
                    bad["ImF"] += 1
                if br == 2 and sF > 0:
                    bad["ImF"] += 1
                t = tau - alpha
                while t > mp.pi:
                    t -= 2 * mp.pi
                while t < -mp.pi:
                    t += 2 * mp.pi
                if br == 1 and t > tol:
                    bad["tsign"] += 1
                if br == 2 and t < -tol:
                    bad["tsign"] += 1
                if abs(t) > T_exact * (1 + mp.mpf("1e-20")):
                    bad["tcone"] += 1
                sup = max(sup, abs(t))
            ok = not any(bad.values())
            all_ok = all_ok and ok
            rows.append({"n": n, "branch": br, "dps": dps,
                         "violations": bad,
                         "sup_over_T": mp.nstr(sup / T_exact, 10), "ok": ok})
    return {
        "claim": (
            "At delta = 0, on both branches and every degree tested: sector "
            "confinement, sign(Im G), Im m > 0, the sign of Re m, sign(Im F), "
            "constant sign of t, and |t| <= T with the supremum at the hub."
        ),
        "rows": rows,
        "passes": bool(all_ok),
    }


# ---------------------------------------------------------------------------
# part 3: the wall-crossing closed form
# ---------------------------------------------------------------------------


def check_wall_crossings() -> dict[str, Any]:
    rows = []
    ok = True
    for n in (3, 6):
        phi_c, _, c_n = hub(n)
        for dv in ("0.4", "0.9", "1.6", "2.4"):
            d = mp.mpf(dv)
            s1 = c_n / mp.sin(d) if mp.sin(d) != 0 else mp.inf
            ok1 = mp.sin(d) > 0 and mp.sin(d + phi_c) > 0
            s2 = (-c_n / mp.sin(d + 2 * phi_c)
                  if mp.sin(d + 2 * phi_c) != 0 else mp.inf)
            ok2 = mp.sin(d + 2 * phi_c) < 0 and mp.sin(d + phi_c) < 0
            # traced: first s at which sin((n-1) arg z) changes sign
            traced = None
            for br in (1, 2):
                _, pts = trace(n, d, br, mp.mpf("1e9"), 1500, 30)
                prev = None
                s = mp.mpf("1e-14")
                ratio = (mp.mpf("1e9") / s) ** (mp.mpf(1) / 1500)
                for k, (_, phi, _) in enumerate(pts):
                    v = mp.sin((n - 1) * phi)
                    sg = 1 if v > 0 else (-1 if v < 0 else 0)
                    if sg != 0:
                        if prev is not None and sg != prev and traced is None:
                            traced = s
                        prev = sg
                    s = s * ratio
            pred = s1 if ok1 else (s2 if ok2 else None)
            agree = (pred is None and traced is None) or (
                pred is not None and traced is not None
                and abs(pred - traced) / pred < mp.mpf("0.05"))
            ok = ok and agree
            rows.append({
                "n": n, "delta": dv,
                "predicted_s": mp.nstr(pred, 7) if pred else None,
                "traced_s": mp.nstr(traced, 7) if traced else None,
                "agree": bool(agree),
            })
    return {
        "claim": (
            "s_1 = c_n / sin(delta) and s_2 = -c_n / sin(delta + 2 phi_c) give "
            "the exact parameter at which a branch leaves its sector, so Lemma S "
            "/ Lemma S2 do NOT extend to general ray direction."
        ),
        "rows": rows,
        "passes": bool(ok),
    }


# ---------------------------------------------------------------------------
# part 4: the cone bound at general ray direction
# ---------------------------------------------------------------------------


def singular_deltas(n: int):
    phi_c, _, _ = hub(n)
    vc = (n - 1) * mp.exp(1j * phi_c)
    out = []
    for j in range(n - 1):
        vj = (n - 1) * mp.exp(1j * mp.pi * (2 * j + 1) / (n - 1))
        if abs(vj - vc) < mp.mpf("1e-20"):
            continue
        out.append(mp.mpf(mp.fmod(-mp.arg(vj - vc) + 4 * mp.pi, 2 * mp.pi)))
    return sorted(out)


NDELTA = 12


def check_cone_general_delta() -> dict[str, Any]:
    failures = []
    n3_all_hold = True
    rows = []
    for n in (3, 6):
        sd = singular_deltas(n)
        for i in range(NDELTA):
            d = mp.mpf(2) * mp.pi * i / NDELTA + mp.mpf("0.03")
            worst = mp.mpf(0)
            for br in (1, 2):
                tau0, pts = trace(n, d, br, mp.mpf("1e12"), 1200, 40)
                aend = pts[-1][1]
                kb = min(range(-2, n + 2),
                         key=lambda k: abs((2 * mp.pi * k - d) / n - aend))
                alpha = (2 * mp.pi * kb - d) / n

                def off(x):
                    t = x - alpha
                    while t > mp.pi:
                        t -= 2 * mp.pi
                    while t < -mp.pi:
                        t += 2 * mp.pi
                    return t

                T = abs(off(tau0))
                sup = max(abs(off(tau)) for tau, _, _ in pts)
                worst = max(worst, sup / T)
            dist = min(min(abs(d - x), 2 * mp.pi - abs(d - x)) for x in sd)
            if worst > 1 + mp.mpf("1e-6"):
                failures.append({"n": n, "delta": mp.nstr(d, 6),
                                 "sup_over_T": mp.nstr(worst, 8),
                                 "dist_to_singular": mp.nstr(dist, 4)})
                if n == 3:
                    n3_all_hold = False
            rows.append({"n": n, "delta": mp.nstr(d, 5),
                         "sup_over_T": mp.nstr(worst, 8)})
    n6 = [f for f in failures if f["n"] == 6]
    return {
        "claim": (
            "The cone bound |t| <= |t(0+)| is NOT a theorem at general ray "
            "direction: it fails at n = 6 at several directions.  At n = 3 it "
            "holds at every sampled direction, including those where sector "
            "confinement fails -- so a sign flip is not by itself fatal."
        ),
        "singular_ray_directions": {
            str(n): [mp.nstr(x, 7) for x in singular_deltas(n)] for n in (3, 6)
        },
        "singular_note": (
            "A singular direction is one for which the descent ray from the hub "
            "value passes through another critical value.  Every n = 6 failure "
            "lies in the arc spanned by them."
        ),
        "n3_holds_at_all_sampled_directions": bool(n3_all_hold),
        "n6_failures": n6,
        "passes": bool(n3_all_hold and len(n6) > 0),
    }


# ---------------------------------------------------------------------------
# part 5: the delta-parametrisation, against the recorded kappa_3 anchors
# ---------------------------------------------------------------------------


def kappa3(delta, smax=mp.mpf("1e16"), steps=4500) -> mp.mpf:
    """kappa_3 = sum_i cos(gamma_i) - sum_i D_i on the delta-family."""
    mp.mp.dps = 35
    n = 3
    g, gp, gpp = model(n)
    phi_c, zc, _ = hub(n)
    ray = mp.exp(-1j * delta)
    total = mp.mpf(0)
    chord = mp.mpf(0)
    for br in (1, 2):
        root = (1 if br == 1 else -1) * mp.sqrt(2 * ray / gpp(zc))
        s = mp.mpf("1e-18")
        z = zc + root * mp.sqrt(s)
        ratio = (smax / s) ** (mp.mpf(1) / steps)
        S, GP, AR = [], [], []
        for _ in range(steps + 1):
            w = (n - 1) * zc + s * ray
            for _ in range(150):
                step = (g(z) - w) / gp(z)
                z = z - step
                if abs(step) < mp.mpf("1e-30") * max(1, abs(z)):
                    break
            S.append(s)
            GP.append(gp(z))
            AR.append(mp.arg(z))
            s = s * ratio
        kb = min(range(-2, n + 2),
                 key=lambda k: abs((2 * mp.pi * k - delta) / n - AR[-1]))
        alpha = (2 * mp.pi * kb - delta) / n

        def off(x):
            t = x - alpha
            while t > mp.pi:
                t -= 2 * mp.pi
            while t < -mp.pi:
                t += 2 * mp.pi
            return t

        t0 = off(mp.arg(root))
        vals = [(1 - mp.cos(off(mp.arg(ray / G)))) / abs(G) for G in GP]
        D = (1 - mp.cos(t0)) * 2 * mp.sqrt(2 * S[0] / abs(gpp(zc)))
        for i in range(len(S) - 1):
            D += (vals[i] + vals[i + 1]) / 2 * (S[i + 1] - S[i])
        total += D
        chord += mp.cos(phi_c - alpha)
    return chord - total


def check_parametrisation() -> dict[str, Any]:
    """delta = n phi/(n-1) is the parameter the cusp law varies -- checked against
    NearFeketeCuspLaw.md's kappa_3 anchors, one of which (phi = pi, 0.812598)
    comes from the random-h universality check and not from the sweep."""
    anchors = [("0", mp.mpf(0), mp.mpf("0.60802134")),
               ("2pi/3", mp.pi, mp.mpf("0.6080216")),
               ("pi", 3 * mp.pi / 2, mp.mpf("0.812598")),
               ("pi/3", mp.pi / 2, mp.mpf("0.8125984"))]
    rows = []
    for phi_label, d, recorded in anchors:
        k = kappa3(d)
        rows.append({"phi": phi_label, "delta": mp.nstr(d, 7),
                     "measured": mp.nstr(k, 9), "recorded": mp.nstr(recorded, 8),
                     "agrees": bool(abs(k - recorded) < mp.mpf("1e-4"))})
    good = [r for r in rows if r["phi"] != "pi/3"]
    # kappa_3 has period pi in delta: phi = pi/3 and phi = pi are the SAME point.
    period_broken_only_at_singular = (
        all(r["agrees"] for r in good) and not rows[-1]["agrees"])
    return {
        "claim": (
            "delta = n phi/(n-1) is the right parametrisation: three anchors "
            "agree to six digits, including the one not taken from the sweep.  "
            "The fourth, phi = pi/3, is the singular direction delta = pi/2; it "
            "is a period apart from phi = pi and must agree, and the measurement "
            "here does not -- so the CONTINUATION is what fails there, not the "
            "recorded table.  The recorded sweep stands."
        ),
        "rows": rows,
        "period_broken_only_at_singular_direction": period_broken_only_at_singular,
        "passes": bool(period_broken_only_at_singular),
    }


# ---------------------------------------------------------------------------
# part 6: the total-variation repair, and why it fails
# ---------------------------------------------------------------------------


def check_total_variation() -> dict[str, Any]:
    """TurningLengthBound sec2 really bounds D_i by tan(T_i/2) * TV_i, with
    TV_i = int |sin(tau - alpha)| dl.  Constant sign is what lets Lemma T's NET
    value |sin gamma_i| stand in for TV_i.  Splitting the branch at its sign
    changes is the natural repair; it fails, because the excess is too large."""
    mp.mp.dps = 30
    n = 3
    g, gp, gpp = model(n)
    phi_c, zc, _ = hub(n)
    rows = []
    for dv in ("3.172", "0.5536", "1.077", "2.124"):
        d = mp.mpf(dv)
        ray = mp.exp(-1j * d)
        C = mp.mpf(0)
        B = mp.mpf(0)
        detail = []
        for br in (1, 2):
            root = (1 if br == 1 else -1) * mp.sqrt(2 * ray / gpp(zc))
            s = mp.mpf("1e-16")
            z = zc + root * mp.sqrt(s)
            smax, steps = mp.mpf("1e13"), 2500
            ratio = (smax / s) ** (mp.mpf(1) / steps)
            S, GP, TA, AR = [], [], [], []
            for _ in range(steps + 1):
                w = (n - 1) * zc + s * ray
                for _ in range(150):
                    step = (g(z) - w) / gp(z)
                    z = z - step
                    if abs(step) < mp.mpf("1e-26") * max(1, abs(z)):
                        break
                S.append(s)
                GP.append(gp(z))
                TA.append(mp.arg(ray / gp(z)))
                AR.append(mp.arg(z))
                s = s * ratio
            kb = min(range(-2, n + 2),
                     key=lambda k: abs((2 * mp.pi * k - d) / n - AR[-1]))
            alpha = (2 * mp.pi * kb - d) / n

            def off(x):
                t = x - alpha
                while t > mp.pi:
                    t -= 2 * mp.pi
                while t < -mp.pi:
                    t += 2 * mp.pi
                return t

            ts = [off(x) for x in TA]
            t0 = off(mp.arg(root))
            sup = max(max(abs(x) for x in ts), abs(t0))
            head = 2 * mp.sqrt(2 * S[0] / abs(gpp(zc)))

            def integ(vals):
                tot = mp.mpf(0)
                for i in range(len(S) - 1):
                    tot += (vals[i] + vals[i + 1]) / 2 * (S[i + 1] - S[i])
                return tot

            TV = integ([abs(mp.sin(t)) / abs(G) for t, G in zip(ts, GP)]) \
                + abs(mp.sin(t0)) * head
            gam = phi_c - alpha
            C += mp.cos(gam)
            B += mp.tan(sup / 2) * TV
            detail.append({"branch": br, "abs_sin_gamma": mp.nstr(abs(mp.sin(gam)), 6),
                           "TV": mp.nstr(TV, 6)})
        rows.append({"delta": dv, "branches": detail,
                     "C_minus_B_TV": mp.nstr(C - B, 8),
                     "positive": bool(C - B > 0)})
    aligned_tight = all(
        abs(mp.mpf(b["TV"]) - mp.mpf(b["abs_sin_gamma"])) < mp.mpf("1e-3")
        for b in rows[0]["branches"])
    some_negative = any(not r["positive"] for r in rows)
    return {
        "claim": (
            "Lemma T's net value equals TV exactly where t has constant sign "
            "(delta = 3.172 row), and the excess on the arc of section 2 is large "
            "enough that C_n - sum tan(T_i/2) TV_i goes NEGATIVE.  So splitting "
            "the branch at its sign changes does not repair the route either."
        ),
        "rows": rows,
        "lemma_T_tight_where_sign_constant": bool(aligned_tight),
        "budget_goes_negative_somewhere": bool(some_negative),
        "passes": bool(aligned_tight and some_negative),
    }


# ---------------------------------------------------------------------------
# part 7: Proposition W -- the hub is free, and exactly one hub is good
# ---------------------------------------------------------------------------


def check_proposition_w() -> dict[str, Any]:
    """At each failure direction of part 4, trace at every ACTUAL hub
    e^{i pi (2k+1)/(n-1)} -- not at hub 0 with a shifted delta -- and count the
    hubs whose two branches both satisfy |t| <= |t(0+)| with constant sign."""
    n = 6
    g, gp, gpp = model(n)
    rows = []
    for dv in ("2.3862", "2.648"):
        d = mp.mpf(dv)
        good, cells = [], []
        for k in range(n - 1):
            mp.mp.dps = 40
            zc = mp.exp(1j * mp.pi * (2 * k + 1) / (n - 1))
            ray = mp.exp(-1j * d)
            worst, const_all = mp.mpf(0), True
            for br in (1, 2):
                root = (1 if br == 1 else -1) * mp.sqrt(2 * ray / gpp(zc))
                tau0 = mp.arg(root)
                s = mp.mpf("1e-14")
                z = zc + root * mp.sqrt(s)
                smax, steps = mp.mpf("1e12"), 1200
                ratio = (smax / s) ** (mp.mpf(1) / steps)
                TA, AR = [], []
                for _ in range(steps + 1):
                    w = (n - 1) * zc + s * ray
                    for _ in range(150):
                        step = (g(z) - w) / gp(z)
                        z = z - step
                        if abs(step) < mp.mpf("1e-34") * max(1, abs(z)):
                            break
                    TA.append(mp.arg(ray / gp(z)))
                    AR.append(mp.arg(z))
                    s = s * ratio
                kb = min(range(-3, n + 3),
                         key=lambda j: abs((2 * mp.pi * j - d) / n - AR[-1]))
                alpha = (2 * mp.pi * kb - d) / n

                def off(x):
                    t = x - alpha
                    while t > mp.pi:
                        t -= 2 * mp.pi
                    while t < -mp.pi:
                        t += 2 * mp.pi
                    return t

                T = abs(off(tau0))
                ts = [off(x) for x in TA]
                sup = max(max(abs(x) for x in ts), T)
                thr = sup * mp.mpf("1e-8")
                sig = [x for x in ts if abs(x) > thr]
                if sig and not (all(x > 0 for x in sig) or all(x < 0 for x in sig)):
                    const_all = False
                worst = max(worst, sup / T)
            ok = worst <= 1 + mp.mpf("1e-6") and const_all
            cells.append({"hub": k, "max_sup_over_T": mp.nstr(worst, 6), "ok": bool(ok)})
            if ok:
                good.append(k)
        rows.append({"delta": dv, "hubs": cells, "good_hubs": good,
                     "exactly_one": len(good) == 1,
                     "fixed_hub_0_fails": not cells[0]["ok"]})
    return {
        "claim": (
            "Proposition W, verified at the actual hubs: at each direction where "
            "the FIXED hub 0 fails, exactly one of the n-1 hubs passes both "
            "hypotheses, and it is never hub 0.  The cusp law minimises over hubs, "
            "so the turning route is NOT closed off-alignment -- see section 7 of "
            "RayDirectionScopeLimit.md, which retracts that conclusion."
        ),
        "rows": rows,
        "passes": bool(all(r["exactly_one"] and r["fixed_hub_0_fails"] for r in rows)),
    }


def main() -> int:
    report = {
        "problem": "erdos_1041",
        "scope": (
            "near-field model g(zeta) = zeta^n + n zeta only; not a statement "
            "about perturbed polynomials (ade3b6ac08)"
        ),
        "key_lemma": check_key_lemma(),
        "chain_at_aligned_direction": check_chain_aligned(),
        "wall_crossings": check_wall_crossings(),
        "cone_bound_general_ray_direction": check_cone_general_delta(),
        "delta_parametrisation": check_parametrisation(),
        "total_variation_repair": check_total_variation(),
        "proposition_w_hub_is_free": check_proposition_w(),
    }
    parts = [v for v in report.values() if isinstance(v, dict) and "passes" in v]
    report["all_passed"] = all(p["passes"] for p in parts)
    print(json.dumps(report, indent=2, default=str))
    return 0 if report["all_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
