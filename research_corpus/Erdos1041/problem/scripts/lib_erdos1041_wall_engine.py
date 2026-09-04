"""Certified point-certification engine for the Erdos-1041 quintic pair excess.

Model (chamber normalisation of QuinticTraceMaxUniversalChamber.md):

    F_mu(x) = x^5 + 5x^4 + 10x^3 + (10+mu) x^2      = x^2 (x^3+5x^2+10x+10+mu)
    F_mu'(x) = x C_mu(x),   C_mu(x) = 5x^3+20x^2+30x+20+2mu
    gaps     g_j = x_j (2mu+20-3mu x_j)/5   at the roots x_j of C_mu
    arms     F_mu(x_a(s)) = e^{-i phi} s,  s > 0, born at the double root x=0
    excess   e_a = lim_S [ int_0^S |x_a'| ds - |1 + x_a(S)| ],   E = e_+ + e_-

Everything certified here is EXACT dyadic ball arithmetic (cball.py).  Floats /
mpmath appear only as scouts; no scouted value is ever trusted.

Structure
    head    [0, s0]     analytic cone bound around the Puiseux ray
    march   [s0, S]     validated tube + Krawczyk nodes + chord/cone lengths
    tail    [S, oo)     the explicit tail theorem (see tail_bound docstring)
"""

import time
from fractions import Fraction as Fr

import mpmath as mp

import importlib.util as _ilu
from pathlib import Path as _Path
_spec = _ilu.spec_from_file_location(
    "lib_erdos1041_cball", _Path(__file__).with_name("lib_erdos1041_cball.py"))
_cball = _ilu.module_from_spec(_spec)
_spec.loader.exec_module(_cball)
CB, cb, cb_pt, krawczyk, mpf_to_fr = (_cball.CB, _cball.cb, _cball.cb_pt,
                                      _cball.krawczyk, _cball.mpf_to_fr)
nthroot_hi, nthroot_lo, poly_cb = (_cball.nthroot_hi, _cball.nthroot_lo,
                                   _cball.poly_cb)
snap_dn, snap_up, sqrt_hi, sqrt_lo = (_cball.snap_dn, _cball.snap_up,
                                      _cball.sqrt_hi, _cball.sqrt_lo)

mp.mp.dps = 50

ONE = cb(1)
TWO = cb(2)


# --------------------------------------------------------------- utilities --

def asin_hi(t):
    """Upper bound for arcsin(t), 0 <= t < 1.  Uses arcsin t <= t/sqrt(1-t^2)."""
    t = Fr(t)
    if t < 0:
        raise ValueError
    d = 1 - t * t
    if d <= 0:
        raise ValueError("asin_hi: |t| >= 1")
    return snap_up(t / sqrt_lo(d))


def cos_lo_from_sin(t):
    """Lower bound for cos(arcsin t) = sqrt(1-t^2)."""
    t = Fr(t)
    d = 1 - t * t
    if d <= 0:
        raise ValueError("cos_lo_from_sin: |t| >= 1")
    return sqrt_lo(d)


def cos_lo_sum(t1, t2):
    """cos(a1+a2) >= sqrt(1-t1^2) sqrt(1-t2^2) - t1 t2, with sin ai = ti."""
    c1, c2 = cos_lo_from_sin(t1), cos_lo_from_sin(t2)
    v = c1 * c2 - snap_up(Fr(t1) * Fr(t2))
    return snap_dn(v) if v > 0 else Fr(0)


def cos_lo_from_angle(th):
    """cos(th) >= 1 - th^2/2 (valid for all real th)."""
    v = 1 - Fr(th) * Fr(th) / 2
    return v


# ------------------------------------------------------------ model pieces --

def model(muC):
    """(F coeffs, F' coeffs, C coeffs, F'' coeffs) as ball lists, high degree first."""
    ten_mu = cb(10) + muC
    Fc = [cb(1), cb(5), cb(10), ten_mu, cb(0), cb(0)]
    Fp = [cb(5), cb(20), cb(30), TWO * ten_mu, cb(0)]
    Cc = [cb(5), cb(20), cb(30), cb(20) + TWO * muC]
    Fpp = [cb(20), cb(60), cb(60), TWO * ten_mu]
    return Fc, Fp, Cc, Fpp


def gaps_certified(muC, mu_mp):
    """Rigorous enclosures of the three critical gaps g_j."""
    Fc, Fp, Cc, _ = model(muC)
    Cd = [cb(15), cb(40), cb(30)]
    roots = mp.polyroots([mp.mpf(5), mp.mpf(20), mp.mpf(30),
                          20 + 2 * mu_mp], maxsteps=200, extraprec=200)
    out = []
    for rt in roots:
        # separation-scaled trial radius
        sep = min([abs(rt - o) for o in roots if o is not rt] or [mp.mpf(1)])
        rad = Fr(str(mp.nstr(sep / 8, 12)))
        if rad <= 0:
            rad = Fr(1, 10 ** 6)
        ctr = cb_pt(rt)
        enc = None
        for scale in (1, 2, 8, 32):
            enc = krawczyk(Cc, Cd, cb(0), ctr, rad / scale, iters=40)
            if enc is not None:
                break
        if enc is None:
            raise RuntimeError("gap root not certified")
        g = enc * (cb(20) + TWO * muC - cb(3) * muC * enc) * cb(Fr(1, 5))
        out.append((enc, g))
    return out


def wall_w(muC, mu_mp, endpoint=+1):
    """Ball for w = e^{-i phi} at a WALL point (arc endpoint) of the chamber.

    Allowed phases: Re(e^{i phi} g_j) >= 0 for all j, i.e.
    phi in intersection_j [c_j - pi/2, c_j + pi/2] with c_j = -arg g_j.
    Endpoint +1 = upper endpoint phi = min_j c_j + pi/2  ->  w = -i g_{j*}/|g_{j*}|
    Endpoint -1 = lower endpoint phi = max_j c_j - pi/2  ->  w = +i g_{j*}/|g_{j*}|
    No transcendental function is needed: w is algebraic in the certified g.
    """
    gs = gaps_certified(muC, mu_mp)
    cand = []
    for enc, g in gs:
        if g.contains_zero():
            continue                      # gap-zero: condition is vacuous
        gm = complex(float(g.a), float(g.b))
        import cmath
        cj = -cmath.phase(gm)
        cand.append((cj, g))
    if not cand:
        raise RuntimeError("no active gap")
    # bring the c_j into one window of width < pi (chamber non-empty)
    cj0 = cand[0][0]
    norm = []
    for cj, g in cand:
        d = cj - cj0
        while d > mp.pi:
            d -= 2 * mp.pi
        while d < -mp.pi:
            d += 2 * mp.pi
        norm.append((float(cj0 + d), g))
    if endpoint > 0:
        _, g = min(norm, key=lambda t: t[0])
        rot = cb(0, -1)
    else:
        _, g = max(norm, key=lambda t: t[0])
        rot = cb(0, 1)
    gabs2 = g.cabs2()
    lo = sqrt_lo(gabs2) - g.r
    hi = sqrt_hi(gabs2) + g.r
    if lo <= 0:
        raise RuntimeError("gap enclosure straddles 0")
    absg = CB((lo + hi) / 2, Fr(0), snap_up((hi - lo) / 2))
    w = rot * g * absg.inv()
    return w, [g for _, g in cand]


def wall_phi_float(mu_mp, endpoint=+1):
    """Float wall phase (scout / reporting only)."""
    import cmath
    rts = mp.polyroots([mp.mpf(5), mp.mpf(20), mp.mpf(30), 20 + 2 * mu_mp],
                       maxsteps=200, extraprec=200)
    cs = []
    for rt in rts:
        g = rt * (2 * mu_mp + 20 - 3 * mu_mp * rt) / 5
        gc = complex(g)
        if abs(gc) < 1e-12:
            continue
        cs.append(-cmath.phase(gc))
    c0 = cs[0]
    cs = [c0 + ((c - c0 + mp.pi) % (2 * mp.pi) - mp.pi) for c in cs]
    return (min(cs) + mp.pi / 2) if endpoint > 0 else (max(cs) - mp.pi / 2)


# --------------------------------------------------------------------- head --

def head_bound(muC, wC, s0, xs0, sign):
    """Certified [lo, hi] for the arc length of the arm on [0, s0].

    Near 0:  F = (10+mu) x^2 (1+q(x)),  q = (x^3+5x^2+10x)/(10+mu)
             F' = 2(10+mu) x (1+Q(x)),  Q = (5x^3+20x^2+30x)/(2(10+mu))
    Confinement: if |x| <= r0 on the head then |F(x)| = s <= s0 forces
             |x|^2 <= s0/(|10+mu|(1-qmax)) =: r1^2,
    so a first-crossing argument gives |x(s)| <= r1 < r0 throughout.
    Tangent direction = [arg w - arg(10+mu)]/2 + arg(1+q)/2 - arg(1+Q) (mod pi),
    hence lies in a cone of half-angle
             Theta = (sig_w + sig_mu)/2 + asin(q1)/2 + asin(Q1).
    Then chord <= length <= chord / cos(Theta), chord = |x(s0)|.
    """
    tm = cb(10) + muC
    tm_lo = tm.abs_lo()
    if tm_lo <= 0:
        raise RuntimeError("10+mu straddles 0")
    s0 = Fr(s0)
    r_scout = float(mp.sqrt(mp.mpf(float(s0)) / float(tm_lo)))
    ok = False
    for mult in (4, 8, 20, 60):
        r0 = snap_up(Fr(r_scout) * mult)
        qmax = snap_up((r0 ** 3 + 5 * r0 ** 2 + 10 * r0) / tm_lo)
        if qmax >= Fr(1, 2):
            continue
        r1 = sqrt_hi(s0 / (tm_lo * (1 - qmax)))
        if r1 < r0:
            ok = True
            break
    if not ok:
        raise RuntimeError("head confinement failed")
    q1 = snap_up((r1 ** 3 + 5 * r1 ** 2 + 10 * r1) / tm_lo)
    Q1 = snap_up((5 * r1 ** 3 + 20 * r1 ** 2 + 30 * r1) / (2 * tm_lo))
    if q1 >= 1 or Q1 >= 1:
        raise RuntimeError("head series bounds too weak")
    sig_w = asin_hi(snap_up(wC.r / wC.abs_lo())) if wC.r > 0 else Fr(0)
    sig_mu = asin_hi(snap_up(tm.r / tm_lo)) if tm.r > 0 else Fr(0)
    Theta = snap_up((sig_w + sig_mu) / 2 + asin_hi(q1) / 2 + asin_hi(Q1))
    cth = cos_lo_from_angle(Theta)
    if cth <= 0:
        raise RuntimeError("head cone too wide")
    chord_lo, chord_hi = xs0.abs_lo(), xs0.abs_hi()
    return chord_lo, snap_up(chord_hi / cth), r1


# --------------------------------------------------------------- tail bound --

def tail_bound(muC, wC, yS, k, uC):
    """Explicit tail theorem.  Returns (tail1_hi, term_re_lo, diag).

    With y = 1+x the arm satisfies exactly
        y^5 = w s + P(y),   P(y) = -mu y^2 + (2mu+5) y - (mu+4)          (N2')
    Set p2=|mu|, p1=|2mu+5|, p0=|mu+4| and eta(m) = (p2 m^2 + p1 m + p0)/m^5
    (decreasing in m).  Suppose |y(S)| > m0, eta0 := eta(m0) < 1 and
    m0^5 (1+eta0) <= S.  Then for every s >= S:
        (i)   |y(s)| > m0, hence |P| <= eta0 |y|^5 and
              lam s^{1/5} <= |y(s)| <= Lam s^{1/5},
              lam = (1+eta0)^{-1/5},  Lam = (1-eta0)^{-1/5};
        (ii)  |arg(y/(u s^{1/5}))| <= asin(eta1(s))/5 =: Psi(s), u^5 = w,
              eta1(s) = (p2 Lam^2 s^{2/5} + p1 Lam s^{1/5} + p0)/s
              (the tract index is fixed by continuity from s = S);
        (iii) tangent arg(dy/ds) obeys |arg(dy/ds) - arg u| <= 4 Psi + asin(nu),
              nu(s) = (2 p2 Lam s^{1/5} + p1)/(5 lam^4 s^{4/5});
        (iv)  |dy/ds| <= G(s) = 1/(5 lam^4 s^{4/5} (1-nu(s))).
    Since |y(T)| >= Re(conj(u) y(T)),
        0 <= e_a - u_S <= (|y(S)| - Re(conj(u) y(S))) + Tail1(S),
        Tail1(S) = int_S^oo (1 - cos(arg(dy/ds) - arg u)) |dy|
                 <= int_S^oo (Theta(s)^2/2) G(s) ds
    with Theta(s) <= c3 s^{-3/5} + c4 s^{-4/5} + c5 s^{-1}, giving the closed
    form returned below.  S = k^5 is used so every power of S is exact.
    """
    p2 = muC.abs_hi()
    p1 = (TWO * muC + cb(5)).abs_hi()
    p0 = (muC + cb(4)).abs_hi()
    S = Fr(k) ** 5

    m0 = snap_dn(yS.abs_lo() * Fr(9, 10))
    if m0 <= 0:
        raise RuntimeError("tail: |y(S)| lower bound is 0")
    eta0 = snap_up((p2 * m0 ** 2 + p1 * m0 + p0) / m0 ** 5)
    if eta0 >= Fr(1, 2):
        raise RuntimeError("tail: eta0 = %s not < 1/2 (S too small)" % float(eta0))
    if m0 ** 5 * (1 + eta0) > S:
        raise RuntimeError("tail: bootstrap hypothesis m0^5(1+eta0) <= S fails")

    lam = nthroot_lo(1 / (1 + eta0), 5)
    Lam = nthroot_hi(1 / (1 - eta0), 5)
    if lam <= 0:
        raise RuntimeError("tail: lam = 0")

    kk = Fr(k)
    eta1 = snap_up((p2 * Lam ** 2 * kk ** 2 + p1 * Lam * kk + p0) / S)
    nu = snap_up((2 * p2 * Lam * kk + p1) / (5 * lam ** 4 * kk ** 4))
    if eta1 >= Fr(1, 2) or nu >= Fr(1, 2):
        raise RuntimeError("tail: eta1/nu too large (S too small)")

    A1 = snap_up(1 / cos_lo_from_sin(eta1))
    A2 = snap_up(1 / cos_lo_from_sin(nu))

    c3 = snap_up(Fr(4, 5) * A1 * p2 * Lam ** 2 + A2 * 2 * p2 * Lam / (5 * lam ** 4))
    c4 = snap_up(Fr(4, 5) * A1 * p1 * Lam + A2 * p1 / (5 * lam ** 4))
    c5 = snap_up(Fr(4, 5) * A1 * p0)
    g0 = snap_up(1 / (5 * lam ** 4 * (1 - nu)))

    tail1 = snap_up((g0 / 2) * (
        c3 ** 2 / kk ** 5
        + Fr(5, 3) * c3 * c4 / kk ** 6
        + Fr(5, 7) * (c4 ** 2 + 2 * c3 * c5) / kk ** 7
        + Fr(5, 4) * c4 * c5 / kk ** 8
        + Fr(5, 9) * c5 ** 2 / kk ** 9))

    # tract membership at s = S : y(S)/(u k) must lie in the sector |arg|<pi/5
    rho = yS * uC.inv() * cb(Fr(1, k))
    TAN36 = Fr(726, 1000)                 # < tan(pi/5) = 0.72654...
    if not (rho.a - rho.r > 0 and (abs(rho.b) + rho.r) <= (rho.a - rho.r) * TAN36):
        raise RuntimeError("tail: tract identification failed")

    term = (uC.conj() * yS)               # Re(conj(u) y(S))
    term_re_lo = term.re_lo()

    # gradient tail:  int_S^oo |x'| K ds  with K = |N1||y-1|/|N2|^2,
    #   N1 = -10y^4+20y^3+2 mu y-2 mu-10,  N2 = 5y^4+2 mu y - 2 mu - 5
    Mp = Lam * kk
    Mm = lam * kk
    f1 = snap_up(1 + 1 / Mp)
    f2 = snap_up(1 + 2 / Mp + p2 / (5 * Lam ** 3 * kk ** 3)
                 + (2 * p2 + 10) / (10 * Lam ** 4 * kk ** 4))
    f3 = 1 - snap_up(2 * p2 * Lam / (5 * lam ** 4 * kk ** 3)) \
           - snap_up((2 * p2 + 5) / (5 * lam ** 4 * kk ** 4))
    if f3 <= 0:
        raise RuntimeError("tail-gradient: f3 <= 0")
    A = snap_up(2 * Lam ** 5 * f1 * f2 / (25 * lam ** 12 * f3 ** 2 * (1 - nu)))
    grad_tail = snap_up(Fr(5, 2) * A / kk ** 2)

    # phi-gradient tail:  int_S^oo |x'| |Im(F'' F / F'^2)| ds.
    #   F'' F / F'^2 = 4/5 + N3/(5 N2^2)   with N2 = 5y^4+2mu y-2mu-5 and
    #   N3 = 30 mu y^5 - 60(2mu+5) y^4 + 100(mu+4) y^3 - 6 mu^2 y^2
    #        + 6 mu(2mu+5) y - (6 mu^2 + 40 mu + 100)
    # (the y^8 terms cancel: the leading value 4/5 is REAL, which is exactly
    #  why the phi-derivative integral converges).
    Bphi = snap_up(30 * p2
                   + 60 * (2 * p2 + 5) / (Lam * kk)
                   + 100 * (p2 + 4) / (Lam ** 2 * kk ** 2)
                   + 6 * p2 ** 2 / (Lam ** 3 * kk ** 3)
                   + 6 * p2 * (2 * p2 + 5) / (Lam ** 4 * kk ** 4)
                   + (6 * p2 ** 2 + 40 * p2 + 100) / (Lam ** 5 * kk ** 5))
    Aphi = snap_up(Lam ** 5 * Bphi / (625 * lam ** 12 * f3 ** 2 * (1 - nu)))
    gradphi_tail = snap_up(Fr(5, 2) * Aphi / kk ** 2)

    diag = dict(m0=float(m0), eta0=float(eta0), eta1=float(eta1), nu=float(nu),
                lam=float(lam), Lam=float(Lam), c3=float(c3), c4=float(c4),
                c5=float(c5), g0=float(g0))
    return tail1, term_re_lo, grad_tail, gradphi_tail, diag


# -------------------------------------------------------------------- march --

class ArmResult(object):
    pass


def arg_abs_hi(z):
    """Upper bound for |arg z| when the ball z has Re > |Im| (small-angle use).

    |arg(c)| <= |Im c| / Re c  (arctan t <= t) and the ball adds asin(r/|c|).
    """
    if z.a - z.r <= 0:
        raise RuntimeError("arg_abs_hi: ball not in right half plane")
    base = snap_up(abs(z.b) / z.a) if z.a > 0 else None
    if base is None:
        raise RuntimeError("arg_abs_hi: bad centre")
    if z.r > 0:
        clo = sqrt_lo(z.cabs2())
        if z.r >= clo:
            raise RuntimeError("arg_abs_hi: ball contains 0")
        base = snap_up(base + asin_hi(snap_up(z.r / clo)))
    return base


def arg_abs_lo(z):
    """Lower bound for |arg z| over the ball z (Re > r >= 0), else 0.

    |arg z| >= arctan(|Im c|/Re c) - asin(r/|c|),  arctan t >= t - t^3/3.
    """
    a, b, r = z.a, abs(z.b), z.r
    if a - r <= 0:
        return Fr(0)
    t = snap_dn(b / a)
    lo = t - snap_up(t ** 3) / 3
    if r > 0:
        chi = sqrt_lo(z.cabs2())          # |c| LOWER bound -> angular half
        if chi <= r:                      # width UPPER bound (must over-cut)
            return Fr(0)
        lo = lo - asin_hi(snap_up(r / chi))
    return lo if lo > 0 else Fr(0)


def sec_lo(t):
    """1/cos(t) >= 1 + t^2/2  for |t| < pi/2."""
    return 1 + Fr(t) * Fr(t) / 2


def march_arm(muC, wC, mu_mp, w_mp, sign, s0, k, ratio=0.06, msub=6,
              eps_step=Fr(1, 10 ** 8), want_grad=True,
              gradient_only=False, verbose=False):
    """Certify one arm from x=0 out to S = k^5 and add the tail bound.

    Per step the length is bounded by the MONOTONE-TURNING cone bound around
    the chord direction:  if Im(F'' w / F'^2) has one sign on the validated
    tube then theta(s) = arg(w) - arg F'(x(s)) is monotone, so the tangent
    stays between its two endpoint values; with u = chord/|chord|,
        chord <= length <= Re(conj(u) dx) / cos(beta) = |chord| / cos(beta),
        beta  = max(|arg(T_A/u)|, |arg(T_B/u)|),  T = w/F'(X).
    This is ~5x tighter than the tube-wide cone bound, which is kept as a
    fallback when monotonicity is not certified.
    """
    S = Fr(k) ** 5
    Fc, Fp, Cc, Fpp = model(muC)
    Fpd = [cb(20), cb(60), cb(60), TWO * (cb(10) + muC)]   # F''
    F3 = [cb(60), cb(120), cb(60)]                        # F'''
    Ac = [cb(1), cb(5), cb(10), cb(10) + muC]             # F = x^2 A, F' = x B
    Cd = [cb(15), cb(40), cb(30)]

    def Fmp(x):
        return x * x * (x * x * x + 5 * x * x + 10 * x + 10 + mu_mp)

    def Fpmp(x):
        return x * (5 * x ** 3 + 20 * x ** 2 + 30 * x + 20 + 2 * mu_mp)

    def scout(x, s):
        for _ in range(40):
            d = (Fmp(x) - w_mp * s) / Fpmp(x)
            x = x - d
            if abs(d) < abs(x) * mp.mpf(10) ** (-32):
                break
        return x

    # ---- start node -----------------------------------------------------
    s0 = Fr(s0)
    s0mp = mp.mpf(s0.numerator) / mp.mpf(s0.denominator)
    x_mp = sign * mp.sqrt(w_mp * s0mp / (10 + mu_mp))
    x_mp = scout(x_mp, s0mp)
    ctr = cb_pt(x_mp)
    target0 = wC * cb(s0)
    X = None
    for frac in (Fr(3, 10), Fr(1, 10), Fr(1, 50)):
        X = krawczyk(Fc, Fp, target0, ctr, snap_up(frac * ctr.abs_hi()), iters=12)
        if X is not None:
            break
    if X is None:
        raise RuntimeError("start node not certified")

    hl, hh, r1 = head_bound(muC, wC, s0, X, sign)
    L_lo, L_hi = hl, hh

    # gradient over the head: K on |x| <= r1
    grad = Fr(0)
    gradphi = Fr(0)
    if want_grad:
        Dh = CB(Fr(0), Fr(0), r1, _raw=True)
        Ch = poly_cb(Cc, Dh)
        if Ch.contains_zero():
            raise RuntimeError("head: C_mu straddles 0")
        Ci = Ch.inv()
        Kh = (TWO * Ci - poly_cb(Fpd, Dh) * Ci * Ci).abs_hi()
        grad = grad + Kh * hh
        Jp = poly_cb(Fpd, Dh) * poly_cb(Ac, Dh) * Ci * Ci
        gradphi = gradphi + snap_up(abs(Jp.b) + Jp.r) * hh

    # ---- schedule -------------------------------------------------------
    import math
    nsteps = max(60, int(math.ceil(math.log(float(S / s0)) / math.log(1 + ratio))))
    q = (float(S) / float(s0)) ** (1.0 / nsteps)
    svals = [s0]
    cur = float(s0)
    for i in range(1, nsteps):
        cur *= q
        svals.append(Fr(cur))
    svals.append(S)

    x_mp_cur = x_mp
    nfail = 0
    nbis = 0
    beta_max = Fr(0)
    nmono = 0
    t0 = time.time()
    i = 0
    while i < len(svals) - 1:
        sa, sb = svals[i], svals[i + 1]
        ds = sb - sa
        ok = False
        for attempt in range(8):
            # --- validated tube (a-priori enclosure of the arc) ----------
            base = X.r + snap_up(Fr(float(abs(w_mp / Fpmp(x_mp_cur)))) * ds)
            for grow in (Fr(11, 10), Fr(3, 2), Fr(5, 2), Fr(6), Fr(20), Fr(80)):
                rho = snap_up(base * grow)
                T = CB(X.a, X.b, rho, _raw=True)
                FpT = poly_cb(Fp, T)
                fplo = FpT.abs_lo()
                if fplo <= 0:
                    continue
                Lip = snap_up(wC.abs_hi() / fplo)
                if X.r + Lip * ds < rho:
                    ok = True
                    break
            if ok:
                break
            ds = ds / 2
            sb = sa + ds
            svals.insert(i + 1, sb)
        if not ok:
            raise RuntimeError("tube validation failed at s=%g" % float(sa))

        reach = snap_up(X.r + Lip * ds)
        # --- next node ------------------------------------------------------
        x_next = scout(x_mp_cur, mp.mpf(sb.numerator) / mp.mpf(sb.denominator))
        ctr = cb_pt(x_next)
        dctr = CB(ctr.a - X.a, ctr.b - X.b, Fr(0), _raw=True)
        R = snap_up(dctr.abs_hi() + reach)
        Xn = krawczyk(Fc, Fp, wC * cb(sb), ctr, R, iters=3)
        if Xn is None:
            nfail += 1
            ds = ds / 2
            svals.insert(i + 1, sa + ds)
            if nfail > 600:
                raise RuntimeError("too many Krawczyk failures")
            continue

        # Parameter tubes can make the two endpoint root balls overlap even
        # though the validated a-priori arc tube is perfectly regular.  For
        # gradient-only transport no chord lower bound is needed: the same
        # tube proof gives length <= Lip*ds, and the two gradient densities
        # below are nonnegative.  Paying this coarse length once avoids every
        # cancellation and oriented-lens dependency.
        if gradient_only:
            step_hi = snap_up(Lip * ds)
            L_hi = L_hi + step_hi
            if want_grad:
                CT = poly_cb(Cc, T)
                if CT.contains_zero():
                    raise RuntimeError("C_mu straddles 0 on gradient tube")
                Ci = CT.inv()
                FppT = poly_cb(Fpd, T)
                Kb = (TWO * Ci - FppT * Ci * Ci).abs_hi()
                grad = grad + Kb * step_hi
                Jp = FppT * poly_cb(Ac, T) * Ci * Ci
                gradphi = gradphi + snap_up(abs(Jp.b) + Jp.r) * step_hi
            X = Xn
            x_mp_cur = x_next
            i += 1
            if i % 256 == 0:
                L_hi = snap_up(L_hi, 90)
                grad = snap_up(grad, 90)
                gradphi = snap_up(gradphi, 90)
            continue

        # --- certified length on the step ------------------------------------
        chord = Xn - X
        c_lo, c_hi = chord.abs_lo(), chord.abs_hi()
        if c_lo <= 0:
            raise RuntimeError("degenerate chord")
        chordi = chord.inv()
        # (a) crude a-priori: length <= min(Lip*ds, chord/cos(tube cone))
        Cc_, Rr = sqrt_lo(FpT.cabs2()), FpT.r
        if Rr >= Cc_:
            raise RuntimeError("tube cone too wide")
        t1 = snap_up(Rr / Cc_)
        t2 = snap_up(wC.r / wC.abs_lo()) if wC.r > 0 else Fr(0)
        cb0 = cos_lo_sum(t1, t2)
        step_hi = snap_up(Lip * ds)
        if cb0 > 0:
            alt = snap_up(c_hi / cb0)
            if alt < step_hi:
                step_hi = alt
        # (b) iterated ORIENTED lens refinement.  Given any length bound
        #     L <= chord(1+e), the arc lies in the ellipse with foci X, Xn and
        #     major axis chord(1+e), hence within distance
        #        H = (chord/2) sqrt((1+e)^2 - 1)
        #     of the chord SEGMENT.  Split the segment into msub pieces; piece
        #     j lies in the ORIENTED box  c_j + u([-A,A] + i[-H,H]),
        #     u = chord/|chord|, A = chord/(2 msub).  First-order expansion
        #        F'(z)/F'(c_j) = 1 + G(a + i h) + Rem/F'(c_j),
        #        G = F''(c_j) u / F'(c_j),  |Rem| <= (1/2) max|F'''| (A+H)^2,
        #     gives  |Im Delta| <= A |Im G| + H |Re G| + rho_R  while
        #     |Delta| <= (A+H)|G| + rho_R.  Because u is nearly parallel to the
        #     arm, |Im G| << |G|: this is what makes the ALONG-arc extent of
        #     the box almost free, and is ~60x tighter than an isotropic disc.
        #     Finally length <= (chord/msub) sum_j sec(beta_j), partitioning by
        #     the (monotone) projection coordinate a = Re(conj(u)(x - X)).
        absc = CB((c_lo + c_hi) / 2, Fr(0), snap_up((c_hi - c_lo) / 2))
        uhat = chord * absc.inv()
        mids = [X + chord * cb(Fr(2 * j + 1, 2 * msub)) for j in range(msub)]
        rmax = max(m_.r for m_ in mids)
        A = snap_up(c_hi / (2 * msub) + rmax)
        pre = []
        try:
            for mid in mids:
                Fpm = poly_cb(Fp, mid)
                if Fpm.contains_zero():
                    pre = None
                    break
                Fpmi = Fpm.inv()
                G = poly_cb(Fpd, mid) * uhat * Fpmi
                zeta = wC * Fpmi * chordi
                pre.append((mid, Fpm, G, arg_abs_hi(zeta), arg_abs_lo(zeta)))
        except Exception:
            pre = None
        step_lo = c_lo
        # The projection coordinate a = Re(conj(u)(x - X)) must be strictly
        # monotone for the piecewise partition to be well defined.  The tangent
        # lies within beta_tube of a fixed axis and so does the chord
        # direction u, hence |theta - arg u| <= 2 beta_tube; require
        # beta_tube < pi/4, i.e. cos(beta_tube) > sqrt(2)/2.
        if cb0 <= Fr(7072, 10000):
            pre = None
        if pre:
            for _ in range(10):
                e = snap_up(step_hi / c_lo) - 1
                if e <= 0:
                    break
                H = snap_up((c_hi / 2) * sqrt_hi((1 + e) ** 2 - 1) + rmax)
                secsum = Fr(0)
                secsum_lo = Fr(0)
                good = True
                for (mid, Fpm, G, base_arg, base_lo) in pre:
                    Dj = CB(mid.a, mid.b, snap_up(A + H), _raw=True)
                    M3 = poly_cb(F3, Dj).abs_hi()
                    fpl = Fpm.abs_lo()
                    if fpl <= 0:
                        good = False
                        break
                    rhoR = snap_up(M3 * (A + H) ** 2 / (2 * fpl))
                    Gh = G.abs_hi()
                    ImG = snap_up(abs(G.b) + G.r)
                    ReG = snap_up(abs(G.a) + G.r)
                    dmax = snap_up((A + H) * Gh + rhoR)
                    if dmax >= 1:
                        good = False
                        break
                    immax = snap_up(A * ImG + H * ReG + rhoR)
                    delta = snap_up(immax / (1 - dmax))
                    bj = snap_up(base_arg + delta)
                    cbj = cos_lo_from_angle(bj)
                    if cbj <= 0:
                        good = False
                        break
                    secsum += 1 / cbj
                    blo = base_lo - delta
                    if blo > 0:
                        secsum_lo += sec_lo(snap_dn(blo))
                    else:
                        secsum_lo += 1
                    if bj > beta_max:
                        beta_max = bj
                if not good:
                    break
                new_hi = snap_up(c_hi * secsum / msub)
                new_lo = snap_dn(c_lo * secsum_lo / msub)
                if new_lo > step_lo:
                    step_lo = new_lo
                if new_hi >= step_hi:
                    break
                step_hi = new_hi
                nmono += 1
        # --- adaptive control on the CERTIFIED per-step width ----------------
        if step_hi - step_lo > eps_step and nbis < 6000:
            nbis += 1
            svals.insert(i + 1, sa + ds / 2)
            continue
        L_lo = L_lo + step_lo
        L_hi = L_hi + step_hi

        if want_grad:
            CT = poly_cb(Cc, T)
            if CT.contains_zero():
                raise RuntimeError("C_mu straddles 0 on tube")
            Ci = CT.inv()
            FppT = poly_cb(Fpd, T)
            Kb = (TWO * Ci - FppT * Ci * Ci).abs_hi()
            grad = grad + Kb * step_hi
            Jp = FppT * poly_cb(Ac, T) * Ci * Ci
            gradphi = gradphi + snap_up(abs(Jp.b) + Jp.r) * step_hi

        X = Xn
        x_mp_cur = x_next
        i += 1
        if i % 256 == 0:
            L_lo = snap_dn(L_lo, 90)
            L_hi = snap_up(L_hi, 90)
            grad = snap_up(grad, 90)
            gradphi = snap_up(gradphi, 90)

    res = ArmResult()
    res.X_S = X
    res.len_lo = snap_dn(L_lo)
    res.len_hi = snap_up(L_hi)
    res.grad_march = snap_up(grad)
    res.gradphi_march = snap_up(gradphi)
    res.nodes = len(svals)
    res.nfail = nfail
    res.nbis = nbis
    res.beta_max = float(beta_max)
    res.nref = nmono
    res.seconds = time.time() - t0
    res.x_mp = x_mp_cur
    return res


def fifth_root_of_w(wC, w_mp, y_mp):
    """Certified u with u^5 = w, chosen in the tract of y (arg u ~ arg y)."""
    best, bestd = None, None
    for j in range(5):
        u = mp.exp(1j * (mp.arg(w_mp) + 2 * mp.pi * j) / 5)
        d = abs(mp.arg(y_mp / u))
        if bestd is None or d < bestd:
            best, bestd = u, d
    coeffs = [cb(1), cb(0), cb(0), cb(0), cb(0), cb(0)]
    coeffs = [cb(1), cb(0), cb(0), cb(0), cb(0), -wC]     # u^5 - w
    dco = [cb(5), cb(0), cb(0), cb(0), cb(0)]
    ctr = cb_pt(mp.mpc(best))
    for rad in (Fr(1, 4), Fr(1, 16), Fr(1, 64)):
        u = krawczyk(coeffs, dco, cb(0), ctr, rad, iters=40)
        if u is not None:
            return u
    raise RuntimeError("fifth root not certified")


# --------------------------------------------------------------- assemble ---

def certified_excess(mu_mp, w_mp, muC=None, wC=None, k=60, s0=Fr(1, 10 ** 10),
                     ratio=0.06, msub=6, eps_step=Fr(1, 10 ** 8),
                     want_grad=True, gradient_only=False, verbose=False):
    """Certified [lo, hi] enclosure of E(mu, phi) with w = e^{-i phi}.

    Returns dict with lo, hi, width, per-arm data, gradient bound, timings.
    """
    if muC is None:
        muC = CB(Fr(mp.nstr(mp.mpf(mu_mp.real if hasattr(mu_mp, 'real') else mu_mp), 40)),
                 Fr(mp.nstr(mp.mpf(mu_mp.imag if hasattr(mu_mp, 'imag') else 0), 40)))
    if wC is None:
        wC = CB(Fr(mp.nstr(w_mp.real, 40)), Fr(mp.nstr(w_mp.imag, 40)))
    t0 = time.time()
    E_lo = Fr(0)
    E_hi = Fr(0)
    gradsum = Fr(0)
    gradphisum = Fr(0)
    arms = []
    for sign in (+1, -1):
        r = march_arm(muC, wC, mu_mp, w_mp, sign, s0, k, ratio=ratio,
                      msub=msub, eps_step=eps_step, want_grad=want_grad,
                      gradient_only=gradient_only, verbose=verbose)
        yS = ONE + r.X_S
        y_mp = 1 + r.x_mp
        uC = fifth_root_of_w(wC, w_mp, y_mp)
        tail1, term_re_lo, grad_tail, gradphi_tail, diag = tail_bound(
            muC, wC, yS, k, uC)
        e_lo = snap_dn(r.len_lo - yS.abs_hi())
        e_hi = snap_up(r.len_hi - term_re_lo + tail1)
        E_lo += e_lo
        E_hi += e_hi
        gradsum += r.grad_march + grad_tail
        gradphisum += r.gradphi_march + gradphi_tail
        arms.append(dict(sign=sign, e_lo=float(e_lo), e_hi=float(e_hi),
                         len_lo=float(r.len_lo), len_hi=float(r.len_hi),
                         tail1=float(tail1), nodes=r.nodes, nfail=r.nfail, nbis=r.nbis,
                         beta_max=r.beta_max, seconds=r.seconds,
                         grad=float(r.grad_march + grad_tail), diag=diag,
                         xS=complex(float(r.X_S.a), float(r.X_S.b)),
                         xS_rad=float(r.X_S.r)))
    return dict(lo=E_lo, hi=E_hi, width=snap_up(E_hi - E_lo),
                grad_phi_q=gradphisum, grad_phi=float(gradphisum),
                lo_f=float(E_lo), hi_f=float(E_hi), width_f=float(E_hi - E_lo),
                grad_mu_q=gradsum, grad_mu=float(gradsum),
                arms=arms, seconds=time.time() - t0,
                k=k, S=float(Fr(k) ** 5), ratio=ratio)
