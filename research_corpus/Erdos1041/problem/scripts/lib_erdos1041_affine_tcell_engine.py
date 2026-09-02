"""Exact affine-predictor cells for the ordered double-tight carrier.

The scalar parameter ``t`` is real.  Complex arithmetic used for acceptance is
the exact dyadic-disc arithmetic of ``lib_erdos1041_cball``.  Floating point is
used only to Newton-scout a centre and its tangent.

The important implementation detail is that the predictor residual is not
evaluated by ordinary interval substitution.  We substitute

    a(t)  = a0  + a1 (t-t0),
    mu(t) = mu0 + mu1 (t-t0)

into the two carrier polynomials in a tiny polynomial ring over exact complex
balls.  Thus the cancelled linear coefficient stays cancelled, and the
Krawczyk defect is genuinely quadratic in the cell radius.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr
import importlib.util
from pathlib import Path
from typing import Sequence

import mpmath as mp


HERE = Path(__file__).resolve().parent

CB_SPEC = importlib.util.spec_from_file_location(
    "affine_tcell_cball", HERE / "lib_erdos1041_cball.py"
)
CB_MOD = importlib.util.module_from_spec(CB_SPEC)
assert CB_SPEC.loader is not None
CB_SPEC.loader.exec_module(CB_MOD)
CB, cb, cb_pt = CB_MOD.CB, CB_MOD.cb, CB_MOD.cb_pt

SUPPORT_SPEC = importlib.util.spec_from_file_location(
    "affine_tcell_support", HERE / "lib_erdos1041_support_engine.py"
)
SUPPORT = importlib.util.module_from_spec(SUPPORT_SPEC)
assert SUPPORT_SPEC.loader is not None
SUPPORT_SPEC.loader.exec_module(SUPPORT)

mp.mp.dps = 90


def cpow(z: CB, n: int) -> CB:
    out, base = cb(1), z
    while n:
        if n & 1:
            out = out * base
        base = base * base
        n >>= 1
    return out


def abc(mu: CB) -> tuple[CB, CB, CB]:
    A = cb(4) * (mu + cb(4))
    B = -cb(Fr(12, 25)) * (
        cb(3) * cpow(mu, 3) - cb(5) * cpow(mu, 2)
        - cb(100) * mu - cb(200)
    )
    C = cb(Fr(4, 3125)) * cpow(mu + cb(10), 3) * (
        cb(27) * cpow(mu, 2) + cb(140) * mu + cb(200)
    )
    return A, B, C


def abc_prime(mu: CB) -> tuple[CB, CB, CB]:
    Ap = cb(4)
    Bp = -cb(Fr(12, 25)) * (
        cb(9) * cpow(mu, 2) - cb(10) * mu - cb(100)
    )
    Cp = cb(Fr(4, 3125)) * (
        cb(3) * cpow(mu + cb(10), 2)
        * (cb(27) * cpow(mu, 2) + cb(140) * mu + cb(200))
        + cpow(mu + cb(10), 3) * (cb(54) * mu + cb(140))
    )
    return Ap, Bp, Cp


def carrier(t: CB, a: CB, mu: CB) -> tuple[CB, CB]:
    A, B, C = abc(mu)
    one = cb(1)
    return (
        (one + t + cpow(t, 2)) * cpow(a, 2) + (one + t) * A * a + B,
        t * (one + t) * cpow(a, 3) + t * A * cpow(a, 2) - C,
    )


def jacobian(t: CB, a: CB, mu: CB) -> list[list[CB]]:
    A, _, _ = abc(mu)
    Ap, Bp, Cp = abc_prime(mu)
    one = cb(1)
    return [
        [
            cb(2) * (one + t + cpow(t, 2)) * a + (one + t) * A,
            (one + t) * Ap * a + Bp,
        ],
        [
            cb(3) * t * (one + t) * cpow(a, 2) + cb(2) * t * A * a,
            t * Ap * cpow(a, 2) - Cp,
        ],
    ]


def t_derivative(t: CB, a: CB, mu: CB) -> tuple[CB, CB]:
    A, _, _ = abc(mu)
    one = cb(1)
    return (
        (one + cb(2) * t) * cpow(a, 2) + A * a,
        (one + cb(2) * t) * cpow(a, 3) + A * cpow(a, 2),
    )


def matmul(A: Sequence[Sequence[CB]], B: Sequence[Sequence[CB]]) -> list[list[CB]]:
    return [
        [sum((A[i][k] * B[k][j] for k in range(2)), cb(0)) for j in range(2)]
        for i in range(2)
    ]


def matvec(A: Sequence[Sequence[CB]], x: Sequence[CB]) -> list[CB]:
    return [sum((A[i][k] * x[k] for k in range(2)), cb(0)) for i in range(2)]


# Ascending coefficient order, over exact complex balls.
Poly = list[CB]


def pconst(z: CB | int | Fr) -> Poly:
    return [z if isinstance(z, CB) else cb(z)]


def paffine(z0: CB, z1: CB) -> Poly:
    return [z0, z1]


def padd(x: Poly, y: Poly) -> Poly:
    n = max(len(x), len(y))
    return [
        (x[k] if k < len(x) else cb(0)) + (y[k] if k < len(y) else cb(0))
        for k in range(n)
    ]


def pneg(x: Poly) -> Poly:
    return [-z for z in x]


def psub(x: Poly, y: Poly) -> Poly:
    return padd(x, pneg(y))


def pmul(x: Poly, y: Poly) -> Poly:
    out = [cb(0) for _ in range(len(x) + len(y) - 1)]
    for i, xi in enumerate(x):
        for j, yj in enumerate(y):
            out[i + j] = out[i + j] + xi * yj
    return out


def pscale(c: CB | int | Fr, x: Poly) -> Poly:
    cc = c if isinstance(c, CB) else cb(c)
    return [cc * z for z in x]


def ppow(x: Poly, n: int) -> Poly:
    out, base = pconst(1), x
    while n:
        if n & 1:
            out = pmul(out, base)
        base = pmul(base, base)
        n >>= 1
    return out


def carrier_predictor_polys(
    t0: CB, a0: CB, mu0: CB, a1: CB, mu1: CB
) -> tuple[Poly, Poly]:
    """Exact coefficients after affine substitution in tau=t-t0."""
    tau_t = paffine(t0, cb(1))
    tau_a = paffine(a0, a1)
    tau_mu = paffine(mu0, mu1)
    one = pconst(1)
    A = pscale(4, padd(tau_mu, pconst(4)))
    B = pscale(
        -Fr(12, 25),
        psub(
            psub(
                psub(pscale(3, ppow(tau_mu, 3)), pscale(5, ppow(tau_mu, 2))),
                pscale(100, tau_mu),
            ),
            pconst(200),
        ),
    )
    C = pscale(
        Fr(4, 3125),
        pmul(
            ppow(padd(tau_mu, pconst(10)), 3),
            padd(padd(pscale(27, ppow(tau_mu, 2)), pscale(140, tau_mu)), pconst(200)),
        ),
    )
    E1 = padd(
        padd(
            pmul(padd(padd(one, tau_t), ppow(tau_t, 2)), ppow(tau_a, 2)),
            pmul(pmul(padd(one, tau_t), A), tau_a),
        ),
        B,
    )
    E2 = psub(
        padd(
            pmul(pmul(tau_t, padd(one, tau_t)), ppow(tau_a, 3)),
            pmul(pmul(tau_t, A), ppow(tau_a, 2)),
        ),
        C,
    )
    return E1, E2


def symmetric_poly_enclosure(p: Poly, radius: Fr) -> CB:
    """Contain p(tau) for real |tau|<=radius without losing linear cancellation."""
    out = p[0]
    power = Fr(1)
    extra = Fr(0)
    for coefficient in p[1:]:
        power *= radius
        extra = CB_MOD.snap_up(extra + coefficient.abs_hi() * power)
    return out.widen(extra)


def _mp_abc(mu: mp.mpc) -> tuple[mp.mpc, mp.mpc, mp.mpc]:
    A = 4 * (mu + 4)
    B = -mp.mpf(12) / 25 * (3 * mu**3 - 5 * mu**2 - 100 * mu - 200)
    C = mp.mpf(4) / 3125 * (mu + 10)**3 * (27 * mu**2 + 140 * mu + 200)
    return A, B, C


def _mp_carrier(t: mp.mpf, a: mp.mpc, mu: mp.mpc) -> mp.matrix:
    A, B, C = _mp_abc(mu)
    return mp.matrix([
        (1 + t + t**2) * a**2 + (1 + t) * A * a + B,
        t * (1 + t) * a**3 + t * A * a**2 - C,
    ])


def _mp_jacobian(t: mp.mpf, a: mp.mpc, mu: mp.mpc) -> mp.matrix:
    A, _, _ = _mp_abc(mu)
    Bp = -mp.mpf(12) / 25 * (9 * mu**2 - 10 * mu - 100)
    Cp = mp.mpf(4) / 3125 * (
        3 * (mu + 10)**2 * (27 * mu**2 + 140 * mu + 200)
        + (mu + 10)**3 * (54 * mu + 140)
    )
    return mp.matrix([
        [2 * (1 + t + t**2) * a + (1 + t) * A, 4 * (1 + t) * a + Bp],
        [3 * t * (1 + t) * a**2 + 2 * t * A * a, 4 * t * a**2 - Cp],
    ])


def _mp_t_derivative(t: mp.mpf, a: mp.mpc, mu: mp.mpc) -> mp.matrix:
    A, _, _ = _mp_abc(mu)
    return mp.matrix([
        (1 + 2 * t) * a**2 + A * a,
        (1 + 2 * t) * a**3 + A * a**2,
    ])


def newton_scout(t: Fr, a: mp.mpc, mu: mp.mpc) -> tuple[mp.mpc, mp.mpc]:
    tm = mp.mpf(t.numerator) / t.denominator
    x = mp.matrix([a, mu])
    for _ in range(30):
        step = _mp_jacobian(tm, x[0], x[1]) ** -1 * _mp_carrier(tm, x[0], x[1])
        x -= step
        if max(abs(step[0]), abs(step[1])) < mp.mpf("1e-75"):
            break
    return mp.mpc(x[0]), mp.mpc(x[1])


@dataclass
class AffineCell:
    t0: Fr
    radius: Fr
    a0: CB
    mu0: CB
    a1: CB
    mu1: CB
    correction_a: Fr
    correction_mu: Fr
    krawczyk_a: Fr
    krawczyk_mu: Fr
    det_lower: Fr
    cross_margin: Fr
    mu_box: CB
    w_box: CB
    a_scout: mp.mpc
    mu_scout: mp.mpc
    ray_scout: mp.mpc
    pair_upper: Fr | None = None
    arm_data: tuple | None = None

    @property
    def left(self) -> Fr:
        return self.t0 - self.radius

    @property
    def right(self) -> Fr:
        return self.t0 + self.radius

    def predictor_at(self, t: Fr) -> tuple[CB, CB]:
        dt = cb(t - self.t0)
        return self.a0 + self.a1 * dt, self.mu0 + self.mu1 * dt


def certify_affine_cell(
    t0: Fr,
    radius: Fr,
    a_scout: mp.mpc,
    mu_scout: mp.mpc,
    *,
    correction_a: Fr,
    correction_mu: Fr,
    support_cells: int = 0,
) -> AffineCell:
    """Certify one carrier cell, optionally proving its support sign directly."""
    a_scout, mu_scout = newton_scout(t0, a_scout, mu_scout)
    tm = mp.mpf(t0.numerator) / t0.denominator
    Jmp = _mp_jacobian(tm, a_scout, mu_scout)
    tangent = -(Jmp ** -1) * _mp_t_derivative(tm, a_scout, mu_scout)
    a0, mu0 = cb_pt(a_scout), cb_pt(mu_scout)
    a1, mu1 = cb_pt(tangent[0]), cb_pt(tangent[1])
    Ymp = Jmp ** -1
    Y = [[cb_pt(Ymp[i, j]) for j in range(2)] for i in range(2)]

    polys = carrier_predictor_polys(cb(t0), a0, mu0, a1, mu1)
    Fpred = [symmetric_poly_enclosure(poly, radius) for poly in polys]
    tC = CB(t0, 0, radius, _raw=True)
    aC = CB(a0.a, a0.b, CB_MOD.snap_up(a1.abs_hi() * radius + correction_a), _raw=True)
    muC = CB(mu0.a, mu0.b, CB_MOD.snap_up(mu1.abs_hi() * radius + correction_mu), _raw=True)
    JX = jacobian(tC, aC, muC)
    M = matmul(Y, JX)
    M = [[cb(1 if i == j else 0) - M[i][j] for j in range(2)] for i in range(2)]
    YF = matvec(Y, Fpred)
    corrections = (correction_a, correction_mu)
    kr = [
        YF[i].abs_hi() + sum(M[i][j].abs_hi() * corrections[j] for j in range(2))
        for i in range(2)
    ]
    if not (kr[0] < correction_a and kr[1] < correction_mu):
        raise RuntimeError(
            "affine Krawczyk failure: "
            f"Ka={float(kr[0]):.12g}/{float(correction_a):.12g}, "
            f"Kmu={float(kr[1]):.12g}/{float(correction_mu):.12g}"
        )

    J = jacobian(tC, aC, muC)
    det = J[0][0] * J[1][1] - J[0][1] * J[1][0]
    if det.contains_zero():
        raise RuntimeError("interval Jacobian determinant contains zero")

    p = (cb(1) + tC) * aC
    third = -abc(muC)[0] - p
    cross = p.conj() * third
    cross_margin = abs(cross.b) - cross.r
    if cross_margin <= 0:
        raise RuntimeError("wall orientation not separated")
    epsilon = -1 if cross.b > 0 else 1
    p2 = p.cabs2()
    p_lo = CB_MOD.sqrt_lo(p2) - p.r
    p_hi = CB_MOD.sqrt_hi(p2) + p.r
    if p_lo <= 0:
        raise RuntimeError("pair direction contains zero")
    p_abs = CB((p_lo + p_hi) / 2, 0, CB_MOD.snap_up((p_hi - p_lo) / 2), _raw=True)
    wC = cb(0, -epsilon) * p * p_abs.inv()

    p_mid = (1 + tm) * a_scout
    ray = -epsilon * 1j * p_mid / abs(p_mid)
    result = AffineCell(
        t0=t0,
        radius=radius,
        a0=a0,
        mu0=mu0,
        a1=a1,
        mu1=mu1,
        correction_a=correction_a,
        correction_mu=correction_mu,
        krawczyk_a=kr[0],
        krawczyk_mu=kr[1],
        det_lower=det.abs_lo(),
        cross_margin=cross_margin,
        mu_box=muC,
        w_box=wC,
        a_scout=a_scout,
        mu_scout=mu_scout,
        ray_scout=ray,
    )
    if support_cells:
        support_mu = SUPPORT.CB(muC.a, muC.b, muC.r, _raw=True)
        support_w = SUPPORT.CB(wC.a, wC.b, wC.r, _raw=True)
        arms = tuple(
            SUPPORT.certified_arm(
                support_mu, support_w, mu_scout, ray, sign, cells=support_cells
            )
            for sign in (+1, -1)
        )
        result.arm_data = arms
        result.pair_upper = CB_MOD.snap_up(arms[0][0] + arms[1][0])
    return result


def certify_overlap(left: AffineCell, right: AffineCell, t: Fr) -> dict:
    """Prove the two cell branches agree at one common rational parameter."""
    if not (left.left <= t <= left.right and right.left <= t <= right.right):
        raise ValueError("matching parameter is not in both cells")
    la, lm = left.predictor_at(t)
    ra, rm = right.predictor_at(t)
    # Use the right predictor point as centre and a polydisc containing both
    # already-proved roots at this fixed parameter.
    ac, mc = ra.mid(), rm.mid()
    rad_a = CB_MOD.snap_up(max(
        right.correction_a,
        (la - ac).abs_hi() + left.correction_a,
    ) * Fr(6, 5))
    rad_mu = CB_MOD.snap_up(max(
        right.correction_mu,
        (lm - mc).abs_hi() + left.correction_mu,
    ) * Fr(6, 5))
    tC = cb(t)
    aC = CB(ac.a, ac.b, rad_a, _raw=True)
    muC = CB(mc.a, mc.b, rad_mu, _raw=True)
    tm = mp.mpf(t.numerator) / t.denominator
    Jmp = _mp_jacobian(tm, right.a_scout, right.mu_scout)
    Ymp = Jmp ** -1
    Y = [[cb_pt(Ymp[i, j]) for j in range(2)] for i in range(2)]
    F0 = carrier(tC, ac, mc)
    YF = matvec(Y, F0)
    M = matmul(Y, jacobian(tC, aC, muC))
    M = [[cb(1 if i == j else 0) - M[i][j] for j in range(2)] for i in range(2)]
    radii = (rad_a, rad_mu)
    kr = [
        YF[i].abs_hi() + sum(M[i][j].abs_hi() * radii[j] for j in range(2))
        for i in range(2)
    ]
    if not (kr[0] < rad_a and kr[1] < rad_mu):
        raise RuntimeError("overlap uniqueness Krawczyk failure")
    return {
        "t": t,
        "radius_a": rad_a,
        "radius_mu": rad_mu,
        "krawczyk_a": kr[0],
        "krawczyk_mu": kr[1],
    }
