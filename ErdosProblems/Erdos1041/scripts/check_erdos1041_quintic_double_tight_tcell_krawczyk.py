#!/usr/bin/env python3
"""Exact parametric Krawczyk replay for one regular double-tight t-cell.

All acceptance inequalities use Fraction arithmetic and the exact outward-
rounded complex discs from lib_erdos1041_cball.py.  Decimal centres are only
Newton scouts: the Krawczyk self-map is the existence/uniqueness proof.
"""

from __future__ import annotations

from fractions import Fraction as Fr
import importlib.util
from pathlib import Path
import mpmath as mp


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("cball", HERE / "lib_erdos1041_cball.py")
BALL = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(BALL)
CB, cb, cb_pt = BALL.CB, BALL.cb, BALL.cb_pt

SUPPORT_SPEC = importlib.util.spec_from_file_location(
    "support_engine", HERE / "lib_erdos1041_support_engine.py"
)
SUPPORT = importlib.util.module_from_spec(SUPPORT_SPEC)
assert SUPPORT_SPEC.loader is not None
SUPPORT_SPEC.loader.exec_module(SUPPORT)


def report(name: str, ok: bool, detail: str = "") -> None:
    print(("PASS " if ok else "FAIL ") + name + ((" :: " + detail) if detail else ""))
    if not ok:
        raise AssertionError(name)


def cpow(z: CB, n: int) -> CB:
    out = cb(1)
    for _ in range(n):
        out = out * z
    return out


def abc(mu: CB) -> tuple[CB, CB, CB]:
    A = cb(4) * (mu + cb(4))
    B = -cb(Fr(12, 25)) * (
        cb(3) * cpow(mu, 3) - cb(5) * cpow(mu, 2) - cb(100) * mu - cb(200)
    )
    C = cb(Fr(4, 3125)) * cpow(mu + cb(10), 3) * (
        cb(27) * cpow(mu, 2) + cb(140) * mu + cb(200)
    )
    return A, B, C


def abc_prime(mu: CB) -> tuple[CB, CB, CB]:
    Ap = cb(4)
    Bp = -cb(Fr(12, 25)) * (cb(9) * cpow(mu, 2) - cb(10) * mu - cb(100))
    Cp = cb(Fr(4, 3125)) * (
        cb(3) * cpow(mu + cb(10), 2)
        * (cb(27) * cpow(mu, 2) + cb(140) * mu + cb(200))
        + cpow(mu + cb(10), 3) * (cb(54) * mu + cb(140))
    )
    return Ap, Bp, Cp


def carrier(t: CB, a: CB, mu: CB) -> tuple[CB, CB]:
    A, B, C = abc(mu)
    one = cb(1)
    E1 = (one + t + cpow(t, 2)) * cpow(a, 2) + (one + t) * A * a + B
    E2 = t * (one + t) * cpow(a, 3) + t * A * cpow(a, 2) - C
    return E1, E2


def jacobian(t: CB, a: CB, mu: CB) -> list[list[CB]]:
    A, _, _ = abc(mu)
    Ap, Bp, Cp = abc_prime(mu)
    one = cb(1)
    return [
        [cb(2) * (one + t + cpow(t, 2)) * a + (one + t) * A,
         (one + t) * Ap * a + Bp],
        [cb(3) * t * (one + t) * cpow(a, 2) + cb(2) * t * A * a,
         t * Ap * cpow(a, 2) - Cp],
    ]


def t_derivative(t: CB, a: CB, mu: CB) -> tuple[CB, CB]:
    A, _, _ = abc(mu)
    one = cb(1)
    return ((one + cb(2) * t) * cpow(a, 2) + A * a,
            (one + cb(2) * t) * cpow(a, 3) + A * cpow(a, 2))


def matmul(A: list[list[CB]], B: list[list[CB]]) -> list[list[CB]]:
    return [[sum((A[i][k] * B[k][j] for k in range(2)), cb(0))
             for j in range(2)] for i in range(2)]


def matvec(A: list[list[CB]], x: tuple[CB, CB] | list[CB]) -> list[CB]:
    return [sum((A[i][k] * x[k] for k in range(2)), cb(0)) for i in range(2)]


mp.mp.dps = 80
T0 = Fr(1, 1000)
T_RADIUS = Fr(1, 5000000)  # [0.0009998,0.0010002]
A_RADIUS = Fr(1, 250)
MU_RADIUS = Fr(1, 2000)

# Newton scouts at t=1/1000.  They carry no acceptance authority.
a_mp = mp.mpc(
    "6.81037351291131349533675529051033966781454967749276693432113",
    "-56.0253967664757432057546974556872290565201325754425564087594",
)
mu_mp = mp.mpc(
    "-13.1212730489269275803414246629045547501488310966193728200182",
    "1.7637781695171781718210306195912684115951886828383777239068",
)
a0, mu0 = cb_pt(a_mp), cb_pt(mu_mp)
tC = CB(T0, 0, T_RADIUS, _raw=True)
aC = CB(a0.a, a0.b, A_RADIUS, _raw=True)
muC = CB(mu0.a, mu0.b, MU_RADIUS, _raw=True)


def mp_jacobian(t: mp.mpf, a: mp.mpc, mu: mp.mpc) -> mp.matrix:
    A = 4 * (mu + 4)
    Bp = -mp.mpf(12) / 25 * (9 * mu**2 - 10 * mu - 100)
    Cp = mp.mpf(4) / 3125 * (
        3 * (mu + 10)**2 * (27 * mu**2 + 140 * mu + 200)
        + (mu + 10)**3 * (54 * mu + 140)
    )
    return mp.matrix([
        [2 * (1 + t + t**2) * a + (1 + t) * A, 4 * (1 + t) * a + Bp],
        [3 * t * (1 + t) * a**2 + 2 * t * A * a, 4 * t * a**2 - Cp],
    ])


# Exact rational approximation to a numerical inverse is allowed: all error is
# retained by the subsequent ball self-map test.
Ymp = mp_jacobian(mp.mpf(1) / 1000, a_mp, mu_mp) ** -1
Y = [[cb_pt(Ymp[i, j]) for j in range(2)] for i in range(2)]
F0 = carrier(tC, a0, mu0)
YF = matvec(Y, F0)
JX = jacobian(tC, aC, muC)
M = matmul(Y, JX)
M = [[cb(1 if i == j else 0) - M[i][j] for j in range(2)] for i in range(2)]
radii = (A_RADIUS, MU_RADIUS)
kraw_radii = [
    YF[i].abs_hi() + sum(M[i][j].abs_hi() * radii[j] for j in range(2))
    for i in range(2)
]
report("TC1 parametric Krawczyk self-map",
       kraw_radii[0] < A_RADIUS and kraw_radii[1] < MU_RADIUS,
       f"Ka={float(kraw_radii[0]):.9g}<{float(A_RADIUS):.9g}, "
       f"Kmu={float(kraw_radii[1]):.9g}<{float(MU_RADIUS):.9g}")

# Invert the interval Jacobian algebraically and differentiate the two carrier
# equations.  Nonvanishing is certified by the exact disc lower bound.
J = jacobian(tC, aC, muC)
det = J[0][0] * J[1][1] - J[0][1] * J[1][0]
report("TC2 interval Jacobian nonsingular", det.abs_lo() > 12000,
       f"|det|>{float(det.abs_lo()):.6f}")
Ft = t_derivative(tC, aC, muC)
a_t = -(J[1][1] * Ft[0] - J[0][1] * Ft[1]) / det
mu_t = -(-J[1][0] * Ft[0] + J[0][0] * Ft[1]) / det
report("TC3 derivative bounds", a_t.abs_hi() < 10000 and mu_t.abs_hi() < 1500,
       f"|a_t|<{float(a_t.abs_hi()):.6f}, |mu_t|<{float(mu_t.abs_hi()):.6f}")

# The wall sign is constant.  Since p=(1+t)a and h=-A-p, epsilon=-1 and
# d=e^{-i phi}=i p/|p| throughout this cell.
p = (cb(1) + tC) * aC
h = -abc(muC)[0] - p
cross = p.conj() * h
report("TC4 wall side and direction fixed", cross.b - cross.r > 1900,
       f"Im(conj(p)h)>{float(cross.b-cross.r):.6f}, epsilon=-1")
p_t = aC + (cb(1) + tC) * a_t
logp_t = p_t / p
phi_t = abs(logp_t.b) + logp_t.r
report("TC5 wall-angle derivative", phi_t < 87,
       f"|phi_t|<{float(phi_t):.6f}")

# Relate the already-certified kappa=1/1000 anchor to this t-chart.  On
# [0,1], kappa(t)=t/(1+t^2) is strictly increasing.  Direct rational
# comparisons bracket its unique preimage t_* in [t0,t0+2e-9].
def kappa(q: Fr) -> Fr:
    return q / (1 + q*q)

tstar_hi = T0 + Fr(1, 500000000)
report("TC6 anchor preimage bracket",
       kappa(T0) < Fr(1, 1000) < kappa(tstar_hi))

# Certify the sign on the entire parameter tube directly.  This deliberately
# avoids importing any arm-gradient bound.  The support engine integrates a
# nonnegative half-angle/Stieltjes density, so parameter widening cannot be
# hidden by cancellation between two large arclengths.
p2 = p.cabs2()
p_lo = SUPPORT.wall.sqrt_lo(p2) - p.r
p_hi = SUPPORT.wall.sqrt_hi(p2) + p.r
report("TC7 active direction separated from zero", p_lo > 50,
       f"|p|>{float(p_lo):.6f}")
p_abs = CB((p_lo + p_hi) / 2, 0, SUPPORT.wall.snap_up((p_hi - p_lo) / 2), _raw=True)
wC = cb(0, 1) * p * p_abs.inv()
p_mp = (1 + mp.mpf(1) / 1000) * a_mp
w_mp = 1j * p_mp / abs(p_mp)
mu_support = SUPPORT.CB(muC.a, muC.b, muC.r, _raw=True)
w_support = SUPPORT.CB(wC.a, wC.b, wC.r, _raw=True)
arms = [
    SUPPORT.certified_arm(mu_support, w_support, mu_mp, w_mp, sign, cells=2048)
    for sign in (+1, -1)
]
pair_upper = SUPPORT.wall.snap_up(arms[0][0] + arms[1][0])
report("TC8 direct support bound on the whole t-cell", pair_upper < -Fr(1, 200),
       f"E<{float(pair_upper):.9f}<-1/200")

# A second, scalable certificate pays parameter uncertainty only once.  First
# isolate the exact centre fibre kappa=t/(1+t^2)=1000/1000001 and certify its
# arclength excess.  Then rerun only the nonnegative gradient integrals on the
# full parameter tube and apply the exact chain rule.
mu_point_C, w_point_C, mu_point, w_point, _ = SUPPORT.certified_carrier_input(
    Fr(1000, 1000001), scout_mu=mu_mp
)
point = SUPPORT.wall.certified_excess(
    mu_point, w_point, muC=mu_point_C, wC=w_point_C, k=20,
    s0=Fr(1, 10**10), ratio=0.06, msub=6,
    eps_step=Fr(1, 10**7), want_grad=True,
)
report("TC9 exact centre excess", point["hi"] < -Fr(1, 10),
       f"E0<{point['hi_f']:.9f}<-1/10")
tube = SUPPORT.wall.certified_excess(
    mu_mp, w_mp, muC=mu_support, wC=w_support, k=20,
    s0=Fr(1, 10**10), ratio=0.06, msub=6,
    eps_step=Fr(1, 10**7), want_grad=True, gradient_only=True,
)
transport_L = (
    tube["grad_mu_q"] * mu_t.abs_hi()
    + tube["grad_phi_q"] * phi_t
)
transport_upper = point["hi"] + transport_L * T_RADIUS
report("TC10 exact gradient transport on the whole t-cell",
       transport_upper < -Fr(1, 10),
       f"Gmu<{tube['grad_mu']:.6f}, Gphi<{tube['grad_phi']:.6f}, "
       f"E<{float(transport_upper):.9f}<-1/10")

print("ALL CHECKS PASSED")
