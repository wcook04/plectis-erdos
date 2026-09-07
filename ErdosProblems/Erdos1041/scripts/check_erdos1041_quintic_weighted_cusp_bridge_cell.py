#!/usr/bin/env python3
"""Exact full five-sheet bridge cell next to the weighted quintic cusp.

The parameter interval is

    1/10000 <= u <= 1001/10000000,       kappa = u^3.

Three sheets are isolated in the weighted mu=-10 chart.  The other two are
isolated in the regular (t,a,mu) chart at the upper mu_* germ.  Every
acceptance test uses Fraction arithmetic and outward complex discs.  The
mpmath values are Newton scouts only.
"""

from __future__ import annotations

from fractions import Fraction as Fr
import importlib.util
from pathlib import Path

import mpmath as mp
import sympy as sp


HERE = Path(__file__).resolve().parent


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


BALL = load("bridge_cball", HERE / "lib_erdos1041_cball.py")
WALL = load("bridge_wall", HERE / "lib_erdos1041_wall_engine.py")
CB, cb, cb_pt = BALL.CB, BALL.cb, BALL.cb_pt
mp.mp.dps = 70


def report(name: str, ok: bool, detail: str = "") -> None:
    print(("PASS " if ok else "FAIL ") + name + ((" :: " + detail) if detail else ""))
    if not ok:
        raise AssertionError(name)


def cpow(value: CB, power: int) -> CB:
    out = cb(1)
    for _ in range(power):
        out = out * value
    return out


def as_fraction(value: sp.Expr) -> Fr:
    value = sp.Rational(value)
    return Fr(int(value.p), int(value.q))


def absolute_ball(value: CB) -> CB:
    lo = WALL.sqrt_lo(value.cabs2()) - value.r
    hi = WALL.sqrt_hi(value.cabs2()) + value.r
    report("direction is separated from zero", lo > 0)
    return CB((lo + hi) / 2, 0, WALL.snap_up((hi - lo) / 2), _raw=True)


U_LO = Fr(1, 10000)
U_HI = Fr(1001, 10000000)
U = CB((U_LO + U_HI) / 2, 0, (U_HI - U_LO) / 2, _raw=True)


# ---------------------------------------------------------------- mu=-10 chart

u, z, sigma = sp.symbols("u z sigma")
kappa = sigma * u**3
mu = -10 + sigma * u * z
A = 4 * (mu + 4)
B = -sp.Rational(12, 25) * (3 * mu**3 - 5 * mu**2 - 100 * mu - 200)
C = sp.Rational(4, 3125) * (mu + 10) ** 3 * (27 * mu**2 + 140 * mu + 200)
K = sp.expand(
    C**2 * (1 + kappa) ** 3
    - A * B * C * kappa * (1 + kappa) * (1 + 4 * kappa)
    + (A**3 * C + B**3) * kappa**2 * (1 + 2 * kappa)
    - A**2 * B**2 * kappa**3
)
H = sp.cancel(K / u**6)
D = A**2 * kappa - B * (1 + kappa)
P = sp.cancel((C * (1 + kappa) ** 2 - A * B * kappa**2) / (kappa * D))
H0 = sp.Rational(2304, 625) * (z**6 + 16200 * z**3 + 590490000)
report("BR1 weighted carrier is polynomial", sp.denom(H) == 1)
report("BR2 weighted limiting fibre", sp.expand(H.subs({sigma: 1, u: 0}) - H0) == 0)


def eval_u(poly_expr: sp.Expr, u_ball: CB) -> CB:
    poly = sp.Poly(sp.expand(poly_expr), u)
    out = cb(0)
    for power in range(poly.degree(), -1, -1):
        out = out * u_ball + cb(as_fraction(poly.nth(power)))
    return out


def coeffs_in_z(poly_expr: sp.Expr, u_ball: CB) -> list[CB]:
    poly = sp.Poly(sp.expand(poly_expr), z)
    return [eval_u(poly.nth(power), u_ball) for power in range(poly.degree(), -1, -1)]


def eval_uz(poly_expr: sp.Expr, u_ball: CB, z_ball: CB) -> CB:
    return BALL.poly_cb(coeffs_in_z(poly_expr, u_ball), z_ball)


def eval_rational(expr: sp.Expr, u_ball: CB, z_ball: CB) -> CB:
    numerator, denominator = sp.together(expr).as_numer_denom()
    return eval_uz(numerator, u_ball, z_ball) / eval_uz(denominator, u_ball, z_ball)


hs = sp.expand(H.subs(sigma, 1))
hz = sp.diff(hs, z)
ps = sp.cancel(P.subs(sigma, 1))

# Rouché on |z|=30.  The limiting factor lower bound is
# (2304/625)*(27000-24300)^2.
h0_poly = sp.Poly(hs.subs(u, 0), z)
h_poly = sp.Poly(hs, z)
perturbation = Fr(0)
for power in range(h_poly.degree() + 1):
    delta = eval_u(h_poly.nth(power), U) - cb(as_fraction(h0_poly.nth(power)))
    perturbation += delta.abs_hi() * Fr(30) ** power
rouche_lower = Fr(2304, 625) * Fr(2700) ** 2
report(
    "BR3 six weighted roots remain exhaustive",
    perturbation < rouche_lower,
    f"ratio={float(perturbation / rouche_lower):.8f}",
)

q_plus = -8100 + 16200j * mp.sqrt(2)
limiting_roots: list[mp.mpc] = []
for q_scout in (q_plus, q_plus.conjugate()):
    root = mp.exp(mp.log(q_scout) / 3)
    limiting_roots.extend(root * mp.exp(2j * mp.pi * j / 3) for j in range(3))
upper_scouts = [root for root in limiting_roots if root.imag > 0]


def certify_wall(mu_ball: CB, ray_ball: CB, mu_scout, ray_scout, *, cusp: bool):
    return WALL.certified_excess(
        mu_scout,
        ray_scout,
        muC=WALL.CB(mu_ball.a, mu_ball.b, mu_ball.r, _raw=True),
        wC=WALL.CB(ray_ball.a, ray_ball.b, ray_ball.r, _raw=True),
        k=20,
        s0=Fr(1, 10**14) if cusp else Fr(1, 10**10),
        ratio=0.06,
        eps_step=Fr(1, 10000),
        want_grad=True,
    )


cusp_boxes: list[CB] = []
cusp_results = []
u_mid_mp = mp.mpf((U_LO + U_HI).numerator) / (U_LO + U_HI).denominator
u_mid_mp *= mp.mpf("0.5")
hfun = sp.lambdify((u, z), hs, "mpmath")
for index, root0 in enumerate(upper_scouts):
    scout = mp.findroot(lambda zz: hfun(u_mid_mp, zz), root0)
    enclosure = None
    for radius in (Fr(1, 100), Fr(1, 20), Fr(1, 10), Fr(1, 2)):
        enclosure = BALL.krawczyk(
            coeffs_in_z(hs, U),
            coeffs_in_z(hz, U),
            cb(0),
            cb_pt(scout),
            radius,
            iters=30,
        )
        if enclosure is not None:
            break
    report(f"BR4 cusp sheet {index} Krawczyk", enclosure is not None)
    assert enclosure is not None
    report(f"BR5 cusp sheet {index} stays upper", enclosure.b - enclosure.r > 0)
    cusp_boxes.append(enclosure)

    mu_ball = cb(-10) + U * enclosure
    pair_sum = eval_rational(ps, U, enclosure)
    third = -cb(4) * (mu_ball + cb(4)) - pair_sum
    cross = pair_sum.conj() * third
    report(f"BR6 cusp sheet {index} chamber separated", abs(cross.b) > cross.r)
    epsilon = -1 if cross.b > 0 else 1
    ray_ball = -cb(epsilon) * cb(0, 1) * pair_sum * absolute_ball(pair_sum).inv()
    mu_scout = -10 + u_mid_mp * scout
    pair_scout = mp.mpc(
        mp.mpf(pair_sum.a.numerator) / pair_sum.a.denominator,
        mp.mpf(pair_sum.b.numerator) / pair_sum.b.denominator,
    )
    ray_scout = -epsilon * 1j * pair_scout / abs(pair_scout)
    result = certify_wall(mu_ball, ray_ball, mu_scout, ray_scout, cusp=True)
    report(
        f"BR7 cusp sheet {index} uniform negative excess",
        result["hi"] < -Fr(1, 20),
        f"E<{result['hi_f']:.9f}",
    )
    report(
        f"BR8 cusp sheet {index} compact gradients",
        result["grad_mu_q"] < Fr(1, 2) and result["grad_phi_q"] < Fr(13, 2),
        f"Gmu<{result['grad_mu']:.6f}, Gphi<{result['grad_phi']:.6f}",
    )
    cusp_results.append(result)

report(
    "BR9 three upper cusp tubes are disjoint",
    all((cusp_boxes[i] - cusp_boxes[j]).abs_lo() > 0 for i in range(3) for j in range(i)),
)


# ---------------------------------------------------------------- mu_* chart

def abc(mu_ball: CB) -> tuple[CB, CB, CB]:
    return (
        cb(4) * (mu_ball + cb(4)),
        -cb(Fr(12, 25))
        * (cb(3) * cpow(mu_ball, 3) - cb(5) * cpow(mu_ball, 2) - cb(100) * mu_ball - cb(200)),
        cb(Fr(4, 3125))
        * cpow(mu_ball + cb(10), 3)
        * (cb(27) * cpow(mu_ball, 2) + cb(140) * mu_ball + cb(200)),
    )


def abc_prime(mu_ball: CB) -> tuple[CB, CB, CB]:
    return (
        cb(4),
        -cb(Fr(12, 25)) * (cb(9) * cpow(mu_ball, 2) - cb(10) * mu_ball - cb(100)),
        cb(Fr(4, 3125))
        * (
            cb(3) * cpow(mu_ball + cb(10), 2)
            * (cb(27) * cpow(mu_ball, 2) + cb(140) * mu_ball + cb(200))
            + cpow(mu_ball + cb(10), 3) * (cb(54) * mu_ball + cb(140))
        ),
    )


def carrier(t: CB, a: CB, mu_ball: CB) -> tuple[CB, CB]:
    aa, bb, cc = abc(mu_ball)
    one = cb(1)
    return (
        (one + t + t * t) * a * a + (one + t) * aa * a + bb,
        t * (one + t) * cpow(a, 3) + t * aa * a * a - cc,
    )


def jacobian(t: CB, a: CB, mu_ball: CB) -> list[list[CB]]:
    aa, _, _ = abc(mu_ball)
    ap, bp, cp = abc_prime(mu_ball)
    one = cb(1)
    return [
        [cb(2) * (one + t + t * t) * a + (one + t) * aa, (one + t) * ap * a + bp],
        [cb(3) * t * (one + t) * a * a + cb(2) * t * aa * a, t * ap * a * a - cp],
    ]


def matmul(left, right):
    return [[sum((left[i][k] * right[k][j] for k in range(2)), cb(0)) for j in range(2)] for i in range(2)]


def matvec(matrix, vector):
    return [sum((matrix[i][k] * vector[k] for k in range(2)), cb(0)) for i in range(2)]


kappa_lo = U_LO**3
kappa_hi = U_HI**3
t_lo = kappa_lo
t_hi = kappa_hi + 4 * kappa_hi**3
report("BR10 t-preimage enclosure is in monotone range", 0 < t_lo < t_hi < Fr(1, 4))
t_ball = CB((t_lo + t_hi) / 2, 0, (t_hi - t_lo) / 2, _raw=True)
t_mid_mp = mp.mpf((t_lo + t_hi).numerator) / (t_lo + t_hi).denominator / 2
mu_star = (-mp.mpf(70) + 10j * mp.sqrt(5)) / 27
A_star = 4 * (mu_star + 4)
B_star = -mp.mpf(12) / 25 * (3 * mu_star**3 - 5 * mu_star**2 - 100 * mu_star - 200)
a_starts = mp.polyroots([1, A_star, B_star], maxsteps=200)

mustar_boxes: list[tuple[CB, CB]] = []
mustar_results = []
for index, a_start in enumerate(a_starts):
    a_scout, mu_scout = mp.findroot(
        lambda av, mv: (
            (1 + t_mid_mp + t_mid_mp**2) * av**2
            + (1 + t_mid_mp) * 4 * (mv + 4) * av
            - mp.mpf(12) / 25 * (3 * mv**3 - 5 * mv**2 - 100 * mv - 200),
            t_mid_mp * (1 + t_mid_mp) * av**3
            + t_mid_mp * 4 * (mv + 4) * av**2
            - mp.mpf(4) / 3125 * (mv + 10) ** 3 * (27 * mv**2 + 140 * mv + 200),
        ),
        (a_start, mu_star),
        tol=mp.mpf("1e-60"),
        maxsteps=100,
    )
    a0, mu0 = cb_pt(a_scout), cb_pt(mu_scout)
    if index == 0:
        a_radius, mu_radius = Fr(1, 10**13), Fr(1, 10**14)
    else:
        a_radius, mu_radius = Fr(1, 2 * 10**12), Fr(1, 3 * 10**13)
    a_ball = CB(a0.a, a0.b, a_radius, _raw=True)
    mu_ball = CB(mu0.a, mu0.b, mu_radius, _raw=True)

    # Numerical inverse, snapped to exact rationals; the ball self-map below
    # is the proof and retains the entire inverse error.
    cp_scout = mp.mpf(4) / 3125 * (
        3 * (mu_scout + 10) ** 2 * (27 * mu_scout**2 + 140 * mu_scout + 200)
        + (mu_scout + 10) ** 3 * (54 * mu_scout + 140)
    )
    bp_scout = -mp.mpf(12) / 25 * (9 * mu_scout**2 - 10 * mu_scout - 100)
    jac_scout = mp.matrix(
        [
            [
                2 * (1 + t_mid_mp + t_mid_mp**2) * a_scout + (1 + t_mid_mp) * 4 * (mu_scout + 4),
                4 * (1 + t_mid_mp) * a_scout + bp_scout,
            ],
            [
                3 * t_mid_mp * (1 + t_mid_mp) * a_scout**2
                + 2 * t_mid_mp * 4 * (mu_scout + 4) * a_scout,
                4 * t_mid_mp * a_scout**2 - cp_scout,
            ],
        ]
    )
    inverse = jac_scout**-1
    inverse_ball = [[cb_pt(inverse[i, j]) for j in range(2)] for i in range(2)]
    residual = matvec(inverse_ball, carrier(t_ball, a0, mu0))
    defect = matmul(inverse_ball, jacobian(t_ball, a_ball, mu_ball))
    defect = [[cb(1 if i == j else 0) - defect[i][j] for j in range(2)] for i in range(2)]
    radii = (a_radius, mu_radius)
    kraw_radii = [
        residual[i].abs_hi() + sum(defect[i][j].abs_hi() * radii[j] for j in range(2))
        for i in range(2)
    ]
    report(
        f"BR11 mu_* sheet {index} parametric Krawczyk",
        kraw_radii[0] < a_radius and kraw_radii[1] < mu_radius,
        f"Ka={float(kraw_radii[0]):.3e}, Kmu={float(kraw_radii[1]):.3e}",
    )
    mustar_boxes.append((a_ball, mu_ball))

    pair_sum = (cb(1) + t_ball) * a_ball
    third = -abc(mu_ball)[0] - pair_sum
    cross = pair_sum.conj() * third
    report(f"BR12 mu_* sheet {index} chamber separated", abs(cross.b) > cross.r)
    epsilon = -1 if cross.b > 0 else 1
    ray_ball = -cb(epsilon) * cb(0, 1) * pair_sum * absolute_ball(pair_sum).inv()
    pair_scout = (1 + t_mid_mp) * a_scout
    ray_scout = -epsilon * 1j * pair_scout / abs(pair_scout)
    result = certify_wall(mu_ball, ray_ball, mu_scout, ray_scout, cusp=False)
    report(
        f"BR13 mu_* sheet {index} uniform negative excess",
        result["hi"] < -Fr(1),
        f"E<{result['hi_f']:.9f}",
    )
    report(
        f"BR14 mu_* sheet {index} compact gradients",
        result["grad_mu_q"] < Fr(2, 5) and result["grad_phi_q"] < Fr(13, 2),
        f"Gmu<{result['grad_mu']:.6f}, Gphi<{result['grad_phi']:.6f}",
    )
    mustar_results.append(result)

report("BR15 two mu_* sheets are separated by the a-coordinate", (mustar_boxes[0][0] - mustar_boxes[1][0]).abs_lo() > 0)
report(
    "BR16 all five upper sheets have a common exact cell bound",
    max(result["hi"] for result in cusp_results + mustar_results) < -Fr(1, 20),
)
report(
    "BR17 all five upper sheets satisfy SS22 gradients",
    all(result["grad_mu_q"] < 2 and result["grad_phi_q"] < 8 for result in cusp_results + mustar_results),
)

print("CERTIFIED full five-sheet bridge cell: 1e-4 <= u <= 1.001e-4.")
print("ALL CHECKS PASSED")
