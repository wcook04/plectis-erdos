#!/usr/bin/env python3
"""Exact carrier-side certificate for the microscopic double-tight cusp.

This checker treats

    kappa = sigma*u^3,  mu = -10 + sigma*u*z,  sigma in {-1,+1},
    0 <= u <= 10^-4.

It proves, with rational/dyadic complex-ball arithmetic, that the six finite
branches issuing from the mu=-10 carrier fibre remain simple and exhaustive
in |z|<30, and that along each branch

    |d mu/du| < 30,       |d phi/du| < 6.

The mpmath values below are root *scouts* only.  Every asserted enclosure is
reproved by the exact Krawczyk routine in lib_erdos1041_cball.py.

Boundary: this is deliberately not a certificate for the two compact arm
gradient bounds G_mu<=2 and G_phi<=8 in SS22.  Consequently it does not, by
itself, invoke SS23 or close the punctured cusp neighborhood.
"""

from __future__ import annotations

import importlib.util
from fractions import Fraction as Fr
from pathlib import Path

import mpmath as mp
import sympy as s


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "lib_erdos1041_cball", HERE / "lib_erdos1041_cball.py"
)
CBALL = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(CBALL)
CB = CBALL.CB
cb = CBALL.cb
cb_pt = CBALL.cb_pt
krawczyk = CBALL.krawczyk
poly_cb = CBALL.poly_cb


def report(name: str, ok: bool, detail: str = "") -> None:
    suffix = f"  {detail}" if detail else ""
    print(("PASS " if ok else "FAIL ") + name + suffix)
    if not ok:
        raise AssertionError(name)


# ---------------------------------------------------------------- symbolic carrier

u, z, sigma = s.symbols("u z sigma")
kappa = sigma * u**3
mu = -10 + sigma * u * z
A = 4 * (mu + 4)
B = -s.Rational(12, 25) * (3 * mu**3 - 5 * mu**2 - 100 * mu - 200)
C = s.Rational(4, 3125) * (mu + 10) ** 3 * (27 * mu**2 + 140 * mu + 200)
K = s.expand(
    C**2 * (1 + kappa) ** 3
    - A * B * C * kappa * (1 + kappa) * (1 + 4 * kappa)
    + (A**3 * C + B**3) * kappa**2 * (1 + 2 * kappa)
    - A**2 * B**2 * kappa**3
)
H = s.cancel(K / u**6)
D = A**2 * kappa - B * (1 + kappa)
P = s.cancel((C * (1 + kappa) ** 2 - A * B * kappa**2) / (kappa * D))

H0_TARGET = s.Rational(2304, 625) * (
    z**6 + 16200 * z**3 + 590490000
)
report("CUSP1 weighted carrier is polynomial", s.denom(H) == 1)
report(
    "CUSP2 limiting fibre",
    all(s.expand(H.subs({sigma: sg, u: 0}) - H0_TARGET) == 0 for sg in (-1, 1)),
)


# --------------------------------------------------------------- exact ball helpers

def as_fraction(value: s.Expr) -> Fr:
    value = s.Rational(value)
    return Fr(int(value.p), int(value.q))


def eval_u(poly_expr: s.Expr, u_ball: CB) -> CB:
    """Evaluate a rational polynomial in u on a dyadic complex ball."""
    poly = s.Poly(s.expand(poly_expr), u)
    out = cb(0)
    for power in range(poly.degree(), -1, -1):
        out = out * u_ball + cb(as_fraction(poly.nth(power)))
    return out


def coeffs_in_z(poly_expr: s.Expr, u_ball: CB) -> list[CB]:
    poly = s.Poly(s.expand(poly_expr), z)
    return [eval_u(poly.nth(power), u_ball) for power in range(poly.degree(), -1, -1)]


def eval_uz(poly_expr: s.Expr, u_ball: CB, z_ball: CB) -> CB:
    return poly_cb(coeffs_in_z(poly_expr, u_ball), z_ball)


def eval_rational(expr: s.Expr, u_ball: CB, z_ball: CB) -> CB:
    numerator, denominator = s.together(expr).as_numer_denom()
    return eval_uz(numerator, u_ball, z_ball) / eval_uz(denominator, u_ball, z_ball)


# The complex disc centred at 1/20000 with radius 1/20000 contains the real
# interval [0,10^-4].  Proving on this disc is stronger than required.
U = CB(Fr(1, 20000), 0, Fr(1, 20000), _raw=True)
RADIUS = Fr(30)
ROUCHE_LOWER = Fr(2304, 625) * Fr(2700) ** 2

# Exact modulus of each root q of q^2+16200q+590490000 is 24300.  Hence on
# |z|=30 each factor |z^3-q| is at least 27000-24300=2700.
report("CUSP3 exact limiting q-root modulus", 24300**2 == 590490000)

mp.mp.dps = 80
q_plus = -8100 + 16200j * mp.sqrt(2)
root_scouts: list[mp.mpc] = []
for q_scout in (q_plus, q_plus.conjugate()):
    root = mp.exp(mp.log(q_scout) / 3)
    root_scouts.extend(root * mp.exp(2j * mp.pi * j / 3) for j in range(3))

max_mu_prime = Fr(0)
max_phi_prime = Fr(0)
max_z = Fr(0)
max_z_prime = Fr(0)
min_p = None
rouche_ratios: list[Fr] = []
all_boxes: dict[int, list[CB]] = {}

for sg in (-1, 1):
    hs = s.expand(H.subs(sigma, sg))
    hu = s.diff(hs, u)
    hz = s.diff(hs, z)
    ps = s.cancel(P.subs(sigma, sg))
    pu = s.diff(ps, u)
    pz = s.diff(ps, z)

    # Rouché: H=H(0,.)+Delta has exactly the six limiting roots in |z|<30.
    h0 = s.Poly(hs.subs(u, 0), z)
    hz_poly = s.Poly(hs, z)
    perturbation = Fr(0)
    for power in range(hz_poly.degree() + 1):
        delta_coeff = eval_u(hz_poly.nth(power), U) - cb(as_fraction(h0.nth(power)))
        perturbation += delta_coeff.abs_hi() * RADIUS**power
    report(
        f"CUSP4 sigma={sg:+d} Rouche six-root count",
        perturbation < ROUCHE_LOWER,
        f"perturbation/lower={float(perturbation / ROUCHE_LOWER):.6f}",
    )
    rouche_ratios.append(perturbation / ROUCHE_LOWER)

    h_coeffs = coeffs_in_z(hs, U)
    hz_coeffs = coeffs_in_z(hz, U)
    boxes: list[CB] = []
    for index, root_scout in enumerate(root_scouts):
        enclosure = None
        for radius in (Fr(1, 100), Fr(1, 20), Fr(1, 10), Fr(1, 2)):
            enclosure = krawczyk(
                h_coeffs,
                hz_coeffs,
                cb(0),
                cb_pt(root_scout),
                radius,
                iters=20,
            )
            if enclosure is not None:
                break
        report(f"CUSP5 sigma={sg:+d} branch={index} Krawczyk", enclosure is not None)
        assert enclosure is not None
        boxes.append(enclosure)

        hz_value = eval_uz(hz, U, enclosure)
        hu_value = eval_uz(hu, U, enclosure)
        report(
            f"CUSP6 sigma={sg:+d} branch={index} simple",
            not hz_value.contains_zero(),
        )
        z_prime = -hu_value / hz_value
        mu_prime = sg * (enclosure + U * z_prime)

        p_value = eval_rational(ps, U, enclosure)
        p_total_prime = eval_rational(pu, U, enclosure) + eval_rational(
            pz, U, enclosure
        ) * z_prime
        logarithmic_p_prime = p_total_prime / p_value

        max_z = max(max_z, enclosure.abs_hi())
        max_z_prime = max(max_z_prime, z_prime.abs_hi())
        max_mu_prime = max(max_mu_prime, mu_prime.abs_hi())
        max_phi_prime = max(max_phi_prime, logarithmic_p_prime.abs_hi())
        min_p = p_value.abs_lo() if min_p is None else min(min_p, p_value.abs_lo())

    # Pairwise disjoint boxes plus the Rouché count identify all six roots.
    disjoint = all(
        (boxes[i] - boxes[j]).abs_lo() > 0
        for i in range(len(boxes))
        for j in range(i)
    )
    report(f"CUSP7 sigma={sg:+d} six boxes disjoint", disjoint)
    all_boxes[sg] = boxes

report("CUSP8 all finite cusp roots satisfy |z|<30", max_z < 30, f"upper={float(max_z):.9f}")
report(
    "CUSP9 carrier derivative |dmu/du|<30",
    max_mu_prime < 30,
    f"upper={float(max_mu_prime):.9f}",
)
report(
    "CUSP10 wall derivative |dphi/du|<6",
    max_phi_prime < 6,
    f"upper={float(max_phi_prime):.9f}",
)
report("CUSP11 active-pair sum stays nonzero", min_p is not None and min_p > 35,
       f"lower={float(min_p):.9f}")

# This is only the exact implication requested in SS22--SS23.  The checker
# does not assert its hypotheses G_mu<=2 and G_phi<=8.
conditional_chain_constant = Fr(2) * Fr(30) + Fr(8) * Fr(6)
conditional_margin = -Fr(1, 80) + conditional_chain_constant * Fr(1, 10000)
report("CUSP12 conditional chain constant", conditional_chain_constant == 108)
report("CUSP13 conditional SS23 margin", conditional_margin == -Fr(17, 10000))

# ---------------------------------------------------------------- arm-gradient algebra
#
# These identities expose a cheaper exact route to the two still-open arm
# inequalities.  The mu-gradient is not merely bounded by a rational
# density: it is exactly the arclength density of the rational image x/C.
# For the phase density one can subtract a real constant (which does not
# affect its imaginary part) and use the inner value 1/2 or terminal value
# 4/5.  The latter differs from six copies of the mu primitive by one
# explicit delta-divisible correction.
x, m = s.symbols("x m")
F_model = x**5 + 5 * x**4 + 10 * x**3 + (10 + m) * x**2
A_model = x**3 + 5 * x**2 + 10 * x + 10 + m
C_model = 5 * x**3 + 20 * x**2 + 30 * x + 20 + 2 * m
Fpp_model = s.diff(F_model, x, 2)
mu_primitive = x / C_model
phase_scalar = s.cancel(Fpp_model * A_model / C_model**2)
mu_density = s.cancel(2 / C_model - Fpp_model / C_model**2)
report(
    "CUSP14 mu density is d(x/C)/dx",
    s.cancel(s.diff(mu_primitive, x) - mu_density) == 0,
)

outer_correction = s.cancel(
    2
    * (m + 10)
    * (-3 * m + 15 * x**3 + 15 * x**2 - 40 * x - 60)
    / (5 * C_model**2)
)
report(
    "CUSP15 outer phase identity",
    s.cancel(phase_scalar - s.Rational(4, 5) - 6 * mu_density - outer_correction)
    == 0,
)
inner_numerator = x * (
    24 * m * x**2
    + 60 * m * x
    + 40 * m
    + 15 * x**5
    + 120 * x**4
    + 420 * x**3
    + 840 * x**2
    + 900 * x
    + 400
)
report(
    "CUSP16 inner phase identity",
    s.cancel(phase_scalar - s.Rational(1, 2) - inner_numerator / (2 * C_model**2))
    == 0,
)

# Exact blow-up cancellation for the new identities.  Multiplication by
# dx=u dX removes the sole displayed 1/u in both phase remainders.
X = s.symbols("X")
m_weighted = -10 + sigma * u * z
x_weighted = u * X
c_weighted = s.cancel(C_model.subs({m: m_weighted, x: x_weighted}) / u)
outer_weighted = s.cancel(
    outer_correction.subs({m: m_weighted, x: x_weighted}) * u
)
inner_weighted = s.cancel(
    (inner_numerator / (2 * C_model**2)).subs(
        {m: m_weighted, x: x_weighted}
    )
    * u
)
report(
    "CUSP17 outer correction has no u pole after dx=u dX",
    s.Poly(s.denom(outer_weighted), u).nth(0) != 0,
)
report(
    "CUSP18 inner correction has no u pole after dx=u dX",
    s.Poly(s.denom(inner_weighted), u).nth(0) != 0,
)

print(
    "CERTIFIED carrier-side cusp bounds: "
    f"max Rouche ratio={float(max(rouche_ratios)):.9f}, "
    f"max |z'|={float(max_z_prime):.9f}, "
    f"max |mu'|={float(max_mu_prime):.9f}, "
    f"max |phi'|={float(max_phi_prime):.9f}."
)
print("OPEN exact compact-arm inequalities: G_mu<=2 and G_phi<=8.")
print("ALL ASSERTED CHECKS PASSED")
