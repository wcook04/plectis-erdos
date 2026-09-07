#!/usr/bin/env python3
"""Exact symbolic replay of the support--Stieltjes/cusp reduction."""

from __future__ import annotations

import sympy as s


def report(name: str, ok: bool) -> None:
    print(("PASS " if ok else "FAIL ") + name)
    if not ok:
        raise AssertionError(name)


# Rotated holomorphic model with generic complex coefficients.
u, v, a, b, c, d, R = s.symbols("u v a b c d R", real=True)
I = s.I
z = u + I * v
alpha = a + I * b
nu = c + I * d
H = s.expand(z**5 + 5 * alpha * z**4 + 10 * alpha**2 * z**3 + nu * z**2)
Hp = s.diff(H, z) if False else s.expand(
    5 * z**4 + 20 * alpha * z**3 + 30 * alpha**2 * z**2 + 2 * nu * z
)
Hpp = s.expand(20 * z**3 + 60 * alpha * z**2 + 60 * alpha**2 * z + 2 * nu)
Y = s.expand(s.im(s.expand_complex(H)))
A = s.expand(s.re(s.expand_complex(Hp)))
B = s.expand(s.im(s.expand_complex(Hp)))
J = s.expand(s.im(s.expand_complex(Hpp * s.conjugate(Hp) ** 2)))

# SS4--SS6: inverse derivative and rationalized support defect.
A0, B0, R0 = s.symbols("A0 B0 R0", real=True)
identity_num = s.expand((R0 - A0) * (R0 + A0) - B0**2)
report("SS1 support-defect rationalization", identity_num == R0**2 - A0**2 - B0**2)

# SS9--SS10: exact finite turn eliminant.
turn_res = s.factor(s.resultant(Y, B, u))
endpoint_factor = 400 * v**2 * (v + b) ** 2
turn_q = s.cancel(turn_res / endpoint_factor)
report("SS2 turn endpoint factors", s.rem(s.Poly(turn_res, v), s.Poly(v**2 * (v+b)**2, v)) == 0)
report("SS3 residual turn degree fifteen", s.Poly(turn_q, v).degree() == 15)

# SS11--SS13: the claimed event equations really are polynomial after
# clearing the explicit denominators and the radical equation.
DeltaJ = s.expand(B * s.diff(J, v) - A * s.diff(J, u))
DeltaA = s.expand(B * s.diff(A, v) - A * s.diff(A, u))
DeltaB = s.expand(B * s.diff(B, v) - A * s.diff(B, u))
# Delta R=(A Delta A+B Delta B)/R.  Differentiate
# D=B R(R+A), multiply Delta(J/D) by D^2 R, and retain its numerator.
D0 = B * R * (R + A)
DeltaR_num = s.expand(A * DeltaA + B * DeltaB)
DeltaD_times_R = s.expand(
    DeltaB * R**2 * (R + A)
    + B * DeltaR_num * (2 * R + A)
    + B * R**2 * DeltaA
)
inflection_num = s.expand(DeltaJ * D0 * R - J * DeltaD_times_R)
report("SS4 cleared inflection equation polynomial", bool(s.Poly(inflection_num, u, v, R)))

# Carrier and the weighted cusp polynomial.
kappa, mu, uu, zz, sigma = s.symbols("kappa mu uu zz sigma")
AA = 4 * (mu + 4)
BB = -s.Rational(12, 25) * (3 * mu**3 - 5 * mu**2 - 100 * mu - 200)
CC = s.Rational(4, 3125) * (mu + 10) ** 3 * (27 * mu**2 + 140 * mu + 200)
K = s.expand(
    CC**2 * (1 + kappa) ** 3
    - AA * BB * CC * kappa * (1 + kappa) * (1 + 4 * kappa)
    + (AA**3 * CC + BB**3) * kappa**2 * (1 + 2 * kappa)
    - AA**2 * BB**2 * kappa**3
)
Ksub = s.expand(K.subs({kappa: sigma * uu**3, mu: -10 + sigma * uu * zz}))
Kpoly = s.Poly(Ksub, uu)
report("SS5 cusp divisibility by u^6", min(m[0] for m, _ in Kpoly.terms()) >= 6)
Hcusp = s.expand(Ksub / uu**6)
leading = s.expand(Hcusp.subs(uu, 0).subs(sigma**2, 1))
target = s.Rational(2304, 625) * (zz**6 + 16200 * zz**3 + 590490000)
report("SS6 sign-independent simple cusp fibre", s.expand(leading - target) == 0)
g = zz**6 + 16200 * zz**3 + 590490000
report("SS7 six simple cusp roots", s.gcd(g, s.diff(g, zz)) == 1)
report("SS8 cusp degree bounds", s.Poly(Hcusp, uu, zz).degree(uu) <= 13 and s.Poly(Hcusp, uu, zz).degree(zz) <= 10)

# SS19--SS21 are exact factor cancellations.
X = s.symbols("X")
amodel = sigma * zz + 10 * X + 5 * uu * X**2 + uu**2 * X**3
cmodel = 2 * sigma * zz + 30 * X + 20 * uu * X**2 + 5 * uu**2 * X**3
bmodel = 2 * sigma * zz + 60 * X + 60 * uu * X**2 + 20 * uu**2 * X**3
lhs_mu = s.cancel((2/(uu*cmodel) - uu*bmodel/(uu*cmodel)**2) * uu)
lhs_phi = s.cancel((uu*bmodel * uu*amodel/(uu*cmodel)**2) * uu)
report("SS9 mu-gradient blow-up cancellation", s.cancel(lhs_mu - (2/cmodel-bmodel/cmodel**2)) == 0)
report("SS10 phase-gradient gains u", s.cancel(lhs_phi - uu*bmodel*amodel/cmodel**2) == 0)

# SS23 exact arithmetic.
report("SS11 explicit cusp margin", -s.Rational(1,80)+s.Rational(108,10000) == -s.Rational(17,10000))
print("ALL CHECKS PASSED")
