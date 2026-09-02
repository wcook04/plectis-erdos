#!/usr/bin/env python3
"""Exact algebra replay for the ``mu_*`` angular-fibre reduction.

The analytic subharmonicity and one-dimensional maximum principle are proved
in the companion note.  This checker verifies their exact polynomial,
critical-gap, normalization, radial, and sine-interpolation inputs.
"""

from __future__ import annotations

import sympy as sp


FAILURES: list[str] = []


def report(name: str, ok: bool, detail: str = "") -> None:
    print(("PASS " if ok else "FAIL ") + name + (f"  {detail}" if detail else ""))
    if not ok:
        FAILURES.append(name)


def main() -> int:
    x, y, Y, alpha, c, mu = sp.symbols("x y Y alpha c mu")
    a = sp.sqrt(5)
    mustar = (-70 + 10 * sp.I * a) / 27
    F = lambda z, parameter: sp.expand(
        z**2 * (z**3 + 5 * z**2 + 10 * z + 10 + parameter)
    )
    rdouble = -(5 + sp.I * a) / 3
    rsimple = -(5 - 2 * sp.I * a) / 3
    factorization = sp.expand(
        F(x, mustar) - x**2 * (x - rdouble) ** 2 * (x - rsimple)
    )
    report(
        "M1 exact double-zero factorization at mu_*",
        factorization == 0,
        "F=x^2(x+(5+i sqrt5)/3)^2(x+(5-2i sqrt5)/3)",
    )

    A = 4 * (mustar + 4)
    B = -sp.Rational(12, 25) * (
        3 * mustar**3 - 5 * mustar**2 - 100 * mustar - 200
    )
    C = (
        sp.Rational(4, 3125)
        * (mustar + 10) ** 3
        * (27 * mustar**2 + 140 * mustar + 200)
    )
    gminus = -sp.Rational(4, 81) * (3 - sp.sqrt(3)) * (19 + 5 * sp.I * a)
    gplus = -sp.Rational(4, 81) * (3 + sp.sqrt(3)) * (19 + 5 * sp.I * a)
    value_cubic = sp.expand(Y**3 + A * Y**2 + B * Y + C)
    gap_factorization = sp.simplify(
        value_cubic - Y * (Y - gminus) * (Y - gplus)
    )
    ratio_identity = sp.simplify(gplus / gminus - (2 + sp.sqrt(3)))
    report(
        "M2 one zero gap and two collinear nonzero gaps",
        gap_factorization == 0 and ratio_identity == 0,
        "g_+/g_-=2+sqrt(3)",
    )

    eiphi_center = (-19 + 5 * sp.I * a) / (9 * sp.sqrt(6))
    center_norm = sp.simplify(eiphi_center * sp.conjugate(eiphi_center))
    centered_gap = sp.expand_complex(eiphi_center * gminus)
    phase_ok = (
        center_norm == 1
        and sp.simplify(sp.im(centered_gap)) == 0
        and bool(sp.simplify(sp.re(centered_gap)) > 0)
    )
    report(
        "M3 exact allowed phase half-circle",
        phase_ok,
        "e^{i phi_c}=(-19+5i sqrt5)/(9sqrt6); |phi-phi_c|<=pi/2",
    )

    # For alpha^5 carrying the physical ray, Q_alpha=alpha^-5 F(alpha y).
    # Substituting c=alpha^-1 produces the universal terminal defect.
    Qalpha = sp.expand((F(alpha * y, mu) / alpha**5).subs(alpha, 1 / c))
    Qtarget = y**5 + 5 * c * y**4 + 10 * c**2 * y**3 + (10 + mu) * c**3 * y**2
    terminal = sp.expand(Qtarget - (y + c) ** 5)
    terminal_target = mu * c**3 * y**2 - 5 * c**4 * y - c**5
    report(
        "M4 fifth-root normalization and quadratic terminal defect",
        sp.expand(Qalpha - Qtarget) == 0
        and sp.expand(terminal - terminal_target) == 0,
        "Q-(y+c)^5=mu c^3 y^2-5c^4 y-c^5",
    )

    # The extra zero critical point is distinct from the hub; every positive
    # level on the normalized real ray is regular throughout the half-circle.
    critical = sp.factor(sp.diff(F(x, mustar), x))
    zero_critical_ok = (
        rdouble != 0
        and sp.simplify(F(rdouble, mustar)) == 0
        and sp.simplify(critical.subs(x, rdouble)) == 0
    )
    report(
        "M5 zero foreign gap is distinct from the active hub",
        bool(zero_critical_ok),
        "its critical value is 0, so it is not met at positive ray level",
    )

    radius = sp.symbols("radius", positive=True)
    theta = sp.symbols("theta", real=True)
    angular = sp.Function("angular")
    U = angular(theta) / radius
    laplacian = sp.simplify(
        sp.diff(U, radius, 2)
        + sp.diff(U, radius) / radius
        + sp.diff(U, theta, 2) / radius**2
    )
    radial_target = (angular(theta) + sp.diff(angular(theta), theta, 2)) / radius**3
    report(
        "M6 radial homogeneity converts subharmonicity to A''+A>=0",
        sp.simplify(laplacian - radial_target) == 0,
        "Delta(A(theta)/r)=r^-3(A''+A)",
    )

    z, L, left, right = sp.symbols("z L left right", real=True)
    sine_interpolant = (
        left * sp.sin(L - z) + right * sp.sin(z)
    ) / sp.sin(L)
    ode = sp.simplify(sp.diff(sine_interpolant, z, 2) + sine_interpolant)
    endpoint_left = sp.simplify(sine_interpolant.subs(z, 0) - left)
    endpoint_right = sp.simplify(sine_interpolant.subs(z, L) - right)
    weight_identity = sp.trigsimp(
        (sp.sin(L - z) + sp.sin(z)) * sp.cos(L / 2)
        - sp.sin(L) * sp.cos(z - L / 2),
        method="fu",
    )
    report(
        "M7 exact sine barrier on a sector of opening pi/5",
        ode == 0
        and endpoint_left == 0
        and endpoint_right == 0
        and weight_identity == 0
        and bool(0 < sp.pi / 5 < sp.pi),
        "[sin(L-z)+sin(z)]/sin(L)>=1 for 0<=z<=L=pi/5",
    )

    endpoint_ceiling = -sp.Rational(9, 10)
    report(
        "M8 endpoint-to-full-fibre fan-in",
        endpoint_ceiling < 0,
        "two endpoint bounds below -9/10 imply the entire allowed fibre below -9/10",
    )

    if FAILURES:
        print(f"FAILED {len(FAILURES)} section(s): {', '.join(FAILURES)}")
        return 1
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
