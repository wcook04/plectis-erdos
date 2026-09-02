#!/usr/bin/env python3
"""Exact algebra replay for QuinticWallSheetSubharmonicReduction.md.

The analytic subharmonicity and maximum-principle argument is proved in the
companion note.  This checker verifies every finite algebraic input used by
that argument and by its one-dimensional double-tight boundary carrier:

  S1  the active-critical-root coordinate mu(u), the remaining quadratic,
      and the active gap lambda(u);
  S2  fifth-root gap normalization, the fixed wall ray, and the terminal
      normalizer identity;
  S3  exact Euclidean length/endpoint scaling;
  S4  all gap-zero and mu=-10 exceptional fibres;
  S5  the degree-ten double-tight resultant P_t(x), its rational recovery of
      the second critical root, and the denominator-exception resultant;
  S6  the complete real branch-event list on the ordered ratio interval
      -1 <= t <= 1, from the exact x-discriminant;
  S7  exact t=0 and t=1 endpoint factorizations.

There are no floating-point proof inputs.  Exit 0 iff all exact identities
and sign/discriminant classifications pass.
"""

from __future__ import annotations

import sympy as sp


FAILURES: list[str] = []


def report(name: str, ok: bool, detail: str = "") -> None:
    print(("PASS " if ok else "FAIL ") + name + (f"  {detail}" if detail else ""))
    if not ok:
        FAILURES.append(name)


def main() -> int:
    x, u, z, y, mu, c, alpha, tau = sp.symbols("x u z y mu c alpha tau")
    radius = sp.symbols("radius", positive=True, real=True)
    t = sp.symbols("t", real=True)
    eps = sp.symbols("eps", real=True)

    F = lambda zz, mm: sp.expand(
        zz**2 * (zz**3 + 5 * zz**2 + 10 * zz + 10 + mm)
    )
    C = lambda zz, mm: sp.expand(
        5 * zz**3 + 20 * zz**2 + 30 * zz + 20 + 2 * mm
    )
    gap = lambda zz: sp.expand(
        sp.Rational(1, 2) * zz**3 * (3 * zz**2 + 10 * zz + 10)
    )

    # S1: normalize the critical-root cover by the active critical root u.
    mu_u = -sp.Rational(5, 2) * (u + 2) * (u**2 + 2 * u + 2)
    remaining = z**2 + (u + 4) * z + (u**2 + 4 * u + 6)
    cover_factorization = sp.expand(C(z, mu_u) - 5 * (z - u) * remaining)
    lam_u = gap(u)
    s1 = (
        sp.expand(C(u, mu_u)) == 0
        and cover_factorization == 0
        and sp.expand(F(u, mu_u) + lam_u) == 0
    )
    report(
        "S1 active-root cover, remaining quadratic, and F_mu(u)=-lambda(u)",
        s1,
    )

    # S2: if alpha^5=lambda and c=alpha^{-1}, the active wall ray is fixed.
    P = y**5 + 5 * c * y**4 + 10 * c**2 * y**3 + (10 + mu) * c**3 * y**2
    P_from_F = sp.expand((F(alpha * y, mu) / alpha**5).subs(alpha, 1 / c))
    terminal = sp.expand(P - (y + c) ** 5)
    terminal_target = mu * c**3 * y**2 - 5 * c**4 * y - c**5

    # Convention: e^{i phi} lambda = -eps*i*|lambda|.  Then
    # e^{-i phi}=eps*i*lambda/|lambda| and s=|lambda|*tau.
    lam = sp.symbols("lam", nonzero=True)
    eiphi = -eps * sp.I * radius / lam
    emiphi = eps * sp.I * lam / radius
    phase_inverse = sp.expand((eiphi * emiphi).subs(eps**2, 1)) == 1
    fixed_ray = sp.simplify((emiphi * radius * tau / lam).subs(eps**2, 1))

    # The other chamber inequalities become
    # eps*Im(conj(lambda)*h)>=0 in this convention.
    lr, li, hr, hi = sp.symbols("lr li hr hi", real=True)
    lbar = lr - sp.I * li
    h = hr + sp.I * hi
    rotated_h = sp.expand(-eps * sp.I * lbar * h / radius)
    rotated_real = sp.expand(sp.re(rotated_h))
    rotated_target = eps * (lr * hi - li * hr) / radius
    s2 = (
        sp.simplify(P_from_F - P) == 0
        and sp.expand(terminal - terminal_target) == 0
        and phase_inverse
        and sp.simplify(fixed_ray - eps * sp.I * tau) == 0
        and sp.simplify(rotated_real - rotated_target) == 0
    )
    report("S2 gap normalization, fixed ray, and degree-two terminal defect", s2)

    # S3: |1+alpha*y|=|alpha|*|alpha^{-1}+y| exactly.
    ar, ai, yr, yi = sp.symbols("ar ai yr yi", real=True)
    alpha_sq = ar**2 + ai**2
    prod_re = ar * yr - ai * yi
    prod_im = ar * yi + ai * yr
    lhs_sq = sp.expand((1 + prod_re) ** 2 + prod_im**2)
    c_re, c_im = ar / alpha_sq, -ai / alpha_sq
    rhs_sq = sp.factor(
        alpha_sq * ((c_re + yr) ** 2 + (c_im + yi) ** 2)
    )
    report(
        "S3 exact endpoint scaling |1+alpha*y|=|alpha||c+y|",
        sp.simplify(lhs_sq - rhs_sq) == 0,
    )

    # S4: exceptional fibres on the active-root cover.
    gap_factor = sp.factor(2 * lam_u)
    mu_minus_ten = sp.factor(mu_u + 10)
    gap_quadratic = 3 * u**2 + 10 * u + 10
    gap_zero_image = sp.rem(
        sp.Poly(27 * mu_u**2 + 140 * mu_u + 200, u),
        sp.Poly(gap_quadratic, u),
    ).as_expr()
    mustar_factor = sp.rem(
        sp.Poly(
            F(z, mu_u) - z**2 * (z - u) ** 2 * (z + 5 + 2 * u),
            u,
        ),
        sp.Poly(gap_quadratic, u),
    ).as_expr()
    s4 = (
        gap_factor == u**3 * gap_quadratic
        and mu_minus_ten == -sp.Rational(5, 2) * u * (u**2 + 4 * u + 6)
        and sp.expand(gap_zero_image) == 0
        and sp.expand(mustar_factor) == 0
    )
    report(
        "S4 exceptional fibres: mu=-10 and 27mu^2+140mu+200=0",
        s4,
    )

    # S5: exact carrier for a double-tight pair.  Distinct critical roots
    # x,u over the same mu satisfy q_x(u)=0.  Their real gap ratio is t.
    q = sp.expand(u**2 + (x + 4) * u + (x**2 + 4 * x + 6))
    ratio_remainder = sp.Poly(
        sp.rem(sp.Poly(2 * (gap(u) - t * gap(x)), u), sp.Poly(q, u)), u
    ).as_expr()
    M = sp.expand((x**2 + 6 * x + 6) * (3 * x**2 + 8 * x + 8))
    N = sp.expand(
        3 * t * x**5
        + 10 * t * x**4
        + 10 * t * x**3
        + 3 * x**5
        + 24 * x**4
        + 84 * x**3
        + 156 * x**2
        + 156 * x
        + 72
    )
    P = sp.expand(
        9 * t**2 * x**10
        + 60 * t**2 * x**9
        + 160 * t**2 * x**8
        + 200 * t**2 * x**7
        + 100 * t**2 * x**6
        + 9 * t * x**10
        + 60 * t * x**9
        + 100 * t * x**8
        - 240 * t * x**7
        - 1260 * t * x**6
        - 2144 * t * x**5
        - 1680 * t * x**4
        - 480 * t * x**3
        + 9 * x**10
        + 150 * x**9
        + 1180 * x**8
        + 5700 * x**7
        + 18600 * x**6
        + 42616 * x**5
        + 69120 * x**4
        + 78000 * x**3
        + 58320 * x**2
        + 25920 * x
        + 5184
    )
    resultant_p = sp.expand(sp.resultant(q, 2 * (gap(u) - t * gap(x)), u))
    norm_p = sp.expand(N**2 - (x + 4) * N * M + (x**2 + 4 * x + 6) * M**2)
    denominator_resultant = sp.factor(sp.resultant(P, M, x))
    denominator_target = (
        15850845241344
        * (2 * t**2 - 2 * t - 1) ** 2
        * (32 * t**2 - 32 * t + 9) ** 2
    )
    s5 = (
        sp.expand(ratio_remainder + M * u + N) == 0
        and sp.expand(resultant_p - P) == 0
        and sp.expand(norm_p - P) == 0
        and sp.expand(denominator_resultant - denominator_target) == 0
    )
    report("S5 degree-ten double-tight carrier and second-root recovery", s5)

    # S6: all real branch events of P_t on the ordered compact interval.
    discriminant = sp.factor(sp.resultant(P, sp.diff(P, x), x))
    disc_constant, disc_factors = sp.factor_list(discriminant)
    expected = {
        sp.Poly(t, t).monic().as_expr(): 4,
        sp.Poly(t - 1, t).monic().as_expr(): 4,
        sp.Poly(t**2 + t + 1, t).monic().as_expr(): 1,
        sp.Poly(2 * t**2 - 2 * t - 1, t).monic().as_expr(): 2,
        sp.Poly(9 * t**2 - 32 * t + 32, t).monic().as_expr(): 1,
        sp.Poly(9 * t**2 + 14 * t + 9, t).monic().as_expr(): 1,
        sp.Poly(32 * t**2 - 32 * t + 9, t).monic().as_expr(): 3,
    }
    observed: dict[sp.Expr, int] = {}
    for factor, exponent in disc_factors:
        observed[sp.Poly(factor, t).monic().as_expr()] = exponent
    quadratic_discriminants = {
        sp.discriminant(t**2 + t + 1, t),
        sp.discriminant(9 * t**2 - 32 * t + 32, t),
        sp.discriminant(9 * t**2 + 14 * t + 9, t),
        sp.discriminant(32 * t**2 - 32 * t + 9, t),
    }
    t_star = (1 - sp.sqrt(3)) / 2
    only_events = (
        observed == expected
        and all(d < 0 for d in quadratic_discriminants)
        and -1 < t_star < 0
        and (1 + sp.sqrt(3)) / 2 > 1
        and sp.Poly(P, x).LC() == 9 * (t**2 + t + 1)
    )
    report(
        "S6 only real ratio-branch events on [-1,1] are t*, 0, 1",
        bool(only_events),
        "t*=(1-sqrt(3))/2; leading coefficient never vanishes",
    )

    # S7: exact algebraic endpoint fibres used by the future 1D atlas.
    p0 = sp.factor(P.subs(t, 0))
    p1 = sp.factor(P.subs(t, 1))
    p0_target = (x**2 + 4 * x + 6) ** 3 * (
        9 * x**4 + 42 * x**3 + 82 * x**2 + 72 * x + 24
    )
    p1_target = (3 * x**2 + 8 * x + 6) ** 3 * (
        x**4 + 2 * x**3 + 10 * x**2 + 24 * x + 24
    )
    report(
        "S7 t=0 exceptional and t=1 collision endpoint factorizations",
        sp.expand(p0 - p0_target) == 0 and sp.expand(p1 - p1_target) == 0,
    )

    if FAILURES:
        print(f"FAILED {len(FAILURES)} section(s): {', '.join(FAILURES)}")
        return 1
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
