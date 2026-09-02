#!/usr/bin/env python3
"""Exact replay of the unordered double-tight critical-value carrier.

This checker verifies the finite algebraic reduction and compact arm chart in
``QuinticDoubleTightCriticalValueCarrier.md``.  It does not claim the future
interval atlas or its negative excess inequalities.
"""

from __future__ import annotations

import sympy as sp


FAILURES: list[str] = []


def report(name: str, ok: bool, detail: str = "") -> None:
    print(("PASS " if ok else "FAIL ") + name + (f"  {detail}" if detail else ""))
    if not ok:
        FAILURES.append(name)


def factor_signature(expression: sp.Expr, variable: sp.Symbol) -> dict[sp.Expr, int]:
    """Return the monic nonconstant factor multiset, ignoring constants."""

    _, factors = sp.factor_list(expression)
    return {
        sp.Poly(factor, variable).monic().as_expr(): exponent
        for factor, exponent in factors
    }


def main() -> int:
    x, y, mu, Y = sp.symbols("x y mu Y")
    kap, ratio = sp.symbols("kap ratio", real=True)
    pair_sum, pair_product = sp.symbols("pair_sum pair_product")

    critical = 5 * x**3 + 20 * x**2 + 30 * x + 20 + 2 * mu
    gap = sp.Rational(1, 2) * x**3 * (3 * x**2 + 10 * x + 10)
    A = 4 * (mu + 4)
    B = -sp.Rational(12, 25) * (
        3 * mu**3 - 5 * mu**2 - 100 * mu - 200
    )
    C = (
        sp.Rational(4, 3125)
        * (mu + 10) ** 3
        * (27 * mu**2 + 140 * mu + 200)
    )
    Qvalue = Y**3 + A * Y**2 + B * Y + C

    value_resultant = sp.factor(sp.resultant(critical, Y - gap, x))
    report(
        "C1 exact cubic of the three critical gaps",
        sp.expand(value_resultant + 3125 * Qvalue) == 0,
        "Res_x(C_mu,Y-g)=-3125(Y^3+A Y^2+B Y+C)",
    )

    # For a selected unordered pair a,b put p=a+b, q=ab and let the third
    # root be h=-A-p.  Double tightness makes a/b real and
    # kap=q/(a^2+b^2)=q/(p^2-2q).
    f_ratio = sp.expand(kap * pair_sum**2 - (1 + 2 * kap) * pair_product)
    f_vieta_2 = sp.expand(pair_product - A * pair_sum - pair_sum**2 - B)
    f_vieta_3 = sp.expand(pair_product * (A + pair_sum) - C)
    reduced_2 = sp.resultant(f_ratio, f_vieta_2, pair_product)
    reduced_3 = sp.resultant(f_ratio, f_vieta_3, pair_product)
    elimination = sp.factor(sp.resultant(reduced_2, reduced_3, pair_sum))

    K = sp.expand(
        C**2 * (1 + kap) ** 3
        - A * B * C * kap * (1 + kap) * (1 + 4 * kap)
        + (A**3 * C + B**3) * kap**2 * (1 + 2 * kap)
        - A**2 * B**2 * kap**3
    )
    D = sp.expand(A**2 * kap - B * (1 + kap))
    recovered_sum = (C * (1 + kap) ** 2 - A * B * kap**2) / (kap * D)

    # Verify the recovery universally in independent coefficient symbols;
    # this avoids concealing the Vieta argument inside the special formulas
    # for A(mu),B(mu),C(mu).
    AA, BB, CC = sp.symbols("AA BB CC")
    generic_2 = (1 + 2 * kap) * (AA * pair_sum + BB) + (1 + kap) * pair_sum**2
    generic_3 = -(kap * pair_sum**2 * (AA + pair_sum)) + CC * (1 + 2 * kap)
    generic_K = sp.expand(
        CC**2 * (1 + kap) ** 3
        - AA * BB * CC * kap * (1 + kap) * (1 + 4 * kap)
        + (AA**3 * CC + BB**3) * kap**2 * (1 + 2 * kap)
        - AA**2 * BB**2 * kap**3
    )
    aa, bb, cc = sp.symbols("aa bb cc")
    pair_product_factorization = sp.expand(
        generic_K.subs(
            {
                AA: -(aa + bb + cc),
                BB: aa * bb + aa * cc + bb * cc,
                CC: -aa * bb * cc,
            },
            simultaneous=True,
        )
        + (kap * (aa**2 + bb**2) - aa * bb)
        * (kap * (aa**2 + cc**2) - aa * cc)
        * (kap * (bb**2 + cc**2) - bb * cc)
    )
    generic_D = AA**2 * kap - BB * (1 + kap)
    generic_sum = (
        CC * (1 + kap) ** 2 - AA * BB * kap**2
    ) / (kap * generic_D)
    recovery_remainders = []
    for relation in (generic_2, generic_3):
        numerator = sp.cancel(
            relation.subs(pair_sum, generic_sum)
        ).as_numer_denom()[0]
        _, remainder = sp.div(
            sp.Poly(numerator, CC), sp.Poly(generic_K, CC)
        )
        recovery_remainders.append(remainder)

    kappa_lower = sp.factor(
        kap.subs(kap, ratio / (1 + ratio**2)) + sp.Rational(1, 2)
    )
    kappa_upper = sp.factor(
        sp.Rational(1, 2) - kap.subs(kap, ratio / (1 + ratio**2))
    )
    report(
        "C2 unordered-pair carrier and rational direction recovery",
        sp.expand(elimination - (1 + 2 * kap) ** 2 * K) == 0
        and pair_product_factorization == 0
        and all(remainder.is_zero for remainder in recovery_remainders)
        and sp.simplify(
            kappa_lower - (ratio + 1) ** 2 / (2 * (ratio**2 + 1))
        )
        == 0
        and sp.simplify(
            kappa_upper - (ratio - 1) ** 2 / (2 * (ratio**2 + 1))
        )
        == 0,
        "K is minus the product over three unordered pairs; p recovered off events",
    )

    # Work with the integral normalization Khat=5^10 K.
    Khat = sp.expand(5**10 * K)
    Kpoly = sp.Poly(Khat, mu)
    J = sp.expand(
        2634375 * kap**9
        - 1903125 * kap**8
        - 837500 * kap**7
        + 459000 * kap**6
        + 334450 * kap**5
        - 91554 * kap**4
        - 57716 * kap**3
        + 13176 * kap**2
        + 3159 * kap
        - 729
    )
    expected_discriminant = sp.expand(
        kap**14
        * (kap + 1) ** 3
        * (2 * kap - 1) ** 6
        * (2 * kap + 1) ** 5
        * (14 * kap + 9)
        * (13 * kap**2 - 2 * kap - 2) ** 2
        * (1553 * kap**2 - 1312 * kap + 288) ** 3
        * J**2
    )
    discriminant = sp.resultant(Khat, sp.diff(Khat, mu), mu)
    denominator_resultant = sp.resultant(Khat, 25 * D, mu)
    expected_denominator = (kap + 1) * J**2

    signature_ok = (
        factor_signature(discriminant, kap)
        == factor_signature(expected_discriminant, kap)
        and factor_signature(denominator_resultant, kap)
        == factor_signature(expected_denominator, kap)
    )

    kminus = (1 - 3 * sp.sqrt(3)) / 13
    kplus = (1 + 3 * sp.sqrt(3)) / 13
    event_poly = sp.Poly(13 * kap**2 - 2 * kap - 2, kap)
    event_isolation = (
        sp.count_roots(event_poly, -sp.Rational(1, 3), -sp.Rational(8, 25)) == 1
        and sp.count_roots(event_poly, sp.Rational(19, 40), sp.Rational(12, 25)) == 1
        and -sp.Rational(1, 2) < kminus < 0 < kplus < sp.Rational(1, 2)
    )
    no_foreign_events = (
        sp.count_roots(sp.Poly(J, kap), -sp.Rational(1, 2), sp.Rational(1, 2))
        == 0
        and sp.discriminant(1553 * kap**2 - 1312 * kap + 288, kap) < 0
        and -sp.Rational(9, 14) < -sp.Rational(1, 2)
        and -1 < -sp.Rational(1, 2)
    )
    report(
        "C3 complete physical branch-event and denominator-safety resultants",
        Kpoly.degree() == 10
        and sp.expand(Kpoly.LC() - 11664 * (kap + 1) ** 3) == 0
        and signature_ok
        and event_isolation
        and no_foreign_events,
        "events only kap=-1/2,k-,0,k+,1/2; D nonzero on regular fibres",
    )

    representatives = (
        -sp.Rational(2, 5),
        -sp.Rational(1, 10),
        sp.Rational(1, 5),
        sp.Rational(49, 100),
    )
    real_root_counts = [
        sp.count_roots(
            sp.Poly(Khat.subs(kap, representative), mu), -sp.oo, sp.oo
        )
        for representative in representatives
    ]
    report(
        "C4 five conjugate branches on each of four regular intervals",
        real_root_counts == [0, 0, 0, 0],
        "degree 10, simple, no real mu roots at four Sturm representatives",
    )

    quintic_minus = (
        27 * mu**5
        + 5450 * mu**4
        + 23000 * mu**3
        - 105000 * mu**2
        - 700000 * mu
        - 1000000
    )
    endpoint_zero = sp.expand(
        Khat.subs(kap, 0)
        - 16 * (mu + 10) ** 6 * (27 * mu**2 + 140 * mu + 200) ** 2
    )
    endpoint_minus = sp.expand(
        Khat.subs(kap, -sp.Rational(1, 2)) - 2 * quintic_minus**2
    )
    endpoint_plus = sp.expand(
        Khat.subs(kap, sp.Rational(1, 2))
        - 2
        * (mu**2 - 100 * mu - 200) ** 2
        * (27 * mu**2 + 100 * mu + 100) ** 3
    )

    event_multiplicity_ok = True
    for event_kappa, event_mu in (
        (kminus, 50 + 30 * sp.sqrt(3)),
        (kplus, 50 - 30 * sp.sqrt(3)),
    ):
        event = sp.Poly(Khat.subs(kap, event_kappa), mu, extension=sp.sqrt(3))
        square = sp.Poly((mu - event_mu) ** 2, mu, extension=sp.sqrt(3))
        quotient, remainder = event.div(square)
        event_multiplicity_ok = event_multiplicity_ok and (
            remainder.is_zero
            and quotient.degree() == 8
            and sp.gcd(quotient, quotient.diff()).degree() == 0
            and quotient.eval(event_mu) != 0
        )
    report(
        "C5 exact zero, opposite-gap, equal-gap, and triple-tight event fibres",
        endpoint_zero == 0
        and endpoint_minus == 0
        and endpoint_plus == 0
        and event_multiplicity_ok,
        "triple-tight mu=50+30sqrt(3),50-30sqrt(3), each exactly double",
    )

    # The projected double roots at the two interior events are transverse
    # conjugate crossings.  Their first nonzero Taylor equations give finite
    # linear slopes rather than Puiseux square roots.
    slope = sp.symbols("slope")
    crossing_data = (
        (
            kminus,
            50 + 30 * sp.sqrt(3),
            slope**2
            + (388 + 228 * sp.sqrt(3)) * slope
            + 459744
            + 265392 * sp.sqrt(3),
            -194
            - 114 * sp.sqrt(3)
            + 2 * sp.I * sp.sqrt(95780 + 55290 * sp.sqrt(3)),
        ),
        (
            kplus,
            50 - 30 * sp.sqrt(3),
            slope**2
            + (388 - 228 * sp.sqrt(3)) * slope
            + 459744
            - 265392 * sp.sqrt(3),
            -194
            + 114 * sp.sqrt(3)
            + 2 * sp.I * sp.sqrt(95780 - 55290 * sp.sqrt(3)),
        ),
    )
    crossing_ok = True
    for event_kappa, event_mu, expected_slope, one_root in crossing_data:
        at_event = {kap: event_kappa, mu: event_mu}
        taylor_slope = sp.Poly(
            sp.diff(K, mu, 2).subs(at_event) * slope**2
            + 2 * sp.diff(K, mu, kap).subs(at_event) * slope
            + sp.diff(K, kap, 2).subs(at_event),
            slope,
            extension=sp.sqrt(3),
        ).monic()
        expected_poly = sp.Poly(
            expected_slope, slope, extension=sp.sqrt(3)
        ).monic()
        crossing_ok = crossing_ok and (
            sp.simplify(K.subs(at_event)) == 0
            and sp.simplify(sp.diff(K, mu).subs(at_event)) == 0
            and sp.simplify(sp.diff(K, kap).subs(at_event)) == 0
            and taylor_slope == expected_poly
            and sp.simplify(expected_poly.eval(one_root)) == 0
            and sp.discriminant(expected_poly.as_expr(), slope) < 0
        )
    report(
        "C5a finite exact slopes at both triple-tight crossings",
        crossing_ok,
        "quadratic Taylor cones have two finite nonreal conjugate slopes",
    )

    # Weighted Newton polygons at kappa=0.  The mu=-10 branches use weight
    # one for delta=mu+10 and weight three for kappa.
    scale_parameter, local_z, local_q = sp.symbols(
        "scale_parameter local_z local_q"
    )
    minus_ten_scaled = sp.expand(
        K.subs(
            {
                mu: -10 + scale_parameter * local_z,
                kap: scale_parameter**3,
            },
            simultaneous=True,
        )
    )
    minus_ten_leading = sp.expand(minus_ten_scaled).coeff(scale_parameter, 6)
    expected_minus_ten = sp.Rational(2304, 625) * (
        local_z**6 + 16200 * local_z**3 + 590490000
    )
    minus_ten_q = local_q**2 + 16200 * local_q + 590490000
    minus_ten_roots = (
        -8100 + 16200 * sp.I * sp.sqrt(2),
        -8100 - 16200 * sp.I * sp.sqrt(2),
    )

    mustar = (-70 + 10 * sp.I * sp.sqrt(5)) / 27
    mustar_scaled = sp.expand(K.subs(mu, mustar + local_q * kap))
    mustar_leading = sp.Poly(mustar_scaled, kap).coeff_monomial(kap**2)
    expected_mustar = (
        local_q**2
        + (-28 + 4 * sp.I * sp.sqrt(5)) * local_q / 15
        + (352 - 112 * sp.I * sp.sqrt(5)) / 675
    )
    mustar_quotient, mustar_remainder = sp.div(
        sp.Poly(mustar_leading, local_q, extension=[sp.sqrt(5), sp.I]),
        sp.Poly(expected_mustar, local_q, extension=[sp.sqrt(5), sp.I]),
    )
    mustar_discriminant = sp.expand(sp.discriminant(expected_mustar, local_q))
    report(
        "C5b regular Newton leading forms at the kappa=0 punctures",
        sp.expand(minus_ten_leading - expected_minus_ten) == 0
        and all(sp.simplify(minus_ten_q.subs(local_q, root)) == 0
                for root in minus_ten_roots)
        and sp.discriminant(minus_ten_q, local_q) != 0
        and mustar_remainder.is_zero
        and mustar_quotient.degree() == 0
        and mustar_quotient.as_expr() != 0
        and sp.expand(
            mustar_discriminant
            - (704 - 224 * sp.I * sp.sqrt(5)) / 675
        )
        == 0
        and mustar_discriminant != 0,
        "q=(mu+10)^3/kappa at -10; mu-mu*=q kappa at mu*",
    )

    # Exact implicit and phase derivatives used by a future one-dimensional
    # mean-value cover.  The checker verifies the algebraic chain rule; the
    # analytic gradient inequalities themselves belong to the wall engine.
    mu_rate = -sp.diff(K, kap) / sp.diff(K, mu)
    p_rate = sp.diff(recovered_sum, kap) + sp.diff(recovered_sum, mu) * mu_rate
    carrier_chain = sp.cancel(sp.diff(K, kap) + sp.diff(K, mu) * mu_rate)
    recovered_chain = sp.cancel(
        p_rate
        - (sp.diff(recovered_sum, kap) + sp.diff(recovered_sum, mu) * mu_rate)
    )
    phase_pr, phase_pi, dpr, dpi = sp.symbols(
        "phase_pr phase_pi dpr dpi", real=True
    )
    phase_rate_real = (
        phase_pi * dpr - phase_pr * dpi
    ) / (phase_pr**2 + phase_pi**2)
    phase_rate_complex = sp.simplify(
        -sp.im((dpr + sp.I * dpi) / (phase_pr + sp.I * phase_pi))
    )
    report(
        "C5c exact DT-Lip branch and phase derivative formulas",
        carrier_chain == 0
        and recovered_chain == 0
        and sp.simplify(phase_rate_complex - phase_rate_real) == 0,
        "mu'=-K_k/K_mu; p'=P_k+P_mu mu'; phi'=-Im(p'/p)",
    )

    # Chamber phase from the unordered pair direction p and third gap h.
    pr, pi, hr, hi, eps, radius = sp.symbols(
        "pr pi hr hi eps radius", real=True
    )
    p_complex = pr + sp.I * pi
    h_complex = hr + sp.I * hi
    d_complex = -eps * sp.I * p_complex / radius
    eiphi = sp.conjugate(d_complex)
    chamber_real = sp.expand(sp.re(eiphi * h_complex))
    cross = pr * hi - pi * hr
    report(
        "C6 exact phase reconstruction and third-gap chamber sign",
        sp.expand(chamber_real + eps * cross / radius) == 0,
        "choose eps=-sign Im(conj(p)h), then Re(e^{i phi}h)>=0",
    )

    # One compact chart simultaneously regularizes the double hub and the
    # monic terminal end.
    r, d = sp.symbols("r d")
    scale = r**5 / (1 - r) ** 2
    level = (r / (1 - r)) ** 10
    F = lambda z: sp.expand(z**2 * (z**3 + 5 * z**2 + 10 * z + 10 + mu))
    G = sp.expand(
        r**15 * y**5
        + 5 * r**10 * (1 - r) ** 2 * y**4
        + 10 * r**5 * (1 - r) ** 4 * y**3
        + (10 + mu) * (1 - r) ** 6 * y**2
        - d
    )
    chart_identity = sp.cancel(
        (1 - r) ** 10 / r**10 * (F(scale * y) - d * level) - G
    )
    derivative_identity = sp.cancel(
        sp.diff(G, y)
        - (1 - r) ** 8 / r**5 * sp.diff(F(x), x).subs(x, scale * y)
    )

    X = sp.symbols("X", positive=True)
    asymptotic_x = (
        X
        - 1
        - sp.Rational(1, 5) * mu * X**-2
        + sp.Rational(1, 5) * (2 * mu + 5) * X**-3
        - sp.Rational(1, 5) * (mu + 4) * X**-4
    )
    asymptotic_residual = sp.cancel(F(asymptotic_x) - X**5)
    asymptotic_order_ok = sp.limit(X * asymptotic_residual, X, sp.oo) == 0

    er, ei, vr, vi = sp.symbols("er ei vr vi", real=True)
    dot = er * vr + ei * vi
    transverse = er * vi - ei * vr
    lagrange_identity = sp.expand(
        dot**2 + transverse**2 - (er**2 + ei**2) * (vr**2 + vi**2)
    )
    report(
        "C7 compact hub-to-infinity arm chart and excess-defect algebra",
        chart_identity == 0
        and derivative_identity == 0
        and sp.expand(G.subs(r, 0) - ((10 + mu) * y**2 - d)) == 0
        and sp.expand(G.subs(r, 1) - (y**5 - d)) == 0
        and asymptotic_order_ok
        and lagrange_identity == 0,
        "G(0,y)=(10+mu)y^2-d; G(1,y)=y^5-d; exact terminal expansion",
    )

    if FAILURES:
        print(f"FAILED {len(FAILURES)} section(s): {', '.join(FAILURES)}")
        return 1
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
