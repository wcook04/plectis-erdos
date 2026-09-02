#!/usr/bin/env python3
"""Replay the exact event-excision theorem for the double-tight atlas.

Novel checks:
  DTE1  the complete kappa=0 limiting fibre and its squarefree Newton charts;
  DTE2  finite conjugate tangent cones at the two triple-tight crossings;
  DTE3  certified strict excess margins at both real triple-tight centres.

The checker consumes the already-certified mu=-10 and mu_* limiting-fibre
theorems.  It does not rerun their much larger independent atlases.  DTE3
does rerun the wall engine with exact dyadic balls; runtime is about two
minutes on the reference machine.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
import sys

import mpmath as mp
import sympy as sp


HERE = Path(__file__).resolve().parent
ENGINE_SPEC = importlib.util.spec_from_file_location(
    "lib_erdos1041_wall_engine", HERE / "lib_erdos1041_wall_engine.py"
)
ENGINE = importlib.util.module_from_spec(ENGINE_SPEC)
assert ENGINE_SPEC.loader is not None
ENGINE_SPEC.loader.exec_module(ENGINE)

FAILURES: list[str] = []


def report(name: str, ok: bool, detail: str = "") -> None:
    print(("PASS " if ok else "FAIL ") + name + (f"  {detail}" if detail else ""))
    if not ok:
        FAILURES.append(name)


def carrier_polynomial(kap: sp.Symbol, mu: sp.Symbol) -> sp.Expr:
    A = 4 * (mu + 4)
    B = -sp.Rational(12, 25) * (3 * mu**3 - 5 * mu**2 - 100 * mu - 200)
    C = sp.Rational(4, 3125) * (mu + 10) ** 3 * (
        27 * mu**2 + 140 * mu + 200
    )
    return sp.expand(
        C**2 * (1 + kap) ** 3
        - A * B * C * kap * (1 + kap) * (1 + 4 * kap)
        + (A**3 * C + B**3) * kap**2 * (1 + 2 * kap)
        - A**2 * B**2 * kap**3
    )


def main() -> int:
    kap, mu = sp.symbols("kap mu", real=True)
    z, q, s = sp.symbols("z q s")
    K = carrier_polynomial(kap, mu)
    Khat = sp.expand(5**10 * K)

    # Complete kappa=0 fibre and its two Newton polygons.
    mustar = (-70 + 10 * sp.I * sp.sqrt(5)) / 27
    fibre0 = sp.expand(
        Khat.subs(kap, 0)
        - 16 * (mu + 10) ** 6 * (27 * mu**2 + 140 * mu + 200) ** 2
    )
    scaled_minus_ten = sp.expand(
        K.subs({mu: -10 + s * z, kap: s**3}, simultaneous=True)
    )
    leading_minus_ten = scaled_minus_ten.coeff(s, 6)
    expected_minus_ten = sp.Rational(2304, 625) * (
        z**6 + 16200 * z**3 + 590490000
    )
    qpoly = q**2 + 16200 * q + 590490000
    qroots = (
        -8100 + 16200 * sp.I * sp.sqrt(2),
        -8100 - 16200 * sp.I * sp.sqrt(2),
    )
    scaled_mustar = sp.Poly(sp.expand(K.subs(mu, mustar + q * kap)), kap)
    leading_mustar = scaled_mustar.coeff_monomial(kap**2)
    mustar_qpoly = (
        q**2
        + (-28 + 4 * sp.I * sp.sqrt(5)) * q / 15
        + (352 - 112 * sp.I * sp.sqrt(5)) / 675
    )
    quotient, remainder = sp.div(
        sp.Poly(leading_mustar, q, extension=[sp.sqrt(5), sp.I]),
        sp.Poly(mustar_qpoly, q, extension=[sp.sqrt(5), sp.I]),
    )
    mustar_disc = sp.expand(sp.discriminant(mustar_qpoly, q))
    dte1 = (
        fibre0 == 0
        and sp.expand(leading_minus_ten - expected_minus_ten) == 0
        and all(sp.simplify(qpoly.subs(q, root)) == 0 for root in qroots)
        and sp.discriminant(qpoly, q) != 0
        and remainder.is_zero
        and quotient.degree() == 0
        and quotient.as_expr() != 0
        and sp.expand(
            mustar_disc - (704 - 224 * sp.I * sp.sqrt(5)) / 675
        )
        == 0
        and mustar_disc != 0
    )
    report(
        "DTE1 complete and squarefree kappa=0 limiting charts",
        dte1,
        "only mu=-10 and mu=(-70+-10i sqrt(5))/27 occur",
    )

    # Exact tangent cones at the two real triple-tight fibres.
    kminus = (1 - 3 * sp.sqrt(3)) / 13
    kplus = (1 + 3 * sp.sqrt(3)) / 13
    crossing_data = (
        (
            kminus,
            50 + 30 * sp.sqrt(3),
            z**2
            + (388 + 228 * sp.sqrt(3)) * z
            + 459744
            + 265392 * sp.sqrt(3),
        ),
        (
            kplus,
            50 - 30 * sp.sqrt(3),
            z**2
            + (388 - 228 * sp.sqrt(3)) * z
            + 459744
            - 265392 * sp.sqrt(3),
        ),
    )
    crossing_ok = True
    for event_kappa, event_mu, expected in crossing_data:
        at = {kap: event_kappa, mu: event_mu}
        tangent = sp.Poly(
            sp.diff(K, mu, 2).subs(at) * z**2
            + 2 * sp.diff(K, mu, kap).subs(at) * z
            + sp.diff(K, kap, 2).subs(at),
            z,
            extension=sp.sqrt(3),
        ).monic()
        expected_poly = sp.Poly(expected, z, extension=sp.sqrt(3)).monic()
        crossing_ok = crossing_ok and (
            sp.simplify(K.subs(at)) == 0
            and sp.simplify(sp.diff(K, mu).subs(at)) == 0
            and sp.simplify(sp.diff(K, kap).subs(at)) == 0
            and tangent == expected_poly
            and sp.discriminant(expected_poly.as_expr(), z) < 0
        )
    report(
        "DTE2 finite conjugate slopes at both triple-tight crossings",
        crossing_ok,
        "ordinary linear charts, not square-root branch points",
    )

    # Fresh exact-dyadic wall-engine replay at both real triple-tight centres.
    # Float/mpmath values merely seed validated Krawczyk tubes; acceptance uses
    # the exact rational upper endpoints returned as result['hi'].
    mp.mp.dps = 50
    engine_rows = []
    for event_mu, ceiling in (
        (50 + 30 * mp.sqrt(3), sp.Rational(-1, 6)),
        (50 - 30 * mp.sqrt(3), sp.Rational(-1, 1)),
    ):
        result = ENGINE.certified_excess(
            event_mu,
            mp.mpc(0, 1),
            k=20,
            ratio=0.12,
            msub=4,
            eps_step=ENGINE.Fr(1, 10**6),
            want_grad=False,
        )
        engine_rows.append((event_mu, ceiling, result))
    dte3 = all(row[2]["hi"] < ENGINE.Fr(int(row[1].p), int(row[1].q))
               for row in engine_rows)
    detail = "; ".join(
        f"mu={mp.nstr(row[0], 10)} E=[{row[2]['lo_f']:.9f},{row[2]['hi_f']:.9f}]"
        for row in engine_rows
    )
    report(
        "DTE3 certified strict margins at both triple-tight centres",
        dte3,
        detail,
    )

    # For real mu, conjugation maps w=i to w=-i and preserves both length and
    # |1+x|.  This syntactic coefficient check is the algebraic premise; the
    # geometric invariance is immediate from conjugating F_mu(x)=w s.
    x = sp.symbols("x", real=True)
    F = x**5 + 5 * x**4 + 10 * x**3 + (10 + mu) * x**2
    real_coefficients = all(coefficient.is_real for coefficient in sp.Poly(F, x).all_coeffs())
    report(
        "DTE4 conjugation supplies the opposite wall orientation",
        bool(real_coefficients),
        "real mu and real model coefficients",
    )

    if FAILURES:
        print(f"FAILED {len(FAILURES)} section(s): {', '.join(FAILURES)}")
        return 1
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
