"""Exact replay for AllDegreePhaseSturmReduction.md.

This checker is deliberately algebraic.  It verifies the arm-calculus
identities with independent real symbols and checks the terminal degree-gap
asymptotics on rational low-mode representatives in degrees 3 through 12.
"""

from __future__ import annotations

import sys
import math

import sympy as sp


FAILURES: list[str] = []


def report(name: str, ok: bool, detail: str = "") -> None:
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


def check_local_calculus() -> None:
    # p=Re Phi, q=Im Phi, rho=|x_s|.  The two input identities are
    # rho_phiphi/rho=q^2-s p_s and s rho_s=(p-1)rho.
    s, rho, p, q, ps = sp.symbols("s rho p q p_s", real=True)
    rho_s = rho * (p - 1) / s
    boundary_derivative = rho * p + s * rho_s * p + s * rho * ps
    lhs = rho * (q**2 - s * ps)
    rhs = rho * (p**2 + q**2) - boundary_derivative
    report("A1 exact speed second-derivative identity", sp.expand(lhs - rhs) == 0)

    # Exact finite-cutoff rearrangement (equation (5) in the note).
    n, integral_phi2, length, r, boundary, rpp = sp.symbols(
        "n integral_phi2 length r boundary rpp"
    )
    e = length - r
    k = n**2 * integral_phi2 - length
    epp = integral_phi2 - boundary - rpp
    residual = sp.expand(n**2 * epp - e - k)
    target = sp.expand(r - n**2 * (boundary + rpp))
    report("A2 exact truncated boundary rearrangement", sp.expand(residual - target) == 0)

    # Integrated square completion used to pass from (A)+(B) to (C).
    z = sp.symbols("z", nonnegative=True)
    report(
        "A3 exact square completion",
        sp.expand(n**2 * z**2 - 1 - ((n * z - 1) ** 2 + 2 * (n * z - 1))) == 0,
    )


def rational_low_mode_polynomial(n: int, x: sp.Symbol) -> sp.Expr:
    """A nontrivial exact representative satisfying F(0)=F'(0)=0."""
    kmax = (n - 1) // 2
    betas: dict[int, sp.Expr] = {}
    for k in range(2, kmax + 1):
        # Small, alternating, nonzero rational modes.
        betas[k] = sp.Rational((-1) ** k * (k + 1), 7 * n + 3 * k)
    betas[1] = -n - sum(k * betas[k] for k in range(2, kmax + 1))
    return sp.expand(
        (1 + x) ** n
        - 1
        + sum(betas[k] * ((1 + x) ** k - 1) for k in range(1, kmax + 1))
    )


def check_terminal_asymptotics() -> None:
    x = sp.symbols("x", positive=True)
    all_ok = True
    details: list[str] = []
    for n in range(3, 13):
        f = rational_low_mode_polynomial(n, x)
        fp = sp.diff(f, x)
        phi = sp.simplify(sp.diff(f / fp, x))
        defect = sp.expand(f - (1 + x) ** n)
        omega_numerator = sp.expand(n * f - (1 + x) * fp)
        phi_numerator = sp.expand((n - 1) * fp**2 - n * f * sp.diff(fp, x))
        simple_hub = sp.simplify(sp.diff(f, x, 2).subs(x, 0)) != 0
        checks = [
            sp.simplify(f.subs(x, 0)) == 0,
            sp.simplify(fp.subs(x, 0)) == 0,
            simple_hub,
            sp.degree(defect, x) <= (n - 1) // 2 <= n - 2,
            sp.degree(omega_numerator, x) < sp.degree(fp, x),
            sp.degree(phi_numerator, x) <= 2 * n - 4,
        ]
        ok = all(bool(v) for v in checks)
        all_ok = all_ok and ok
        details.append(f"n={n}:{'ok' if ok else 'FAIL'}")
    report("T1 degree-gap terminal asymptotics n=3..12", all_ok, " ".join(details))


def check_sturm_weights() -> None:
    # Algebraic trigonometric identity for the sum of the two interpolation
    # weights.  Positivity/monotonicity then follows from 0<=|D-2t|<=D<=pi
    # and n>=2, so both cosine arguments lie in [0,pi/4].
    a, b = sp.symbols("a b", real=True)
    lhs = sp.sin(a) + sp.sin(b)
    rhs = 2 * sp.sin((a + b) / 2) * sp.cos((a - b) / 2)
    identity = sp.simplify(sp.expand_complex((lhs - rhs).rewrite(sp.exp))) == 0
    report("S1 exact sine-weight sum identity", identity)

    # Independent high-precision grid guard for the stated domain.
    worst = 10.0
    ok = True
    for nn in range(2, 14):
        for dnum in range(1, 65):
            dd = math.pi * dnum / 64.0
            for tnum in range(0, 65):
                tt = dd * tnum / 64.0
                value = (math.sin((dd - tt) / nn) + math.sin(tt / nn)) / math.sin(dd / nn)
                worst = min(worst, value)
                if value < 1 - 2e-15:
                    ok = False
    report("S2 sine weights sum to at least one on D<=pi", ok, f"min={worst}")


def main() -> int:
    check_local_calculus()
    check_terminal_asymptotics()
    check_sturm_weights()
    if FAILURES:
        print("FAILURES:", ", ".join(FAILURES))
        return 1
    print("ALL PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
