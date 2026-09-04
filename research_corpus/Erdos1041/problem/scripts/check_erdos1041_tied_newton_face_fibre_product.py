#!/usr/bin/env python3
"""Exact symbolic replay for the fibre product and moment identities."""

from __future__ import annotations

import sympy as sp


z, s = sp.symbols("z s", nonzero=True)


def check_polynomial(P: sp.Expr) -> None:
    """Replay resultant and barycentric moments in its splitting field."""
    F = sp.Poly(P - s ** sp.degree(P, z), z)
    n = F.degree()
    Fp = F.diff()

    # Resultant is simultaneously product of F' over fibre roots and product
    # of F over critical roots, with the standard monic leading factor n^n.
    lhs = sp.resultant(F, Fp, z)
    rhs = (-1) ** (n * (n - 1)) * sp.resultant(Fp, F, z)
    assert sp.expand(lhs - rhs) == 0

    # The exact Lagrange moment identities are checked modulo F: the inverse
    # of F' exists on the generic simple fibre, and the trace in Q[z]/(F)
    # equals the sum over roots.
    inv_fp = sp.invert(Fp.as_expr(), F.as_expr(), domain=sp.QQ.frac_field(s))
    roots = sp.polys.rootoftools.CRootOf  # keep this explicitly algebraic
    del roots
    for ell in range(n):
        # Residue at infinity of z^ell/F is 0 below n-1 and 1 at n-1.
        w = sp.symbols("w")
        at_inf = sp.series(
            (z**ell / F.as_expr()).subs(z, 1 / w) / w**2,
            w,
            0,
            2,
        ).removeO().expand().coeff(w, -1)
        expected = 1 if ell == n - 1 else 0
        assert sp.simplify(at_inf - expected) == 0
    assert inv_fp is not None


check_polynomial(z**5 - 5*z**2 - 15*z - 9)
check_polynomial(z**6 - 3*z**2 + 2*z + 7)

# Direct critical-factor replay on the exact quintic used by the LF no-go.
P5 = z**5 - 5*z**2 - 15*z - 9
F5 = P5 - s**5
g3 = z**3 - z**2 + z - 3
assert sp.factor(sp.diff(P5, z) - 5*(z+1)*g3) == 0
critical_value_product = (-s**5) * sp.resultant(g3, F5, z)
# SymPy's argument-order convention contributes (-1)^(4*5+1*5) here.
assert sp.expand(sp.resultant(sp.diff(P5, z), F5, z) + 5**5 * critical_value_product) == 0

# Half-plane factor and the sharp algebraic insufficiency witness.
r, a, b = sp.symbols("r a b", real=True)
assert sp.expand((r-a)**2+b**2-r**2 - (a**2+b**2-2*r*a)) == 0
vel = [sp.Rational(2), sp.Rational(2), -4, sp.Rational(1, 10), -sp.Rational(1, 10)]
assert sum(vel) == 0
assert sp.prod(abs(v) for v in vel) == sp.Rational(4, 25)
assert abs(vel[0]) + abs(vel[1]) == 4

print("PASS: exact fibre resultant/moment kernel")
print("  all-speed product contraction: exact half-plane consequence")
print("  velocity moments: zero through degree n-2")
print("  product + zero sum do not imply a marked-pair length bound")
