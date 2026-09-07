#!/usr/bin/env python3
"""Exact checker for the hubwise horizontal-fibre sign no-go."""

from __future__ import annotations

import sympy as sp


z, x, y = sp.symbols("z x y", real=False)
Q = 15 * z + 5 * z**2 - z**5
Qp = sp.diff(Q, z)

assert sp.expand(Qp + 5 * (z + 1) * (z**3 - z**2 + z - 3)) == 0
assert Q.subs(z, -1) == -9
assert Qp.subs(z, -1) == 0
assert sp.diff(Qp, z).subs(z, -1) == 30

g = z**3 - z**2 + z - 3
assert sp.discriminant(g, z) == -204
assert g.subs(z, 1) < 0 < g.subs(z, 2)
assert g.subs(z, sp.Rational(8, 5)) == sp.Rational(17, 125)
assert sp.discriminant(3 * x**2 - 2 * x + 1, x) == -8

# On every cubic critical point, Q=3z(z+4).
rem = sp.rem(Q - 3 * z * (z + 4), g, domain=sp.QQ)
assert rem == 0

# A nonreal cubic root cannot have real critical value.  Real critical value
# would force x=-2; the two parts of g(-2+iy) then contradict one another.
yy = sp.symbols("yy", real=True)
g_at = sp.expand(g.subs(z, -2 + sp.I * yy))
assert sp.re(g_at).expand(complex=True) == 7 * yy**2 - 17
assert sp.expand(sp.im(g_at).expand(complex=True) - yy * (17 - yy**2)) == 0

# Imaginary-axis crossings and their level.
a = sp.root(15, 4)
q_iy = sp.expand(Q.subs(z, sp.I * yy))
assert sp.re(q_iy).expand(complex=True) == -5 * yy**2
assert sp.im(q_iy).expand(complex=True) == 15 * yy - yy**5
assert sp.simplify(Q.subs(z, sp.I * a) + 5 * sp.sqrt(15)) == 0
assert sp.simplify(5 * sp.sqrt(15) - 9) > 0

qp_cross = sp.expand(Qp.subs(z, sp.I * a))
assert sp.simplify(qp_cross - (-60 + 10 * sp.I * a)) == 0
reciprocal_re = sp.simplify(sp.re(1 / qp_cross).expand(complex=True))
assert sp.simplify(reciprocal_re + 60 / (3600 + 100 * sp.sqrt(15))) == 0
assert reciprocal_re < 0

# Exact asymptotic projection constant 2 cos(2pi/5).
golden = (sp.sqrt(5) - 1) / 2
assert sp.simplify(2 * sp.cos(2 * sp.pi / 5) - golden) == 0
assert golden > 0

print("PASS: exact hubwise horizontal-fibre no-go kernel")
print(f"  Q(-1)={Q.subs(z, -1)}, Q''(-1)={sp.diff(Qp, z).subs(z, -1)}")
print(f"  crossing level={-5 * sp.sqrt(15)} < -9")
print(f"  defect lower bound={golden} > 0")
print("  analytic branch continuation and defect convergence: ordinary proof")
