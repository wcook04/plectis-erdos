#!/usr/bin/env python3
"""Exact algebra replay for QuinticTraceMinQualitativeTransfer.md."""

import sympy as sp


def main() -> None:
    r, qr, qi = sp.symbols("r qr qi", real=True, positive=True)
    hir, hii, hjr, hji = sp.symbols("hir hii hjr hji", real=True)
    q = qr + sp.I * qi
    hi = hir + sp.I * hii
    hj = hjr + sp.I * hji
    absq = sp.symbols("Q", real=True, positive=True)

    def abs2(z: sp.Expr) -> sp.Expr:
        return sp.expand_complex(z * sp.conjugate(z))

    lhs = sp.expand(abs2(q + r**5 * hi) - abs2(q + r**5 * hj))
    direct = sp.expand(
        2 * r**5 * sp.re(sp.conjugate(q) * (hi - hj))
        + r**10 * (abs2(hi) - abs2(hj))
    )
    assert sp.simplify(lhs - direct) == 0

    # M=-conj(q/|q|)P turns finite modulus minimisation into trace maximisation.
    Mi = -sp.conjugate(q) * hi / absq
    Mj = -sp.conjugate(q) * hj / absq
    ordered = sp.expand(
        -2 * r**5 * absq * sp.re(Mi - Mj)
        + r**10 * (abs2(hi) - abs2(hj))
    )
    assert sp.simplify(direct.subs(qr**2 + qi**2, absq**2) - ordered) == 0

    # Exact normalized ray equation (T5).
    s = sp.symbols("s", real=True, nonnegative=True)
    Mc = sp.symbols("Mc")
    t = 1 - s * r**5 / absq
    # From P(w)=t P(c)+(t-1)q/r^5, multiply by -conj(qhat).
    ray_rhs = sp.expand(t * Mc + s)
    claimed = sp.expand(Mc + s * (1 - r**5 * Mc / absq))
    assert sp.simplify(ray_rhs - claimed) == 0

    # Exact similarity scaling of the pair excess (T6).
    l1, l2, w1, w2 = sp.symbols("l1 l2 w1 w2", real=True, nonnegative=True)
    finite_excess = r * l1 + r * l2 - (r * w1 + r * w2)
    assert sp.factor(finite_excess - r * (l1 + l2 - w1 - w2)) == 0

    # Quintic critical-product identity: Res(f,f')=5^5 product f(c).
    z = sp.symbols("z")
    a4, a3, a2, a1, a0 = sp.symbols("a4 a3 a2 a1 a0")
    f = z**5 + a4 * z**4 + a3 * z**3 + a2 * z**2 + a1 * z + a0
    resultant = sp.resultant(f, sp.diff(f, z), z)
    discriminant = sp.discriminant(f, z)
    # n(n-1)/2=10 is even, hence no sign change at n=5.
    assert sp.expand(resultant - discriminant) == 0
    assert sp.LC(sp.diff(f, z), z) == 5
    assert sp.degree(sp.diff(f, z), z) == 4

    print("[ok] exact finite critical-value ordering identity (T4)")
    print("[ok] exact normalized descending-ray identity (T5)")
    print("[ok] exact pair-excess similarity identity (T6)")
    print("[ok] quintic resultant/discriminant sign and leading factor")


if __name__ == "__main__":
    main()
