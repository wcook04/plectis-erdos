"""Wave-9: scale test + the (R1) consequence of the divisor-pairing anchor.

THEOREM P (proved).  x = 3^i 5^j, c = log2 x.  If
   (B1) j*beta <= i*alpha + alpha - 1/2 and (B2) i*alpha <= j*beta + beta - 1/2,
then  N*(x) := #{y smooth : x^2 < 2y^2 < 4x^2}  is ODD.
   [ |log2(y/x)| < 1/2  <=>  x^2 < 2y^2  and  y^2 < 2x^2 ]

COROLLARY.  With K = floor(c - 1/2),
   s(K) = N*(x) - #{y : 2^{K+1} <= y < x*sqrt2} + #{y : 2^K <= y <= x/sqrt2}
so   s(K) = 1 + E1 + E2  (mod 2),
E1 = #{y smooth : 2^K <= y, 2y^2 <= x^2},  E2 = #{y smooth : 2^{K+1} <= y, y^2 < 2x^2}.
All predicates are integer comparisons.
"""
from fractions import Fraction
import exact

AL, AH, BL, BH = exact.ALPHA_LO, exact.ALPHA_HI, exact.BETA_LO, exact.BETA_HI


def balanced(i, j):
    outs = set()
    for al, be in ((AL, BL), (AH, BH)):
        outs.add((j * be <= i * al + al - Fraction(1, 2),
                  i * al <= j * be + be - Fraction(1, 2)))
    if len(outs) != 1:
        return None
    a, b = outs.pop()
    return a and b


def smooth_upto(lim):
    """all 3^u5^v <= lim, sorted"""
    out = []
    p3 = 1
    while p3 <= lim:
        y = p3
        while y <= lim:
            out.append(y)
            y *= 5
        p3 *= 3
    return sorted(out)


def analyse(i, j):
    x = 3 ** i * 5 ** j
    x2 = x * x
    S = smooth_upto(2 * x)                      # covers y < x*sqrt2 < 2x
    Nstar = sum(1 for y in S if x2 < 2 * y * y and y * y < 2 * x2)
    # K = floor(log2 x - 1/2)  <=>  2^K <= x/sqrt2 < 2^{K+1}  <=>  2^{2K+1} <= x^2 < 2^{2K+3}
    # 2^(2K+1) <= x^2 < 2^(2K+3)  <=>  2K+2 <= bitlen(x^2) <= 2K+3
    K = (x2.bit_length() - 2) // 2
    if K < 0:
        return None
    assert (1 << (2 * K + 1)) <= x2 < (1 << (2 * K + 3))
    E1 = sum(1 for y in S if y >= (1 << K) and 2 * y * y <= x2)
    E2 = sum(1 for y in S if y >= (1 << (K + 1)) and y * y < 2 * x2)
    sK = sum(1 for y in S if (1 << K) <= y < (1 << (K + 1)))
    return Nstar, K, E1, E2, sK


print("== THEOREM P at scale, and the s(K) = 1 + E1 + E2 corollary ==")
bad_odd = bad_cor = tested = 0
maxN = 0
for i in range(0, 170):
    for j in range(0, 170):
        b = balanced(i, j)
        assert b is not None
        if not b:
            continue
        res = analyse(i, j)
        if res is None:
            continue
        Nstar, K, E1, E2, sK = res
        tested += 1
        maxN = max(maxN, Nstar)
        if Nstar % 2 == 0:
            bad_odd += 1
            print("   THEOREM P FAILS at (i,j)=(%d,%d): N*=%d" % (i, j, Nstar))
        if (sK - (1 + E1 + E2)) % 2 != 0:
            bad_cor += 1
            print("   COROLLARY FAILS at (i,j)=(%d,%d): s=%d 1+E1+E2=%d" % (i, j, sK, 1+E1+E2))
print("  balanced (i,j) tested: %d,  max N* = %d" % (tested, maxN))
print("  Theorem P violations : %d" % bad_odd)
print("  Corollary violations : %d" % bad_cor)
