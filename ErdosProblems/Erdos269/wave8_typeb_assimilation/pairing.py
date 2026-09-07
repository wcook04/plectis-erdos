"""Wave-9 probe: divisor-pairing parity anchor for {3,5}-smooth numbers.

CLAIM.  Let x = 3^i 5^j and c = log2 x.  If the "balance" conditions
   (B1)  j*beta <= i*alpha + alpha - 1/2
   (B2)  i*alpha <= j*beta + beta  - 1/2
hold, then  #{ y = 3^u 5^v : |log2 y - c| < 1/2 }  is ODD.

Reason: N = x^2 = 3^{2i}5^{2j} is a perfect SQUARE; (u,v) -> (2i-u, 2j-v)
is d -> N/d, an involution on the set, and (B1)/(B2) keep it inside the
quadrant.  Its unique fixed point is x itself.

Every test below is a pure INTEGER comparison:
   |log2(y/x)| < 1/2   <=>   x^2 < 2 y^2  and  y^2 < 2 x^2 .
"""
from fractions import Fraction
import exact

AL, AH = exact.ALPHA_LO, exact.ALPHA_HI      # alpha = log2 3
BL, BH = exact.BETA_LO,  exact.BETA_HI       # beta  = log2 5


def balanced(i, j):
    """(B1) and (B2), certified under both bracket endpoints."""
    outs = set()
    for al, be in ((AL, BL), (AH, BH)):
        outs.add((j * be <= i * al + al - Fraction(1, 2),
                  i * al <= j * be + be - Fraction(1, 2)))
    if len(outs) != 1:
        return None
    b1, b2 = outs.pop()
    return b1 and b2


def window_count(i, j):
    """#{(u,v)>=0 : x^2 < 2y^2 and y^2 < 2x^2},  x=3^i5^j, y=3^u5^v.  Exact."""
    x = 3 ** i * 5 ** j
    x2 = x * x
    n = 0
    p3 = 1
    u = 0
    while True:
        # smallest v with y^2*2 > x^2  ->  scan v upward while y^2 < 2x^2
        y = p3
        if 2 * y * y <= x2:
            # raise y by powers of 5 until in range
            while 2 * y * y <= x2:
                y *= 5
        v_ok = False
        while y * y < 2 * x2:
            if x2 < 2 * y * y:
                n += 1
                v_ok = True
            y *= 5
        u += 1
        p3 *= 3
        # stop when even v=0 overshoots: 3^u alone has y^2 >= 2x^2
        if p3 * p3 >= 2 * x2 and not v_ok and p3 * p3 >= 2 * x2:
            if p3 * p3 >= 2 * x2:
                break
    return n


print("== divisor-pairing parity: exhaustive over balanced (i,j) ==")
bad = 0; tested = 0; unbal = 0; counts = []
for i in range(0, 26):
    for j in range(0, 26):
        b = balanced(i, j)
        assert b is not None, (i, j)
        if not b:
            unbal += 1
            continue
        n = window_count(i, j)
        tested += 1
        counts.append(n)
        if n % 2 == 0:
            bad += 1
            print("   EVEN at (i,j)=(%d,%d): count=%d" % (i, j, n))
print("  balanced pairs tested: %d   (unbalanced skipped: %d)" % (tested, unbal))
print("  EVEN counts (violations): %d" % bad)
print("  count range: %d .. %d" % (min(counts), max(counts)))

print()
print("== control: is the balance condition load-bearing? ==")
ev = od = 0
for i in range(0, 26):
    for j in range(0, 26):
        if balanced(i, j):
            continue
        n = window_count(i, j)
        if n % 2: od += 1
        else: ev += 1
print("  UNbalanced pairs: %d odd, %d even  (theorem makes no claim here)" % (od, ev))
