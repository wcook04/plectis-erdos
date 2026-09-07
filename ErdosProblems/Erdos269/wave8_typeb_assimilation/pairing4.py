"""Wave-9: where does the anchor actually bite, and why can't it be aligned?"""
from fractions import Fraction
import exact

AL, AH, BL, BH = exact.ALPHA_LO, exact.ALPHA_HI, exact.BETA_LO, exact.BETA_HI

def balanced(i, j):
    outs = set()
    for al, be in ((AL, BL), (AH, BH)):
        outs.add((j*be <= i*al + al - Fraction(1,2), i*al <= j*be + be - Fraction(1,2)))
    if len(outs) != 1: return None
    a, b = outs.pop(); return a and b

def smooth_upto(lim):
    out, p3 = [], 1
    while p3 <= lim:
        y = p3
        while y <= lim: out.append(y); y *= 5
        p3 *= 3
    return sorted(out)

hits, offs = [], []
for i in range(1, 130):
    for j in range(0, 130):
        if not balanced(i, j): continue
        x = 3**i * 5**j; x2 = x*x
        K = (x2.bit_length()-2)//2
        if K < 1: continue
        S = smooth_upto(2*x)
        E1 = sum(1 for y in S if y >= (1<<K) and 2*y*y <= x2)
        E2 = sum(1 for y in S if y >= (1<<(K+1)) and y*y < 2*x2)
        sK = sum(1 for y in S if (1<<K) <= y < (1<<(K+1)))
        # offset = c - (K+1/2)  in [0,1);  certified bracket
        lo = i*AL + j*BL - K - Fraction(1,2); hi = i*AH + j*BH - K - Fraction(1,2)
        offs.append((K, float(lo), E1, E2, sK))
        if E1 == 0 and E2 == 0:
            hits.append((K, i, j, sK, float(lo)))

print("anchors proving s(K) ODD unconditionally (E1 = E2 = 0):")
print("   K    i   j   s(K)  offset c-(K+1/2)")
for K,i,j,sK,o in hits: print("  %-4d %-3d %-3d %-5d %.6f" % (K,i,j,sK,o))
print()
print("smallest offsets found over all %d anchors (offset must be < ~2^-K to force emptiness):" % len(offs))
for K,o,E1,E2,sK in sorted(offs, key=lambda r: r[1])[:8]:
    print("  K=%-4d offset=%.3e   2^-K=%.3e   E1=%-4d E2=%-4d s(K)=%d" % (K,o,2.0**-K if K<1000 else 0.0,E1,E2,sK))
print()
print("=> the anchor is exactly aligned only if i*a + j*b = K + 1/2, i.e. 3^{2i}5^{2j} = 2^{2K+1}:")
print("   impossible by unique factorization; and the achievable offset is polynomial in the")
print("   anchor size while emptiness needs 2^-K, i.e. exponentially smaller.")
