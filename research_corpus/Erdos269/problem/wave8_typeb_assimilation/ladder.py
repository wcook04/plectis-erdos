"""Wave-9 discriminating test: do unconditional ODD anchors occur cofinally?

Anchor = balanced (i,j).  offset = i*alpha + j*beta - K - 1/2,  K = floor(c-1/2).
If the two edge intervals [K, K+offset] and [K+1, K+1+offset] are EMPTY of
smooth points, then  s(K) = N* = ODD  unconditionally (Theorem P).

Heuristic: edges empty needs offset < gap_K ~ 3.7/K, and offset is ~uniform
in [0,1) over the ~0.4-per-level balanced anchors, so the number of qualifying
levels K <= X should grow like c*log X -- i.e. INFINITELY many, but sparsely.
"""
from fractions import Fraction
import sys, math
import exact

AL, AH, BL, BH = exact.ALPHA_LO, exact.ALPHA_HI, exact.BETA_LO, exact.BETA_HI
IMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 4000


def balanced(i, j):
    outs = set()
    for al, be in ((AL, BL), (AH, BH)):
        outs.add((j*be <= i*al + al - Fraction(1,2), i*al <= j*be + be - Fraction(1,2)))
    if len(outs) != 1: return None
    a, b = outs.pop(); return a and b


# ---- stage 1: cheap rational scan for balanced anchors with small offset ----
cands, n_anchor = [], 0
for i in range(1, IMAX):
    # balance forces j ~ i*alpha/beta; scan a tiny window
    j0 = int(i * 0.6826)
    for j in range(max(0, j0 - 2), j0 + 3):
        b = balanced(i, j)
        assert b is not None, (i, j)
        if not b: continue
        n_anchor += 1
        clo, chi = i*AL + j*BL, i*AH + j*BH
        Klo = int(clo - Fraction(1,2)); Khi = int(chi - Fraction(1,2))
        if Klo != Khi: continue
        K = Klo
        off_lo = clo - K - Fraction(1,2); off_hi = chi - K - Fraction(1,2)
        if K > 0 and off_hi < Fraction(12, K):
            cands.append((K, i, j, off_lo, off_hi))

print("balanced anchors found: %d   (i < %d)" % (n_anchor, IMAX))
print("stage-1 survivors (offset < 12/K): %d" % len(cands))

# ---- stage 2: exact edge-emptiness via certified floor sums ----
hits = []
for (K, i, j, olo, ohi) in cands:
    clo, chi = i*AL + j*BL, i*AH + j*BH
    TK   = exact.T_real(Fraction(K), Fraction(K))
    TK1  = exact.T_real(Fraction(K+1), Fraction(K+1))
    Tlo  = exact.T_real(clo - Fraction(1,2), chi - Fraction(1,2))
    Thi  = exact.T_real(clo + Fraction(1,2), chi + Fraction(1,2))
    if None in (TK, TK1, Tlo, Thi):
        print("  uncertified at K=%d" % K); continue
    E1, E2 = Tlo - TK, Thi - TK1
    sK, Nstar = TK1 - TK, Thi - Tlo
    assert sK == Nstar - E2 + E1
    assert Nstar % 2 == 1, ("Theorem P FAILED", i, j)
    if E1 == 0 and E2 == 0:
        hits.append((K, i, j, sK, float(ohi)))

print()
print("UNCONDITIONAL ODD levels (E1 = E2 = 0  =>  s(K) is ODD, proved):")
print("   K      i     j     s(K)   offset")
for K,i,j,sK,o in sorted(hits):
    assert sK % 2 == 1
    print("  %-7d %-5d %-5d %-6d %.3e" % (K,i,j,sK,o))
print("\ncount = %d over K <= %d" % (len(hits), max(h[0] for h in hits)))
X = max(h[0] for h in hits)
print("log-growth check: count/ln(K_max) = %.2f" % (len(hits)/math.log(X)))
for cut in (100, 500, 2000, 10000, 50000):
    c = sum(1 for h in hits if h[0] <= cut)
    if c: print("   K <= %-6d : %2d hits   (c/lnK = %.2f)" % (cut, c, c/math.log(cut)))
