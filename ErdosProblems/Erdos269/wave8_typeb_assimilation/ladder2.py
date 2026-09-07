"""Wave-9: one-edge variant of the anchor.

The involution d -> N/d preserves |log2(y/x)| < w for EVERY w, so the balance
condition (B1_w) j*beta <= i*alpha+alpha-w, (B2_w) i*alpha <= j*beta+beta-w
gives an ODD count on (c-w, c+w) for every admissible w.

Take w = c - K exactly: the LEFT endpoint sits on the integer K, so
   (K, 2c-K)  has ODD count, and with 2c-K = K+1+2*off  (off = c-K-1/2),
   s(K) = 1 + E   (mod 2),    E = #{smooth in [K+1, K+1+2*off)} -- ONE edge.
"""
from fractions import Fraction
import sys, math, exact
AL, AH, BL, BH = exact.ALPHA_LO, exact.ALPHA_HI, exact.BETA_LO, exact.BETA_HI
IMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 6000

def bal_w(i, j, w_lo, w_hi):
    outs=set()
    for al,be in ((AL,BL),(AH,BH)):
        outs.add((j*be <= i*al+al-w_hi, i*al <= j*be+be-w_hi))
    if len(outs)!=1: return None
    a,b=outs.pop(); return a and b

cands=[]; n=0
for i in range(1, IMAX):
    j0=int(i*0.6826)
    for j in range(max(0,j0-2), j0+3):
        clo,chi = i*AL+j*BL, i*AH+j*BH
        K=int(clo-Fraction(1,2))
        if int(chi-Fraction(1,2))!=K or K<1: continue
        w_lo, w_hi = clo-K, chi-K                    # w = c-K  (~1/2)
        b=bal_w(i,j,w_lo,w_hi)
        if b is None or not b: continue
        n+=1
        off_hi = chi-K-Fraction(1,2)
        if off_hi < Fraction(12,K): cands.append((K,i,j,clo,chi))
print("balanced-for-w anchors: %d ; stage-1 survivors: %d" % (n, len(cands)))

hits=[]
for (K,i,j,clo,chi) in cands:
    TK  = exact.T_real(Fraction(K),Fraction(K))
    TK1 = exact.T_real(Fraction(K+1),Fraction(K+1))
    Tr  = exact.T_real(2*clo-K, 2*chi-K)             # right endpoint 2c-K
    if None in (TK,TK1,Tr): print("  uncertified K=%d"%K); continue
    Nstar = Tr - TK
    assert Nstar % 2 == 1, ("one-edge Theorem P FAILED", i, j, Nstar)
    E  = Tr - TK1
    sK = TK1 - TK
    assert (sK - (1+E)) % 2 == 0, ("corollary failed", i, j)
    if E == 0: hits.append((K,i,j,sK,float(chi-K-Fraction(1,2))))

print("\nUNCONDITIONAL ODD levels via the ONE-EDGE anchor (E = 0):")
print("   K       i     j     s(K)   offset")
for K,i,j,sK,o in sorted(hits):
    assert sK % 2 == 1
    print("  %-8d %-5d %-5d %-6d %.3e" % (K,i,j,sK,o))
print("\ncount = %d  over K <= %d" % (len(hits), max(c[0] for c in cands)))
for cut in (400, 2000, 10000, 30000):
    c=sum(1 for h in hits if h[0]<=cut)
    if c: print("   K <= %-6d : %2d   (c/lnK = %.2f)" % (cut,c,c/math.log(cut)))
