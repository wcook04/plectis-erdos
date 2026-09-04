"""Why do the unconditional anchors dry up? Look at the offset sequence."""
from fractions import Fraction
import math, exact
AL, AH, BL, BH = exact.ALPHA_LO, exact.ALPHA_HI, exact.BETA_LO, exact.BETA_HI

def balanced(i, j):
    outs=set()
    for al,be in ((AL,BL),(AH,BH)):
        outs.add((j*be <= i*al+al-Fraction(1,2), i*al <= j*be+be-Fraction(1,2)))
    if len(outs)!=1: return None
    a,b=outs.pop(); return a and b

rows=[]
for i in range(1, 6000):
    j0=int(i*0.6826)
    for j in range(max(0,j0-2), j0+3):
        if not balanced(i,j): continue
        clo,chi = i*AL+j*BL, i*AH+j*BH
        K=int(clo-Fraction(1,2))
        if int(chi-Fraction(1,2))!=K or K<1: continue
        off=float(clo-K-Fraction(1,2))
        rows.append((K,i,j,off))
rows.sort()
print("balanced anchors: %d, K range %d..%d" % (len(rows), rows[0][0], rows[-1][0]))
print("levels covered: %d distinct" % len({r[0] for r in rows}))

# how close does offset*K get to 0 in successive octaves?
print("\noctave      #anchors   min(offset)    min(offset*K)   3.7/K at top")
lo=1
while lo < rows[-1][0]:
    hi=lo*4
    seg=[r for r in rows if lo<=r[0]<hi]
    if seg:
        m=min(seg, key=lambda r:r[3])
        mk=min(seg, key=lambda r:r[3]*r[0])
        print("  %-6d-%-6d %-9d  %.3e     %.4f        %.3e"
              % (lo,hi,len(seg),m[3],mk[3]*mk[0],3.7/hi))
    lo=hi

# distribution of offsets: uniform?
import collections
b=collections.Counter(int(r[3]*10) for r in rows)
print("\noffset decile histogram (uniform would be flat):")
print("  ", dict(sorted(b.items())))
