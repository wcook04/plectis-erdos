"""Independent re-derivation of GapAvoidance section 3: is the normalised skip
position v_n = rho_{n-1}/w_n equidistributed on [0,1) for large q?
Ratio reported is P(v > 1-eps)/eps at eps = 2^-2 .. 2^-12; 1.00 = equidistributed."""
import sys, random
sys.path.insert(0,'formal_math/erdos257_period_noncollapse/scripts')
from late_hazard_profile import build_tables

DEPTH=250; P=3*DEPTH+200; MINRANK=40
Z,TT=build_tables(P)

def skips(R0, err0):
    """certified forced greedy; yield v = r/z at each certified skip with n >= MINRANK"""
    R,err=R0,err0; out=[]
    for n in range(1, DEPTH+1):
        zn=Z[n]
        if R >= zn+1:
            R=R-zn-1; err+=1
            if R+err < 1: return out
            continue
        if R+err < zn:
            if n>=MINRANK: out.append(R/zn)
            hi=TT[n]+(P-n)+2
            if R > hi: return out          # certified death
            if R+err <= TT[n]: continue
            return out                      # indeterminate: stop, do not resolve
        return out                          # indeterminate take
    return out

EPS=[2.0**-e for e in range(2,13)]
def profile(vs):
    n=len(vs); out=[]
    for e in EPS:
        c=sum(1 for v in vs if v > 1-e)
        out.append((c/n)/e if n else float('nan'))
    return out

rng=random.Random(4242)
ranges={"q 3..200":(3,200,1500),"q 1e5..2e5":(10**5,2*10**5,1500),"q 1e12..2e12":(10**12,2*10**12,1500)}
print(f"{'range':>14} {'skips':>8}  " + "".join(f"{('2^-'+str(e)):>8}" for e in range(2,13)))
for label,(lo,hi,ntar) in ranges.items():
    vs=[]
    for _ in range(ntar):
        q=rng.randrange(lo,hi+1)
        pmax=(q*TT[0])>>P
        if pmax<1: continue
        p=rng.randrange(1,pmax+1)
        vs.extend(skips((p<<P)//q, 1))
    pr=profile(vs)
    print(f"{label:>14} {len(vs):>8}  " + "".join(f"{x:>8.2f}" for x in pr), flush=True)
print("\nsection 3 reports: q 3..200 -> 0.94 .. 0.79 ; q 1e5..2e5 -> 1.00 .. 1.16 ; q 1e12..2e12 -> 1.00 .. 1.01")
