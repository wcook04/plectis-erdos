"""Wave-8: exact checks of the returns' algebraic claims."""
from fractions import Fraction
import exact, itertools, random

TH3 = (exact.ALPHA_LO, exact.ALPHA_HI)   # a*theta3 = a/alpha  (theta3=log_3 2)
def B(a): 
    lo = (a*exact.ALPHA_HI.denominator)//exact.ALPHA_HI.numerator
    hi = (a*exact.ALPHA_LO.denominator)//exact.ALPHA_LO.numerator
    assert lo==hi, a
    return lo
def C(a):
    lo = (a*exact.BETA_HI.denominator)//exact.BETA_HI.numerator
    hi = (a*exact.BETA_LO.denominator)//exact.BETA_LO.numerator
    assert lo==hi, a
    return lo
def Q(a): return 2**a * 3**B(a) * 5**C(a)

# ---- (a) LCM homogenisation (Returns 4 + 5): rho = Pbar_L / P_{a,L} in {1,3,5,15}
print("== (a) LCM homogenisation ==")
seen=set(); bad=0; n=0
for L in range(1,45):
    fl3, fl5 = B(L), C(L)          # floor(L*theta3), floor(L*theta5)
    Pbar = 2**L * 3**(fl3+1) * 5**(fl5+1)
    for a in range(0,400):
        P = Q(a+L)//Q(a); n+=1
        r = Fraction(Pbar, P)
        if r.denominator!=1 or int(r) not in (1,3,5,15): bad+=1
        else: seen.add(int(r))
print("  %d (a,L) pairs, rho values realised %s, violations %d" % (n, sorted(seen), bad))

# ---- (b) Return 6 CRT-star: kappa >= 1/3  and  1/2 N^{-1/m} <= 1/3
print("== (b) CRT terminal-digit star ==")
def kappa(res, N):
    best=Fraction(1,2)
    for q in range(1,N):
        mx=max(min((q*e)%N, N-((q*e)%N)) for e in res)
        best=min(best, Fraction(mx,N))
    return best
bad=0; rows=[]
for (a,b,c) in [(3,0,0),(0,3,0),(0,0,2),(2,1,1),(3,2,1),(1,1,2),(4,1,1),(2,2,1)]:
    N=2**a*3**b*5**c
    if N<2: continue
    res=[]
    for j in range(a): res.append((N//2**a)*2**j*1)          # u odd
    for j in range(b): res.append((N//3**b)*3**j*1)          # 3 nmid u
    for j in range(c):
        res.append((N//5**c)*5**j*1); res.append((N//5**c)*5**j*2)   # v/u = 2
    m=a+b+2*c
    if not res: continue
    k=kappa(res,N)
    ok = k>=Fraction(1,3)
    tgt = Fraction(N,1) >= Fraction(3,2)**m      # N >= (3/2)^m  <=> 1/2 N^{-1/m} <= 1/3
    rows.append((a,b,c,N,m,str(k),ok,tgt))
    if not (ok and tgt): bad+=1
for r in rows: print("   a,b,c=%d,%d,%d N=%-6d m=%-2d kappa=%-8s kappa>=1/3:%s  N>=(3/2)^m:%s"%r)
print("  violations:", bad)

# ---- (c) Return 6 dyadic ladder: kappa >= 1/3
print("== (c) dyadic unit ladder ==")
bad=0
for N in range(3,400):
    K=max(0,(N//3).bit_length())
    res=sorted({pow(2,k,N) for k in range(K+2)})
    if kappa(res,N) < Fraction(1,3): bad+=1; print("   FAIL N=%d kappa=%s"%(N,kappa(res,N)))
print("  N=3..399 violations:", bad)

# ---- (f) Return 5 rectangle top-corner:  sigma(Nc)+sigma(Nc-p a)+sigma(Nc-q b) = 1 mod 2
print("== (f) rectangle top-corner forcing ==")
AL, BE = exact.ALPHA_LO, exact.BETA_LO   # use tight rationals, check both brackets
def sigma_cnt(t_lo, t_hi):
    """#{(u,v)>=0 : t <= u*alpha+v*beta < t+1} certified, small t only."""
    outs=set()
    for al,be in ((exact.ALPHA_LO,exact.BETA_LO),(exact.ALPHA_HI,exact.BETA_HI)):
        c=0; u=0
        while u*al <= t_hi+2:
            v=0
            while u*al+v*be < t_hi+1:
                if t_lo <= u*al+v*be < t_lo+1: c+=1
                v+=1
            u+=1
        outs.add(c)
    return outs.pop() if len(outs)==1 else None
bad=0; tested=0
for p in range(1,9):
    for q in range(1,9):
        pa = p*exact.ALPHA_LO; qb = q*exact.BETA_LO
        Wd = (p-1)*exact.ALPHA_LO + (q-1)*exact.BETA_LO
        Nc = int(Wd)
        vals=[sigma_cnt(Fraction(Nc),Fraction(Nc)), sigma_cnt(Nc-pa,Nc-pa), sigma_cnt(Nc-qb,Nc-qb)]
        if any(v is None for v in vals): continue
        tested+=1
        if sum(vals)%2 != 1: bad+=1; print("   FAIL p=%d q=%d vals=%s"%(p,q,vals))
print("  %d (p,q) pairs tested, violations %d"%(tested,bad))
