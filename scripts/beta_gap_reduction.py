"""
EXACT REFORMULATION of Erdos 257 (derived, then verified below).

rho_n = greedy Mersenne residual;  beta_n := 2^n rho_n.  Then
        beta_n = 2 beta_{n-1} - b_n * 2^n/(2^n - 1),      b_n in {0,1},
and  y = sum_{d in A} 1/(2^d-1)  with A={n: b_n=1}   <=>   beta_n in [0,1) for all n.

The digit is FORCED:
   b_n = 0  needs  beta_{n-1} <  1/2
   b_n = 1  needs  beta_{n-1} >= T_n := 2^{n-1}/(2^n-1) = 1/2 + 1/(2(2^n-1))
so the process DIES iff  beta_{n-1} in [ 1/2 , T_n )  -- a "sliver" of width 1/(2(2^n-1)).

=> Erdos 257 is FALSE iff some rational y has an orbit avoiding every sliver.
No divisor counts, no LCM, no carries, no Boolean ancestry: one 1-D map.
"""
from fractions import Fraction

def orbit_exact(p,q,R):
    beta=Fraction(p,q); A=[]
    for n in range(1,R+1):
        if beta==0: return A,None,"TERMINATED"
        T=Fraction(1<<(n-1),(1<<n)-1)
        if beta<Fraction(1,2): beta=2*beta
        elif beta>=T: A.append(n); beta=2*beta-Fraction(1<<n,(1<<n)-1)
        else: return A,n,"SLIVER"
        assert 0<=beta<1,(n,beta)
    return A,None,"ALIVE"

if __name__=="__main__":
    # validation: reproduce known expansions and check the sum is exactly y
    for p,q in [(1,7),(1,3),(1,21),(1,465),(1,6),(4,9),(1,105),(2,5),(3,11)]:
        A,fail,st=orbit_exact(p,q,120)
        S=sum(Fraction(1,2**d-1) for d in A)
        tail=sum(Fraction(1,2**d-1) for d in range(121,400))
        ok = (S==Fraction(p,q)) if st=="TERMINATED" else (0<=Fraction(p,q)-S<=tail)
        print(f"{p}/{q:4d}: {st:10s} fail@{str(fail):5s} |A|={len(A):3d} A[:12]={A[:12]}  residual-consistent={ok}")
