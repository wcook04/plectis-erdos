"""Independent Mahler-nullity detector, exact rational linear algebra.
Looks for  sum_{i=0..d} p_i(x) Y(x^(k^i)) = q(x)  with deg p_i <= D, deg q <= Dq.
Nullity = dim of the solution space (0 = no low-order Mahler relation)."""
from fractions import Fraction as F

def nullity(bits, k, d=2, D=5, Dq=None, M=None):
    if Dq is None: Dq = D + 6
    if M is None: M = 160
    # unknowns: p_i coefficients (i=0..d, deg 0..D), then q coefficients (0..Dq)
    npv = (d+1)*(D+1); nq = Dq+1; nun = npv + nq
    rows = []
    for m in range(0, M+1):
        row = [F(0)]*nun
        for i in range(d+1):
            ki = k**i
            for e in range(D+1):
                # p_i coeff e times Y(x^{k^i}) coeff (m-e)/k^i
                r = m - e
                if r >= 0 and r % ki == 0:
                    idx = r//ki
                    if idx < len(bits) and bits[idx]:
                        row[i*(D+1)+e] += 1
        if m <= Dq:
            row[npv+m] -= 1
        rows.append(row)
    # rank over Q by Gaussian elimination
    R = [r[:] for r in rows]; rank = 0; piv = []
    for c in range(nun):
        p = None
        for r in range(rank, len(R)):
            if R[r][c] != 0: p = r; break
        if p is None: continue
        R[rank], R[p] = R[p], R[rank]
        pv = R[rank][c]
        R[rank] = [v/pv for v in R[rank]]
        for r in range(len(R)):
            if r != rank and R[r][c] != 0:
                f = R[r][c]
                R[r] = [a - f*b for a, b in zip(R[r], R[rank])]
        piv.append(c); rank += 1
        if rank == len(R): break
    return nun - rank

N = 400
def ind(S): 
    b = [0]*(N+1)
    for a in S:
        if a <= N: b[a] = 1
    return b

def thue_morse(N):
    return [bin(n).count('1') % 2 for n in range(N+1)]
def primes(N):
    s=[True]*(N+1); s[0]=s[1]=False
    for i in range(2,int(N**.5)+1):
        if s[i]:
            for j in range(i*i,N+1,i): s[j]=False
    return {i for i,b in enumerate(s) if b}

controls = {
 "Thue-Morse (control)": thue_morse(N),
 "powers of 2":          ind({2**j for j in range(0,9)}),
 "powers of 3":          ind({3**j for j in range(0,6)}),
 "2^(2^k)":              ind({2**(2**j) for j in range(0,4)}),
 "N (all naturals)":     ind(set(range(1,N+1))),
 "primes":               ind(primes(N)),
}
print(f"{'sequence':>22} {'k=2':>6} {'k=3':>6} {'k=4':>6}   <- controls, compare to section AN")
for name, b in controls.items():
    print(f"{name:>22} " + "".join(f"{nullity(b,k):>6}" for k in (2,3,4)))

print("\n--- explicit witness that N must fire: Y_N(x) = x/(1-x) is RATIONAL ---")
print("    (1 - x) * Y(x) + 0*Y(x^k) + 0*Y(x^k^2) = x   -> an exact solution, so nullity > 0")

print("\n--- realised greedy supports of rational targets (finite prefixes) ---")
import sys
sys.path.insert(0,'formal_math/erdos257_period_noncollapse/scripts')
from late_hazard_profile import build_tables, run_target
DEPTH=380; P=3*DEPTH+200
Z,TT=build_tables(P)
for label,(p,q) in {"1/21":(1,21),"4/9":(4,9),"3/(2^7-1)":(3,127),"3/(2^13-1)":(3,8191),"1/1009":(1,1009)}.items():
    R0=(p<<P)//q
    st,rank,supp=run_target(R0,1,DEPTH,P,Z,TT)
    if st!="alive": print(f"{label:>12} {st} at {rank} -- skipped"); continue
    b=[0]*(N+1)
    for a in supp:
        if a<=N: b[a]=1
    print(f"{label:>12} |supp|={len(supp):>4}  nullity k=2,3,4 = " +
          "".join(f"{nullity(b,k):>4}" for k in (2,3,4)))
