"""Independent reconstruction of Zudilin 2004, direction (14,12,14;27), index n.
Built from the paper's printed formulas (8),(10),(11),(16),(22) only.
"""
import sys, time
from fractions import Fraction
from sympy import symbols, Poly, ZZ, cyclotomic_poly, totient
from mpmath import mp, mpf, log, nsum, inf, nstr

sys.set_int_max_str_digits(0)
p = symbols('p')
n = int(sys.argv[1]) if len(sys.argv) > 1 else 1
t0 = time.time()

al0, al1, al2, be = 14, 12, 14, 27
a0, a1, a2, b = al0*n+1, al1*n+1, al2*n+1, be*n+2
assert a1 <= a2 and a1 + a2 <= b <= a0 + a2          # (14)
c00, c01, c11, c21, c12, c22 = a0+a1+a2-b-1, a0-1, a1-1, a2-1, b-a1-1, b-a2-1
mc = max(c00, c01, c11, c21, c12, c22)               # m(c) = 15 n
N = mc
M = a1*(a1-1)//2 + a0*a1 + (b-a2)*(a2-a1)            # (16)
print(f"n={n}: a=({a0},{a1},{a2}) b={b} c=({c00},{c01},{c11},{c21},{c12},{c22}) m(c)={mc} M={M}")

# q-binomial [n choose k]_p via q-Pascal, exact integer polys
_qb = {}
def qbin(nn, kk):
    if kk < 0 or kk > nn: return Poly(0, p, domain=ZZ)
    if kk == 0 or kk == nn: return Poly(1, p, domain=ZZ)
    key = (nn, kk)
    if key not in _qb:
        # [n,k] = [n-1,k-1] + p^k [n-1,k]
        _qb[key] = qbin(nn-1, kk-1) + Poly(p**kk, p, domain=ZZ) * qbin(nn-1, kk)
    return _qb[key]

def Ak(k):                                           # (8), p-form
    e = a1*(a1-1)//2 - (b-a2)*(b-a2-1)//2 + (b-k)*(b-k-1)//2
    s = (-1)**(a1+a2+k+1)
    return s, e, qbin(k-1, a1-1) * qbin(b-a2-1, b-k-1)

# cyclotomics and D_N
Phi = {l: Poly(cyclotomic_poly(l, p), p, domain=ZZ) for l in range(1, N+1)}
D = Poly(1, p, domain=ZZ)
for l in range(1, N+1): D = D * Phi[l]
degD = D.degree()
assert degD == sum(int(totient(l)) for l in range(1, N+1))

# nu_l from (22), Omega
nu = {}
for l in range(2, mc+1):
    fl = lambda x: x // l
    nu[l] = max(0, fl(c21)+fl(c22)-fl(c11)-fl(c12), fl(c01)+fl(c21)-fl(c00)-fl(c12))
Omega = Poly(1, p, domain=ZZ)
for l, v in nu.items():
    for _ in range(v): Omega = Omega * Phi[l]
print("  nu_l=1 at l =", [l for l in nu if nu[l] >= 1], " max nu =", max(nu.values()), " deg Omega =", Omega.degree())

# A(p), D*B1, D*B2  (all exact in Z[p])
A = Poly(0, p, domain=ZZ)
Aterm = {}
for k in range(a2, b):
    s, e, Q = Ak(k)
    Aterm[k] = Q * Poly(s * p**(e + a0*k), p, domain=ZZ)
    A = A + Aterm[k]
K = A.degree()
print(f"  deg A = {K}   K_n formula = {(1091*n*n+81*n+2)//2}   lead A = {A.LC()}   ord_0 A = {min(m[0] for m in A.monoms())}")

Dover = {}
for l in range(1, N+1):
    q_, r_ = D.div(Poly(p**l - 1, p, domain=ZZ)); assert r_.is_zero
    Dover[l] = q_
DB1 = Poly(0, p, domain=ZZ)
for l in range(1, N+1):                              # (10): l runs 1..k-a1, so k >= a1+l
    inner = Poly(0, p, domain=ZZ)
    for k in range(max(a2, a1+l), b):
        inner = inner + Aterm[k]
    if not inner.is_zero: DB1 = DB1 + Dover[l] * inner
DB2 = Poly(0, p, domain=ZZ)
for j in range(1, a0):                               # (11)
    inner = Poly(0, p, domain=ZZ)
    for k in range(a2, b):
        s, e, Q = Ak(k)
        inner = inner + Q * Poly(s * p**(e + a0*k - j*(k-a1)), p, domain=ZZ)
    DB2 = DB2 + Dover[j] * inner
DB = DB1 + DB2
print(f"  built A, D*B in {time.time()-t0:.1f}s")

# Lemma 7 checks
DA = D * A
qU, rU = DA.div(Omega); qV, rV = DB.div(Omega)
print("  Omega | D*A :", rU.is_zero, "   Omega | D*(B1+B2) :", rV.is_zero)
ordU = min(m[0] for m in qU.monoms()); ordV = min(m[0] for m in qV.monoms())
print(f"  ord_0 of D*A/Omega = {ordU} (need >= M={M}),  ord_0 of D*B/Omega = {ordV}")
U = qU.exquo(Poly(p**M, p, domain=ZZ)); V = qV.exquo(Poly(p**M, p, domain=ZZ))
W = K - M + degD - Omega.degree()
print(f"  W_n formula = {W};  deg U = {U.degree()}  deg V = {V.degree()};  lead U={U.LC()} lead V={V.LC()};  U coeffs all int: {U.domain}, V: {V.domain}")
print(f"  ord_0 U = {min(m[0] for m in U.monoms())}   V(0) = {V.eval(0)}")
# S phi, S nu phi
Sphi = sum(int(totient(l)) for l in range(1, N+1)); Snu = sum(nu[l]*int(totient(l)) for l in nu)
print(f"  sum phi(l<= {N}) = {Sphi}   sum nu_l phi(l) = {Snu}   K-W = {K-W}   (K-W)/n^2 = {(K-W)/n/n:.4f}   K/n^2={K/n/n:.3f}")

# numerical identity checks at rational p
def checks(pa, pb):
    mp.dps = int(K * log(pa/pb, 10)) + 120 if pa/pb > 1 else 200
    P = mpf(pa) / pb; q = 1 / P
    # F_n(p) = sum_{t>=0} R(q^t) from the product definition (paper, before (7))
    def qp(x, m):  # (x;q)_m
        r = mpf(1)
        for nu_ in range(1, m+1): r *= (1 - x*q**(nu_-1))
        return r
    den1 = qp(q, a1-1); num2 = qp(q, b-a2-1)
    def R(T): return qp(q*T, a1-1)/den1 * num2/qp(q**a2 * T, b-a2-1) * T**a0
    F = nsum(lambda t: R(q**int(t)), [0, inf])
    h = nsum(lambda m_: 1/(P**int(m_) - 1), [1, inf])
    Ap = A.eval(P); B1 = DB1.eval(P)/D.eval(P); B2 = DB2.eval(P)/D.eval(P)
    lhs9 = Ap*h - B1 - B2
    Up = U.eval(P); Vp = V.eval(P)
    Lam = P**(-M) * D.eval(P)/Omega.eval(P) * F
    lin = Up*h - Vp
    # homogenised integers
    Uh = Fraction(0); Vh = Fraction(0)
    for (dg,), cf in U.terms(): Uh += Fraction(int(cf)) * Fraction(pa, pb)**dg * Fraction(pb)**W
    for (dg,), cf in V.terms(): Vh += Fraction(int(cf)) * Fraction(pa, pb)**dg * Fraction(pb)**W
    Uh1 = Fraction(0)
    for (dg,), cf in U.terms(): Uh1 += Fraction(int(cf)) * Fraction(pa, pb)**dg * Fraction(pb)**(W-1)
    lamhat = mpf(pb)**W * Lam
    main = K*log(pb) - (K-W)*log(pa)
    print(f"  p={pa}/{pb}: identity(9) rel = {nstr(abs(F-lhs9)/F, 3)};  U h - V vs Lambda rel = {nstr(abs(lin-Lam)/Lam, 3)};  Lambda>0: {Lam>0};  F={nstr(F,8)}")
    print(f"      b^W U(a/b) integer: {Uh.denominator==1}  b^W V(a/b) integer: {Vh.denominator==1}  b^(W-1) U integer: {Uh1.denominator==1}")
    print(f"      log(b^W Lambda) = {nstr(log(lamhat),8)}   K log b - (K-W) log a = {nstr(main,8)}   residual = {nstr(log(lamhat)-main,5)}   logF = {nstr(log(F),5)}")
    # bound check on F: (q;q)_inf^2 <= F <= (q;q)_inf^-2/(1-q^a0)
    qq = nsum(lambda i: 0, [0,0])  # placeholder
    qinf = mpf(1)
    for i in range(1, 400): qinf *= (1 - q**i)
    print(f"      F bounds: (q;q)^2={nstr(qinf**2,6)} <= F={nstr(F,6)} <= {nstr(qinf**-2/(1-q**a0),6)} : {qinf**2 <= F <= qinf**-2/(1-q**a0)}")

for pa, pb in [(31, 4), (3, 1), (7, 2)]:
    checks(pa, pb)
print(f"  total {time.time()-t0:.1f}s")
