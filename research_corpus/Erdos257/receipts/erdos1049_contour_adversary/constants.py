"""Independent C_0, C_1, J, theta* from Zudilin (25),(26) and Lemma 2; plus W_n bookkeeping for n<=6."""
from fractions import Fraction as Fr
from math import floor, log
from mpmath import mp, mpf, psi, pi, nstr
from sympy import totient
mp.dps = 40

al0, al1, al2, be = 14, 12, 14, 27
c00, c01, c11, c21, c12, c22 = al0+al1+al2-be, al0, al1, al2, be-al1, be-al2   # direction c (Section 5)
assert (c00,c01,c11,c21,c12,c22) == (13,14,12,14,15,13)
mm = max(c00,c01,c11,c21,c12,c22)
C1 = Fr(al0+al1+al2)*be - Fr(al1**2+al2**2+be**2, 2)
print("C1 =", C1, float(C1))

def omega(x):  # (26) with direction c; x rational
    f = lambda c: floor(c*x)
    return max(0, f(c21)+f(c22)-f(c11)-f(c12), f(c01)+f(c21)-f(c00)-f(c12))

# breakpoints: multiples of 1/c for the six c's; evaluate omega on each cell of [0,1)
bps = sorted({Fr(k, c) for c in (c00,c01,c11,c21,c12,c22) for k in range(c+1)})
cells = [(bps[i], bps[i+1]) for i in range(len(bps)-1)]
vals = [(u, v, omega((u+v)/2)) for u, v in cells]
assert all(w in (0,1) for _,_,w in vals)
# merge consecutive omega=1 cells
ints = []
for u, v, w in vals:
    if w == 1:
        if ints and ints[-1][1] == u: ints[-1] = (ints[-1][0], v)
        else: ints.append((u, v))
print("omega=1 intervals (%d):" % len(ints), " ".join(f"[{u},{v})" for u,v in ints))
paper = "[1/14,1/12) [1/7,1/6) [3/14,1/4) [2/7,1/3) [5/14,2/5) [3/7,7/15) [1/2,8/15) [4/7,3/5) [9/14,2/3) [5/7,11/15) [11/14,4/5) [6/7,13/15) [13/14,14/15)"
mine = " ".join(f"[{u},{v})" for u,v in ints)
print("matches paper list:", mine == paper)

J = sum(psi(1, mpf(u.numerator)/u.denominator) - psi(1, mpf(v.numerator)/v.denominator) for u, v in ints)
C0 = mpf(al1**2)/2 + al0*al1 + (be-al2)*(al2-al1) - 3/pi**2 * (mm**2 - J)
print("J  =", nstr(J, 25))
print("C0 =", nstr(C0, 25), "   paper 221.30008816...")
print("C1/C0 =", nstr(mpf(C1.numerator)/C1.denominator / C0, 25), "   paper Theorem 1: 2.46497868...")
theta = C0 / (mpf(C1.numerator)/C1.denominator)
print("theta* = C0/C1 =", nstr(theta, 25), "   note: 0.40568302138...")
print("BV threshold 1/2 - 1/pi^2 =", nstr(mpf(1)/2 - 1/pi**2, 20), "   1/mu_BV with mu_BV=2pi^2/(pi^2-2):", nstr((pi**2-2)/(2*pi**2), 20))
print("log4/log31 =", nstr(mpf(log(4))/log(31), 20), "  81/200 =", 0.405, "  inside ours:", float(theta) > log(4)/log(31), " outside BV:", log(4)/log(31) > 0.5 - 1/float(pi)**2)
print("C1 log 4 - C0 log 31 =", nstr(mpf(C1.numerator)/C1.denominator*log(4) - C0*log(31), 10))
print("theta* > 81/200:", theta > mpf(81)/200)

# Independent W_n bookkeeping from the definitions, n = 1..8
print("\n n   K_n   M_n   S_phi  S_nu_phi   W_n    (K-W)/n^2   K/n^2   deg formula matches note?")
for n in range(1, 9):
    a0,a1,a2,b = al0*n+1, al1*n+1, al2*n+1, be*n+2
    K = (1091*n*n+81*n+2)//2
    # direct degree: max over k of d_k with d_k strictly increasing
    ds = []
    for k in range(a2, b):
        e = a1*(a1-1)//2 - (b-a2)*(b-a2-1)//2 + (b-k)*(b-k-1)//2
        ds.append(a0*k + e + (a1-1)*(k-a1) + (b-k-1)*(k-a2))
    assert all(ds[i+1] > ds[i] for i in range(len(ds)-1)) and ds[-1] == K
    M = a1*(a1-1)//2 + a0*a1 + (b-a2)*(a2-a1)
    assert M == 266*n*n + 34*n + 1
    N = 15*n
    Sphi = sum(int(totient(l)) for l in range(1, N+1))
    Snu = 0
    for l in range(2, N+1):
        f = lambda c: (c*n)//l
        nu = max(0, f(c21)+f(c22)-f(c11)-f(c12), f(c01)+f(c21)-f(c00)-f(c12))
        assert nu == omega(Fr(n, l))
        Snu += nu*int(totient(l))
    W = K - M + Sphi - Snu
    print(f" {n}  {K:5d} {M:5d}  {Sphi:5d}  {Snu:5d}   {W:5d}   {(K-W)/n/n:8.3f}  {K/n/n:8.3f}")
# check l > 15n never has nu_l = 1 (u >= 1/14 => l <= 14 n)
for n in (1,2,3,5):
    bad = [l for l in range(15*n+1, 40*n) if omega(Fr(n,l)) != 0]
    print(f" n={n}: nu_l != 0 for some l > 15n? {bad}")
# large-n limits of (K-W)/n^2 and rate
for n in (10, 100, 400, 2000):
    K = (1091*n*n+81*n+2)//2; M = 266*n*n+34*n+1; N = 15*n
    Sphi = sum(int(totient(l)) for l in range(1, N+1))
    Snu = 0
    for l in range(2, N+1):
        f = lambda c: (c*n)//l
        Snu += max(0, f(c21)+f(c22)-f(c11)-f(c12), f(c01)+f(c21)-f(c00)-f(c12))*int(totient(l))
    W = K - M + Sphi - Snu
    main = K*log(4) - (K-W)*log(31)
    print(f" n={n}: (K-W)/n^2 = {(K-W)/n/n:.4f}  K/n^2 = {K/n/n:.4f}   main/n^2 at 31/4 = {main/n/n:.4f}")
