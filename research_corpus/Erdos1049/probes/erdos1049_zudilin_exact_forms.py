"""Exact reconstruction of Zudilin's (2004) linear forms for the direction
(14,12,14;27) at index n, as polynomials in p over Z, and the rational-base
homogenisation test.

Everything is a product of cyclotomic polynomials times +-p^e, so no rational
function arithmetic is needed:
  A_k  = (-1)^{a1+a2+k+1} p^{E_k} [k-1 choose a1-1]_p [b-a2-1 choose b-k-1]_p
  A    = sum_k A_k p^{a0 k}
  D B1 = sum_l (D/(p^l-1)) * sum_{k >= a1+l} A_k p^{a0 k}
  D B2 = sum_j (D/(p^j-1)) * sum_k A_k p^{a0 k - j(k-a1)}
  D    = prod_{l<=15n} Phi_l,  D/(p^l-1) = prod_{l' <= 15n, l' not| l} Phi_{l'}
  U    = p^{-M} (D/Omega) A,  V = p^{-M} (D/Omega)(B1+B2)
Checks: Omega | D*A and Omega | D*(B1+B2) exactly (Lemma 7), p^M | both,
deg U = W_n, deg V = W_n - 1, V(0) = 1, ord_0 U = 2n^2, leading coeff +-1,
and numerically U(p) h_p(1) - V(p) = p^{-M} (D/Omega)(p) F_n(p) > 0.
"""
import sys
from fractions import Fraction
from math import gcd
from sympy import cyclotomic_poly, symbols, Poly, totient
from mpmath import mp, mpf, log, nstr, nsum, inf

sys.set_int_max_str_digits(0)
X = symbols("p")

# ---------- integer polynomial arithmetic via Kronecker substitution ----------
def kmul_nonneg(P, Q, bits):
    """P, Q lists of nonneg ints (low degree first)."""
    if not P or not Q:
        return []
    a = sum(c << (bits * i) for i, c in enumerate(P))
    b = sum(c << (bits * i) for i, c in enumerate(Q))
    c = a * b
    mask = (1 << bits) - 1
    out = []
    n = len(P) + len(Q) - 1
    for _ in range(n):
        out.append(c & mask)
        c >>= bits
    return out


def pmul(P, Q):
    if not P or not Q:
        return []
    bp = max(abs(c) for c in P)
    bq = max(abs(c) for c in Q)
    bits = (bp * bq * min(len(P), len(Q))).bit_length() + 2
    Pp = [max(c, 0) for c in P]; Pm = [max(-c, 0) for c in P]
    Qp = [max(c, 0) for c in Q]; Qm = [max(-c, 0) for c in Q]
    pp = kmul_nonneg(Pp, Qp, bits); mm = kmul_nonneg(Pm, Qm, bits)
    pm = kmul_nonneg(Pp, Qm, bits); mp_ = kmul_nonneg(Pm, Qp, bits)
    n = len(P) + len(Q) - 1
    out = [0] * n
    for arr, s in ((pp, 1), (mm, 1), (pm, -1), (mp_, -1)):
        for i, c in enumerate(arr):
            out[i] += s * c
    return trim(out)


def trim(P):
    while P and P[-1] == 0:
        P.pop()
    return P


def padd(P, Q):
    n = max(len(P), len(Q))
    out = [0] * n
    for i, c in enumerate(P): out[i] += c
    for i, c in enumerate(Q): out[i] += c
    return trim(out)


def pshift(P, e):
    """multiply by p^e (e may be negative if divisible)."""
    if e >= 0:
        return [0] * e + P
    assert all(c == 0 for c in P[:-e]), "not divisible by p^%d" % (-e)
    return P[-e:]


def pdivmod_monic(P, Q):
    """exact-or-not division by monic Q; returns (quotient, remainder)."""
    P = list(P)
    dq = len(Q) - 1
    assert Q[-1] == 1
    quo = [0] * max(len(P) - dq, 0)
    for i in range(len(P) - 1, dq - 1, -1):
        c = P[i]
        if c:
            quo[i - dq] = c
            for j, qc in enumerate(Q):
                P[i - dq + j] -= c * qc
    return trim(quo), trim(P)


def order(P):
    for i, c in enumerate(P):
        if c: return i
    return None


def peval(P, x):
    r = Fraction(0)
    for c in reversed(P):
        r = r * x + c
    return r


# ---------- cyclotomic machinery ----------
_cyc = {}
def Phi(l):
    if l not in _cyc:
        _cyc[l] = [int(c) for c in reversed(Poly(cyclotomic_poly(l, X), X).all_coeffs())]
    return _cyc[l]


def prod_cyc(ls):
    P = [1]
    for l in ls:
        P = pmul(P, Phi(l))
    return P


def gauss_binom(nn, kk):
    """[nn choose kk]_p as product of cyclotomics."""
    if kk < 0 or kk > nn:
        return []
    ls = [l for l in range(2, nn + 1) if (nn // l - kk // l - (nn - kk) // l) == 1]
    return prod_cyc(ls)


def build(n):
    a0, a1, a2, b = 14 * n + 1, 12 * n + 1, 14 * n + 1, 27 * n + 2
    N = 15 * n
    M = a1 * (a1 - 1) // 2 + a0 * a1 + (b - a2) * (a2 - a1)
    assert M == 266 * n * n + 34 * n + 1
    # nu_l and Omega
    def nu(l):
        return max(0, (14 * n) // l + (13 * n) // l - (12 * n) // l - (15 * n) // l,
                   2 * ((14 * n) // l) - (13 * n) // l - (15 * n) // l)
    nus = {l: nu(l) for l in range(2, N + 1)}
    assert all(v in (0, 1) for v in nus.values())
    Omega = prod_cyc([l for l in range(2, N + 1) if nus[l] == 1])
    DoverOmega = prod_cyc([l for l in range(1, N + 1) if l == 1 or nus[l] == 0])
    degD = sum(int(totient(l)) for l in range(1, N + 1))
    degOmega = sum(int(totient(l)) for l in range(2, N + 1) if nus[l] == 1)

    # A_k as (sign, exponent, polynomial without the p-power)
    Ak = {}
    for k in range(a2, b):
        E = a1 * (a1 - 1) // 2 - (b - a2) * (b - a2 - 1) // 2 + (b - k) * (b - k - 1) // 2
        sgn = (-1) ** (a1 + a2 + k + 1)
        core = pmul(gauss_binom(k - 1, a1 - 1), gauss_binom(b - a2 - 1, b - k - 1))
        Ak[k] = (sgn, E, core)

    def Ak_times_p(k, e):
        sgn, E, core = Ak[k]
        tot = E + e
        P = [sgn * c for c in core]
        return tot, P  # Laurent: p^tot * P

    # A(p): Laurent polynomial; collect with a global offset
    def laurent_sum(terms):
        mn = min(t for t, _ in terms)
        out = []
        for t, P in terms:
            out = padd(out, pshift(P, t - mn))
        return mn, out

    offA, Acore = laurent_sum([Ak_times_p(k, a0 * k) for k in range(a2, b)])
    degA = offA + len(Acore) - 1
    ordA = offA + order(Acore)
    K = (1091 * n * n + 81 * n + 2) // 2
    assert 2 * K == 1091 * n * n + 81 * n + 2
    print(f"n={n}: deg A = {degA} (return K_n = {K}), ord_0 A = {ordA} = M + {ordA - M} (return: M+2n^2 = {M + 2*n*n})")

    # D*B1 = sum_l (D/(p^l-1)) * sum_{k>=a1+l} A_k p^{a0 k}
    def D_over(l):
        return prod_cyc([lp for lp in range(1, N + 1) if l % lp != 0])
    DB1_terms = []
    for l in range(1, b - a1):
        ks = [k for k in range(a2, b) if k - a1 >= l]
        if not ks: continue
        off, S = laurent_sum([Ak_times_p(k, a0 * k) for k in ks])
        DB1_terms.append((off, pmul(D_over(l), S)))
    # D*B2 = sum_j (D/(p^j-1)) * sum_k A_k p^{a0 k - j(k-a1)}
    DB2_terms = []
    for j in range(1, a0):
        off, S = laurent_sum([Ak_times_p(k, a0 * k - j * (k - a1)) for k in range(a2, b)])
        DB2_terms.append((off, pmul(D_over(j), S)))
    offB, DBcore = laurent_sum(DB1_terms + DB2_terms)
    # D*A
    DA = pmul(prod_cyc(range(1, N + 1)), Acore)  # times p^offA

    # divide by Omega exactly
    qA, rA = pdivmod_monic(DA, Omega)
    qB, rB = pdivmod_monic(DBcore, Omega)
    print(f"   Lemma 7 divisibility: Omega | D*A: {not rA}, Omega | D*(B1+B2): {not rB}   (deg Omega = {len(Omega)-1}, deg D = {degD})")
    assert not rA and not rB
    # p^M divisibility and final polynomials U, V (true polynomials in p)
    U = pshift(qA, offA - M)
    V = pshift(qB, offB - M)
    W = K - M + degD - degOmega
    print(f"   W_n formula = {W}; deg U = {len(U)-1}, deg V = {len(V)-1}; lead U = {U[-1]}, lead V = {V[-1]}")
    print(f"   ord_0 U = {order(U)} (return 2n^2 = {2*n*n}); U reduced const = {U[order(U)]}; V(0) = {V[0]} (return: 1)")
    print(f"   K_n - W_n = {K - W}, (K_n-W_n)/n^2 = {(K-W)/n/n:.4f} -> C0=221.3;  K_n/n^2 = {K/n/n:.3f} -> C1=545.5")
    return dict(n=n, a=(a0, a1, a2, b), M=M, K=K, W=W, U=U, V=V, DoverOmega=DoverOmega, N=N)


def numeric_check(R, a, b):
    """Check U h - V = p^{-M}(D/Omega)(p) F_n(p) at p=a/b, positivity, and homogenised size."""
    n = R["n"]; a0, a1, a2, bb = R["a"]; M = R["M"]; W = R["W"]; K = R["K"]
    import math
    mp.dps = int(K * math.log10(a / b)) + 300
    p = mpf(a) / b; q = 1 / p
    h = mpf(0); m = 1
    while True:
        t = 1 / (p**m - 1); h += t; m += 1
        if t < mpf(10) ** (-mp.dps - 5): break
    Up = peval(R["U"], Fraction(a, b)); Vp = peval(R["V"], Fraction(a, b))
    lhs = mpf(Up.numerator) / Up.denominator * h - mpf(Vp.numerator) / Vp.denominator
    # F_n = sum_t R(q^t)
    def qpoch(x, r):
        out = mpf(1)
        for j in range(r): out *= (1 - x * q**j)
        return out
    def Rq(t):
        T = q**t
        return qpoch(q * T, a1 - 1) / qpoch(q, a1 - 1) * qpoch(q, bb - a2 - 1) / qpoch(q**a2 * T, bb - a2 - 1) * T**a0
    F = mpf(0); t = 0
    while True:
        r = Rq(t); F += r; t += 1
        if r < mpf(10) ** (-mp.dps - 5): break
    DO = peval(R["DoverOmega"], Fraction(a, b))
    rhs = p**(-M) * mpf(DO.numerator) / DO.denominator * F
    hom_U = Up * b**W; hom_V = Vp * b**W
    assert hom_U.denominator == 1 and hom_V.denominator == 1, "homogenised coefficients not integers"
    assert (Up * b**(W - 1)).denominator != 1, "degree strictly less than W?"
    lam_hat = lhs * b**W
    pred = K * log(b) - (K - W) * log(a)
    print(f"   p={a}/{b}: U h - V = {nstr(lhs, 12)}  vs  p^-M (D/Omega) F = {nstr(rhs, 12)}  rel.diff {nstr(abs(lhs/rhs-1), 3)}; positive: {lhs > 0}")
    print(f"      log(b^W Lambda) = {nstr(log(lam_hat), 10)};  K log b - (K-W) log a = {nstr(pred, 10)};  bounded residual log F + cyclotomic = {nstr(log(lam_hat) - pred, 6)};  log F = {nstr(log(F), 6)}")
    print(f"      gcd(hom U, hom V) = {gcd(int(hom_U), int(hom_V))}")


if __name__ == "__main__":
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    for n in range(1, nmax + 1):
        R = build(n)
        for (a, b) in ((31, 4), (3, 2), (7, 2)):
            numeric_check(R, a, b)
