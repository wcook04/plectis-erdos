"""Reconstruct Zudilin (2004, Acta Arith. 111.2) constants C_1, C_0 for the
direction (alpha0, alpha1, alpha2; beta) = (14, 12, 14; 27) and check the
packet's contour 0.40568302138... = C_0/C_1 = 1/mu_Zudilin.

Source formulas (paper, Section 5):
  C_1 = (a0+a1+a2) b - (a1^2 + a2^2 + b^2)/2                          ... (25)
  C_0 = a1^2/2 + a0 a1 + (b-a2)(a2-a1)
        - (3/pi^2) * ( m^2 - int_0^1 omega(x) d(-psi'(x)) )           ... (26)
  omega(x) = max{0, [c21 x]+[c22 x]-[c11 x]-[c12 x], [c01 x]+[c21 x]-[c00 x]-[c12 x]}
  with c00=13, c01=14, c11=12, c21=14, c12=15, c22=13, m = max c = 15.
  int_{[u,v)} d(-psi') = psi_1(u) - psi_1(v)  (Lemma 2).
"""
from fractions import Fraction
from mpmath import mp, mpf, pi, polygamma, zeta, log, nstr

mp.dps = 40

a0, a1, a2, b = 14, 12, 14, 27
c00, c01, c11, c21, c12, c22 = a0 + a1 + a2 - b, a0, a1, a2, b - a1, b - a2
m = max(c00, c01, c11, c21, c12, c22)
print("c =", (c00, c01, c11, c21, c12, c22), "m =", m)

C1 = Fraction((a0 + a1 + a2) * b) - Fraction(a1 * a1 + a2 * a2 + b * b, 2)
Mcoef = Fraction(a1 * a1, 2) + a0 * a1 + (b - a2) * (a2 - a1)
print("C1 =", C1, "=", float(C1))
print("M/n^2 coefficient =", Mcoef, "=", float(Mcoef))


def omega(x: Fraction) -> int:
    fl = lambda c: (c * x).numerator // (c * x).denominator
    return max(0, fl(c21) + fl(c22) - fl(c11) - fl(c12), fl(c01) + fl(c21) - fl(c00) - fl(c12))


# omega is a step function with breakpoints at k/c for the six c's.
bps = sorted({Fraction(k, c) for c in (c00, c01, c11, c21, c12, c22) for k in range(0, c + 1)})
intervals = []  # maximal [u, v) with omega == 1
cur = None
for u, v in zip(bps, bps[1:]):
    val = omega((u + v) / 2)
    assert val in (0, 1), (u, v, val)
    if val == 1:
        if cur and cur[1] == u:
            cur[1] = v
        else:
            cur = [u, v]
            intervals.append(cur)
print("omega==1 intervals (%d):" % len(intervals))
for u, v in intervals:
    print("   [%s, %s)" % (u, v))

# J = int_0^1 omega(x) d(-psi'(x)) = sum (psi_1(u) - psi_1(v))
psi1 = lambda x: polygamma(1, mpf(x.numerator) / x.denominator)
J = sum(psi1(u) - psi1(v) for u, v in intervals)
print("J =", nstr(J, 25))
C0 = mpf(Mcoef.numerator) / Mcoef.denominator - 3 / pi**2 * (m * m - J)
print("C0 =", nstr(C0, 25), "   (paper: 221.30008816...)")
C1m = mpf(C1.numerator) / C1.denominator
print("C1/C0 = mu =", nstr(C1m / C0, 25), "   (paper: 2.46497868...)")
theta = C0 / C1m
print("C0/C1 = theta* =", nstr(theta, 25), "   (packet: 0.40568302138...)")
print("81/200 =", 81 / 200, "  theta* > 81/200:", theta > mpf(81) / 200)
bv = mpf(1) / 2 - 1 / pi**2
print("BV 1/2-1/pi^2 =", nstr(bv, 20), " = 1/mu_BV, mu_BV = 2pi^2/(pi^2-2) =", nstr(2 * pi**2 / (pi**2 - 2), 20))
print("log4/log31 =", nstr(log(4) / log(31), 15), "  inside:", log(4) / log(31) < theta)
print("log2/log3  =", nstr(log(2) / log(3), 15), "  inside:", log(2) / log(3) < theta)
# Return's rational lower bound for J: retain k<10 terms of psi_1(u)-psi_1(v) = sum_k (v-u)(2k+u+v)/((k+u)^2 (k+v)^2)
Jlow = sum(sum((v - u) * (2 * k + u + v) / ((k + u) ** 2 * (k + v) ** 2) for k in range(10)) for u, v in intervals)
print("J lower bound (k<10, exact rational) =", Jlow, "=", float(Jlow), "  return: 389699/5000 =", 389699 / 5000)
C0low = Fraction(Mcoef) - Fraction(3) / Fraction(157, 50) ** 2 * (m * m - Jlow)
print("C0 lower bound with pi>157/50 =", float(C0low), "  > 88371/400 =", float(Fraction(88371, 400)), ":", C0low > Fraction(88371, 400))
print("88371/400 / C1 =", Fraction(88371, 400) / C1)
# Exponent budget at 3/2 quoted by the return
print("E_{3/2} = C1 log2 - C0 log3 =", nstr(C1m * log(2) - C0 * log(3), 15), "  (return: 134.98879065)")
print("(C1-C0) = W_n/n^2 limit =", nstr(C1m - C0, 20))
print("(3/pi^2)(225-J) =", nstr(3 / pi**2 * (m * m - J), 20))
