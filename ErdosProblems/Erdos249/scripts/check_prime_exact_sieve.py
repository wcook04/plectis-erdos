"""Erdos 249: exact checks for the prime-exact sieve family c_P.

Audits, by exact integer / Fraction computation, the claims of the prime-exact
sieve return (batch erdos249_20260905_eight_return_stream_01, r08):

    n = s_P(n) t_P(n)  (P-smooth part times P-free part)
    c_P(n) = phi(s_P(n))              if t_P(n) = 1
           = phi(s_P(n)) (t_P(n) - 1) if t_P(n) > 1
    C_P    = sum_n c_P(n) 2^{-n}

  * (2) phi(n) <= c_P(n) <= n, c_P(p) = p-1 at every prime;
  * (3) the Euler law c_P(pn) = (p-1)c_P(n) or p c_P(n) for p in P;
  * (5) C_empty = 3/2 and (4) C_P - C_Q > 0 for P strictly inside Q;
  * (10) the Euler-sieve coefficient phi(s_P(n)) sigma(t_P(n)), whose first
    deviation from phi is at n = r with coefficient 2 (the corpus row
    finite_euler_sieve_sharp_tail), versus c_P whose first deviation is at
    n = r^2 with coefficient r-1;
  * (16)/(17) rationality of A_P = sum_{d | M_P} mu(d) 2^d/(2^d-1)^2;
  * Lemma 3 (25): h_P(N_L + m) = b_P(m) for m <= L, and N_L + m never
    P-smooth;
  * (6)/(7)/(40)-(42): the quadratic first-error estimate, plus the sharper
    second term (r + r' - 2) 2^{-r r'} with r' the next prime after r;
  * the failure certificate (51).

Run:  ./repo-python <this file> --quick
      ./repo-python <this file>
"""

from __future__ import annotations

import argparse
import math
from fractions import Fraction


def sieve(n):
    phi = list(range(n + 1))
    spf = [0] * (n + 1)
    for i in range(2, n + 1):
        if phi[i] == i:  # i prime
            for j in range(i, n + 1, i):
                phi[j] -= phi[j] // i
                if spf[j] == 0:
                    spf[j] = i
    spf[1] = 1
    is_prime = [False] * (n + 1)
    for i in range(2, n + 1):
        is_prime[i] = spf[i] == i
    return phi, spf, is_prime


def split(n, P, spf):
    s, t = 1, 1
    x = n
    while x > 1:
        p = spf[x]
        e = 0
        while x % p == 0:
            x //= p
            e += 1
        if p in P:
            s *= p ** e
        else:
            t *= p ** e
    return s, t


def c_P(n, P, spf, phi):
    s, t = split(n, P, spf)
    return phi[s] if t == 1 else phi[s] * (t - 1)


def rho_P(n, P, spf, phi):
    s, t = split(n, P, spf)
    return 0 if t == 1 else phi[s] * (t - 1 - phi[t])


def sigma(n, spf):
    s, x = 1, n
    while x > 1:
        p = spf[x]
        e = 0
        while x % p == 0:
            x //= p
            e += 1
        s *= (p ** (e + 1) - 1) // (p - 1)
    return s


def log2_int(n):
    n = abs(n)
    if n <= 1:
        return 0.0
    b = n.bit_length()
    return math.log2(n) if b <= 900 else (b - 200) + math.log2(n >> (b - 200))


def log2_frac(f):
    if f == 0:
        return float("-inf")
    return log2_int(f.numerator) - log2_int(f.denominator)


def bracket(coef, M):
    """[lo, hi] for sum_n coef(n) 2^-n given 0 <= coef(n) <= n; hi-lo = (2L+2)2^-L."""
    v = Fraction(0)
    for n in range(1, M + 1):
        c = coef(n)
        if c:
            v += Fraction(c, 1 << n)
    L = M + 1
    return v, v + Fraction(2 * L + 2, 1 << L)


NAMES = {0: "{}", 1: "{2}", 2: "{2,3}", 3: "{2,3,5}", 4: "{2,3,5,7}"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()
    M = 300 if args.quick else 420
    CHK = 3000 if args.quick else 8000
    NB = 700000 if args.quick else 900000
    phi, spf, is_prime = sieve(NB)

    Ps = [frozenset(), frozenset({2}), frozenset({2, 3}), frozenset({2, 3, 5}),
          frozenset({2, 3, 5, 7})]
    nm = {P: NAMES[len(P)] for P in Ps}

    print("## (2)/(3): phi(n) <= c_P(n) <= n, c_P(p) = p-1, Euler law inside P")
    for P in Ps:
        ok2 = all(phi[n] <= c_P(n, P, spf, phi) <= n for n in range(1, CHK + 1))
        okp = all(c_P(p, P, spf, phi) == p - 1
                  for p in range(2, CHK + 1) if is_prime[p])
        ok3 = all(c_P(p * n, P, spf, phi)
                  == ((p - 1) if n % p else p) * c_P(n, P, spf, phi)
                  for p in P for n in range(1, CHK // p + 1))
        print(f"   P={nm[P]:>9}: (2) {ok2}   c_P(p)=p-1 {okp}   (3) {ok3}")

    print("\n## (10) supplied Euler sieve phi(s_P)sigma(t_P) vs (1) c_P: first "
          "deviation from phi")
    print(f"{'P':>10} {'r':>3} {'sieve 1st idx':>14} {'coef-phi':>9} "
          f"{'c_P 1st idx':>12} {'coef-phi':>9}")
    for P in Ps[1:]:
        r = min(p for p in range(2, 200) if is_prime[p] and p not in P)
        e1 = next(n for n in range(1, 4 * r * r)
                  if phi[split(n, P, spf)[0]] * sigma(split(n, P, spf)[1], spf)
                  != phi[n])
        d1 = (phi[split(e1, P, spf)[0]] * sigma(split(e1, P, spf)[1], spf) - phi[e1])
        e2 = next(n for n in range(1, 4 * r * r) if rho_P(n, P, spf, phi))
        print(f"{nm[P]:>10} {r:>3} {e1:>14} {d1:>9} {e2:>12} "
              f"{c_P(e2,P,spf,phi)-phi[e2]:>9}")

    print("\n## (5) C_empty = 3/2 and (4) C_P - C_Q > 0")
    Cs = {}
    for P in Ps:
        Cs[P] = bracket(lambda n, P=P: c_P(n, P, spf, phi), M)
        print(f"   C_{nm[P]:<9} in [{float(Cs[P][0]):.16f}, {float(Cs[P][1]):.16f}]")
    print(f"   3/2 in bracket for C_empty : "
          f"{Cs[Ps[0]][0] <= Fraction(3,2) <= Cs[Ps[0]][1]}")
    for i in range(len(Ps) - 1):
        P, Q = Ps[i], Ps[i + 1]
        gap = Cs[P][0] - Cs[Q][1]
        print(f"   C_{nm[P]} - C_{nm[Q]} >= {float(gap):.4e} > 0 : {gap > 0}")

    print("\n## (6)/(7): C_P - S = (r-1)2^-r^2 + E_P, 0 <= E_P <= (2r^2+4r+2)2^-(r^2+2r)")
    print(f"{'P':>10} {'r':>3} {'idx1':>5} {'c1':>4} {'idx2':>5} {'c2':>4} "
          f"{'log2(C_P-S)':>12} {'log2 E_P':>10} {'(6) bound':>10} {'(6)':>5} {'(7)':>5}")
    for P in Ps[1:]:
        r = min(p for p in range(2, 200) if is_prime[p] and p not in P)
        rp = min(p for p in range(r + 1, 400) if is_prime[p])
        idx = [n for n in range(1, min(NB, 5 * r * r)) if rho_P(n, P, spf, phi)]
        lo, hi = bracket(lambda n, P=P: rho_P(n, P, spf, phi), M)
        lead = Fraction(r - 1, 1 << (r * r))
        lead2 = Fraction(r + rp - 2, 1 << (r * rp))
        b6 = Fraction(2 * r * r + 4 * r + 2, 1 << (r * r + 2 * r))
        ok6 = (lo - lead >= 0) and (hi - lead <= b6)
        ok7 = (lo > 0) and (hi < Fraction(r, 1 << (r * r)))
        print(f"{nm[P]:>10} {r:>3} {idx[0]:>5} {rho_P(idx[0],P,spf,phi):>4} "
              f"{idx[1]:>5} {rho_P(idx[1],P,spf,phi):>4} "
              f"{log2_frac(lo):>12.3f} {log2_frac(hi-lead):>10.3f} "
              f"{log2_frac(b6):>10.3f} {str(ok6):>5} {str(ok7):>5}")
        print(f"       idx1 == r^2 = {r*r}: {idx[0]==r*r} (coef r-1 = {r-1}: "
              f"{rho_P(r*r,P,spf,phi)==r-1});  idx2 == r*r' = {r*rp}: "
              f"{idx[1]==r*rp} (coef r+r'-2 = {r+rp-2}: "
              f"{rho_P(idx[1],P,spf,phi)==r+rp-2});  return's r^2+2r = {r*r+2*r}")
        print(f"       sharpened: C_P - S - (r-1)2^-r^2 - (r+r'-2)2^-rr' = "
              f"2^{log2_frac(hi-lead-lead2):.1f}  (return majorant "
              f"2^{log2_frac(b6):.1f})")

    print("\n## (16)/(17) Lemma 2: A_P = sum_{d|M_P} mu(d) 2^d/(2^d-1)^2 is rational")
    for P in Ps:
        MP = 1
        for p in P:
            MP *= p
        A = Fraction(0)
        for d in range(1, MP + 1):
            if MP % d:
                continue
            m = 1
            x = d
            while x > 1:
                p = spf[x]
                e = 0
                while x % p == 0:
                    x //= p
                    e += 1
                m = 0 if e >= 2 else -m
            if d == 1:
                m = 1
            if m:
                A += Fraction(m * (1 << d), ((1 << d) - 1) ** 2)
        lo, hi = bracket(
            lambda n, P=P: phi[split(n, P, spf)[0]] * split(n, P, spf)[1], M)
        print(f"   P={nm[P]:>9}: M_P={MP:>4}  A_P bracket-consistent {lo <= A <= hi}"
              f"   (2^M_P-1)^2 A_P integral "
              f"{(Fraction(((1 << MP)-1)**2) * A).denominator == 1}"
              f"   log2 den(A_P) = {log2_int(A.denominator):.1f}")

    print("\n## A_P as a RATIONAL approximant to S, and the (U) scale test")
    print("   A_P = sum_{d|M_P} mu(d) A_1(2^-d) is the P-smooth-divisor truncation of")
    print("   the Mobius-Lambert representation S = sum_{d>=1} mu(d) 2^d/(2^d-1)^2.")
    print(f"{'P':>10} {'r':>3} {'M_P':>5} {'log2 den(A_P)':>14} {'log2(A_P-S)':>12} "
          f"{'log2 q|A_P-S|':>14} {'2M_P<r^2 ?':>11}")
    for P in Ps[1:]:
        r = min(p for p in range(2, 200) if is_prime[p] and p not in P)
        MP = math.prod(P)
        A = Fraction(0)
        for d in range(1, MP + 1):
            if MP % d:
                continue
            m, x = 1, d
            while x > 1:
                p = spf[x]
                e = 0
                while x % p == 0:
                    x //= p
                    e += 1
                m = 0 if e >= 2 else -m
            if d == 1:
                m = 1
            if m:
                A += Fraction(m * (1 << d), ((1 << d) - 1) ** 2)
        lo, hi = bracket(
            lambda n, P=P: phi[split(n, P, spf)[0]]
            * (split(n, P, spf)[1] - phi[split(n, P, spf)[1]]), M)
        q = A.denominator
        print(f"{nm[P]:>10} {r:>3} {MP:>5} {log2_int(q):>14.1f} "
              f"{log2_frac(hi):>12.3f} {log2_int(q)+log2_frac(lo):>14.1f} "
              f"{str(2*MP < r*r):>11}")
    print("   A_P - S has leading term 2^-r (first non-P-smooth index).")
    print("   The (U) lattice test needs den(A_P)*eps_r < 1, i.e. 2 M_P < r^2 with")
    print("   M_P = prod_{p<r} p: true only for r = 3, 5, and false from r = 7 on:")
    print("   " + ", ".join(
        f"r={r}: 2M={2*math.prod(p for p in range(2, r) if is_prime[p])} vs r^2={r*r}"
        for r in (3, 5, 7, 11, 13, 17)))

    print("\n## Lemma 3 (23)-(25): h_P(N_L+m) = b_P(m) for m <= L; N_L+m never P-smooth")
    for P in Ps[1:4]:
        for L in ((12, 30) if args.quick else (12, 40)):
            NL = 1
            for p in sorted(P):
                a = 1
                while p ** a <= L:
                    a += 1
                NL *= p ** a
            ok, nonsmooth = True, True
            for m in range(1, L + 1):
                s, t = split(NL + m, P, spf)
                if t == 1:
                    nonsmooth = False
                h = phi[s] - (phi[NL + m] if t == 1 else 0)
                if h != phi[split(m, P, spf)[0]]:
                    ok = False
            print(f"   P={nm[P]:>9} L={L:>3} N_L={NL:>8}: (25) {ok}, "
                  f"N_L+m non-P-smooth {nonsmooth}, "
                  f"(27) N_L <= M_P L^|P| {NL <= math.prod(P) * L**len(P)}")

    print("\n## (44) sum_{n>=L} n 2^-n = (2L+2) 2^-L")
    for L in (1, 2, 3, 5, 10, 40):
        s = sum(Fraction(n, 1 << n) for n in range(L, L + 900))
        cl = Fraction(2 * L + 2, 1 << L)
        print(f"   L={L:>3}: closed form - truncated tail = 2^{log2_frac(cl-s):.1f} "
              f"(>0 and tiny: {0 < cl - s})")

    print("\n## failure certificate (51): x_r = 1 + (r-1)2^-r^2 + sqrt2 2^-(r^2+2r)")
    import decimal
    decimal.getcontext().prec = 400
    s2 = decimal.Decimal(2).sqrt()
    rs = [3, 5, 7, 11, 13]
    xs = {r: 1 + decimal.Decimal(r - 1) / (1 << (r * r))
          + s2 / (1 << (r * r + 2 * r)) for r in rs}
    print(f"   strictly decreasing to the RATIONAL limit 1: "
          f"{all(xs[rs[i]] > xs[rs[i+1]] for i in range(len(rs)-1))}")
    print("   (x_r - 1)/((r-1)2^-r^2) = "
          + ", ".join(f"{float((xs[r]-1)*(1 << (r*r))/(r-1)):.9f}" for r in rs))
    print("   every x_r and every positive rational combination of the differences "
          "x_r - x_s is irrational, yet lim x_r = 1 in Q.")


if __name__ == "__main__":
    main()
