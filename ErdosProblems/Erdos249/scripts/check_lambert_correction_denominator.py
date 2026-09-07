"""Erdos 249: exact checks for the signed-Lambert-correction denominator theory.

Audits, by exact integer / Fraction computation, the arithmetic claims of the
prime-or-height return (batch erdos249_20260905_eight_return_stream_01, r07):

  * kappa = prod_p (1 - 2/p^2 + 1/p^3), computed two ways;
  * log2 den(T_N) / N^2 -> kappa, where T_N = sum_{d<=N} mu(d)/(2^d-1)^2;
  * the divisibility certificate (W_N/gcd(W_N,D_N))^2 | den(R_N), including
    D_N > 1 and nonzero signed corrections;
  * den(T_N) | prod_{m<=N squarefree} Phi_m(2)^2;
  * the section-5 exact example N=13 (C_91 = C_143 = 0, C_77 = 2,
    Phi_77(2) | den(R_13));
  * the theta-derivative Lambert identities
        sum_d mu(d) d^k A_k(2^{-jd}) = 2^{-j}   (A_k(y) = sum_m m^k y^m),
    their exact divisor-sum core, and S = sum_d mu(d) A_1(2^{-d});
  * the exact rational coincidence T_2 - (1/2 - U_2) = 3/2;
  * Theorem 2 (q_N |Theta - R_N| -> infinity) on the jet-matching family;
  * the height threshold for cancelling a (2^d-1)^2 layer with derivative
    (k=1) corrections.

Run:  ./repo-python <this file> --quick
      ./repo-python <this file>
"""

from __future__ import annotations

import argparse
import math
from fractions import Fraction

# --------------------------------------------------------------- elementary


def sieve_mu(n):
    mu = [1] * (n + 1)
    primes = []
    composite = [False] * (n + 1)
    for i in range(2, n + 1):
        if not composite[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            if i * p > n:
                break
            composite[i * p] = True
            if i % p == 0:
                mu[i * p] = 0
                break
            mu[i * p] = -mu[i]
    mu[0] = 0
    return mu, primes


def sieve_phi(n):
    phi = list(range(n + 1))
    for i in range(2, n + 1):
        if phi[i] == i:
            for j in range(i, n + 1, i):
                phi[j] -= phi[j] // i
    return phi


def divisors(n):
    ds = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            ds.append(i)
            if i != n // i:
                ds.append(n // i)
        i += 1
    return sorted(ds)


def cyclotomic_at_2(m, mu):
    """Phi_m(2) as an exact integer, via prod_{d|m} (2^d - 1)^{mu(m/d)}."""
    num, den = 1, 1
    for d in divisors(m):
        e = mu[m // d]
        if e == 1:
            num *= (1 << d) - 1
        elif e == -1:
            den *= (1 << d) - 1
    assert num % den == 0
    return num // den


def log2_int(n):
    n = abs(n)
    if n <= 1:
        return 0.0
    b = n.bit_length()
    if b <= 900:
        return math.log2(n)
    return (b - 200) + math.log2(n >> (b - 200))


def log2_frac(f):
    if f == 0:
        return float("-inf")
    return log2_int(f.numerator) - log2_int(f.denominator)


# --------------------------------------------------------------- kappa


def kappa_accelerated(limit):
    """kappa = zeta(2)^{-2} * prod_p (1 + 1/((p-1)(p+1)^2)).

    Identity: (1 - 2x^2 + x^3) = (1 - x^2)^2 * (1 + x^3/((1-x)(1+x)^2)) at x=1/p.
    """
    _, primes = sieve_mu(limit)
    acc = 0.0
    for p in primes:
        acc += math.log1p(1.0 / ((p - 1) * (p + 1) ** 2))
    zeta2 = math.pi ** 2 / 6.0
    tail = 1.0 / (2.0 * limit ** 2)
    return math.exp(acc) / zeta2 ** 2, tail


def kappa_direct(limit):
    _, primes = sieve_mu(limit)
    acc = 0.0
    for p in primes:
        acc += math.log(1.0 - 2.0 / p ** 2 + 1.0 / p ** 3)
    return math.exp(acc)


# --------------------------------------------------------------- approximants


def T_prefix(N, mu):
    s = Fraction(0)
    for d in range(1, N + 1):
        if mu[d]:
            s += Fraction(mu[d], ((1 << d) - 1) ** 2)
    return s


def A1(j, d):
    """A_1(2^{-jd}) = 2^{jd}/(2^{jd}-1)^2 as an exact Fraction."""
    return Fraction(1 << (j * d), ((1 << (j * d)) - 1) ** 2)


def L_prefix(j, N, mu):
    s = Fraction(0)
    for d in range(1, N + 1):
        if mu[d]:
            s += Fraction(mu[d], (1 << (j * d)) - 1)
    return s


def U_prefix(j, N, mu):
    s = Fraction(0)
    for d in range(1, N + 1):
        if mu[d]:
            s += mu[d] * d * A1(j, d)
    return s


def build_R(N, D, a0, a1, mu):
    """R_N = T_N + (1/D) [ sum_j a0_j (2^-j - L_{j,N}) + sum_j a1_j (2^-j - U_{j,N}) ]."""
    acc = T_prefix(N, mu) * D
    for j, c in a0.items():
        if c:
            acc += c * (Fraction(1, 1 << j) - L_prefix(j, N, mu))
    for j, c in a1.items():
        if c:
            acc += c * (Fraction(1, 1 << j) - U_prefix(j, N, mu))
    return acc / D


def theta_minus_R(N, D, a0, a1, mu, extra=40):
    """Theta - R_N = (1/D) sum_{d>N} mu(d) G_N(2^{-d}); exact to 2^{-r*extra}."""
    tot = Fraction(0)
    for d in range(N + 1, N + extra + 1):
        if not mu[d]:
            continue
        g = Fraction(D, ((1 << d) - 1) ** 2)
        for j, c in a0.items():
            if c:
                g -= c * Fraction(1, (1 << (j * d)) - 1)
        for j, c in a1.items():
            if c:
                g -= c * d * A1(j, d)
        tot += mu[d] * g
    return tot / D


def W_certificate(N, mu, primes):
    """W_N of the return's (27): squarefree m in (N/(K+1), N], primes ell > N."""
    K = max(1, int(math.floor(math.sqrt(math.log(N))))) if N > 2 else 1
    lo = N / (K + 1)
    w = 1
    for m in range(1, N + 1):
        if mu[m] == 0 or m <= lo:
            continue
        v = cyclotomic_at_2(m, mu)
        for p in primes:
            if p > N:
                break
            while v % p == 0:
                v //= p
        w *= v
    return w, K


# --------------------------------------------------------------- reports


def report_kappa(limit):
    ks, tail = kappa_accelerated(limit)
    kd = kappa_direct(min(limit, 200000))
    print("## kappa = prod_p (1 - 2/p^2 + 1/p^3)")
    print(f"   accelerated (primes <= {limit}) : {ks:.12f}  (tail < {tail:.2e})")
    print(f"   naive product (primes <= {min(limit,200000)}) : {kd:.12f}"
          f"   [naive tail ~ 2*sum_{{p>x}}p^-2 ~ {2/(min(limit,200000)*math.log(min(limit,200000))):.1e}]")
    return ks


def report_denominators(Ns, mu, primes, ks):
    print("\n## (6) log2 den(T_N)/N^2 -> kappa ; (28) W_N^2 | den(T_N) ; "
          "(30) den(T_N) | prod Phi_m(2)^2")
    phi = sieve_phi(max(Ns))
    print(f"{'N':>4} {'log2 den(T_N)':>14} {'ratio/N^2':>10} "
          f"{'2*sum_sf phi/N^2':>17} {'W_N^2|den':>10} {'den|prodPhi^2':>14}")
    for N in Ns:
        den = T_prefix(N, mu).denominator
        ld = log2_int(den)
        sf = sum(phi[m] for m in range(1, N + 1) if mu[m])
        w, _ = W_certificate(N, mu, primes)
        prod = 1
        for m in range(1, N + 1):
            if mu[m]:
                prod *= cyclotomic_at_2(m, mu) ** 2
        print(f"{N:>4} {ld:>14.2f} {ld/N**2:>10.6f} {2*sf/N**2:>17.6f} "
              f"{str(den % (w*w) == 0):>10} {str(prod % den == 0):>14}")
    print(f"   target kappa = {ks:.8f}")


def report_certificate_with_D(mu, primes, Ns):
    """(28) with D_N > 1 and nonzero signed k=0 corrections (deterministic LCG)."""
    print("\n## (28) certificate (W_N/gcd(W_N,D_N))^2 | q_N with D_N>1 and signed a_j")
    seed = 12345
    print(f"{'N':>4} {'D':>5} {'max|a_j|':>9} {'cert holds':>11} "
          f"{'log2 q_N':>10} {'log2 cert^2':>12}")
    for N in Ns:
        seed = (1103515245 * seed + 12345) % (1 << 31)
        D = 1 + seed % 30
        a0 = {}
        for j in range(1, N + 1):
            seed = (1103515245 * seed + 12345) % (1 << 31)
            a0[j] = (seed % 41) - 20
        R = build_R(N, D, a0, {}, mu)
        w, _ = W_certificate(N, mu, primes)
        cert = (w // math.gcd(w, D)) ** 2
        print(f"{N:>4} {D:>5} {max(abs(v) for v in a0.values()):>9} "
              f"{str(R.denominator % cert == 0):>11} "
              f"{log2_int(R.denominator):>10.1f} {log2_int(cert):>12.1f}")


def report_n13(mu):
    print("\n## section-5 exact example: N=13, D=1, a_13=1, a_7=a_11=-1")
    N, a0 = 13, {13: 1, 7: -1, 11: -1}
    R = build_R(N, 1, a0, {}, mu)
    c91 = -a0[13] + mu[13] * a0[7]
    c143 = -a0[13] + mu[13] * a0[11]
    c77 = a0[7] * mu[11] + a0[11] * mu[7]
    phi77 = cyclotomic_at_2(77, mu)
    print(f"   C_91 = {c91}, C_143 = {c143}, C_77 = {c77}   (return claims 0, 0, 2)")
    print(f"   Phi_77(2) = (2^77-1)/((2^7-1)(2^11-1)) has {phi77.bit_length()} bits")
    print(f"   Phi_77(2)   | den(R_13) : {R.denominator % phi77 == 0}")
    print(f"   Phi_77(2)^2 | den(R_13) : {R.denominator % (phi77**2) == 0}"
          "   [first power only: the pair layer is a SIMPLE pole]")
    print(f"   log2 den(R_13) = {log2_int(R.denominator):.2f} vs "
          f"log2 den(T_13) = {log2_int(T_prefix(13, mu).denominator):.2f}")


def report_derivative_identities(mu, nmax, kmax, dmax):
    print("\n## theta-derivative Lambert identities")
    ok = True
    for k in range(kmax + 1):
        for n in range(1, nmax + 1):
            s = sum(mu[d] * d ** k * (n // d) ** k for d in divisors(n))
            if s != (1 if n == 1 else 0):
                ok = False
    print(f"   exact core  sum_{{d|n}} mu(d) d^k (n/d)^k = [n=1]  for n<={nmax}, "
          f"k<={kmax} : {ok}")
    for k in (0, 1):
        for j in (1, 2, 3):
            s = Fraction(0)
            for d in range(1, dmax + 1):
                if mu[d]:
                    s += mu[d] * d ** k * (Fraction(1, (1 << (j * d)) - 1) if k == 0
                                           else A1(j, d))
            err = s - Fraction(1, 1 << j)
            print(f"   k={k} j={j}: |sum_{{d<={dmax}}} - 2^-j| = "
                  f"2^({log2_frac(err):.1f})")
    # S = sum_d mu(d) A_1(2^{-d}) with NO weight d
    phi = sieve_phi(400)
    Sk1 = sum(mu[d] * A1(1, d) for d in range(1, dmax + 1) if mu[d])
    Sdir = sum(Fraction(phi[n], 1 << n) for n in range(1, 350))
    print(f"   S = sum_d mu(d) A_1(2^-d) vs sum_n phi(n)2^-n : difference "
          f"2^({log2_frac(Sk1 - Sdir):.1f})  [tail-limited]")
    T2 = T_prefix(2, mu)
    U2 = U_prefix(1, 2, mu)
    val = T2 - (Fraction(1, 2) - U2)
    print(f"   (54): T_2 = {T2}, U_2 = {U2}, T_2 - (1/2 - U_2) = {val}  "
          f"[= 3/2 : {val == Fraction(3, 2)}]")
    print("   layer identity behind (54): 1 + d*2^d = (2^d-1)^2 has the unique "
          f"solution d=2 : {[d for d in range(1, 40) if 1 + d*(1 << d) == ((1 << d)-1)**2]}")


def report_theorem2(mu, Ns):
    print("\n## Theorem 2 on the jet-matching family D=1, a_j = phi(j) (2<=j<=J=N//2)")
    phi = sieve_phi(max(Ns) + 4)
    print(f"{'N':>4} {'J':>4} {'r_N':>5} {'nu_N':>5} {'log2 q_N':>10} "
          f"{'log2|Th-R|':>12} {'-r_N nu_N':>10} {'log2 q|Th-R|':>13}")
    for N in Ns:
        J = max(1, N // 2)
        a0 = {j: phi[j] for j in range(2, J + 1)}
        R = build_R(N, 1, a0, {}, mu)
        err = theta_minus_R(N, 1, a0, {}, mu)
        rN, n = None, 1
        while rN is None:
            c = (n - 1) - sum(a0.get(j, 0) for j in divisors(n) if j <= N)
            if c != 0:
                rN = n
            n += 1
        nu = next(d for d in range(N + 1, N + 40) if mu[d])
        lq, le = log2_int(R.denominator), log2_frac(err)
        print(f"{N:>4} {J:>4} {rN:>5} {nu:>5} {lq:>10.1f} {le:>12.1f} "
              f"{-rN*nu:>10} {lq+le:>13.1f}")


def report_k1_layers(mu, Nmax):
    print("\n## derivative (k=1) corrections DO reach valuation -2e: layer cancellation")
    print("   layer d of D*T_N + b_1*(...) has numerator mu(d)(D - b_1 d 2^d) over "
          "(2^d-1)^2")
    print(f"{'d':>3} {'(2^d-1)^2 bits':>15} {'min |b_1| (D=1)':>16} "
          f"{'2^d/d':>10} {'bits saved':>11}")
    for d in range(2, Nmax + 1):
        if not mu[d]:
            continue
        M = ((1 << d) - 1) ** 2
        try:
            inv = pow((d << d) % M, -1, M)
            b = min(inv % M, M - (inv % M))
        except ValueError:
            b = None
        print(f"{d:>3} {M.bit_length():>15} {str(b):>16} {(1 << d)/d:>10.1f} "
              f"{2*math.log2((1 << d)-1):>11.2f}")
    print("   (b_1 d 2^d - D) != 0 and divisible by (2^d-1)^2 forces")
    print("   max(D,|b_1|) >= ((2^d-1)^2 - 1)/(d 2^d + 1) > 2^d/d - 1,")
    print("   and (b_1 d 2^d - D) = 0 forces D >= d 2^d.  Either way H >= 2^d/d - 1.")


def report_k1_box(mu, Nmax, B):
    print(f"\n## box search R_N = T_N + sum_{{j=1..3}} b_j (2^-j - U_{{j,N}}), "
          f"|b_j| <= {B}")
    print(f"{'N':>3} {'log2 den(T_N)':>14} {'best log2 q':>12} {'(b1,b2,b3)':>14} "
          f"{'bits saved':>11} {'log2 q|Th-R|':>13}")
    for N in range(2, Nmax + 1):
        base = log2_int(T_prefix(N, mu).denominator)
        X = {j: Fraction(1, 1 << j) - U_prefix(j, N, mu) for j in (1, 2, 3)}
        T0 = T_prefix(N, mu)
        best = None
        for b1 in range(-B, B + 1):
            r1 = T0 + b1 * X[1]
            for b2 in range(-B, B + 1):
                r2 = r1 + b2 * X[2]
                for b3 in range(-B, B + 1):
                    q = (r2 + b3 * X[3]).denominator
                    if best is None or q < best[0]:
                        best = (q, (b1, b2, b3))
        b = best[1]
        a1 = {1: b[0], 2: b[1], 3: b[2]}
        err = theta_minus_R(N, 1, {}, a1, mu)
        lq, le = log2_int(best[0]), log2_frac(err)
        print(f"{N:>3} {base:>14.2f} {lq:>12.2f} {str(b):>14} "
              f"{base-lq:>11.2f} {lq+le:>13.1f}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true",
                    help="smaller deterministic ranges")
    args = ap.parse_args()

    if args.quick:
        Ns = [4, 8, 12, 16, 20, 30, 40, 50, 60]
        klimit, nmax, dmax = 200000, 200, 40
        thm2 = [6, 8, 10, 12, 16, 20, 24]
        boxN, boxB = 12, 8
    else:
        Ns = [4, 8, 12, 16, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110, 120]
        klimit, nmax, dmax = 1000000, 400, 60
        thm2 = [6, 8, 10, 12, 16, 20, 24, 28, 32, 36, 40]
        boxN, boxB = 12, 12

    mu, primes = sieve_mu(max(4000, 40 * max(Ns)))
    ks = report_kappa(klimit)
    report_denominators(Ns, mu, primes, ks)
    report_certificate_with_D(mu, primes, [8, 12, 16, 20, 24])
    report_n13(mu)
    report_derivative_identities(mu, nmax, 4, dmax)
    report_theorem2(mu, thm2)
    report_k1_layers(mu, 14)
    report_k1_box(mu, boxN, boxB)


if __name__ == "__main__":
    main()
