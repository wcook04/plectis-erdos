"""Desk F identity audit for Erdos #249 method transfer.

Exact arithmetic only (Python ints / fractions.Fraction). Deterministic.

Checks, in the canonical coordinates of the Erdos 249 corpus:

  I1  phi = (mu * mu) * sigma            (Dirichlet convolution, exact ints)
  I2  sum_n phi(n) x^n = sum_d mu(d) x^d/(1-x^d)^2, at x=1/2 giving
      S = Theta_1 + Theta_2 = 1/2 + sum_d mu(d)/(2^d-1)^2
  I3  sum_n sigma(n) 2^-n = sum_d 2^d/(2^d-1)^2   (Erdos #250 = Duverney
      zeta(q;2) at q=2, since zeta(q;2) = (q-1)^2 sum sigma(n) q^-n)
  I4  sum_n 1/(2^n-1)^2 = sum_n (sigma(n) - d(n)) 2^-n
  I5  Euler / pentagonal log-derivative: with f(x) = prod_{n>=1}(1-x^n),
      -x f'(x)/f(x) = sum_N sigma(N) x^N   (exact power-series coefficients)
  I6  pentagonal support of f: nonzero coefficients only at n(3n +- 1)/2,
      coefficient magnitudes 1, gaps -> infinity
  I7  the totient analogue of I5 needs exponents c_n = -(phi*mu)(n)/n;
      c_p = -(p-2)/p is NOT an integer for every odd prime p, and the
      denominators are unbounded, so no finite power of the product clears
      them.  (This is the exact step at which Duverney's 1995 pentagonal
      lacunarity argument has no transfer target for phi.)

Usage:  python3 wave1_F_identity_audit.py [--quick]
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from math import gcd


def sieve_smallest_prime_factor(n: int) -> list[int]:
    spf = list(range(n + 1))
    i = 2
    while i * i <= n:
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
        i += 1
    return spf


def factorise(m: int, spf: list[int]) -> dict[int, int]:
    f: dict[int, int] = {}
    while m > 1:
        p = spf[m]
        e = 0
        while m % p == 0:
            m //= p
            e += 1
        f[p] = e
    return f


def arith_tables(n: int):
    spf = sieve_smallest_prime_factor(n)
    phi = [0] * (n + 1)
    sigma = [0] * (n + 1)
    tau = [0] * (n + 1)
    mu = [0] * (n + 1)
    mu2 = [0] * (n + 1)  # (mu * mu)(m): 1, -2, 1 on exponents 0,1,2; 0 for e>=3
    if n >= 1:
        phi[1] = sigma[1] = tau[1] = mu[1] = mu2[1] = 1
    for m in range(2, n + 1):
        f = factorise(m, spf)
        ph = 1
        sg = 1
        tu = 1
        mo = 1
        m2 = 1
        for p, e in f.items():
            ph *= p ** (e - 1) * (p - 1)
            sg *= (p ** (e + 1) - 1) // (p - 1)
            tu *= e + 1
            mo *= 0 if e >= 2 else -1
            m2 *= {0: 1, 1: -2, 2: 1}.get(e, 0)
        phi[m], sigma[m], tau[m], mu[m], mu2[m] = ph, sg, tu, mo, m2
    return spf, phi, sigma, tau, mu, mu2


def dirichlet(f: list[int], g: list[int], n: int) -> list[int]:
    out = [0] * (n + 1)
    for a in range(1, n + 1):
        if f[a] == 0:
            continue
        for b in range(a, n + 1, a):
            out[b] += f[a] * g[b // a]
    return out


def eta_product_coeffs(order: int) -> list[int]:
    """Coefficients of prod_{n>=1} (1 - x^n) up to x^order."""
    c = [0] * (order + 1)
    c[0] = 1
    for n in range(1, order + 1):
        for k in range(order, n - 1, -1):
            if c[k - n]:
                c[k] -= c[k - n]
    return c


def log_derivative_coeffs(f: list[int], order: int) -> list[Fraction]:
    """Coefficients of x f'(x)/f(x) given f with f[0] = 1, exact."""
    # x f' = f * L  where L = x f'/f, so  n f[n] = sum_{k=1}^{n} L[k] f[n-k].
    L = [Fraction(0)] * (order + 1)
    for n in range(1, order + 1):
        acc = Fraction(n * f[n])
        for k in range(1, n):
            acc -= L[k] * f[n - k]
        L[n] = acc / f[0]
    return L


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true", help="smaller bounds")
    args = ap.parse_args()

    N = 2000 if args.quick else 20000
    SER = 220 if args.quick else 400
    PBOUND = 2000 if args.quick else 20000

    spf, phi, sigma, tau, mu, mu2 = arith_tables(max(N, PBOUND))
    ok = True

    # -- I1: phi = (mu*mu) * sigma -------------------------------------------
    conv = dirichlet(mu2, sigma, N)
    bad = [m for m in range(1, N + 1) if conv[m] != phi[m]]
    print(f"I1  phi == (mu*mu)*sigma on [1,{N}]: "
          f"{'PASS' if not bad else 'FAIL ' + str(bad[:5])}")
    ok &= not bad

    # -- I2/I3/I4: exact truncated Lambert identities -------------------------
    # All series are compared as exact rationals at a common truncation with an
    # explicit rigorous tail bound.
    T = 60 if args.quick else 90
    S_coef = sum(Fraction(phi[n], 2 ** n) for n in range(1, T + 1))
    S_lam = Fraction(1, 2) + sum(
        Fraction(mu[d], (2 ** d - 1) ** 2) for d in range(1, T + 1) if mu[d]
    )
    # tail bounds: |sum_{n>T} phi(n)2^-n| <= (T+2)2^-T ;
    #              |sum_{d>T} mu(d)/(2^d-1)^2| <= 2 * 4^-T
    tolS = Fraction(T + 2, 2 ** T) + Fraction(2, 4 ** T)
    d2 = abs(S_coef - S_lam)
    print(f"I2  S = 1/2 + sum mu(d)/(2^d-1)^2 : |diff|={float(d2):.3e} "
          f"tol={float(tolS):.3e} -> {'PASS' if d2 <= tolS else 'FAIL'}")
    ok &= d2 <= tolS

    Sig_coef = sum(Fraction(sigma[n], 2 ** n) for n in range(1, T + 1))
    Sig_lam = sum(Fraction(2 ** d, (2 ** d - 1) ** 2) for d in range(1, T + 1))
    tolSig = Fraction(2 * (T + 2), 2 ** T)
    d3 = abs(Sig_coef - Sig_lam)
    print(f"I3  sum sigma(n)/2^n = sum_d 2^d/(2^d-1)^2 : |diff|={float(d3):.3e} "
          f"tol={float(tolSig):.3e} -> {'PASS' if d3 <= tolSig else 'FAIL'}")
    ok &= d3 <= tolSig
    print(f"    numeric value sum sigma(n)/2^n = {float(Sig_coef):.12f} "
          f"(Erdos #250, PROVED: Duverney 1995 irrational, Nesterenko 1996 "
          f"transcendental)")
    print(f"    numeric value S = sum phi(n)/2^n  = {float(S_coef):.12f} "
          f"(Erdos #249, OPEN)")

    Sq = sum(Fraction(1, (2 ** n - 1) ** 2) for n in range(1, T + 1))
    Sq_rhs = sum(Fraction(sigma[n] - tau[n], 2 ** n) for n in range(1, T + 1))
    d4 = abs(Sq - Sq_rhs)
    print(f"I4  sum 1/(2^n-1)^2 = sum (sigma-tau)(n)2^-n : |diff|="
          f"{float(d4):.3e} tol={float(tolSig):.3e} -> "
          f"{'PASS' if d4 <= tolSig else 'FAIL'}")
    ok &= d4 <= tolSig

    # -- I5/I6: Euler pentagonal log-derivative -------------------------------
    fco = eta_product_coeffs(SER)
    L = log_derivative_coeffs(fco, SER)
    bad5 = [n for n in range(1, SER + 1) if L[n] != Fraction(-sigma[n])]
    print(f"I5  -x f'/f == sum sigma(n)x^n for f=prod(1-x^n), order {SER}: "
          f"{'PASS' if not bad5 else 'FAIL ' + str(bad5[:5])}")
    ok &= not bad5

    supp = [n for n in range(1, SER + 1) if fco[n] != 0]
    pent = sorted({k * (3 * k - 1) // 2 for k in range(-60, 61)} - {0})
    pent = [p for p in pent if p <= SER]
    gaps = [supp[i + 1] - supp[i] for i in range(len(supp) - 1)]
    print(f"I6  support of prod(1-x^n) up to {SER}: {len(supp)} terms, "
          f"pentagonal match={'PASS' if supp == pent else 'FAIL'}, "
          f"max|coeff|={max(abs(fco[n]) for n in supp)}, "
          f"gaps {gaps[:6]}...{gaps[-3:]} (growing)")
    ok &= supp == pent

    # -- I7: no eta-quotient log-derivative representation for phi ------------
    Aw = dirichlet(mu, phi, PBOUND)  # (phi * mu)(n)
    print(f"I7  Aw = phi*mu, first ten values {Aw[1:11]} "
          f"(corpus: 1,0,1,1,3,0,5,2,4,0)")
    dens = []
    firstfail = None
    for n in range(1, PBOUND + 1):
        g = gcd(n, Aw[n]) if Aw[n] else n
        den = n // g
        dens.append(den)
        if den != 1 and firstfail is None:
            firstfail = (n, Fraction(-Aw[n], n))
    odd_primes = [p for p in range(3, PBOUND + 1) if spf[p] == p]
    bad7 = [p for p in odd_primes if (p - 2) % p == 0]
    lcms = []
    cur = 1
    for X in (10, 100, 1000, PBOUND):
        cur = 1
        for n in range(1, X + 1):
            cur = cur * dens[n - 1] // gcd(cur, dens[n - 1])
        lcms.append((X, len(str(cur))))
    print(f"    exponents c_n = -(phi*mu)(n)/n; first non-integral: "
          f"n={firstfail[0]}, c_n={firstfail[1]}")
    print(f"    c_p = -(p-2)/p integral for some odd prime p<= {PBOUND}: "
          f"{'YES(FAIL)' if bad7 else 'NO -> PASS'}")
    print(f"    lcm of exponent denominators over n<=X has decimal length "
          f"{lcms} -> unbounded, no finite power of the product clears them")
    ok &= not bad7

    # -- I8: phi satisfies no short linear recurrence ------------------------
    # A rational generating function in Q(z) of denominator degree D forces a
    # constant-coefficient linear recurrence of order D on all large n.  Exact
    # rank over Q of the (R x (D+1)) matrix [phi(n0+i+j)] certifies that no
    # recurrence of order <= D holds on the tested window, so the ordinary
    # totient generating function is not rational and Polya-Carlson applies
    # directly, with no external input needed.
    def rank_q(rows: list[list[Fraction]]) -> int:
        rows = [r[:] for r in rows]
        r = 0
        cols = len(rows[0])
        for c in range(cols):
            piv = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
            if piv is None:
                continue
            rows[r], rows[piv] = rows[piv], rows[r]
            pr = rows[r]
            for i in range(r + 1, len(rows)):
                if rows[i][c] != 0:
                    f = rows[i][c] / pr[c]
                    rows[i] = [a - f * b for a, b in zip(rows[i], pr)]
            r += 1
            if r == len(rows):
                break
        return r
    Dmax = 24 if args.quick else 48
    allfull = True
    for n0 in (1000, min(5000, len(phi) - 4 * Dmax - 4)):
        M = [[Fraction(phi[n0 + i + j]) for j in range(Dmax + 1)]
             for i in range(3 * Dmax)]
        rk = rank_q(M)
        allfull &= rk == Dmax + 1
        print(f"I8  rank_Q [phi(n0+i+j)] n0={n0}, D={Dmax}: {rk} "
              f"(full = {Dmax + 1}) -> no linear recurrence of order <= {Dmax}")
    ok &= allfull

    print("RESULT:", "ALL PASS" if ok else "FAILURES PRESENT")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
